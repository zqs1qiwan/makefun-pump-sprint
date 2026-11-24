// pump-sprint: a fast launch-sniper paper-trading bot for the pump.fun replay
// (agent-fun/replay/v2). Single file, Node 22 stdlib only, no dependencies.
//
// How it works:
//  - Every coin is watched from its CreateEvent. In its first few slots the bot
//    reads the opening tape: how big the creator's own buy was, how many other
//    wallets piled in (a launch bundled by many wallets is usually the creator's
//    cluster waiting to dump), whether the creator has already sold, and how
//    much real SOL the curve holds. Only launches that pass the filter get
//    bought, with a small 0.10 SOL stake.
//  - Exits are fast: take profit at +15%, cut at -12%, never hold past ~30
//    slots, leave at once when the creator sells. A partial take-profit sells
//    half at +8% and lets the rest ride under a tight trailing stop.
//  - Guardrail pacing: the run needs round trips on at least 20 coins. When the
//    bot's own fills or distinct coins lag the pace, it opens tiny 0.02 SOL
//    probe round trips on liquid curves and sells them as soon as the buy lands.
//  - Deterministic by construction: no clock, no randomness, no environment;
//    every iteration is over insertion-ordered maps fed by the batch stream.

const LAMPORTS_PER_SOL = 1_000_000_000n;
const BPS = 10_000n;
// Curve fee estimate: protocol 95 bps + creator 30 bps fallback.
const CURVE_FEE_BPS = 125n;
const MAX_SLIPPAGE_BUY_BPS = 10_000;
const MAX_SLIPPAGE_SELL_BPS = 10_000;

// ---- strategy parameters (SOL units unless noted) -------------------------
const P = {
  minAgeSlots: 0, // youngest age (slots since create) at which a coin may be bought
  maxAgeSlots: 3, // oldest age at which a first buy may still be decided
  stakeSol: 0.1, // SOL to aim for per coin in total
  minBuySol: 0.01, // smallest single buy worth paying the tx fee for
  minRqSol: 0.3, // real SOL reserve window at decision time
  maxRqSol: 30,
  maxDevBuySol: 2.5, // creator's own buys in the create slot, at most
  minBuyers: 3, // distinct non-creator buyers before entry, at least
  maxBuyers: 3, // distinct non-creator buyers before entry, at most
  maxRunup: 2.0, // price now over the create price, at most
  tp1Up: 10.0, // first take-profit: sell tp1Part of the position at this gain
  tp1Part: 0.5,
  tpUp: 0.25, // exit when the position is worth this much over its cost
  slDown: 0.08, // exit when it is worth this much under its cost
  slAfterTp1Down: 0.02, // after the first take-profit, stop out at this loss
  trailArmUp: 10.0, // trailing stop arms once value is up this much
  trailDown: 0.05, // exit on a fall of this much from the best value
  maxHoldSlots: 15, // exit after holding this many slots
  targetCoins: 25, // guardrail pacing targets
  targetFills: 200,
  paceSecs: 21_600, // 6h final window; pace saturates at 1 after that
  probeSol: 0.02,
  maxProbes: 1,
  maxExposureSol: 2.5,
};

// ---------------------------------------------------------------------------
// Types (loose: the harness speaks JSON, we only touch the fields we use).
// ---------------------------------------------------------------------------
type Mint = string;

interface Curve {
  mint: Mint;
  createdSlot: number | null;
  vq: bigint; // virtual quote (SOL) reserves
  vt: bigint; // virtual token reserves
  rq: bigint; // real quote (SOL) reserves
  rt: bigint; // real token reserves
  reservesSlot: number;
  complete: boolean;
}

interface Held {
  openedSlot: number;
  peakValue: bigint; // best close value seen, lamports
  tookTp1: boolean;
  exiting: boolean;
  filled: boolean;
}

/** Opening-tape state for one young coin. */
interface Coin {
  createdSlot: number;
  creator: Mint;
  vq0: bigint; // create-time virtual reserves (for the run-up measure)
  vt0: bigint;
  devBuy: bigint; // creator's own buys in the create slot, lamports
  devSold: boolean;
  buyers: Set<Mint>; // distinct non-creator buyers
  bought: bigint; // SOL bought by non-creator wallets
  soldByOthers: bigint; // SOL sold by non-creator wallets
  lastTradeSlot: number;
  done: boolean; // never buy it again
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------
const solToLamports = (sol: number): bigint => BigInt(Math.floor(sol * 1e9));
const lamportsToSol = (lam: bigint): number => Number(lam) / 1e9;

/** Price of one token in SOL, from virtual reserves. */
const priceOf = (vq: bigint, vt: bigint): number =>
  vt === 0n ? 0 : Number(vq) / Number(vt);

/** Estimated SOL received for selling `tokens` into the curve, curve + tx fees out. */
function sellValueLamports(tokens: bigint, vq: bigint, vt: bigint, txFee: bigint): bigint {
  if (tokens === 0n || vt === 0n) return 0n;
  const gross = (tokens * vq) / (vt + tokens);
  const afterCurveFee = (gross * (BPS - CURVE_FEE_BPS)) / BPS;
  const net = afterCurveFee - txFee;
  return net > 0n ? net : 0n;
}

/** Compare value against cost * (1 + frac), with frac in thousandths, in bigint. */
function valueAtLeast(value: bigint, cost: bigint, fracThousandths: number): boolean {
  return value * 1000n >= cost * BigInt(1000 + fracThousandths);
}
function valueBelow(value: bigint, cost: bigint, fracThousandths: number): boolean {
  return value * 1000n < cost * BigInt(1000 + fracThousandths);
}

// ---------------------------------------------------------------------------
// Bot state
// ---------------------------------------------------------------------------
let hello: any = null;
let cash = 0n;
const positions = new Map<Mint, { tokens: bigint; cost: bigint }>();
const curves = new Map<Mint, Curve>();
const pending = new Map<string, { mint: Mint; side: string; amount: bigint }>();
const coins = new Map<Mint, Coin>();
const held = new Map<Mint, Held>();
const probes = new Map<Mint, boolean>(); // false = buying, true = selling
const myCoins = new Set<Mint>();
let myFills = 0;
let firstBlockTime: number | null = null;
let lastBlockTime: number | null = null;
let orderSeq = 0;

function coinOf(mint: Mint, slot: number): Coin {
  let c = coins.get(mint);
  if (c === undefined) {
    c = {
      createdSlot: slot,
      creator: '',
      vq0: 0n,
      vt0: 1n,
      devBuy: 0n,
      devSold: false,
      buyers: new Set(),
      bought: 0n,
      soldByOthers: 0n,
      lastTradeSlot: slot,
      done: false,
    };
    coins.set(mint, c);
  }
  return c;
}

function curveOf(mint: Mint, slot: number): Curve {
  let c = curves.get(mint);
  if (c === undefined) {
    c = {
      mint,
      createdSlot: null,
      vq: 0n,
      vt: 0n,
      rq: 0n,
      rt: 0n,
      reservesSlot: slot,
      complete: false,
    };
    curves.set(mint, c);
  }
  return c;
}

function txFeeLamports(): bigint {
  return BigInt(hello.fees.base_fee_lamports) + BigInt(hello.fees.priority_fee_lamports);
}

function maxBuyLamports(mint: Mint): bigint {
  const c = curves.get(mint);
  if (c === undefined || c.complete) return 0n;
  return (c.rq * BigInt(hello.caps.max_order_bps_of_real_reserve)) / BPS;
}

function committedPositionCount(): number {
  const mints = new Set<Mint>(positions.keys());
  for (const p of pending.values()) if (p.side === 'buy') mints.add(p.mint);
  return mints.size;
}

function freeCashLamports(): bigint {
  const tx = txFeeLamports();
  let free = cash;
  for (const p of pending.values()) {
    free -= tx;
    if (p.side === 'buy') free -= p.amount;
  }
  return free;
}

// ---------------------------------------------------------------------------
// Strategy
// ---------------------------------------------------------------------------
function decideOrders(batch: any): any[] {
  const now: number = batch.slot;
  const orders: any[] = [];
  const cap = hello.caps.max_orders_per_batch as number;
  const tx = txFeeLamports();
  const traded = new Set<Mint>();

  // --- fold fills ----------------------------------------------------------
  for (const f of batch.fills ?? []) {
    pending.delete(f.client_id);
    if (typeof f.client_id === 'string' && f.client_id.startsWith('_')) {
      held.delete(f.mint);
      continue;
    }
    if (f.status === 'filled') {
      myFills++;
      myCoins.add(f.mint);
    }
  }

  // --- fold account --------------------------------------------------------
  cash = BigInt(batch.account.cash_lamports);
  positions.clear();
  for (const p of batch.account.positions ?? []) {
    const tokens = BigInt(p.token_amount);
    if (tokens > 0n) {
      positions.set(p.mint, { tokens, cost: BigInt(p.cost_lamports) });
    }
  }

  // --- fold marks ----------------------------------------------------------
  for (const m of batch.marks ?? []) {
    const c = curves.get(m.mint);
    if (c !== undefined && m.slot < c.reservesSlot) continue;
    const curve = c ?? curveOf(m.mint, m.slot);
    curve.vq = BigInt(m.virtual_quote_reserves);
    curve.vt = BigInt(m.virtual_token_reserves);
    curve.rt = BigInt(m.real_token_reserves);
    curve.rq = BigInt(m.real_quote_reserves);
    curve.reservesSlot = m.slot;
  }

  // --- fold events ---------------------------------------------------------
  for (const e of batch.events ?? []) {
    if (e.block_time !== null && e.block_time !== undefined) {
      if (firstBlockTime === null) firstBlockTime = e.block_time;
      if (lastBlockTime === null || e.block_time > lastBlockTime) lastBlockTime = e.block_time;
    }
    if (e.event === 'CreateEvent') {
      const c = coinOf(e.mint, e.slot);
      c.createdSlot = e.slot;
      c.creator = e.creator;
      c.vq0 = BigInt(e.virtual_quote_reserves);
      c.vt0 = BigInt(e.virtual_token_reserves);
      c.lastTradeSlot = e.slot;
      const cv = curveOf(e.mint, e.slot);
      cv.createdSlot = e.slot;
      cv.vt = BigInt(e.virtual_token_reserves);
      cv.vq = BigInt(e.virtual_quote_reserves);
      cv.rt = BigInt(e.real_token_reserves);
      cv.rq = 0n;
      cv.reservesSlot = e.slot;
    } else if (e.event === 'TradeEvent') {
      const c = coinOf(e.mint, e.slot);
      const sol = BigInt(e.sol_amount);
      c.lastTradeSlot = e.slot;
      const isDev = e.user === c.creator;
      if (e.is_buy) {
        if (isDev && e.slot === c.createdSlot) c.devBuy += sol;
        else if (!isDev) {
          c.buyers.add(e.user);
          c.bought += sol;
        }
      } else if (isDev) {
        c.devSold = true;
      } else {
        c.soldByOthers += sol;
      }
      traded.add(e.mint);
      const cv = curveOf(e.mint, e.slot);
      cv.vq = BigInt(e.virtual_quote_reserves);
      cv.vt = BigInt(e.virtual_token_reserves);
      cv.rt = BigInt(e.real_token_reserves);
      cv.rq = BigInt(e.real_quote_reserves);
      cv.reservesSlot = e.slot;
    } else if (e.event === 'CompleteEvent') {
      curveOf(e.mint, e.slot).complete = true;
      const c = coins.get(e.mint);
      if (c !== undefined) c.done = true;
    }
  }

  const pendingByMint = new Map<Mint, string[]>();
  for (const p of pending.values()) {
    const arr = pendingByMint.get(p.mint) ?? [];
    arr.push(p.side);
    pendingByMint.set(p.mint, arr);
  }
  const hasPendingSell = (mint: Mint): boolean =>
    (pendingByMint.get(mint) ?? []).includes('sell');
  const hasPendingBuy = (mint: Mint): boolean =>
    (pendingByMint.get(mint) ?? []).includes('buy');

  const pushBuy = (mint: Mint, lamports: bigint): void => {
    const id = `o${++orderSeq}`;
    orders.push({
      side: 'buy',
      client_id: id,
      mint,
      quote_lamports: lamports.toString(),
      max_slippage_bps: MAX_SLIPPAGE_BUY_BPS,
    });
    pending.set(id, { mint, side: 'buy', amount: lamports });
  };
  const pushSell = (mint: Mint, tokens: bigint): void => {
    const id = `o${++orderSeq}`;
    orders.push({
      side: 'sell',
      client_id: id,
      mint,
      token_amount: tokens.toString(),
      max_slippage_bps: MAX_SLIPPAGE_SELL_BPS,
    });
    pending.set(id, { mint, side: 'sell', amount: 0n });
  };

  // --- exits first ---------------------------------------------------------
  for (const [mint, pos] of positions) {
    if (orders.length >= cap) break;
    if (probes.has(mint)) continue; // probes are sold by the probe loop below
    if (hasPendingSell(mint)) continue;
    const curve = curves.get(mint);
    if (curve === undefined || curve.complete) continue;
    let h = held.get(mint);
    if (h === undefined) {
      h = { openedSlot: now, peakValue: 0n, tookTp1: false, exiting: false, filled: true };
      held.set(mint, h);
    }
    const value = sellValueLamports(pos.tokens, curve.vq, curve.vt, tx);
    const cost = pos.cost;
    if (value > h.peakValue) h.peakValue = value;
    const c = coins.get(mint);

    // Partial take-profit: bank half at +8%, then let the rest ride.
    if (!h.tookTp1 && valueAtLeast(value, cost, Math.round(P.tp1Up * 1000))) {
      const part = (pos.tokens * BigInt(Math.round(P.tp1Part * 1000))) / 1000n;
      if (part > 0n && part < pos.tokens) {
        pushSell(mint, part);
        h.tookTp1 = true;
        h.peakValue = 0n;
        continue;
      }
    }
    let exit = false;
    if (valueAtLeast(value, cost, Math.round(P.tpUp * 1000))) exit = true;
    const slDown = h.tookTp1 ? P.slAfterTp1Down : P.slDown;
    if (valueBelow(value, cost, -Math.round(slDown * 1000))) exit = true;
    if (
      valueAtLeast(h.peakValue, cost, Math.round(P.trailArmUp * 1000)) &&
      valueBelow(value, h.peakValue, -Math.round(P.trailDown * 1000))
    ) {
      exit = true;
    }
    if (now - h.openedSlot >= P.maxHoldSlots) exit = true;
    if (c !== undefined && c.devSold) exit = true;
    if (!exit) continue;
    pushSell(mint, pos.tokens);
    if (c !== undefined) c.done = true;
  }
  // Drop held records whose position is gone and nothing is in flight.
  for (const mint of [...held.keys()]) {
    if (!positions.has(mint) && !pendingByMint.has(mint)) held.delete(mint);
  }

  // --- probe sells: sell the whole probe as soon as its buy has landed -----
  for (const [mint, selling] of probes) {
    const pos = positions.get(mint);
    const curve = curves.get(mint);
    if (pos === undefined) {
      if (!pendingByMint.has(mint)) probes.delete(mint);
      continue;
    }
    if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
    if (orders.length >= cap) break;
    pushSell(mint, pos.tokens);
    if (!selling) probes.set(mint, true);
  }

  // --- entries: young launches that pass the rug filter --------------------
  let free = freeCashLamports();
  let slotsLeft = hello.caps.max_open_positions - committedPositionCount();
  let exposure = 0;
  for (const [mint, h] of held) {
    exposure += Math.max(0, lamportsToSol(positions.get(mint)?.cost ?? 0n));
  }
  for (const [mint, c] of coins) {
    if (orders.length >= cap) break;
    if (c.done) continue;
    const age = now - c.createdSlot;
    if (age > P.maxAgeSlots) {
      c.done = true;
      continue;
    }
    if (age < P.minAgeSlots) continue;
    if (slotsLeft <= 0) break;
    if (held.has(mint) || probes.has(mint) || hasPendingBuy(mint)) continue;
    if (positions.has(mint)) continue;
    const curve = curves.get(mint);
    if (curve === undefined || curve.complete) continue;
    // Rug filter.
    if (c.devSold) {
      c.done = true;
      continue;
    }
    const rqSol = lamportsToSol(curve.rq);
    if (rqSol < P.minRqSol || rqSol > P.maxRqSol) continue;
    if (lamportsToSol(c.devBuy) > P.maxDevBuySol) continue;
    if (c.buyers.size < P.minBuyers || c.buyers.size > P.maxBuyers) continue;
    if (c.bought > 0n && c.soldByOthers > c.bought) continue;
    const runup = priceOf(curve.vq, curve.vt) / priceOf(c.vq0, c.vt0);
    if (!(runup <= P.maxRunup) || runup <= 0) continue;
    const amount = (() => {
      const want = solToLamports(P.stakeSol);
      const capAmt = maxBuyLamports(mint);
      return want < capAmt ? want : capAmt;
    })();
    if (amount < solToLamports(P.minBuySol)) continue;
    if (amount > solToLamports(P.maxExposureSol - exposure)) continue;
    if (free < amount + tx) continue;
    pushBuy(mint, amount);
    free -= amount + tx;
    exposure += lamportsToSol(amount);
    slotsLeft--;
    held.set(mint, {
      openedSlot: now,
      peakValue: 0n,
      tookTp1: false,
      exiting: false,
      filled: false,
    });
  }

  // --- guardrail pacing: probe round trips when fills/coins lag -------------
  if (
    probes.size < P.maxProbes &&
    slotsLeft > 0 &&
    firstBlockTime !== null &&
    lastBlockTime !== null
  ) {
    const pace = Math.min(1, (lastBlockTime - firstBlockTime) / P.paceSecs);
    const needCoins = myCoins.size < Math.ceil(P.targetCoins * pace);
    const needFills = myFills < Math.ceil(P.targetFills * pace);
    if (needCoins || needFills) {
      const minRqSol = P.probeSol / (hello.caps.max_order_bps_of_real_reserve / 10000);
      for (const mint of traded) {
        if (orders.length >= cap || probes.size >= P.maxProbes) break;
        if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint)) continue;
        if (positions.has(mint)) continue;
        if (needCoins && !needFills && myCoins.has(mint)) continue;
        const curve = curves.get(mint);
        if (curve === undefined || curve.complete) continue;
        if (lamportsToSol(curve.rq) < minRqSol * 1.5) continue;
        if (free < solToLamports(P.probeSol) + 2n * tx) break;
        pushBuy(mint, solToLamports(P.probeSol));
        probes.set(mint, false);
        free -= solToLamports(P.probeSol) + tx;
      }
    }
  }

  return orders;
}

// ---------------------------------------------------------------------------
// Wire loop: newline-delimited JSON on stdin, one reply per batch on stdout.
// ---------------------------------------------------------------------------
let done = false;

function handleLine(line: string): void {
  let msg: any;
  try {
    msg = JSON.parse(line);
  } catch {
    console.error('bad json line');
    process.exit(1);
  }
  if (msg.type === 'hello') {
    hello = msg;
    cash = BigInt(hello.capital.lamports);
  } else if (msg.type === 'batch') {
    const orders = decideOrders(msg);
    const reply = JSON.stringify({ type: 'reply', seq: msg.seq, orders });
    process.stdout.write(reply + '\n');
  } else if (msg.type === 'done') {
    done = true;
    process.exit(0);
  } else {
    console.error(`unknown message type: ${msg.type}`);
    process.exit(1);
  }
}

async function main(): Promise<void> {
  let buf = '';
  const decoder = new TextDecoder();
  process.stdin.on('data', (chunk: Buffer) => {
    buf += decoder.decode(chunk, { stream: true });
    let nl: number;
    while ((nl = buf.indexOf('\n')) !== -1) {
      const line = buf.slice(0, nl).trim();
      buf = buf.slice(nl + 1);
      if (line === '') continue;
      handleLine(line);
      if (done) return;
    }
  });
  await new Promise<void>((resolve) => {
    process.stdin.on('end', resolve);
    process.stdin.on('close', resolve);
  });
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
