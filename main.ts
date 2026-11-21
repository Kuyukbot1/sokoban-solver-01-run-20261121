// Sokoban solver for make.fun sokoban-solver-01-run-20261121.
//
// Strategy: a level is a hallway with 1-4 rooms off it, and a box pushed
// through a door can never come back, so every room is solved on its own
// from its door and the rooms' push counts add up. Each room is solved by
// A* over pushes (a state is the boxes' squares plus the player's reachable
// region), with an admissible heuristic — the cheapest assignment of boxes
// to goals by single-box push distances that know which side of a box the
// player can actually reach — and deadlock pruning (dead squares a box can
// never leave, and frozen 2x2 blocks). A greedy best-first search runs
// first, so a valid solution is in hand before the optimal search, and A*
// then only chases a strictly better push count; a push-space breadth-first
// search stands by when greedy finds nothing. Everything is budgeted by
// expansions and states, never by the wall clock, so two runs write the
// same bytes.
//
// Node 22, standard library only, deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Work budgets (expansions/states), never the clock: the grader runs the
// program twice and the two runs must write identical bytes.
const ASTAR_EXPANSIONS = 250_000;
const BFS_STATES = 250_000;
const GREEDY_EXPANSIONS = 60_000;
const ASTAR_STATES = 600_000;
const GREEDY_STATES = 600_000;
const GLOBAL_EXPANSIONS = 2_500_000;
let globalExpansions = 0;

const DIRS: ReadonlyArray<readonly [number, number, string, string]> = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

interface Level {
  w: number;
  h: number;
  wall: Uint8Array; // 1 = wall
  goals: number[];
  boxes: number[];
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x]!;
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  // The outermost frame is wall whatever it shows.
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/**
 * Squares from which a lone box can be pushed onto some goal: reverse
 * BFS from the goals. A box on a square outside this set is dead — no
 * push sequence ever saves it — so such states are pruned, never explored.
 */
function liveSquares(level: Level): Uint8Array {
  const { w, wall, goals } = level;
  const live = new Uint8Array(wall.length);
  const queue: number[] = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const t = queue[qi]!;
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const p = t - d; // box stood here before the push to t
      const behind = p - d; // the player stood here to make that push
      if (!wall[p] && !wall[behind] && !live[p]) {
        live[p] = 1;
        queue.push(p);
      }
    }
  }
  return live;
}

/**
 * The player's reachable region from `from` with `occupied` in the way,
 * marked in `seen` with `stamp`; returns the region's lowest square, which
 * names the region in a state key.
 */
function reach(
  level: Level,
  occupied: Uint8Array,
  from: number,
  seen: Int32Array,
  stamp: number,
  stack: Int32Array,
): number {
  const { w, wall } = level;
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n]!;
    if (p < low) low = p;
    for (let k = 0; k < 4; k++) {
      const q = k === 0 ? p - w : k === 1 ? p + w : k === 2 ? p - 1 : p + 1;
      if (wall[q] === 0 && occupied[q] === 0 && seen[q] !== stamp) {
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
  }
  return low;
}

/** A box just pushed to `t` is frozen when it sits in a 2x2 block of walls and boxes holding a box off its goal. */
function frozenBlock(level: Level, occupied: Uint8Array, goal: Uint8Array, t: number): boolean {
  const { w, wall } = level;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) || (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower LURD letters (u first on ties). */
function walkTo(level: Level, occupied: Uint8Array, from: number, to: number): string {
  const { w, wall } = level;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi]!;
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: push square out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]!) s = how[p]! + s;
  return s;
}

const keyOf = (boxes: number[], low: number, size: number): number => {
  let k = low;
  for (const b of boxes) k = k * size + b;
  return k;
};

interface PushSolution {
  pushes: number;
  moves: string;
}

/**
 * Push-space search over one (sub-)level: A* when `mode` is 'astar'
 * (f = pushes + assignment heuristic), plain breadth-first when 'bfs'
 * (first solved state is push-optimal), greedy best-first when 'greedy'
 * (f = heuristic only, for a fast fallback solution). Returns the push
 * sequence as moves, or null when the budget runs out.
 */
function searchPushes(
  level: Level,
  mode: 'astar' | 'bfs' | 'greedy',
  budget: number,
  incumbent = Infinity,
  stateCap = Infinity,
): PushSolution | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(level);
  if (level.boxes.some((b) => !live[b])) return null;
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b]);

  // The player's regions with a single box as the only obstacle:
  // regionsFor(box)[square] = the lowest square of the region holding
  // `square` when only `box` blocks the floor. Memoised per box position.
  const regionMemo = new Map<number, Int32Array>();
  const regionsFor = (box: number): Int32Array => {
    const cached = regionMemo.get(box);
    if (cached) return cached;
    const low = new Int32Array(size).fill(-1);
    const stack = new Int32Array(size);
    for (let s = 0; s < size; s++) {
      if (wall[s] || s === box || low[s] !== -1) continue;
      let n = 0;
      stack[n++] = s;
      low[s] = -2;
      let regionLow = s;
      const members = [s];
      while (n > 0) {
        const p = stack[--n]!;
        if (p < regionLow) regionLow = p;
        for (let k = 0; k < 4; k++) {
          const q = k === 0 ? p - w : k === 1 ? p + w : k === 2 ? p - 1 : p + 1;
          if (wall[q] || q === box || low[q] !== -1) continue;
          low[q] = -2;
          members.push(q);
          stack[n++] = q;
        }
      }
      for (const m of members) low[m] = regionLow;
    }
    regionMemo.set(box, low);
    return low;
  };

  // Single-box push distances, region-aware: dist[goal][box * size + region]
  // = fewest pushes to bring one box from `box` (the player anywhere in
  // `region`, the box the only obstacle) onto that goal, ignoring the other
  // boxes. BFS backwards from the goal over (box, region) states: a push
  // from prev to b = prev + d needs the player at prev - d, and leaves the
  // player standing on prev, so the predecessor of (b, region) is
  // (prev, region of prev - d with the box at prev) whenever the region of
  // prev with the box at b is `region`.
  const n = goals.length;
  const dist: Int32Array[] = [];
  for (let gi = 0; gi < n; gi++) {
    const g = goals[gi]!;
    const d = new Int32Array(size * size).fill(-1);
    const queue: number[] = [];
    const gRegions = regionsFor(g);
    const seenRegions = new Set<number>();
    for (let s = 0; s < size; s++) {
      if (wall[s] || s === g) continue;
      const r = gRegions[s]!;
      if (r < 0 || seenRegions.has(r)) continue;
      seenRegions.add(r);
      d[g * size + r] = 0;
      queue.push(g * size + r);
    }
    for (let qi = 0; qi < queue.length; qi++) {
      const code = queue[qi]!;
      const b = Math.floor(code / size);
      const r = code % size;
      const cost = d[code]!;
      for (const [dx, dy] of DIRS) {
        const dd = dy * w + dx;
        const prev = b - dd;
        const behind = prev - dd;
        if (wall[prev] || wall[behind]) continue;
        if (regionsFor(b)[prev]! !== r) continue;
        const rp = regionsFor(prev)[behind]!;
        if (rp < 0) continue;
        const codeP = prev * size + rp;
        if (d[codeP] !== -1) continue;
        d[codeP] = cost + 1;
        queue.push(codeP);
      }
    }
    dist.push(d);
  }
  // Cheapest assignment of boxes to distinct goals (n <= 4: try every
  // permutation). A box that reaches no goal in the assignment is skipped
  // for that goal, not fatal to the whole heuristic: only when no
  // assignment works is the state dead.
  const heuristic = (boxes: number[], player: number): number => {
    let best = Infinity;
    const rec = (i: number, used: number, cost: number): void => {
      if (cost >= best) return;
      if (i === boxes.length) {
        best = cost;
        return;
      }
      const b = boxes[i]!;
      const r = regionsFor(b)[player]!;
      for (let j = 0; j < n; j++) {
        if (used & (1 << j)) continue;
        const c = dist[j]![b * size + r]!;
        if (c < 0) continue;
        rec(i + 1, used | (1 << j), cost + c);
      }
    };
    rec(0, 0, 0);
    return best;
  };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;

  // States in discovery order: boxes, player square after the last push,
  // parent state, and the push (from-square, direction) that made it.
  const statesBoxes: number[][] = [level.boxes.slice()];
  const statesPlayer: number[] = [level.player];
  const parent: number[] = [-1];
  const pushFrom: number[] = [-1];
  const pushDir: number[] = [-1];
  const gScore: number[] = [0];
  const bestG = new Map<number, number>();
  for (const b of level.boxes) occupied[b] = 1;
  bestG.set(keyOf(level.boxes, reach(level, occupied, level.player, seen, ++stamp, stack), size), 0);
  for (const b of level.boxes) occupied[b] = 0;

  // Binary heap on [priority, heuristic, insertion order, state index].
  // astar: priority = g + h; bfs: priority = g; greedy: priority = h.
  const heap: [number, number, number, number][] = [];
  let seq = 0;
  const h0 = mode === 'bfs' ? 0 : heuristic(level.boxes, level.player);
  if (h0 === Infinity) return null;
  heap.push([h0, h0, seq++, 0]);
  const less = (a: [number, number, number, number], b: [number, number, number, number]): boolean =>
    a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])));
  const heapPush = (e: [number, number, number, number]): void => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const heapPop = (): [number, number, number, number] => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };

  let found = solved(level.boxes) ? 0 : -1;
  let expanded = 0;
  while (heap.length > 0 && expanded < budget && globalExpansions < GLOBAL_EXPANSIONS && statesBoxes.length < stateCap) {
    const [, hs, , s] = heapPop();
    const boxes = statesBoxes[s]!;
    const g = gScore[s]!;
    // With an incumbent in hand, a state that cannot beat it is skipped.
    if (mode === 'astar' && g + hs >= incumbent) continue;
    // Skip stale heap entries superseded by a cheaper route to this state.
    for (const b of boxes) occupied[b] = 1;
    const low = reach(level, occupied, statesPlayer[s]!, seen, ++stamp, stack);
    for (const b of boxes) occupied[b] = 0;
    if (bestG.get(keyOf(boxes, low, size)) !== s) continue;
    if (solved(boxes)) {
      found = s;
      break;
    }
    expanded++;
    globalExpansions++;
    // The player's region for this state, used to test push reachability.
    for (const b of boxes) occupied[b] = 1;
    reach(level, occupied, statesPlayer[s]!, seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi]!;
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(level, occupied, goal, t);
        let key = -1;
        let next: number[] | null = null;
        let h = Infinity;
        if (!frozen) {
          next = boxes.slice();
          next[bi] = t;
          next.sort((a, x) => a - x);
          // After the push the player stands on b, the box's old square.
          h = mode === 'bfs' ? 0 : heuristic(next, b);
          if (h !== Infinity) key = keyOf(next, reach(level, occupied, b, mark, ++stamp, stack), size);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || h === Infinity) continue;
        // With an incumbent, only a strictly better solution is worth pursuing.
        if (mode === 'astar' && g + 1 + h >= incumbent) continue;
        const prev = bestG.get(key);
        if (prev !== undefined && gScore[prev]! <= g + 1) continue;
        const tIdx = statesBoxes.length;
        bestG.set(key, tIdx);
        statesBoxes.push(next!);
        statesPlayer.push(b);
        parent.push(s);
        pushFrom.push(b);
        pushDir.push(d);
        gScore.push(g + 1);
        const prio = mode === 'astar' ? g + 1 + h : mode === 'bfs' ? g + 1 : h;
        heapPush([prio, h, seq++, tIdx]);
        if (solved(next!)) {
          found = tIdx;
          break;
        }
      }
    }
    for (const b of boxes) occupied[b] = 0;
    if (found >= 0) break;
  }
  if (found < 0) return null;
  // Rebuild the moves: walk to each push square, then push.
  const path: number[] = [];
  for (let s = found; s > 0; s = parent[s]!) path.push(s);
  path.reverse();
  let moves = '';
  let player = level.player;
  let boxes = level.boxes.slice();
  for (const s of path) {
    const nextBoxes = statesBoxes[s]!;
    const from = pushFrom[s]!;
    const d = pushDir[s]!;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d)!;
    for (const b of boxes) occupied[b] = 1;
    moves += walkTo(level, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    moves += dir[3];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

/** Solve one room's sub-level: greedy first, so a valid solution is in hand before the optimal search runs; then A*, which only chases a strictly better push count than the greedy one (or the optimum, when there is no greedy solution); then push-space breadth-first search. */
function solveRoom(level: Level): PushSolution | null {
  const greedy = searchPushes(level, 'greedy', GREEDY_EXPANSIONS, Infinity, GREEDY_STATES);
  if (greedy !== null) {
    return searchPushes(level, 'astar', ASTAR_EXPANSIONS, greedy.pushes, ASTAR_STATES) ?? greedy;
  }
  return (
    searchPushes(level, 'astar', ASTAR_EXPANSIONS, Infinity, ASTAR_STATES) ??
    searchPushes(level, 'bfs', BFS_STATES, Infinity, BFS_STATES)
  );
}

interface Room {
  squares: number[];
  boxes: number[];
  goals: number[];
  done: boolean;
}

/**
 * Split a level into its rooms: cut the dead squares of the player's row
 * (the hallway — a box there reaches no goal) out of the floor; each
 * remaining part holding boxes is a room. Null when the level is no set of
 * rooms (a box starts in the hallway, or a part's boxes and goals differ).
 */
function roomsOf(level: Level): Room[] | null {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(level);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: Room[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i]! + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [], done: false });
  }
  for (const b of boxes) rooms[part[b]!]!.boxes.push(b);
  for (const g of goals) if (part[g]! >= 0) rooms[part[g]!]!.goals.push(g);
  if (goals.some((g) => part[g]! < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

function solveLevel(text: string): string {
  const level = parseLevel(text);
  if (level.boxes.length === 0) return '';
  const rooms = roomsOf(level);
  if (rooms === null) {
    // No room structure: solve the whole level as one room.
    const solved = solveRoom(level);
    return solved === null ? '' : solved.moves;
  }
  let player = level.player;
  let moves = '';
  for (const room of rooms) {
    // The other rooms' boxes stand as walls (on their goals once done).
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub: Level = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const solved = solveRoom(sub);
    if (solved === null) return '';
    moves += solved.moves;
    // The player ends where the room's last push left it: walk the moves.
    for (const ch of solved.moves.toLowerCase()) {
      player += ch === 'u' ? -level.w : ch === 'd' ? level.w : ch === 'l' ? -1 : 1;
    }
    room.done = true;
  }
  return moves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
