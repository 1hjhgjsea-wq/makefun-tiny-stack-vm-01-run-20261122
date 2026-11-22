import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// A tiny stack virtual machine: a complete interpreter for make.fun's
// tiny stack ISA v1. Signed 32-bit values; traps end the program with
// their own exit code, keeping what it already wrote.

// Per opcode: [immediate bytes, values popped, values pushed].
const B: [number, number, number] = [0, 2, 1];
const SPEC: Record<number, [number, number, number]> = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: B, 0x11: B, 0x12: B, 0x13: B, 0x14: B, 0x15: B, 0x16: B,
  0x17: [0, 1, 1], 0x18: B, 0x19: B, 0x1a: B, 0x1b: [0, 1, 1],
  0x1c: B, 0x1d: B, 0x1e: B, 0x20: B, 0x21: B, 0x22: B,
  0x30: [2, 0, 0], 0x31: [2, 1, 0], 0x32: [2, 1, 0], 0x33: [2, 0, 0],
  0x34: [0, 0, 0],
  0x40: [0, 1, 1], 0x41: [0, 2, 0],
  0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1], 0x53: [0, 1, 0],
};

function run(prog: Uint8Array, inp: Uint8Array): { out: Uint8Array; exit: number } {
  const n = prog.length;
  const st = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ipos = 0;
  let pc = 0;
  let steps = 0;
  const enc = new TextEncoder();
  const done = (exit: number) => ({ out: out.slice(0, olen), exit });
  const rel = (at: number) => ((prog[at] | (prog[at + 1] << 8)) << 16) >> 16;

  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const spec = SPEC[op];
    if (!spec) return done(5);
    const [imm, pops, pushes] = spec;
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    pc = next;
    switch (op) {
      case 0x00:
        return done(0);
      case 0x01:
        st[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02:
        st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 0x05: {
        const top = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = top;
        break;
      }
      case 0x06:
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 0x07: {
        const third = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = third;
        break;
      }
      case 0x17:
        st[sp - 1] = (-st[sp - 1]) | 0;
        break;
      case 0x1b:
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = (a / b) | 0; // |0 truncates toward zero, and wraps INT_MIN/-1 to INT_MIN
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30:
        pc = next + rel(next - 2);
        break;
      case 0x31: {
        const v = st[--sp];
        if (v === 0) pc = next + rel(next - 2);
        break;
      }
      case 0x32: {
        const v = st[--sp];
        if (v !== 0) pc = next + rel(next - 2);
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        cs[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = cs[--cp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1];
        const value = st[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        mem[addr] = value;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(st[sp - 1]));
        if (olen + bytes.length > 65536) return done(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = st[--sp] & 255;
        break;
      case 0x52:
        st[sp++] = ipos < inp.length ? inp[ipos++] : -1;
        break;
      case 0x53:
        return done(st[--sp] & 255);
    }
  }
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inDir).sort()) {
  const d = join(inDir, id);
  const r = run(readFileSync(join(d, 'program.bin')), readFileSync(join(d, 'input.bin')));
  const o = join(outDir, id);
  mkdirSync(o, { recursive: true });
  writeFileSync(join(o, 'stdout.bin'), r.out);
  writeFileSync(join(o, 'exit.txt'), `${r.exit}\n`);
}
