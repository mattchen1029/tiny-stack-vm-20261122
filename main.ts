// Tiny stack VM: interpreter for the make.fun tiny stack ISA v1.
// node main.ts reads MAKEFUN_INPUT_DIR (default /input) <id>/{program,input}.bin
// and writes MAKEFUN_OUTPUT_DIR (default /output) <id>/{stdout.bin,exit.txt}.
import { readdirSync, readFileSync, writeFileSync, mkdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const SCAP = 256, CCAP = 64, MEMW = 256, STEPS = 1_000_000, OCAP = 65_536;
const IMIN = -2147483648;

// Immediate length per opcode byte; a missing byte is not an opcode (trap 5).
const IMM = {
  0x00: 0, 0x01: 1, 0x02: 4, 0x03: 0, 0x04: 0, 0x05: 0, 0x06: 0, 0x07: 0,
  0x10: 0, 0x11: 0, 0x12: 0, 0x13: 0, 0x14: 0, 0x15: 0, 0x16: 0, 0x17: 0,
  0x18: 0, 0x19: 0, 0x1a: 0, 0x1b: 0, 0x1c: 0, 0x1d: 0, 0x1e: 0,
  0x20: 0, 0x21: 0, 0x22: 0, 0x30: 2, 0x31: 2, 0x32: 2, 0x33: 2, 0x34: 0,
  0x40: 0, 0x41: 0, 0x50: 0, 0x51: 0, 0x52: 0, 0x53: 0,
};

class Trap extends Error { constructor(c) { super('trap ' + c); this.c = c; } }

function run(prog, input) {
  const S = new Int32Array(SCAP); let sp = 0;
  const C = new Int32Array(CCAP); let cp = 0;
  const M = new Int32Array(MEMW);
  const O = []; let ip = 0, pc = 0, steps = 0;
  // Stack needs are checked before any effect: underflow trap 2, overflow trap 3.
  const guard = (pops, pushes) => {
    if (sp < pops) throw new Trap(2);
    if (sp - pops + pushes > SCAP) throw new Trap(3);
  };
  try {
    for (;;) {
      if (steps === STEPS) throw new Trap(10); // step limit
      if (pc < 0 || pc >= prog.length) throw new Trap(9); // pc outside program
      const op = prog[pc];
      const imm = IMM[op];
      if (imm === undefined) throw new Trap(5); // unknown opcode
      if (pc + imm >= prog.length) throw new Trap(9); // immediate cut off
      steps++;
      const next = pc + 1 + imm;
      pc = next;
      switch (op) {
        case 0x00: return { out: Buffer.from(O), exit: 0 }; // HALT
        case 0x01: // PUSH8, sign-extended
          guard(0, 1); S[sp++] = (prog[pc - 1] << 24) >> 24; break;
        case 0x02: // PUSH32, little-endian signed
          guard(0, 1);
          S[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24);
          break;
        case 0x03: guard(1, 0); sp--; break; // POP
        case 0x04: guard(1, 2); S[sp] = S[sp - 1]; sp++; break; // DUP
        case 0x05: { guard(2, 2); const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
        case 0x06: guard(2, 3); S[sp] = S[sp - 2]; sp++; break; // OVER
        case 0x07: { // ROT (a b c -- b c a)
          guard(3, 3); const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break;
        }
        case 0x17: guard(1, 1); S[sp - 1] = (-S[sp - 1]) | 0; break; // NEG, wraps
        case 0x1b: guard(1, 1); S[sp - 1] = ~S[sp - 1]; break; // NOT
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
        case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
        case 0x1e: case 0x20: case 0x21: case 0x22: { // two-operand ops (a b -- r)
          guard(2, 1);
          const b = S[sp - 1], a = S[sp - 2];
          let r;
          if (op === 0x10) r = (a + b) | 0;
          else if (op === 0x11) r = (a - b) | 0;
          else if (op === 0x12) r = Math.imul(a, b);
          else if (op === 0x13) { // DIV, toward zero; INT_MIN/-1 is INT_MIN
            if (b === 0) throw new Trap(4);
            r = a === IMIN && b === -1 ? a : ((a / b) | 0);
          } else if (op === 0x14) { // MOD, sign of a; x%-1 is 0
            if (b === 0) throw new Trap(4);
            r = b === -1 ? 0 : ((a % b) | 0);
          } else if (op === 0x15) { // DIVU
            if (b === 0) throw new Trap(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
          } else if (op === 0x16) { // MODU
            if (b === 0) throw new Trap(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
          } else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31);
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
          sp -= 2; S[sp++] = r; break;
        }
        case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset
          const rel = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
          if (op === 0x30) pc = next + rel;
          else {
            guard(1, 0);
            const v = S[--sp];
            if (op === 0x31 ? v === 0 : v !== 0) pc = next + rel;
          }
          break;
        }
        case 0x33: // CALL, unsigned 16-bit absolute target
          if (cp === CCAP) throw new Trap(7);
          C[cp++] = next; pc = prog[pc - 2] | (prog[pc - 1] << 8); break;
        case 0x34: // RET
          if (cp === 0) throw new Trap(8);
          pc = C[--cp]; break;
        case 0x40: { // LOAD
          guard(1, 1); const a = S[sp - 1];
          if (a < 0 || a >= MEMW) throw new Trap(6);
          S[sp - 1] = M[a]; break;
        }
        case 0x41: { // STORE (v addr --)
          guard(2, 0); const a = S[sp - 1], v = S[sp - 2];
          if (a < 0 || a >= MEMW) throw new Trap(6);
          sp -= 2; M[a] = v; break;
        }
        case 0x50: { // PRINT, decimal ASCII, no newline
          guard(1, 0); const t = String(S[sp - 1]);
          if (O.length + t.length > OCAP) throw new Trap(11);
          sp--;
          for (let i = 0; i < t.length; i++) O.push(t.charCodeAt(i));
          break;
        }
        case 0x51: // PUTC, one byte
          guard(1, 0);
          if (O.length + 1 > OCAP) throw new Trap(11);
          O.push(S[--sp] & 255); break;
        case 0x52: // IN, -1 once input is used up
          guard(0, 1); S[sp++] = ip < input.length ? input[ip++] : -1; break;
        case 0x53: // EXIT, low byte
          guard(1, 0); return { out: Buffer.from(O), exit: S[--sp] & 255 };
        default: throw new Trap(5); // unreachable
      }
    }
  } catch (e) {
    if (e instanceof Trap) return { out: Buffer.from(O), exit: e.c };
    throw e;
  }
}

const ids = readdirSync(IN_DIR, { withFileTypes: true })
  .filter((e) => e.isDirectory()).map((e) => e.name).sort();
for (const id of ids) {
  const prog = readFileSync(join(IN_DIR, id, 'program.bin'));
  const p = join(IN_DIR, id, 'input.bin');
  const input = existsSync(p) ? readFileSync(p) : Buffer.alloc(0);
  const { out, exit } = run(prog, input);
  const dir = join(OUT_DIR, id);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, 'stdout.bin'), out);
  writeFileSync(join(dir, 'exit.txt'), String(exit) + '\n');
}
