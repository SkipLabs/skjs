// companion module for: expansion-key-collision (E-EXPKEY); checked together
// with main.ts by the pair run line in main.ts (a directory FILE argument
// checks every .ts beneath it).
export type Box = { s: string };
export function get(b: Box): string {
  return b.s;
}
