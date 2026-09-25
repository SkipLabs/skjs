// A number index signature with its own contract constrains the canonical
// numeric keys ("0", "1.5", "-1", …) apart from the other string keys; the
// model's index constrains every string key alike.
interface Dual {
  [k: string]: number | string;
  [k: number]: number;
}
export function read(x: Dual): number | string | undefined {
  return x["k"];
}
