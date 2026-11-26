// An exported overload group: importers must see exactly the two overload
// signatures (not one per export mention), and calls resolve first-match.
export function fmt(x: string): string;
export function fmt(x: number): string;
export function fmt(x: string | number): string {
  return typeof x === "string" ? x : "num";
}
