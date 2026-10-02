import type { Json } from "@skipruntime/core";

export function values(): Json {
  const accept = (value: Json): Json => value;
  const flag = accept(true);
  const count = accept(42);
  const label = accept("ready");
  const list = accept([flag, count, label, null]);
  return accept({ flag: flag, count: count, label: label, list: list });
}
