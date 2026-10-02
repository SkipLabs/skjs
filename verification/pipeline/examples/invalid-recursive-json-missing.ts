import type { Json, JsonObject } from "@skipruntime/core";

// A string index signature does not establish that a runtime key is present.
export function missingKey(object: JsonObject, key: string): Json | null {
  return object[key];
}
