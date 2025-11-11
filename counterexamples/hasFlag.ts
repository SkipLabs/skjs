export function hasFlag(value: unknown): boolean {
  if (typeof value === "object") {
    return "flag" in value;
  }
  return false;
}

hasFlag(null);
