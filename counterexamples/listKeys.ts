export function listKeys(payload: unknown): Array<string> {
  if (typeof payload === "object") {
    return Object.keys(payload);
  }
  return [];
}

listKeys(null);
