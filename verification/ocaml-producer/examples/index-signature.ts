// A readonly index view promises values only for keys that are present.
function retainDictionary(x: { readonly [key: string]: boolean }): {
  readonly [key: string]: boolean;
} {
  return x;
}

function readPossiblyAbsent(x: {
  readonly [key: string]: boolean;
}): boolean | undefined {
  return x["missing"];
}

// All locations are allocated here, so every present value can be checked.
function makeDictionary(): { readonly [key: string]: boolean } {
  return { ready: true, done: false };
}
