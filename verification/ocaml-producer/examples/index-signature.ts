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
