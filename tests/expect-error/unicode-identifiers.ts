// An identifier's characters are the Unicode ID_Start / ID_Continue sets
// (ECMA-262 sec 12.7), not just ASCII, so these are ordinary names.

export function accented(): number {
  const café = 1;
  return café;
}

export function greek(): number {
  const α = 2;
  return α;
}

export function cyrillic(): number {
  const переменная = 3;
  return переменная;
}

export function cjk(): number {
  const 変数 = 4;
  return 変数;
}

// Property names are identifiers too.
export function property(): number {
  const o = { café: 5 };
  return o.café;
}

// A name may start with an ASCII character and continue with a non-ASCII one.
export function mixed(): number {
  const naïve = 6;
  return naïve;
}
