function bindRequiredPrefix(seed: boolean): boolean {
  const target = (saved: boolean, later: boolean): boolean =>
    saved ? later : !later;
  const bound = target.bind(null, seed);
  return bound(seed);
}

function bindAllRequired(seed: boolean): () => boolean {
  const target = (saved: boolean): boolean => saved;
  return target.bind(null, seed);
}

function bindWrongPrefix(): void {
  const target = (saved: boolean): boolean => saved;
  // @ts-expect-error Argument is not assignable to the parameter's type
  const bound = target.bind(null, "wrong");
}

function bindTooMany(): void {
  const target = (saved: boolean): boolean => saved;
  // @skjs-expect-error Argument is not assignable to the parameter's type
  const bound = target.bind(null, true, false);
}
