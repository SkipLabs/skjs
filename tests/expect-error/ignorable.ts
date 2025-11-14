type T = { f: number };

declare function nonIgnorable(): T;
declare function ignorable(): SKJS_Ignorable<T>;

function doNotIgnore(): void {
  // @ts-expect-error This expression was expected to be of type void
  nonIgnorable();
}

function ignoreAllowed(): void {
  // @ts-expect-error This expression was expected to be of type void
  ignorable();
}
