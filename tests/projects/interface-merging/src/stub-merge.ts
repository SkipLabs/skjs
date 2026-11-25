// Declaration merging against the import stubs: every file sees the stub
// `declare interface PromiseLike<T>` from import-stubs, so a user declaration
// of `PromiseLike` adds its members to the stub interface, like tsc's global
// augmentation.
interface PromiseLike<T> {
  extra(): string;
}

function usePromiseLike(p: PromiseLike<number>): void {
  const s: string = p.extra();
  const q: PromiseLike<number> = p;
}
