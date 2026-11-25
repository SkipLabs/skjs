// Declaration merging against the import stubs: every file sees the stub
// `declare interface PromiseLike<T>` from import-stubs, so a user declaration
// of `PromiseLike` adds its members to the stub interface, like tsc's global
// augmentation.
// @skjs-expect-error Duplicate class declaration 'PromiseLike'
interface PromiseLike<T> {
  extra(): string;
}

// @skjs-expect-error Duplicate class declaration 'PromiseLike'
function usePromiseLike(p: PromiseLike<number>): void {
  // @skjs-expect-error Property 'extra' does not exist on this type
  const s: string = p.extra();
  const q: PromiseLike<number> = p;
}
