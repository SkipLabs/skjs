// Merging a user declaration with a library declaration from a .d.ts stub
// (here the stub `declare interface PromiseLike<T>` from import-stubs) is
// rejected: augmenting a library type is only supported by tsc through an
// explicit `declare global`, which SKJS does not support.
// @skjs-expect-error Merging 'PromiseLike' with its library declaration in a .d.ts stub is not supported by SKJS (ignored)
interface PromiseLike<T> {
  extra(): string;
}
