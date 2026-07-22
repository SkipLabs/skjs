// An empty `declare global {}` declares nothing, so SKJS accepts it — it used
// to crash the checker with an internal error. `export {}` makes this a module,
// which is where tsc requires a global augmentation to live.
export {};
declare global {}
