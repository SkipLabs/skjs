// Re-exports Module A's Node<T> under an alias to exercise cross-module
// references to the same recursive generic declaration.
export type { Node as SharedNode } from "./a.js";
