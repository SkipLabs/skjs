declare global {
  // @skjs-expect-error 'declare global' blocks are not yet supported by SKJS
  interface Window {
    custom: string;
  }
}

// @skjs-expect-error Namespace ('module') declarations are not yet supported by SKJS
declare module "augmented";
