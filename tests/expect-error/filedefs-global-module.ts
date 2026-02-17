declare global {
  // @skjs-expect-error TODO: global
  interface Window {
    custom: string;
  }
}

// @skjs-expect-error TODO: module
declare module "augmented";
