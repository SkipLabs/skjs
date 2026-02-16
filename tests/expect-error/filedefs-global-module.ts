declare global {
  // @skjs-expect-error TODO: global
  interface Window {
    custom: string;
  }
}

declare module "augmented";
