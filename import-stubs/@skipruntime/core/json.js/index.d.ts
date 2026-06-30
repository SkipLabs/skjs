import type { Json } from "@skipruntime/core";

export type JsonPartialObject = {
  readonly [key: string]: Json | null | undefined;
};
export declare abstract class SkManaged {}
