import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code?: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type Counter = { readonly value: number } & {
  readonly [key: string]: Json | null;
};

export type CounterDeltaRequest = { readonly amount?: number } & {
  readonly [key: string]: Json | null;
};

export type CounterDeltaRequest_skip_id_ = { readonly amount?: number } & {
  readonly [key: string]: Json | null;
};

export type CounterDeltaRequest_skip_value_ = { readonly amount?: number } & {
  readonly [key: string]: Json | null;
};
