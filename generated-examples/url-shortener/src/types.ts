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

export type CreateLinkRequest = {
  readonly code?: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type CreateLinkRequest_skip_id_ = {
  readonly code?: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type CreateLinkRequest_skip_value_ = {
  readonly code?: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type GetLinkParams = { readonly linkId: string } & {
  readonly [key: string]: Json | null;
};

export type Link = {
  readonly clickCount: number;
  readonly code: string;
  readonly createdAt: string;
  readonly id: string;
  readonly ownerId: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type LinkByCodeParams = { readonly code: string } & {
  readonly [key: string]: Json | null;
};

export type LinkList = {
  readonly limit: number;
  readonly links: Link[];
  readonly offset: number;
} & { readonly [key: string]: Json | null };

export type LinkList_skip_id_ = {
  readonly limit: number;
  readonly links: Link[];
  readonly offset: number;
} & { readonly [key: string]: Json | null };

export type LinkList_skip_value_ = {
  readonly limit: number;
  readonly links: Link[];
  readonly offset: number;
} & { readonly [key: string]: Json | null };

export type LinkShortCode = string;

export type Link_skip_id_ = string;

export type Link_skip_value_ = {
  readonly clickCount: number;
  readonly code: string;
  readonly createdAt: string;
  readonly ownerId: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type ListMyLinksParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ResolveResponse = {
  readonly code: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type ResolveResponse_skip_id_ = {
  readonly code: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type ResolveResponse_skip_value_ = {
  readonly code: string;
  readonly targetUrl: string;
} & { readonly [key: string]: Json | null };

export type ResolveShortCodeParams = { readonly code: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateLinkRequest = { readonly targetUrl?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateLinkRequest_skip_id_ = { readonly targetUrl?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateLinkRequest_skip_value_ = { readonly targetUrl?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };
