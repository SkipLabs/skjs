export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateLinkRequest = {
  readonly customCode?: string;
  readonly description?: string;
  readonly targetUrl: string;
};

export type CreateLinkRequest_skip_id_ = {
  readonly customCode?: string;
  readonly description?: string;
  readonly targetUrl: string;
};

export type CreateLinkRequest_skip_value_ = {
  readonly customCode?: string;
  readonly description?: string;
  readonly targetUrl: string;
};

export type GetLinkParams = { readonly code: string; readonly userId: string };

export type Link = {
  readonly clickCount: number;
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly ownerId: string;
  readonly targetUrl: string;
};

export type LinkList = { readonly items: Link[]; readonly total?: number };

export type LinkList_skip_id_ = {
  readonly items: Link[];
  readonly total?: number;
};

export type LinkList_skip_value_ = {
  readonly items: Link[];
  readonly total?: number;
};

export type LinkOwnerId = string;

export type Link_skip_id_ = string;

export type Link_skip_value_ = {
  readonly clickCount: number;
  readonly createdAt: string;
  readonly description?: string;
  readonly ownerId: string;
  readonly targetUrl: string;
};

export type ListMyLinksParams = { readonly userId: string };

export type ResolveLinkParams = { readonly code: string };

export type ResolveResponse = {
  readonly code: string;
  readonly targetUrl: string;
};

export type ResolveResponse_skip_id_ = {
  readonly code: string;
  readonly targetUrl: string;
};

export type ResolveResponse_skip_value_ = {
  readonly code: string;
  readonly targetUrl: string;
};

export type UpdateLinkRequest = {
  readonly description?: string;
  readonly targetUrl?: string;
};

export type UpdateLinkRequest_skip_id_ = {
  readonly description?: string;
  readonly targetUrl?: string;
};

export type UpdateLinkRequest_skip_value_ = {
  readonly description?: string;
  readonly targetUrl?: string;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type User = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
};
