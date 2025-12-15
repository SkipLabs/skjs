export type RateLimitConfigId = string;

export type RateLimitConfigValue = {
  endpoint: string;
  maxRequests: number;
  windowMs: number;
};

export type RateLimitConfig = RateLimitConfigValue & { id: RateLimitConfigId };

export type RequestEventId = string;

export type RequestEventValue = {
  clientId: string;
  endpoint: string;
  timestamp: number;
};

export type RequestEvent = RequestEventValue & { id: RequestEventId };

export type RateLimitStatusId = string;

export type RateLimitStatusValue = {
  clientId: string;
  endpoint: string;
  currentCount: number;
  maxRequests: number;
  windowMs: number;
  remainingRequests: number;
  isLimited: number;
  windowResetAt: number;
};

export type RateLimitStatus = RateLimitStatusValue & { id: RateLimitStatusId };

export type ClientStatusId = string;

export type ClientStatusValue = {
  clientId: string;
  totalRequests: number;
  limitedEndpoints: number;
};

export type ClientStatus = ClientStatusValue & { id: ClientStatusId };
