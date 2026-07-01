import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type ClaimJobRequest = { readonly queueName?: string };

export type ClaimJobRequest_skip_id_ = { readonly queueName?: string };

export type ClaimJobRequest_skip_value_ = { readonly queueName?: string };

export type CompleteJobRequest = { readonly result: CompleteJobRequestResult };

export type CompleteJobRequestResult = Record<string, Json>;

export type CompleteJobRequestResult_skip_id_ = Record<string, Json>;

export type CompleteJobRequestResult_skip_value_ = Record<string, Json>;

export type CompleteJobRequest_skip_id_ = {
  readonly result: CompleteJobRequestResult;
};

export type CompleteJobRequest_skip_value_ = {
  readonly result: CompleteJobRequestResult;
};

export type EnqueueJobRequest = {
  readonly kind: string;
  readonly maxAttempts?: number;
  readonly payload: EnqueueJobRequestPayload;
  readonly priority?: number;
  readonly queueName: string;
};

export type EnqueueJobRequestPayload = Record<string, Json>;

export type EnqueueJobRequestPayload_skip_id_ = Record<string, Json>;

export type EnqueueJobRequestPayload_skip_value_ = Record<string, Json>;

export type EnqueueJobRequest_skip_id_ = {
  readonly kind: string;
  readonly maxAttempts?: number;
  readonly payload: EnqueueJobRequestPayload;
  readonly priority?: number;
  readonly queueName: string;
};

export type EnqueueJobRequest_skip_value_ = {
  readonly kind: string;
  readonly maxAttempts?: number;
  readonly payload: EnqueueJobRequestPayload;
  readonly priority?: number;
  readonly queueName: string;
};

export type FailJobRequest = { readonly errorMessage: string };

export type FailJobRequest_skip_id_ = { readonly errorMessage: string };

export type FailJobRequest_skip_value_ = { readonly errorMessage: string };

export type Job = {
  readonly attempts: number;
  readonly claimedAt?: string;
  readonly claimedBy?: string;
  readonly createdAt: string;
  readonly finishedAt?: string;
  readonly id: string;
  readonly kind: string;
  readonly lastError?: string;
  readonly maxAttempts: number;
  readonly ownerId: string;
  readonly payload: JobPayload;
  readonly priority: number;
  readonly queueName: string;
  readonly result?: JobResult;
  readonly status: JobStatus;
};

export type JobList = { readonly jobs: Job[]; readonly total: number };

export type JobList_skip_id_ = { readonly jobs: Job[]; readonly total: number };

export type JobList_skip_value_ = {
  readonly jobs: Job[];
  readonly total: number;
};

export type JobPayload = Record<string, Json>;

export type JobPayload_skip_id_ = Record<string, Json>;

export type JobPayload_skip_value_ = Record<string, Json>;

export type JobResult = Record<string, Json>;

export type JobResult_skip_id_ = Record<string, Json>;

export type JobResult_skip_value_ = Record<string, Json>;

export type JobStatus =
  | "pending"
  | "running"
  | "succeeded"
  | "failed"
  | "cancelled";

export type JobStatus_skip_id_ =
  | "pending"
  | "running"
  | "succeeded"
  | "failed"
  | "cancelled";

export type JobStatus_skip_value_ =
  | "pending"
  | "running"
  | "succeeded"
  | "failed"
  | "cancelled";

export type Job_skip_id_ = string;

export type Job_skip_value_ = {
  readonly attempts: number;
  readonly claimedAt?: string;
  readonly claimedBy?: string;
  readonly createdAt: string;
  readonly finishedAt?: string;
  readonly kind: string;
  readonly lastError?: string;
  readonly maxAttempts: number;
  readonly ownerId: string;
  readonly payload: JobPayload;
  readonly priority: number;
  readonly queueName: string;
  readonly result?: JobResult;
  readonly status: JobStatus;
};

export type ListJobsParams = {
  readonly ownerId?: string;
  readonly queueName?: string;
  readonly status?: string;
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
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
};
