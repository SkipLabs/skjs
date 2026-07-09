import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CreateQueueRequest = {
  readonly concurrencyLimit?: number;
  readonly description?: string;
  readonly name: string;
  readonly paused?: boolean;
} & { readonly [key: string]: Json | null };

export type CreateQueueRequest_skip_id_ = {
  readonly concurrencyLimit?: number;
  readonly description?: string;
  readonly name: string;
  readonly paused?: boolean;
} & { readonly [key: string]: Json | null };

export type CreateQueueRequest_skip_value_ = {
  readonly concurrencyLimit?: number;
  readonly description?: string;
  readonly name: string;
  readonly paused?: boolean;
} & { readonly [key: string]: Json | null };

export type EnqueueJobRequest = {
  readonly kind: string;
  readonly maxAttempts?: number;
  readonly payload: JobPayload;
  readonly priority?: number;
} & { readonly [key: string]: Json | null };

export type EnqueueJobRequest_skip_id_ = {
  readonly kind: string;
  readonly maxAttempts?: number;
  readonly payload: JobPayload;
  readonly priority?: number;
} & { readonly [key: string]: Json | null };

export type EnqueueJobRequest_skip_value_ = {
  readonly kind: string;
  readonly maxAttempts?: number;
  readonly payload: JobPayload;
  readonly priority?: number;
} & { readonly [key: string]: Json | null };

export type FailJobRequest = { readonly error: string } & {
  readonly [key: string]: Json | null;
};

export type FailJobRequest_skip_id_ = { readonly error: string } & {
  readonly [key: string]: Json | null;
};

export type FailJobRequest_skip_value_ = { readonly error: string } & {
  readonly [key: string]: Json | null;
};

export type GetJobParams = { readonly jobId: string } & {
  readonly [key: string]: Json | null;
};

export type GetQueueParams = { readonly queueId: string } & {
  readonly [key: string]: Json | null;
};

export type Job = {
  readonly attempts: number;
  readonly enqueuedAt: string;
  readonly finishedAt?: string;
  readonly id: string;
  readonly kind: string;
  readonly lastError?: string;
  readonly maxAttempts: number;
  readonly payload: JobPayload;
  readonly priority: number;
  readonly queueId: string;
  readonly result?: JobResult;
  readonly startedAt?: string;
  readonly status: JobStatus;
  readonly submitterId: string;
  readonly workerId?: string;
} & { readonly [key: string]: Json | null };

export type JobList = { readonly jobs: Job[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type JobList_skip_id_ = {
  readonly jobs: Job[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type JobList_skip_value_ = {
  readonly jobs: Job[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

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
  readonly enqueuedAt: string;
  readonly finishedAt?: string;
  readonly kind: string;
  readonly lastError?: string;
  readonly maxAttempts: number;
  readonly payload: JobPayload;
  readonly priority: number;
  readonly queueId: string;
  readonly result?: JobResult;
  readonly startedAt?: string;
  readonly status: JobStatus;
  readonly submitterId: string;
  readonly workerId?: string;
} & { readonly [key: string]: Json | null };

export type JobsByQueueRunningCountParams = { readonly queueId: string } & {
  readonly [key: string]: Json | null;
};

export type ListJobsForQueueParams = {
  readonly queueId: string;
  readonly status?: string;
} & { readonly [key: string]: Json | null };

export type ListQueuesParams = Record<string, Json | null>;

export type Queue = {
  readonly concurrencyLimit: number;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly paused: boolean;
} & { readonly [key: string]: Json | null };

export type QueueList = { readonly queues: Queue[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type QueueList_skip_id_ = {
  readonly queues: Queue[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type QueueList_skip_value_ = {
  readonly queues: Queue[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Queue_skip_id_ = string;

export type Queue_skip_value_ = {
  readonly concurrencyLimit: number;
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly paused: boolean;
} & { readonly [key: string]: Json | null };

export type RunningJobCount = number;

export type SucceedJobRequest = { readonly result: JobResult } & {
  readonly [key: string]: Json | null;
};

export type SucceedJobRequest_skip_id_ = { readonly result: JobResult } & {
  readonly [key: string]: Json | null;
};

export type SucceedJobRequest_skip_value_ = { readonly result: JobResult } & {
  readonly [key: string]: Json | null;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateQueueRequest = {
  readonly concurrencyLimit?: number;
  readonly description?: string;
  readonly name?: string;
  readonly paused?: boolean;
} & { readonly [key: string]: Json | null };

export type UpdateQueueRequest_skip_id_ = {
  readonly concurrencyLimit?: number;
  readonly description?: string;
  readonly name?: string;
  readonly paused?: boolean;
} & { readonly [key: string]: Json | null };

export type UpdateQueueRequest_skip_value_ = {
  readonly concurrencyLimit?: number;
  readonly description?: string;
  readonly name?: string;
  readonly paused?: boolean;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
