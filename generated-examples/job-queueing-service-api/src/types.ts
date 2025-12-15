export type PendingProcessingo5ljfmEnum = "completed" | "failed" | "pending" | "processing";

export type JobId = string;

export type JobValue = {
  name: string;
  status: PendingProcessingo5ljfmEnum;
  priority: number;
  createdAt: number;
  updatedAt: number;
  payload: { [name: string]: string } | null;
  result: string | null;
  errorMessage: string | null;
  retryCount: number | null;
  maxRetries: number | null;
};

export type Job = JobValue & { id: JobId };
