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

export type CreateProjectRequest = {
  readonly description?: string;
  readonly name: string;
  readonly status?: ProjectStatus;
} & { readonly [key: string]: Json | null };

export type CreateProjectRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly status?: ProjectStatus;
} & { readonly [key: string]: Json | null };

export type CreateProjectRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly status?: ProjectStatus;
} & { readonly [key: string]: Json | null };

export type CreateTaskRequest = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateTaskRequest_skip_id_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateTaskRequest_skip_value_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type GetProjectParams = { readonly projectId: string } & {
  readonly [key: string]: Json | null;
};

export type GetTaskParams = { readonly taskId: string } & {
  readonly [key: string]: Json | null;
};

export type ListProjectTasksParams = { readonly projectId: string } & {
  readonly [key: string]: Json | null;
};

export type ListProjectsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Project = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly status: ProjectStatus;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type ProjectList = {
  readonly items: Project[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ProjectList_skip_id_ = {
  readonly items: Project[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ProjectList_skip_value_ = {
  readonly items: Project[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ProjectStatus = "ACTIVE" | "ARCHIVED";

export type ProjectStatus_skip_id_ = "ACTIVE" | "ARCHIVED";

export type ProjectStatus_skip_value_ = "ACTIVE" | "ARCHIVED";

export type Project_skip_id_ = string;

export type Project_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly status: ProjectStatus;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type Task = {
  readonly assigneeId?: string;
  readonly completedAt?: string;
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly id: string;
  readonly priority: TaskPriority;
  readonly projectId: string;
  readonly status: TaskStatus;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type TaskList = { readonly items: Task[]; readonly total?: number } & {
  readonly [key: string]: Json | null;
};

export type TaskList_skip_id_ = {
  readonly items: Task[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type TaskList_skip_value_ = {
  readonly items: Task[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type TaskPriority = "LOW" | "MEDIUM" | "HIGH";

export type TaskPriority_skip_id_ = "LOW" | "MEDIUM" | "HIGH";

export type TaskPriority_skip_value_ = "LOW" | "MEDIUM" | "HIGH";

export type TaskStatus = "TODO" | "IN_PROGRESS" | "DONE";

export type TaskStatus_skip_id_ = "TODO" | "IN_PROGRESS" | "DONE";

export type TaskStatus_skip_value_ = "TODO" | "IN_PROGRESS" | "DONE";

export type Task_skip_id_ = string;

export type Task_skip_value_ = {
  readonly assigneeId?: string;
  readonly completedAt?: string;
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority: TaskPriority;
  readonly projectId: string;
  readonly status: TaskStatus;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateProjectRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly status?: ProjectStatus;
} & { readonly [key: string]: Json | null };

export type UpdateProjectRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly status?: ProjectStatus;
} & { readonly [key: string]: Json | null };

export type UpdateProjectRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly status?: ProjectStatus;
} & { readonly [key: string]: Json | null };

export type UpdateTaskRequest = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTaskRequest_skip_id_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTaskRequest_skip_value_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
