export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateProjectRequest = {
  readonly description?: string;
  readonly name: string;
};

export type CreateProjectRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
};

export type CreateProjectRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
};

export type CreateTaskRequest = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly title: string;
};

export type CreateTaskRequest_skip_id_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly title: string;
};

export type CreateTaskRequest_skip_value_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly title: string;
};

export type GetProjectParams = {
  readonly projectId: string;
  readonly userId: string;
};

export type GetTaskParams = {
  readonly projectId: string;
  readonly taskId: string;
};

export type GetUserParams = { readonly userId: string };

export type ListProjectsParams = {
  readonly status?: string;
  readonly userId: string;
};

export type ListTasksParams = {
  readonly assigneeId?: string;
  readonly projectId: string;
  readonly status?: string;
};

export type Project = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly status: ProjectStatus;
  readonly updatedAt: string;
};

export type ProjectList = { readonly items: Project[]; readonly total: number };

export type ProjectList_skip_id_ = {
  readonly items: Project[];
  readonly total: number;
};

export type ProjectList_skip_value_ = {
  readonly items: Project[];
  readonly total: number;
};

export type ProjectStatus = "ACTIVE" | "ARCHIVED" | "COMPLETED";

export type ProjectStatus_skip_id_ = "ACTIVE" | "ARCHIVED" | "COMPLETED";

export type ProjectStatus_skip_value_ = "ACTIVE" | "ARCHIVED" | "COMPLETED";

export type Project_skip_id_ = string;

export type Project_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly status: ProjectStatus;
  readonly updatedAt: string;
};

export type Task = {
  readonly assigneeId?: string;
  readonly createdAt: string;
  readonly creatorId: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly id: string;
  readonly priority?: TaskPriority;
  readonly projectId: string;
  readonly status: TaskStatus;
  readonly title: string;
  readonly updatedAt: string;
};

export type TaskList = { readonly items: Task[]; readonly total: number };

export type TaskList_skip_id_ = {
  readonly items: Task[];
  readonly total: number;
};

export type TaskList_skip_value_ = {
  readonly items: Task[];
  readonly total: number;
};

export type TaskPriority = "LOW" | "MEDIUM" | "HIGH" | "URGENT";

export type TaskPriority_skip_id_ = "LOW" | "MEDIUM" | "HIGH" | "URGENT";

export type TaskPriority_skip_value_ = "LOW" | "MEDIUM" | "HIGH" | "URGENT";

export type TaskStatus = "TODO" | "IN_PROGRESS" | "DONE" | "BLOCKED";

export type TaskStatus_skip_id_ = "TODO" | "IN_PROGRESS" | "DONE" | "BLOCKED";

export type TaskStatus_skip_value_ =
  | "TODO"
  | "IN_PROGRESS"
  | "DONE"
  | "BLOCKED";

export type Task_skip_id_ = string;

export type Task_skip_value_ = {
  readonly assigneeId?: string;
  readonly createdAt: string;
  readonly creatorId: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly projectId: string;
  readonly status: TaskStatus;
  readonly title: string;
  readonly updatedAt: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateProjectRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly status?: ProjectStatus;
};

export type UpdateProjectRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly status?: ProjectStatus;
};

export type UpdateProjectRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly status?: ProjectStatus;
};

export type UpdateTaskRequest = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title?: string;
};

export type UpdateTaskRequest_skip_id_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title?: string;
};

export type UpdateTaskRequest_skip_value_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly priority?: TaskPriority;
  readonly status?: TaskStatus;
  readonly title?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt: string;
};
