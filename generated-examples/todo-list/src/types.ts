export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateTodoRequest = {
  readonly description?: string;
  readonly dueDate?: string;
  readonly title: string;
};

export type CreateTodoRequest_skip_id_ = {
  readonly description?: string;
  readonly dueDate?: string;
  readonly title: string;
};

export type CreateTodoRequest_skip_value_ = {
  readonly description?: string;
  readonly dueDate?: string;
  readonly title: string;
};

export type GetMeParams = { readonly userId: string };

export type GetTodoParams = {
  readonly todoId: string;
  readonly userId: string;
};

export type ListTodosParams = {
  readonly completed?: boolean;
  readonly userId: string;
};

export type Todo = {
  readonly completed: boolean;
  readonly createdAt: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly id: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
};

export type TodoList = { readonly items: Todo[]; readonly total: number };

export type TodoList_skip_id_ = {
  readonly items: Todo[];
  readonly total: number;
};

export type TodoList_skip_value_ = {
  readonly items: Todo[];
  readonly total: number;
};

export type Todo_skip_id_ = string;

export type Todo_skip_value_ = {
  readonly completed: boolean;
  readonly createdAt: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
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

export type UpdateTodoRequest = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title?: string;
};

export type UpdateTodoRequest_skip_id_ = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title?: string;
};

export type UpdateTodoRequest_skip_value_ = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title?: string;
};

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};
