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

export type CreateTodoRequest = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateTodoRequest_skip_id_ = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateTodoRequest_skip_value_ = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type GetTodoParams = {
  readonly todoId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListTodosParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
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
} & { readonly [key: string]: Json | null };

export type TodoList = {
  readonly items: Todo[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type TodoList_skip_id_ = {
  readonly items: Todo[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type TodoList_skip_value_ = {
  readonly items: Todo[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Todo_skip_id_ = string;

export type Todo_skip_value_ = {
  readonly completed: boolean;
  readonly createdAt: string;
  readonly description?: string;
  readonly dueDate?: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

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

export type UpdateTodoRequest = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTodoRequest_skip_id_ = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTodoRequest_skip_value_ = {
  readonly completed?: boolean;
  readonly description?: string;
  readonly dueDate?: string;
  readonly title?: string;
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
