export type TodoIn_progressDoneEnum = "todo" | "in_progress" | "done";

export type TaskId = string;

export type TaskValue = {
  title: string;
  status: TodoIn_progressDoneEnum;
  priority: number;
  createdAt: number;
  description: string | null;
  dueDate: number | null;
};

export type Task = TaskValue & { id: TaskId };
