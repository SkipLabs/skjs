export type TodoId = string;

export type TodoValue = {
  title: string;
  completed: number;
  description: string | null;
  dueDate: number | null;
  createdAt: number;
};

export type Todo = TodoValue & { id: TodoId };
