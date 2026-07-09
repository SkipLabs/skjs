import type { Json } from "@skipruntime/core";

export type ActiveLoanCount = number;

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

export type Book = {
  readonly author: string;
  readonly availableCopies: number;
  readonly createdAt: string;
  readonly id: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
} & { readonly [key: string]: Json | null };

export type BookList = { readonly items: Book[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type BookList_skip_id_ = {
  readonly items: Book[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type BookList_skip_value_ = {
  readonly items: Book[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type BookStored = {
  readonly author: string;
  readonly createdAt: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
} & { readonly [key: string]: Json | null };

export type Book_skip_id_ = string;

export type Book_skip_value_ = {
  readonly author: string;
  readonly availableCopies: number;
  readonly createdAt: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
} & { readonly [key: string]: Json | null };

export type CreateBookRequest = {
  readonly author: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
} & { readonly [key: string]: Json | null };

export type CreateBookRequest_skip_id_ = {
  readonly author: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
} & { readonly [key: string]: Json | null };

export type CreateBookRequest_skip_value_ = {
  readonly author: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
} & { readonly [key: string]: Json | null };

export type CreateLoanRequest = { readonly bookId: string } & {
  readonly [key: string]: Json | null;
};

export type CreateLoanRequest_skip_id_ = { readonly bookId: string } & {
  readonly [key: string]: Json | null;
};

export type CreateLoanRequest_skip_value_ = { readonly bookId: string } & {
  readonly [key: string]: Json | null;
};

export type GetBookParams = { readonly bookId: string } & {
  readonly [key: string]: Json | null;
};

export type GetLoanParams = {
  readonly loanId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetMeParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListLoansParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Loan = {
  readonly bookId: string;
  readonly borrowedAt: string;
  readonly borrowerId: string;
  readonly dueAt: string;
  readonly id: string;
  readonly returnedAt?: string;
  readonly status: LoanStatus;
} & { readonly [key: string]: Json | null };

export type LoanList = { readonly items: Loan[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type LoanList_skip_id_ = {
  readonly items: Loan[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type LoanList_skip_value_ = {
  readonly items: Loan[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type LoanStatus = "ACTIVE" | "RETURNED";

export type LoanStatus_skip_id_ = "ACTIVE" | "RETURNED";

export type LoanStatus_skip_value_ = "ACTIVE" | "RETURNED";

export type Loan_skip_id_ = string;

export type Loan_skip_value_ = {
  readonly bookId: string;
  readonly borrowedAt: string;
  readonly borrowerId: string;
  readonly dueAt: string;
  readonly returnedAt?: string;
  readonly status: LoanStatus;
} & { readonly [key: string]: Json | null };

export type UpdateBookRequest = {
  readonly author?: string;
  readonly isbn?: string;
  readonly title?: string;
  readonly totalCopies?: number;
} & { readonly [key: string]: Json | null };

export type UpdateBookRequest_skip_id_ = {
  readonly author?: string;
  readonly isbn?: string;
  readonly title?: string;
  readonly totalCopies?: number;
} & { readonly [key: string]: Json | null };

export type UpdateBookRequest_skip_value_ = {
  readonly author?: string;
  readonly isbn?: string;
  readonly title?: string;
  readonly totalCopies?: number;
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

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
