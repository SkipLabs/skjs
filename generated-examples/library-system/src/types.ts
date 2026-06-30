export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Book = {
  readonly author: string;
  readonly availableCopies: number;
  readonly createdAt: string;
  readonly id: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
};

export type BookListResponse = {
  readonly items: Book[];
  readonly total: number;
};

export type BookListResponse_skip_id_ = {
  readonly items: Book[];
  readonly total: number;
};

export type BookListResponse_skip_value_ = {
  readonly items: Book[];
  readonly total: number;
};

export type Book_skip_id_ = string;

export type Book_skip_value_ = {
  readonly author: string;
  readonly availableCopies: number;
  readonly createdAt: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
};

export type CreateBookRequest = {
  readonly author: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
};

export type CreateBookRequest_skip_id_ = {
  readonly author: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
};

export type CreateBookRequest_skip_value_ = {
  readonly author: string;
  readonly isbn?: string;
  readonly title: string;
  readonly totalCopies: number;
};

export type CreateLoanRequest = { readonly bookId: string };

export type CreateLoanRequest_skip_id_ = { readonly bookId: string };

export type CreateLoanRequest_skip_value_ = { readonly bookId: string };

export type GetBookParams = { readonly bookId: string };

export type GetLoanParams = {
  readonly loanId: string;
  readonly userId: string;
};

export type ListLoansParams = {
  readonly status?: string;
  readonly userId: string;
};

export type Loan = {
  readonly bookId: string;
  readonly borrowedAt: string;
  readonly borrowerId: string;
  readonly dueAt: string;
  readonly id: string;
  readonly returnedAt?: string;
  readonly status: LoanStatus;
};

export type LoanListResponse = {
  readonly items: Loan[];
  readonly total: number;
};

export type LoanListResponse_skip_id_ = {
  readonly items: Loan[];
  readonly total: number;
};

export type LoanListResponse_skip_value_ = {
  readonly items: Loan[];
  readonly total: number;
};

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
};

export type UpdateBookRequest = {
  readonly author?: string;
  readonly isbn?: string;
  readonly title?: string;
  readonly totalCopies?: number;
};

export type UpdateBookRequest_skip_id_ = {
  readonly author?: string;
  readonly isbn?: string;
  readonly title?: string;
  readonly totalCopies?: number;
};

export type UpdateBookRequest_skip_value_ = {
  readonly author?: string;
  readonly isbn?: string;
  readonly title?: string;
  readonly totalCopies?: number;
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
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};
