export type BookId = string;

export type BookValue = {
  title: string;
  author: string;
  isbn: string;
  publishedYear: number;
  available: number;
};

export type Book = BookValue & { id: BookId };

export type LoanId = string;

export type LoanValue = {
  bookId: string;
  borrowerName: string;
  borrowedAt: number;
  dueAt: number;
  returnedAt: number | null;
};

export type Loan = LoanValue & { id: LoanId };
