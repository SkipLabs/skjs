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

export type AuthorSubjectKey = {
  readonly authorId: string;
  readonly subjectId: string;
} & { readonly [key: string]: Json | null };

export type CreateReviewRequest = {
  readonly body?: string;
  readonly rating: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type CreateReviewRequest_skip_id_ = {
  readonly body?: string;
  readonly rating: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type CreateReviewRequest_skip_value_ = {
  readonly body?: string;
  readonly rating: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type CreateSubjectRequest = {
  readonly category: SubjectCategory;
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateSubjectRequest_skip_id_ = {
  readonly category: SubjectCategory;
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateSubjectRequest_skip_value_ = {
  readonly category: SubjectCategory;
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type GetReviewParams = { readonly reviewId: string } & {
  readonly [key: string]: Json | null;
};

export type GetSubjectParams = { readonly subjectId: string } & {
  readonly [key: string]: Json | null;
};

export type GetUserByIdParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListMyReviewsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListReviewsForSubjectParams = { readonly subjectId: string } & {
  readonly [key: string]: Json | null;
};

export type RatingDistribution = {
  readonly five: number;
  readonly four: number;
  readonly one: number;
  readonly three: number;
  readonly two: number;
} & { readonly [key: string]: Json | null };

export type RatingDistribution_skip_id_ = {
  readonly five: number;
  readonly four: number;
  readonly one: number;
  readonly three: number;
  readonly two: number;
} & { readonly [key: string]: Json | null };

export type RatingDistribution_skip_value_ = {
  readonly five: number;
  readonly four: number;
  readonly one: number;
  readonly three: number;
  readonly two: number;
} & { readonly [key: string]: Json | null };

export type Review = {
  readonly authorId: string;
  readonly body?: string;
  readonly createdAt: string;
  readonly id: string;
  readonly rating: number;
  readonly subjectId: string;
  readonly title?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type ReviewList = {
  readonly reviews: Review[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReviewList_skip_id_ = {
  readonly reviews: Review[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReviewList_skip_value_ = {
  readonly reviews: Review[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Review_skip_id_ = string;

export type Review_skip_value_ = {
  readonly authorId: string;
  readonly body?: string;
  readonly createdAt: string;
  readonly rating: number;
  readonly subjectId: string;
  readonly title?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Subject = {
  readonly averageRating: number;
  readonly category: SubjectCategory;
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ratingDistribution: RatingDistribution;
  readonly reviewCount: number;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type SubjectCategory =
  | "PRODUCT"
  | "SERVICE"
  | "BOOK"
  | "MOVIE"
  | "RESTAURANT"
  | "OTHER";

export type SubjectCategory_skip_id_ =
  | "PRODUCT"
  | "SERVICE"
  | "BOOK"
  | "MOVIE"
  | "RESTAURANT"
  | "OTHER";

export type SubjectCategory_skip_value_ =
  | "PRODUCT"
  | "SERVICE"
  | "BOOK"
  | "MOVIE"
  | "RESTAURANT"
  | "OTHER";

export type SubjectList = {
  readonly subjects: Subject[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SubjectList_skip_id_ = {
  readonly subjects: Subject[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SubjectList_skip_value_ = {
  readonly subjects: Subject[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SubjectStored = {
  readonly category: string;
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly name: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Subject_skip_id_ = string;

export type Subject_skip_value_ = {
  readonly averageRating: number;
  readonly category: SubjectCategory;
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly name: string;
  readonly ratingDistribution: RatingDistribution;
  readonly reviewCount: number;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateReviewRequest = {
  readonly body?: string;
  readonly rating?: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateReviewRequest_skip_id_ = {
  readonly body?: string;
  readonly rating?: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateReviewRequest_skip_value_ = {
  readonly body?: string;
  readonly rating?: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSubjectRequest = {
  readonly category?: SubjectCategory;
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSubjectRequest_skip_id_ = {
  readonly category?: SubjectCategory;
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSubjectRequest_skip_value_ = {
  readonly category?: SubjectCategory;
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
