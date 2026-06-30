export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type AuthorIdKey = string;

export type CreateReviewRequest = {
  readonly body?: string;
  readonly rating: number;
  readonly title?: string;
};

export type CreateReviewRequest_skip_id_ = {
  readonly body?: string;
  readonly rating: number;
  readonly title?: string;
};

export type CreateReviewRequest_skip_value_ = {
  readonly body?: string;
  readonly rating: number;
  readonly title?: string;
};

export type CreateSubjectRequest = {
  readonly description?: string;
  readonly name: string;
};

export type CreateSubjectRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
};

export type CreateSubjectRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
};

export type GetReviewForSubjectParams = {
  readonly authorId: string;
  readonly subjectId: string;
};

export type GetSubjectParams = { readonly subjectId: string };

export type GetSubjectRatingSummaryParams = { readonly subjectId: string };

export type GetUserByIdParams = { readonly userId: string };

export type ListMyReviewsParams = { readonly userId: string };

export type ListReviewsForSubjectParams = { readonly subjectId: string };

export type RatingSummary = {
  readonly averageRating: number;
  readonly ratingHistogram: [number, number, number, number, number];
  readonly reviewCount: number;
  readonly subjectId: string;
};

export type RatingSummaryAccum = {
  readonly count: number;
  readonly h1: number;
  readonly h2: number;
  readonly h3: number;
  readonly h4: number;
  readonly h5: number;
  readonly sum: number;
};

export type RatingSummary_skip_id_ = {
  readonly averageRating: number;
  readonly ratingHistogram: [number, number, number, number, number];
  readonly reviewCount: number;
  readonly subjectId: string;
};

export type RatingSummary_skip_value_ = {
  readonly averageRating: number;
  readonly ratingHistogram: [number, number, number, number, number];
  readonly reviewCount: number;
  readonly subjectId: string;
};

export type RatingValue = number;

export type Review = {
  readonly authorId: string;
  readonly body?: string;
  readonly createdAt: string;
  readonly rating: number;
  readonly subjectId: string;
  readonly title?: string;
  readonly updatedAt?: string;
};

export type ReviewKey = {
  readonly authorId: string;
  readonly subjectId: string;
};

export type ReviewList = { readonly items: Review[]; readonly total: number };

export type ReviewList_skip_id_ = {
  readonly items: Review[];
  readonly total: number;
};

export type ReviewList_skip_value_ = {
  readonly items: Review[];
  readonly total: number;
};

export type ReviewStored = {
  readonly body?: string;
  readonly createdAt: string;
  readonly rating: number;
  readonly title?: string;
  readonly updatedAt?: string;
};

export type Review_skip_id_ = {
  readonly authorId: string;
  readonly subjectId: string;
};

export type Review_skip_value_ = {
  readonly body?: string;
  readonly createdAt: string;
  readonly rating: number;
  readonly title?: string;
  readonly updatedAt?: string;
};

export type Subject = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly updatedAt?: string;
};

export type SubjectIdKey = string;

export type SubjectList = { readonly items: Subject[]; readonly total: number };

export type SubjectList_skip_id_ = {
  readonly items: Subject[];
  readonly total: number;
};

export type SubjectList_skip_value_ = {
  readonly items: Subject[];
  readonly total: number;
};

export type Subject_skip_id_ = string;

export type Subject_skip_value_ = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly description?: string;
  readonly name: string;
  readonly updatedAt?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};

export type UpdateReviewRequest = {
  readonly body?: string;
  readonly rating?: number;
  readonly title?: string;
};

export type UpdateReviewRequest_skip_id_ = {
  readonly body?: string;
  readonly rating?: number;
  readonly title?: string;
};

export type UpdateReviewRequest_skip_value_ = {
  readonly body?: string;
  readonly rating?: number;
  readonly title?: string;
};

export type UpdateSubjectRequest = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateSubjectRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateSubjectRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};
