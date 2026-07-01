import { RatingContributionMapper } from "./mappers/RatingContributionMapper.js";
import { ReviewByAuthorMapper } from "./mappers/ReviewByAuthorMapper.js";
import { ReviewBySubjectMapper } from "./mappers/ReviewBySubjectMapper.js";
import { RatingSummaryReducer } from "./reducers/RatingSummaryReducer.js";
import type {
  ReviewKey,
  ReviewStored,
  Subject_skip_id_,
  Subject,
  Subject_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  SubjectIdKey,
  RatingSummaryAccum,
  AuthorIdKey,
  Review,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly reviews: EagerCollection<ReviewKey, ReviewStored>;
  readonly subjects: EagerCollection<Subject_skip_id_, Subject_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly ratingSummaryBySubject: EagerCollection<
    SubjectIdKey,
    RatingSummaryAccum
  >;
  readonly reviews: EagerCollection<ReviewKey, ReviewStored>;
  readonly reviewsByAuthor: EagerCollection<AuthorIdKey, Review>;
  readonly reviewsBySubject: EagerCollection<SubjectIdKey, Review>;
  readonly subjects: EagerCollection<Subject_skip_id_, Subject_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const ratingContributionsBySubject = inputs.reviews.map(
    RatingContributionMapper,
  );
  const ratingSummaryBySubject =
    ratingContributionsBySubject.reduce(RatingSummaryReducer);
  const output_ratingSummaryBySubject = ratingSummaryBySubject;
  const output_reviews = inputs.reviews;
  const reviewsByAuthor = inputs.reviews.map(ReviewByAuthorMapper);
  const output_reviewsByAuthor = reviewsByAuthor;
  const reviewsBySubject = inputs.reviews.map(ReviewBySubjectMapper);
  const output_reviewsBySubject = reviewsBySubject;
  const output_subjects = inputs.subjects;
  const output_users = inputs.users;
  return {
    ratingSummaryBySubject: output_ratingSummaryBySubject,
    reviews: output_reviews,
    reviewsByAuthor: output_reviewsByAuthor,
    reviewsBySubject: output_reviewsBySubject,
    subjects: output_subjects,
    users: output_users,
  };
}
