import type {
  Review_skip_id_,
  Review,
  Review_skip_value_,
  Subject_skip_id_,
  Subject,
  SubjectStored,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly reviews: EagerCollection<Review_skip_id_, Review_skip_value_>;
  readonly subjects: EagerCollection<Subject_skip_id_, SubjectStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly reviews: EagerCollection<Review_skip_id_, Review_skip_value_>;
  readonly subjects: EagerCollection<Subject_skip_id_, SubjectStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_reviews = inputs.reviews;
  const output_subjects = inputs.subjects;
  const output_users = inputs.users;
  return {
    reviews: output_reviews,
    subjects: output_subjects,
    users: output_users,
  };
}
