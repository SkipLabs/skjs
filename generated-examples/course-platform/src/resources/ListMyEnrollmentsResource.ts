import { EnrollmentsByUserMapper } from "../mappers/EnrollmentsByUserMapper.js";
import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  User_skip_id_,
  EnrollmentByUserValue,
  ListMyEnrollmentsParams,
  Enrollment,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  DepSafe,
} from "@skipruntime/core";
import { deepFreeze } from "@skipruntime/core";

export interface ListMyEnrollmentsResourceInputs extends SharedCollections {
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
}

export class ListMyEnrollmentsResource implements Resource<ListMyEnrollmentsResourceInputs> {
  private readonly status: (("ACTIVE" | "COMPLETED") & DepSafe) | null;
  private readonly userId: string;

  constructor(params: ListMyEnrollmentsParams) {
    this.status = deepFreeze(params.status ?? null);
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyEnrollmentsResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, EnrollmentByUserValue> {
    const enrollmentsByUser = inputs.enrollments.map(
      EnrollmentsByUserMapper,
      this.userId,
      this.status,
    );
    return enrollmentsByUser;
  }
}
