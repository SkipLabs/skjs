import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Metric_skip_id_,
  Metric_skip_value_,
  User_skip_id_,
  Metric,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each metric entry, emit one output pair whose key is sourced from the entry's value's ownerId field (a User primary key) and whose value lists every required field of Metric explicitly — id sourced from the entry's key; ownerId sourced from the entry's value; name sourced from the entry's value; kind sourced from the entry's value; createdAt sourced from the entry's value; and every optional field with an explicit presence clause: displayName present when the entry's value's displayName field is present, sourced from the entry's value, absent otherwise; description present when the entry's value's description field is present, sourced from the entry's value, absent otherwise; unit present when the entry's value's unit field is present, sourced from the entry's value, absent otherwise; updatedAt present when the entry's value's updatedAt field is present, sourced from the entry's value, absent otherwise.
export class MetricByOwnerWithIdMapper implements Mapper<
  Metric_skip_id_,
  Metric_skip_value_,
  User_skip_id_,
  Metric
> {
  mapEntry(
    key: Metric_skip_id_,
    values: Values<Metric_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Metric]> {
    // > body
    const emits: [User_skip_id_, Metric][] = [];
    for (const value of values.toArray()) {
      const metric: Metric = {
        id: key,
        ownerId: value.ownerId,
        name: value.name,
        kind: value.kind,
        createdAt: value.createdAt,
        ...(value.displayName !== undefined && {
          displayName: value.displayName,
        }),
        ...(value.description !== undefined && {
          description: value.description,
        }),
        ...(value.unit !== undefined && { unit: value.unit }),
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([value.ownerId, metric]);
    }
    return emits;
    // < body
  }
}
