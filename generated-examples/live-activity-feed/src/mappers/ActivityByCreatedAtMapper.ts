import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Activity_skip_id_,
  Activity_skip_value_,
  ActivityCreatedAtKey,
  Activity,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each activity entry, compute the numeric epoch-millisecond timestamp by converting the entry's value's createdAt field (an ISO date-time string) via date-to-epoch-millis conversion, then emit one output pair whose key is the unary negation of that numeric epoch-millisecond timestamp (a number; ascending numeric key ordering thus yields newest-first / descending chronological order), paired with a new value of type Activity listing every required field explicitly: the id field is sourced from the entry's key, the authorId field is sourced from the entry's value's authorId field, the type field is sourced from the entry's value's type field, the message field is sourced from the entry's value's message field, the createdAt field is sourced from the entry's value's createdAt field, the targetUrl field is sourced from the entry's value's targetUrl field when present, and the metadata field is sourced from the entry's value's metadata field when present.
export class ActivityByCreatedAtMapper implements Mapper<
  Activity_skip_id_,
  Activity_skip_value_,
  ActivityCreatedAtKey,
  Activity
> {
  mapEntry(
    key: Activity_skip_id_,
    values: Values<Activity_skip_value_>,
    context: Context,
  ): Iterable<[ActivityCreatedAtKey, Activity]> {
    // > body
    const emits: [ActivityCreatedAtKey, Activity][] = [];
    for (const value of values.toArray()) {
      const epoch = new Date(value.createdAt).getTime();
      const activity: Activity = {
        id: key,
        authorId: value.authorId,
        type: value.type,
        message: value.message,
        createdAt: value.createdAt,
        ...(value.targetUrl !== undefined && { targetUrl: value.targetUrl }),
        ...(value.metadata !== undefined && { metadata: value.metadata }),
      };
      emits.push([-epoch, activity]);
    }
    return emits;
    // < body
  }
}
