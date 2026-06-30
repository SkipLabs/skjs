import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollOption,
  Poll,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each poll option entry, emit one output pair whose key is sourced from the entry's key's pollId field, and whose value lists every required field of PollOption explicitly: pollId sourced from the entry's key's pollId field; optionIndex sourced from the entry's key's optionIndex field; text sourced from the entry's value's text field. The original optionIndex from the key is re-injected into the value so downstream assembly can reconstruct the full PollOption shape under the new key keyed by pollId alone.
export class PollOptionByPollMapper implements Mapper<
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollOption
> {
  mapEntry(
    key: PollOption_skip_id_,
    values: Values<PollOption_skip_value_>,
    context: Context,
  ): Iterable<[Poll_skip_id_, PollOption]> {
    // > body
    const emits: [Poll_skip_id_, PollOption][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.pollId,
        {
          pollId: key.pollId,
          optionIndex: key.optionIndex,
          text: value.text,
        },
      ]);
    }
    return emits;
    // < body
  }
}
