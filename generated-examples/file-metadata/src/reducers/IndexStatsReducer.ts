import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { IndexStatsAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns a record whose fileCount is the accumulator's fileCount plus the value's fileCount, whose totalSizeBytes is the accumulator's totalSizeBytes plus the value's totalSizeBytes, whose mimeTypeCounts is a record merging the accumulator's mimeTypeCounts and the value's mimeTypeCounts by summing per-key counts (each property name present in either map appears once, its value being the sum of the counts from both sides — treating absent as zero), and whose tagCounts is built the same way by per-key summation. remove: returns a record whose fileCount is the accumulator's fileCount minus the value's fileCount, whose totalSizeBytes is the accumulator's totalSizeBytes minus the value's totalSizeBytes, whose mimeTypeCounts is the accumulator's mimeTypeCounts with each property mentioned in the value's mimeTypeCounts decremented by the corresponding count (properties whose resulting count is zero are removed from the map), and whose tagCounts is built the same way.
export class IndexStatsReducer implements Reducer<
  IndexStatsAccum,
  IndexStatsAccum
> {
  initial: IndexStatsAccum = {
    fileCount: 0,
    totalSizeBytes: 0,
    mimeTypeCounts: {},
    tagCounts: {},
  };

  add(accum: IndexStatsAccum, value: IndexStatsAccum): IndexStatsAccum {
    // > add
    const mimeTypeCounts: Record<string, number> = {};
    for (const k of Object.keys(accum.mimeTypeCounts)) {
      mimeTypeCounts[k] = accum.mimeTypeCounts[k] ?? 0;
    }
    for (const k of Object.keys(value.mimeTypeCounts)) {
      mimeTypeCounts[k] =
        (mimeTypeCounts[k] ?? 0) + (value.mimeTypeCounts[k] ?? 0);
    }
    const tagCounts: Record<string, number> = {};
    for (const k of Object.keys(accum.tagCounts)) {
      tagCounts[k] = accum.tagCounts[k] ?? 0;
    }
    for (const k of Object.keys(value.tagCounts)) {
      tagCounts[k] = (tagCounts[k] ?? 0) + (value.tagCounts[k] ?? 0);
    }
    return {
      fileCount: accum.fileCount + value.fileCount,
      totalSizeBytes: accum.totalSizeBytes + value.totalSizeBytes,
      mimeTypeCounts,
      tagCounts,
    };
    // < add
  }

  remove(
    accum: IndexStatsAccum,
    value: IndexStatsAccum,
  ): Nullable<IndexStatsAccum> {
    // > remove
    const mimeTypeCounts: Record<string, number> = {};
    for (const k of Object.keys(accum.mimeTypeCounts)) {
      mimeTypeCounts[k] = accum.mimeTypeCounts[k] ?? 0;
    }
    for (const k of Object.keys(value.mimeTypeCounts)) {
      const next = (mimeTypeCounts[k] ?? 0) - (value.mimeTypeCounts[k] ?? 0);
      if (next === 0) {
        delete mimeTypeCounts[k];
      } else {
        mimeTypeCounts[k] = next;
      }
    }
    const tagCounts: Record<string, number> = {};
    for (const k of Object.keys(accum.tagCounts)) {
      tagCounts[k] = accum.tagCounts[k] ?? 0;
    }
    for (const k of Object.keys(value.tagCounts)) {
      const next = (tagCounts[k] ?? 0) - (value.tagCounts[k] ?? 0);
      if (next === 0) {
        delete tagCounts[k];
      } else {
        tagCounts[k] = next;
      }
    }
    return {
      fileCount: accum.fileCount - value.fileCount,
      totalSizeBytes: accum.totalSizeBytes - value.totalSizeBytes,
      mimeTypeCounts,
      tagCounts,
    };
    // < remove
  }
}
