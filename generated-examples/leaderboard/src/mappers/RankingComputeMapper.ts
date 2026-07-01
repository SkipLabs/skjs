import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RankingRow,
  Board_skip_id_,
  Board_skip_value_,
  Ranking,
  ScoreEntry,
  Board,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each board entry, when the entry's key does not equal the boardId param, emit nothing. Otherwise consult entriesByBoard for the ScoreEntry values indexed by the boardId param. Group those values by their userId field. For each group, compute per-user aggregates: entryCount = the number of values in the group; lastEntryAt = the maximum createdAt across the group's values (compared as ISO strings, lexicographic ascending — ISO 8601 with same offset is lex-comparable); totalScore = computed from the entry's value's scoringMode field — when SUM, sum of all points fields in the group; when MAX, maximum of all points fields in the group; when LATEST, the points field of the group's single value selected as follows: first restrict to values whose createdAt equals the maximum createdAt of the group (the lastEntryAt); if exactly one such value exists, take its points; if multiple values tie on createdAt, break the tie by selecting the value whose id field is the smallest (lexicographic ascending on the ScoreEntry id), and take that value's points. Sort groups by totalScore descending, ties broken by userId ascending (lex). Assign 1-based dense ranks: equal totalScore values share the same rank; the next distinct totalScore gets the previous rank + 1. Emit one output pair under the literal-zero key, whose value lists every required field of Ranking explicitly: boardId sourced from the boardId param; scoringMode sourced from the entry's value's scoringMode field; rows is the array of RankingRow objects in sorted order, each row listing rank (computed), userId (the group's userId), totalScore (computed), entryCount (computed) as required fields, and lastEntryAt as an optional field always present when the group is non-empty (sourced from the computed lastEntryAt); totalUsers is optional, always present, sourced from the number of distinct userIds in the consulted values. When the consultation yields no values, emit one output pair under the literal-zero key with boardId from the param, scoringMode from the entry's value, rows as the empty array, totalUsers as zero.
export class RankingComputeMapper implements Mapper<
  Board_skip_id_,
  Board_skip_value_,
  0,
  Ranking
> {
  constructor(
    private boardId: string,
    private entriesByBoard: EagerCollection<Board_skip_id_, ScoreEntry>,
  ) {}

  mapEntry(
    key: Board_skip_id_,
    values: Values<Board_skip_value_>,
    context: Context,
  ): Iterable<[0, Ranking]> {
    // > body
    if (key !== this.boardId) return [];

    const entryValue = values.toArray()[0];
    if (entryValue === undefined) return [];

    const scoringMode = entryValue.scoringMode;
    const scoreEntries = this.entriesByBoard.getArray(this.boardId);

    if (scoreEntries.length === 0) {
      const emptyRanking: Ranking = {
        boardId: this.boardId,
        scoringMode,
        rows: [],
        totalUsers: 0,
      };
      return [[0, emptyRanking]];
    }

    // Group by userId
    const groups = new Map<string, ScoreEntry[]>();
    for (const entry of scoreEntries) {
      const existing = groups.get(entry.userId);
      if (existing === undefined) {
        groups.set(entry.userId, [entry]);
      } else {
        existing.push(entry);
      }
    }

    type GroupAgg = {
      userId: string;
      entryCount: number;
      lastEntryAt: string;
      totalScore: number;
    };

    const aggregates: GroupAgg[] = [];
    for (const [userId, group] of groups) {
      const entryCount = group.length;
      let lastEntryAt = group[0]!.createdAt;
      for (const e of group) {
        if (e.createdAt > lastEntryAt) lastEntryAt = e.createdAt;
      }

      let totalScore: number;
      if (scoringMode === "SUM") {
        let sum = 0;
        for (const e of group) sum += e.points;
        totalScore = sum;
      } else if (scoringMode === "MAX") {
        let max = group[0]!.points;
        for (const e of group) {
          if (e.points > max) max = e.points;
        }
        totalScore = max;
      } else {
        // LATEST
        const latestEntries = group.filter((e) => e.createdAt === lastEntryAt);
        if (latestEntries.length === 1) {
          totalScore = latestEntries[0]!.points;
        } else {
          let chosen = latestEntries[0]!;
          for (const e of latestEntries) {
            if (e.id < chosen.id) chosen = e;
          }
          totalScore = chosen.points;
        }
      }

      aggregates.push({ userId, entryCount, lastEntryAt, totalScore });
    }

    // Sort: totalScore desc, ties by userId asc
    aggregates.sort((a, b) => {
      if (a.totalScore !== b.totalScore) return b.totalScore - a.totalScore;
      if (a.userId < b.userId) return -1;
      if (a.userId > b.userId) return 1;
      return 0;
    });

    // Dense rank
    const rows: RankingRow[] = [];
    let prevScore: number | undefined = undefined;
    let currentRank = 0;
    for (const agg of aggregates) {
      if (prevScore === undefined || agg.totalScore !== prevScore) {
        currentRank += 1;
        prevScore = agg.totalScore;
      }
      const row: RankingRow = {
        rank: currentRank,
        userId: agg.userId,
        totalScore: agg.totalScore,
        entryCount: agg.entryCount,
        lastEntryAt: agg.lastEntryAt,
      };
      rows.push(row);
    }

    const ranking: Ranking = {
      boardId: this.boardId,
      scoringMode,
      rows,
      totalUsers: groups.size,
    };

    return [[0, ranking]];
    // < body
  }
}
