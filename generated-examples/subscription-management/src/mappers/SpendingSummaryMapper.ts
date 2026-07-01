import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  User_skip_value_,
  SpendingSummary,
  Subscription,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, when the entry's key does not equal the userId param, emit nothing. Otherwise consult subscriptionsByOwner for the values indexed by the userId param to obtain every subscription owned by the user. Compute: monthlyTotalCents = sum over subscriptions whose status field equals the literal 'ACTIVE' of roundHalfToEven(costCents * factor) where factor is 1 when billingCycle equals 'MONTHLY', 1/12 when 'YEARLY', 52/12 when 'WEEKLY', 1/3 when 'QUARTERLY'. annualTotalCents = monthlyTotalCents * 12. activeCount = count of subscriptions whose status field equals 'ACTIVE'. cancelledCount = count whose status field equals 'CANCELLED'. currency = the most frequent currency string across active subscriptions; ties broken by lexicographic ascending order of currency code; unconditionally absent when activeCount is zero. Emit one output pair whose key is the literal zero and whose value lists every required field of SpendingSummary: monthlyTotalCents (always present, sourced from the computed sum); annualTotalCents (always present, sourced from monthlyTotalCents multiplied by twelve); activeCount (always present, sourced from the computed active count); cancelledCount (always present, sourced from the computed cancelled count); currency (present when activeCount is strictly greater than zero, sourced from the most-frequent-currency computation with lex tie-break; absent when activeCount equals zero).
export class SpendingSummaryMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  0,
  SpendingSummary
> {
  constructor(
    private userId: string,
    private subscriptionsByOwner: EagerCollection<User_skip_id_, Subscription>,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[0, SpendingSummary]> {
    // > body
    if (key !== this.userId) return [];

    const subscriptions = this.subscriptionsByOwner.getArray(this.userId);

    const roundHalfToEven = (n: number): number => {
      const floor = Math.floor(n);
      const diff = n - floor;
      if (diff < 0.5) return floor;
      if (diff > 0.5) return floor + 1;
      return floor % 2 === 0 ? floor : floor + 1;
    };

    let monthlyTotalCents = 0;
    let activeCount = 0;
    let cancelledCount = 0;
    const currencyCounts = new Map<string, number>();

    for (const sub of subscriptions) {
      if (sub.status === "ACTIVE") {
        activeCount++;
        let factor: number;
        if (sub.billingCycle === "MONTHLY") factor = 1;
        else if (sub.billingCycle === "YEARLY") factor = 1 / 12;
        else if (sub.billingCycle === "WEEKLY") factor = 52 / 12;
        else factor = 1 / 3;
        monthlyTotalCents += roundHalfToEven(sub.costCents * factor);
        currencyCounts.set(
          sub.currency,
          (currencyCounts.get(sub.currency) ?? 0) + 1,
        );
      } else if (sub.status === "CANCELLED") {
        cancelledCount++;
      }
    }

    const annualTotalCents = monthlyTotalCents * 12;

    let currency: string | undefined = undefined;
    if (activeCount > 0) {
      let bestCount = -1;
      let bestCurrency: string | undefined = undefined;
      for (const [c, count] of currencyCounts) {
        if (
          count > bestCount ||
          (count === bestCount &&
            bestCurrency !== undefined &&
            c < bestCurrency)
        ) {
          bestCount = count;
          bestCurrency = c;
        }
      }
      currency = bestCurrency;
    }

    const summary: SpendingSummary = {
      monthlyTotalCents,
      annualTotalCents,
      activeCount,
      cancelledCount,
      ...(currency !== undefined && { currency }),
    };

    return [[0, summary]];
    // < body
  }
}
