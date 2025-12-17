import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "@skipruntime/core";

import type {
  UserId,
  UserValue,
  ReferralId,
  ReferralValue,
  RewardId,
  RewardValue,
  ReferralStatsId,
  ReferralStatsValue,
  PendingCompletedav1jscEnum,
  ReferralsByReferrerResourceParams,
  RewardsByUserResourceParams,
} from "./types.js";

export type ReferralStatus = PendingCompletedav1jscEnum;

export type ReferralForStats = {
  status: ReferralStatus;
  rewardAmount: number;
};

export type StatsAccum = {
  totalReferrals: number;
  completedReferrals: number;
  pendingReferrals: number;
  totalRewardsEarned: number;
};

type Inputs = {
  users: Entry<UserId, UserValue>[];
  referrals: Entry<ReferralId, ReferralValue>[];
  rewards: Entry<RewardId, RewardValue>[];
};

export type InputCollections = {
  users: EagerCollection<UserId, UserValue>;
  referrals: EagerCollection<ReferralId, ReferralValue>;
  rewards: EagerCollection<RewardId, RewardValue>;
};

export type GraphCollections = {
  users: EagerCollection<UserId, UserValue>;
  referrals: EagerCollection<ReferralId, ReferralValue>;
  rewards: EagerCollection<RewardId, RewardValue>;
  referralStats: EagerCollection<ReferralStatsId, ReferralStatsValue>;
};

type Resources = {
  "users": new (params: Json) => Resource<GraphCollections>;
  "referrals": new (params: Json) => Resource<GraphCollections>;
  "referrals-by-referrer": new (params: Json) => Resource<GraphCollections>;
  "referrals-by-status-pending": new (params: Json) => Resource<GraphCollections>;
  "referrals-by-status-completed": new (params: Json) => Resource<GraphCollections>;
  "rewards": new (params: Json) => Resource<GraphCollections>;
  "rewards-by-user": new (params: Json) => Resource<GraphCollections>;
  "stats": new (params: Json) => Resource<GraphCollections>;
};

export class ReferralToUserKeyMapper implements Mapper<ReferralId, ReferralValue, UserId, ReferralForStats> {
  constructor() {
  }

  mapEntry(
    _key: ReferralId,
    values: Values<ReferralValue>,
    _context: Context
  ): Iterable<[UserId, ReferralForStats]> {
    const arr = values.toArray();
    const result: Array<[UserId, ReferralForStats]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      const forStats: ReferralForStats = {
        status: v.status,
        rewardAmount: v.rewardAmount
      };
      result.push([v.referrerId, forStats]);
    }
    return result;
  }
}

export class StatsAccumToStatsValueMapper implements Mapper<UserId, StatsAccum, ReferralStatsId, ReferralStatsValue> {
  constructor() {
  }

  mapEntry(
    key: UserId,
    values: Values<StatsAccum>,
    _context: Context
  ): Iterable<[ReferralStatsId, ReferralStatsValue]> {
    const arr = values.toArray();
    const result: Array<[ReferralStatsId, ReferralStatsValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      const conversionRate = v.totalReferrals > 0 ? v.completedReferrals / v.totalReferrals : 0;
      const statsValue: ReferralStatsValue = {
        userId: key,
        totalReferrals: v.totalReferrals,
        completedReferrals: v.completedReferrals,
        pendingReferrals: v.pendingReferrals,
        totalRewardsEarned: v.totalRewardsEarned,
        conversionRate: conversionRate
      };
      result.push([key, statsValue]);
    }
    return result;
  }
}

export class ReferralByReferrerMapper implements Mapper<ReferralId, ReferralValue, ReferralId, ReferralValue> {
  private referrerId: string;

  constructor(referrerId: string) {
    this.referrerId = referrerId;
  }

  mapEntry(
    key: ReferralId,
    values: Values<ReferralValue>,
    _context: Context
  ): Iterable<[ReferralId, ReferralValue]> {
    const arr = values.toArray();
    const result: Array<[ReferralId, ReferralValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.referrerId === this.referrerId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class ReferralByStatusMapper implements Mapper<ReferralId, ReferralValue, ReferralId, ReferralValue> {
  private status: ReferralStatus;

  constructor(status: ReferralStatus) {
    this.status = status;
  }

  mapEntry(
    key: ReferralId,
    values: Values<ReferralValue>,
    _context: Context
  ): Iterable<[ReferralId, ReferralValue]> {
    const arr = values.toArray();
    const result: Array<[ReferralId, ReferralValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.status === this.status) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class RewardByUserMapper implements Mapper<RewardId, RewardValue, RewardId, RewardValue> {
  private userId: string;

  constructor(userId: string) {
    this.userId = userId;
  }

  mapEntry(
    key: RewardId,
    values: Values<RewardValue>,
    _context: Context
  ): Iterable<[RewardId, RewardValue]> {
    const arr = values.toArray();
    const result: Array<[RewardId, RewardValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class ReferralStatsReducer implements Reducer<ReferralForStats, StatsAccum> {
  initial: Nullable<StatsAccum> = null;

  constructor() {
  }

  add(accum: Nullable<StatsAccum>, value: ReferralForStats & DepSafe): StatsAccum {
    const isCompleted = value.status === "completed" ? 1 : 0;
    const isPending = value.status === "pending" ? 1 : 0;
    const rewardEarned = value.status === "completed" ? value.rewardAmount : 0;
    
    if (accum === null) {
      return {
        totalReferrals: 1,
        completedReferrals: isCompleted,
        pendingReferrals: isPending,
        totalRewardsEarned: rewardEarned
      };
    }
    return {
      totalReferrals: accum.totalReferrals + 1,
      completedReferrals: accum.completedReferrals + isCompleted,
      pendingReferrals: accum.pendingReferrals + isPending,
      totalRewardsEarned: accum.totalRewardsEarned + rewardEarned
    };
  }

  remove(accum: StatsAccum, value: ReferralForStats & DepSafe): Nullable<StatsAccum> {
    const isCompleted = value.status === "completed" ? 1 : 0;
    const isPending = value.status === "pending" ? 1 : 0;
    const rewardEarned = value.status === "completed" ? value.rewardAmount : 0;
    
    const newTotal = accum.totalReferrals - 1;
    if (newTotal <= 0) {
      return null;
    }
    return {
      totalReferrals: newTotal,
      completedReferrals: accum.completedReferrals - isCompleted,
      pendingReferrals: accum.pendingReferrals - isPending,
      totalRewardsEarned: accum.totalRewardsEarned - rewardEarned
    };
  }
}

export class UsersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UserId, UserValue> {
    return cs.users;
  }
}

export class ReferralsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReferralId, ReferralValue> {
    return cs.referrals;
  }
}

export class ReferralsByReferrerResource implements Resource<GraphCollections> {
  private referrerId: string;

  constructor(params: Json) {
    const typed = params as ReferralsByReferrerResourceParams;
    this.referrerId = typed.referrerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReferralId, ReferralValue> {
    return cs.referrals.map(ReferralByReferrerMapper, this.referrerId);
  }
}

export class ReferralsByStatusPendingResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReferralId, ReferralValue> {
    return cs.referrals.map(ReferralByStatusMapper, "pending" as ReferralStatus);
  }
}

export class ReferralsByStatusCompletedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReferralId, ReferralValue> {
    return cs.referrals.map(ReferralByStatusMapper, "completed" as ReferralStatus);
  }
}

export class RewardsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RewardId, RewardValue> {
    return cs.rewards;
  }
}

export class RewardsByUserResource implements Resource<GraphCollections> {
  private userId: string;

  constructor(params: Json) {
    const typed = params as RewardsByUserResourceParams;
    this.userId = typed.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RewardId, RewardValue> {
    return cs.rewards.map(RewardByUserMapper, this.userId);
  }
}

export class StatsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReferralStatsId, ReferralStatsValue> {
    return cs.referralStats;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyUsers: Entry<UserId, UserValue>[] = Array.of();
    const emptyReferrals: Entry<ReferralId, ReferralValue>[] = Array.of();
    const emptyRewards: Entry<RewardId, RewardValue>[] = Array.of();
    this.initialData = { users: emptyUsers, referrals: emptyReferrals, rewards: emptyRewards };
    this.resources = { 
      "users": UsersResource, 
      "referrals": ReferralsResource, 
      "referrals-by-referrer": ReferralsByReferrerResource, 
      "referrals-by-status-pending": ReferralsByStatusPendingResource, 
      "referrals-by-status-completed": ReferralsByStatusCompletedResource, 
      "rewards": RewardsResource, 
      "rewards-by-user": RewardsByUserResource, 
      "stats": StatsResource 
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const referralsByUser = inputs.referrals.map(ReferralToUserKeyMapper);
    const statsAccum = referralsByUser.reduce(ReferralStatsReducer);
    const referralStats = statsAccum.map(StatsAccumToStatsValueMapper);
    
    return { 
      users: inputs.users, 
      referrals: inputs.referrals, 
      rewards: inputs.rewards, 
      referralStats: referralStats 
    };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
