import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  MentionId,
  MentionValue,
  FollowId,
  FollowValue,
  LikeId,
  LikeValue,
  NotificationId,
  NotificationValue,
  MentionFollowLikeEnum,
} from "./types.js";

export type NotificationType = MentionFollowLikeEnum;

export type NotificationEventValue = {
  actorId: string;
  timestamp: number;
};

export type NotificationAccum = {
  count: number;
  latestTimestamp: number;
  actorIds: Array<string>;
};

export type Inputs = {
  mentions: InputDefinition<MentionId, MentionValue>;
  follows: InputDefinition<FollowId, FollowValue>;
  likes: InputDefinition<LikeId, LikeValue>;
};

export type InputCollections = {
  mentions: EagerCollection<MentionId, MentionValue>;
  follows: EagerCollection<FollowId, FollowValue>;
  likes: EagerCollection<LikeId, LikeValue>;
};

export type GraphCollections = {
  notifications: EagerCollection<NotificationId, NotificationValue>;
};

export type Resources = {
  readonly "notifications": ResourceClass<GraphCollections, {}>;
  readonly "notifications-by-user": ResourceClass<GraphCollections, { userId: string }>;
};

export class MentionToNotificationMapper implements Mapper<MentionId, MentionValue, [string, NotificationType], NotificationEventValue> {
  constructor() {
  }

  mapEntry(
    _key: MentionId,
    values: Values<MentionValue>,
    _context: Context
  ): Iterable<[[string, NotificationType], NotificationEventValue]> {
    const result: Array<[[string, NotificationType], NotificationEventValue]> = Array.of();
    for (const v of values) {
      const outputKey: [string, NotificationType] = [v.toUserId, "mention"];
      const outputValue: NotificationEventValue = {
        actorId: v.fromUserId,
        timestamp: v.timestamp
      };
      result.push([outputKey, outputValue]);
    }
    return result;
  }
}

export class FollowToNotificationMapper implements Mapper<FollowId, FollowValue, [string, NotificationType], NotificationEventValue> {
  constructor() {
  }

  mapEntry(
    _key: FollowId,
    values: Values<FollowValue>,
    _context: Context
  ): Iterable<[[string, NotificationType], NotificationEventValue]> {
    const result: Array<[[string, NotificationType], NotificationEventValue]> = Array.of();
    for (const v of values) {
      const outputKey: [string, NotificationType] = [v.toUserId, "follow"];
      const outputValue: NotificationEventValue = {
        actorId: v.fromUserId,
        timestamp: v.timestamp
      };
      result.push([outputKey, outputValue]);
    }
    return result;
  }
}

export class LikeToNotificationMapper implements Mapper<LikeId, LikeValue, [string, NotificationType], NotificationEventValue> {
  constructor() {
  }

  mapEntry(
    _key: LikeId,
    values: Values<LikeValue>,
    _context: Context
  ): Iterable<[[string, NotificationType], NotificationEventValue]> {
    const result: Array<[[string, NotificationType], NotificationEventValue]> = Array.of();
    for (const v of values) {
      const outputKey: [string, NotificationType] = [v.toUserId, "like"];
      const outputValue: NotificationEventValue = {
        actorId: v.fromUserId,
        timestamp: v.timestamp
      };
      result.push([outputKey, outputValue]);
    }
    return result;
  }
}

export class NotificationOutputMapper implements Mapper<[string, NotificationType], NotificationAccum, NotificationId, NotificationValue> {
  constructor() {
  }

  mapEntry(
    key: [string, NotificationType],
    values: Values<NotificationAccum>,
    _context: Context
  ): Iterable<[NotificationId, NotificationValue]> {
    const result: Array<[NotificationId, NotificationValue]> = Array.of();
    for (const v of values) {
      const userId = key[0];
      const notificationType = key[1];
      const notificationId: NotificationId = JSON.stringify([userId, notificationType]);
      const notificationValue: NotificationValue = {
        userId: userId,
        type: notificationType,
        count: v.count,
        latestTimestamp: v.latestTimestamp,
        actorIds: v.actorIds
      };
      result.push([notificationId, notificationValue]);
    }
    return result;
  }
}

export class FilterByUserMapper implements Mapper<NotificationId, NotificationValue, NotificationId, NotificationValue> {
  private userId: string;

  constructor(userId: string) {
    this.userId = userId;
  }

  mapEntry(
    key: NotificationId,
    values: Values<NotificationValue>,
    _context: Context
  ): Iterable<[NotificationId, NotificationValue]> {
    const result: Array<[NotificationId, NotificationValue]> = Array.of();
    for (const v of values) {
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class NotificationReducer implements Reducer<NotificationEventValue, NotificationAccum> {
  initial: Nullable<NotificationAccum> = null;

  constructor() {
  }

  add(accum: Nullable<NotificationAccum>, value: NotificationEventValue & DepSafe): NotificationAccum {
    if (accum === null) {
      return {
        count: 1,
        latestTimestamp: value.timestamp,
        actorIds: Array.of(value.actorId)
      };
    }
    const newActorIds: Array<string> = Array.of();
    let found = false;
    for (const aid of accum.actorIds) {
      newActorIds.push(aid);
      if (aid === value.actorId) {
        found = true;
      }
    }
    if (!found) {
      newActorIds.push(value.actorId);
    }
    return {
      count: accum.count + 1,
      latestTimestamp: value.timestamp > accum.latestTimestamp ? value.timestamp : accum.latestTimestamp,
      actorIds: newActorIds
    };
  }

  remove(accum: NotificationAccum, _value: NotificationEventValue & DepSafe): Nullable<NotificationAccum> {
    if (accum.count <= 1) {
      return null;
    }
    return null;
  }
}

export class NotificationsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications;
  }
}

export class NotificationsByUserResource implements Resource<GraphCollections> {
  private userId: string;

  constructor(params: { userId: string }) {
    this.userId = params.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications.map(FilterByUserMapper, this.userId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                this.inputs = { mentions: new InputDefinition<MentionId, MentionValue>([]), follows: new InputDefinition<FollowId, FollowValue>([]), likes: new InputDefinition<LikeId, LikeValue>([]) };
    this.resources = { 
      "notifications": NotificationsResource,
      "notifications-by-user": NotificationsByUserResource
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const mentionNotifications = inputs.mentions.map(MentionToNotificationMapper);
    const followNotifications = inputs.follows.map(FollowToNotificationMapper);
    const likeNotifications = inputs.likes.map(LikeToNotificationMapper);
    
    const mergedEvents = mentionNotifications
      .merge(followNotifications)
      .merge(likeNotifications);
    
    const aggregatedNotifications = mergedEvents.reduce(NotificationReducer);
    
    const notifications = aggregatedNotifications.map(NotificationOutputMapper);
    
    return { notifications };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
