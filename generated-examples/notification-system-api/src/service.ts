import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

import type {
  NotificationId,
  NotificationValue,
  NotificationsUserResourceParams,
} from "./types.js";


type Inputs = {
  notifications: Entry<NotificationId, NotificationValue>[];
};

export type InputCollections = {
  notifications: EagerCollection<NotificationId, NotificationValue>;
};

export type GraphCollections = {
  notifications: EagerCollection<NotificationId, NotificationValue>;
};

type Resources = {
  "notifications": new (params: Json) => Resource<GraphCollections>;
  "notifications-unread": new (params: Json) => Resource<GraphCollections>;
  "notifications-user": new (params: Json) => Resource<GraphCollections>;
};

export class UnreadNotificationsMapper implements Mapper<NotificationId, NotificationValue, NotificationId, NotificationValue> {
  constructor() {
  }

  mapEntry(
    key: NotificationId,
    values: Values<NotificationValue>,
    _context: Context
  ): Iterable<[NotificationId, NotificationValue]> {
    const result: Array<[NotificationId, NotificationValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.read === 0) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class NotificationsByUserMapper implements Mapper<NotificationId, NotificationValue, NotificationId, NotificationValue> {
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class NotificationsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications;
  }
}

export class NotificationsUnreadResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications.map(UnreadNotificationsMapper);
  }
}

export class NotificationsUserResource implements Resource<GraphCollections> {
  private userId: string;

  constructor(params: Json) {
    const typed = params as NotificationsUserResourceParams;
    this.userId = typed.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications.map(NotificationsByUserMapper, this.userId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyNotifications: Entry<NotificationId, NotificationValue>[] = Array.of();
    this.initialData = { notifications: emptyNotifications };
    this.resources = { "notifications": NotificationsResource, "notifications-unread": NotificationsUnreadResource, "notifications-user": NotificationsUserResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { notifications: inputs.notifications };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
