// Regression test for SkipLabs/skjs#1135: generic method calls returning
// recursive collections whose type parameters are constrained by recursive
// `Json` (combining `EagerCollection.map` + `merge` + transparent aliases +
// `Closed<T>` objects) must typecheck cleanly without blowing up memory or
// losing the nominal value type through redundant `Value & Json` intersection.

import type {
  Context,
  EagerCollection,
  Mapper,
  SharedCollections,
  Values,
} from "@skipruntime/core";

type EventId = string;
type EventIdAlias = EventId;

type PostEvent = Closed<{
  readonly kind: "post";
  readonly id: string;
  readonly authorId: string;
  readonly createdAt: number;
}>;

type LikeEvent = Closed<{
  readonly kind: "like";
  readonly id: string;
  readonly postId: string;
  readonly createdAt: number;
}>;

type FeedEvent = PostEvent | LikeEvent;
type FeedEventAlias = FeedEvent;

type PostStored = Closed<{
  readonly id: string;
  readonly authorId: string;
  readonly createdAt: number;
}>;

type LikeStored = Closed<{
  readonly id: string;
  readonly postId: string;
  readonly createdAt: number;
}>;

class PostToEventMapper
  implements Mapper<EventId, PostStored, EventId, FeedEvent>
{
  mapEntry(
    key: EventId,
    values: Values<PostStored>,
    _context: Context,
  ): Iterable<[EventId, FeedEvent]> {
    const out: Array<[EventId, FeedEvent]> = [];
    for (const v of values.toArray()) {
      out.push([
        key,
        {
          kind: "post",
          id: v.id,
          authorId: v.authorId,
          createdAt: v.createdAt,
        },
      ]);
    }
    return out;
  }
}

class LikeToEventMapper
  implements Mapper<EventId, LikeStored, EventId, FeedEvent>
{
  mapEntry(
    key: EventId,
    values: Values<LikeStored>,
    _context: Context,
  ): Iterable<[EventId, FeedEvent]> {
    const out: Array<[EventId, FeedEvent]> = [];
    for (const v of values.toArray()) {
      out.push([
        key,
        {
          kind: "like",
          id: v.id,
          postId: v.postId,
          createdAt: v.createdAt,
        },
      ]);
    }
    return out;
  }
}

interface GraphCollections extends SharedCollections {
  readonly feedEvents: EagerCollection<EventIdAlias, FeedEventAlias>;
  readonly posts: EagerCollection<EventId, PostStored>;
  readonly likes: EagerCollection<EventId, LikeStored>;
}

export function buildGraph(
  posts: EagerCollection<EventId, PostStored>,
  likes: EagerCollection<EventId, LikeStored>,
): GraphCollections {
  const postEvents = posts.map(PostToEventMapper);
  const likeEvents = likes.map(LikeToEventMapper);
  const merged = postEvents.merge(likeEvents);
  return {
    feedEvents: merged,
    posts,
    likes,
  };
}
