import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Book_skip_id_, Book_skip_value_, Book } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each book entry, when the entry's key does not equal the bookId param, emit nothing. Otherwise emit one output pair whose key is the literal zero and whose value lists every required field of Book explicitly — id sourced from the entry's key; title, author, totalCopies, availableCopies, createdAt sourced from the entry's value; and the optional field isbn, present when the entry's value carries an isbn field, sourced from the entry's value, absent otherwise.
export class GetBookMapper implements Mapper<
  Book_skip_id_,
  Book_skip_value_,
  0,
  Book
> {
  constructor(private bookId: string) {}

  mapEntry(
    key: Book_skip_id_,
    values: Values<Book_skip_value_>,
    context: Context,
  ): Iterable<[0, Book]> {
    // > body
    if (key !== this.bookId) return [];
    const emits: [0, Book][] = [];
    for (const value of values.toArray()) {
      const book: Book = {
        id: key,
        title: value.title,
        author: value.author,
        totalCopies: value.totalCopies,
        availableCopies: value.availableCopies,
        createdAt: value.createdAt,
        ...(value.isbn !== undefined && { isbn: value.isbn }),
      };
      emits.push([0, book]);
    }
    return emits;
    // < body
  }
}
