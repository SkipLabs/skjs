import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Book_skip_id_, Book_skip_value_, Book } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each book entry, emit one output pair whose key is the entry's key and whose value lists every required field of Book explicitly — id sourced from the entry's key; title, author, totalCopies, availableCopies, createdAt sourced from the entry's value; and the optional field isbn, present when the entry's value carries an isbn field, sourced from the entry's value, absent otherwise.
export class AssembleBookMapper implements Mapper<
  Book_skip_id_,
  Book_skip_value_,
  Book_skip_id_,
  Book
> {
  mapEntry(
    key: Book_skip_id_,
    values: Values<Book_skip_value_>,
    context: Context,
  ): Iterable<[Book_skip_id_, Book]> {
    // > body
    const emits: [Book_skip_id_, Book][] = [];
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
      emits.push([key, book]);
    }
    return emits;
    // < body
  }
}
