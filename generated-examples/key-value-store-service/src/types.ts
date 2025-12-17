export type KVEntryId = string;

export type KVEntryValue = { value: string; createdAt: number; updatedAt: number };

export type KVEntry = { id: KVEntryId; value: string; createdAt: number; updatedAt: number };
