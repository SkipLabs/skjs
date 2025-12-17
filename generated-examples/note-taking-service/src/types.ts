export type NoteId = string;

export type NoteValue = {
  title: string;
  content: string;
};

export type Note = NoteValue & { id: NoteId };
