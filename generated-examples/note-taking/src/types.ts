export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateNoteRequest = {
  readonly content: string;
  readonly title: string;
};

export type CreateNoteRequest_skip_id_ = {
  readonly content: string;
  readonly title: string;
};

export type CreateNoteRequest_skip_value_ = {
  readonly content: string;
  readonly title: string;
};

export type GetNoteParams = { readonly noteId: string };

export type ListNotesParams = { readonly userId: string };

export type Note = {
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
};

export type NoteList = { readonly notes: Note[]; readonly total?: number };

export type NoteList_skip_id_ = {
  readonly notes: Note[];
  readonly total?: number;
};

export type NoteList_skip_value_ = {
  readonly notes: Note[];
  readonly total?: number;
};

export type Note_skip_id_ = string;

export type Note_skip_value_ = {
  readonly content: string;
  readonly createdAt: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateNoteRequest = {
  readonly content?: string;
  readonly title?: string;
};

export type UpdateNoteRequest_skip_id_ = {
  readonly content?: string;
  readonly title?: string;
};

export type UpdateNoteRequest_skip_value_ = {
  readonly content?: string;
  readonly title?: string;
};

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};
