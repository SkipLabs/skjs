export type ReviewId = string;

export type ReviewValue = {
  itemId: string;
  userId: string;
  rating: number;
  title: string;
  content: string;
  timestamp: number;
};

export type Review = {
  id: ReviewId;
  itemId: string;
  userId: string;
  rating: number;
  title: string;
  content: string;
  timestamp: number;
};

export type ReviewsByItemResourceParams = {
  itemId: string;
};

export type ReviewsByUserResourceParams = {
  userId: string;
};
