export type UrlId = string;

export type UrlValue = {
  originalUrl: string;
  createdAt: number;
  clickCount: number;
};

export type Url = UrlValue & { id: UrlId };

export type ClickId = string;

export type ClickValue = {
  urlId: string;
  timestamp: number;
};

export type Click = ClickValue & { id: ClickId };

export type UrlStatsId = string;

export type UrlStatsValue = {
  totalClicks: number;
  lastClickAt: number | null;
};

export type UrlStats = UrlStatsValue & { id: UrlStatsId };
