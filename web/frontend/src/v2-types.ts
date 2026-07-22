export interface LinkView {
  label: string;
  href?: string | null;
}

export interface BreadcrumbView extends LinkView {}

export interface MetricView {
  label: string;
  value: string | number;
  detail?: string | null;
}

export interface CardView {
  title: string;
  summary: string;
  href?: string | null;
  eyebrow?: string | null;
  meta?: string | null;
}

export interface TextBlock {
  kind: "prose";
  /** HTML is rendered and sanitized by the Flask content pipeline. */
  html: string;
}

export interface CardsBlock {
  kind: "cards";
  items: CardView[];
  columns?: 2 | 3 | 4;
}

export interface CalloutBlock {
  kind: "callout";
  tone: "info" | "success" | "warning" | "trust";
  title: string;
  body?: string | null;
  items?: string[];
}

export interface StepsBlock {
  kind: "steps";
  items: Array<{ title: string; body: string; href?: string | null }>;
}

export interface CodeBlock {
  kind: "code";
  language: string;
  code: string;
  caption?: string | null;
  sourceHref?: string | null;
}

export interface MathBlock {
  kind: "math";
  latex: string;
  display?: boolean;
  label?: string | null;
}

export interface TableBlock {
  kind: "table";
  caption?: string | null;
  columns: Array<{ key: string; label: string }>;
  rows: Array<Record<string, string | number | boolean | null>>;
}

export interface GraphNodeView {
  id: string;
  label: string;
  x: number;
  y: number;
  kind?: string | null;
  summary?: string | null;
  href?: string | null;
}

export interface GraphEdgeView {
  id: string;
  source: string;
  target: string;
  label?: string | null;
}

export interface GraphBlock {
  kind: "graph";
  title?: string | null;
  description?: string | null;
  nodes: GraphNodeView[];
  edges: GraphEdgeView[];
  legend?: Array<{ label: string; kind: string }>;
}

export interface LinksBlock {
  kind: "links";
  items: Array<{ label: string; href: string; description?: string | null }>;
}

export interface StatsBlock {
  kind: "stats";
  items: MetricView[];
}

export type ContentBlock =
  | TextBlock
  | CardsBlock
  | CalloutBlock
  | StepsBlock
  | CodeBlock
  | MathBlock
  | TableBlock
  | GraphBlock
  | LinksBlock
  | StatsBlock;

export interface SectionView {
  id: string;
  title?: string | null;
  eyebrow?: string | null;
  summary?: string | null;
  blocks: ContentBlock[];
}

export interface VerificationSummaryView {
  state: "verified" | "unverified" | "unavailable";
  label: string;
  summary: string;
  details?: Array<{ label: string; value: string }>;
}

export interface PageView {
  id: string;
  title: string;
  eyebrow?: string | null;
  summary: string;
  description?: string | null;
  breadcrumbs?: BreadcrumbView[];
  metrics?: MetricView[];
  sections: SectionView[];
  verification?: VerificationSummaryView | null;
  canonicalPath?: string | null;
}

export interface SiteView {
  name: string;
  tagline: string;
  navigation: Array<{ label: string; href: string }>;
  snapshot: string;
  searchEnabled: boolean;
  verification: VerificationSummaryView;
}

export interface SearchFacetView {
  field: "kind" | "module";
  label: string;
  value: string;
  count: number;
  active: boolean;
}

export interface SearchResultView {
  id: string;
  title: string;
  summary: string;
  href: string;
  kind: string;
  module?: string | null;
  /** Highlight fragments are sanitized by the Flask search service. */
  highlights?: string[];
}

export interface SearchView {
  query: string;
  total: number;
  page: number;
  pageSize: number;
  facets: SearchFacetView[];
  results: SearchResultView[];
}

export interface SourceExcerptView {
  sourceId: string;
  path: string;
  sha256: string;
  startLine: number;
  endLine: number;
  totalLines: number;
  content: string;
}
