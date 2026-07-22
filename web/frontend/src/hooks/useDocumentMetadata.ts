import { useEffect } from "react";

export function useDocumentMetadata(
  title: string,
  description: string,
  canonicalPath?: string | null,
) {
  useEffect(() => {
    document.title = `${title} · Hypostructure`;

    let descriptionTag = document.querySelector<HTMLMetaElement>(
      'meta[name="description"]',
    );
    if (!descriptionTag) {
      descriptionTag = document.createElement("meta");
      descriptionTag.name = "description";
      document.head.append(descriptionTag);
    }
    descriptionTag.content = description;

    let canonical = document.querySelector<HTMLLinkElement>('link[rel="canonical"]');
    if (canonicalPath) {
      if (!canonical) {
        canonical = document.createElement("link");
        canonical.rel = "canonical";
        document.head.append(canonical);
      }
      canonical.href = new URL(canonicalPath, window.location.origin).href;
    } else {
      canonical?.remove();
    }
  }, [canonicalPath, description, title]);
}
