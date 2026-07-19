import { createContext, useContext, useEffect, useMemo, useState } from "react";

export type DocumentationAudience = "mathematician" | "leanUser";

interface AudienceContextValue {
  audience: DocumentationAudience;
  setAudience: (audience: DocumentationAudience) => void;
}

const STORAGE_KEY = "structural-exhaustion.documentation-audience";
const AudienceContext = createContext<AudienceContextValue>({
  audience: "mathematician",
  setAudience: () => undefined,
});

export function AudienceProvider({ children }: { children: React.ReactNode }) {
  const [audience, setAudience] = useState<DocumentationAudience>(() => {
    if (typeof window === "undefined") return "mathematician";
    return window.localStorage.getItem(STORAGE_KEY) === "leanUser"
      ? "leanUser"
      : "mathematician";
  });

  useEffect(() => {
    window.localStorage.setItem(STORAGE_KEY, audience);
  }, [audience]);

  const value = useMemo(() => ({ audience, setAudience }), [audience]);
  return <AudienceContext.Provider value={value}>{children}</AudienceContext.Provider>;
}

export function useDocumentationAudience(): AudienceContextValue {
  return useContext(AudienceContext);
}
