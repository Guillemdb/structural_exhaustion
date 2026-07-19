import { Navigate, Route, Routes } from "react-router-dom";

import { FrameworkPage } from "./pages/FrameworkPage";
import { ErdosGyarfasPage } from "./pages/ErdosGyarfasPage";
import { ExamplePage } from "./pages/ExamplePage";
import { ExamplesPage } from "./pages/ExamplesPage";
import { TacticPage } from "./pages/TacticPage";
import { ERDOS_GYARFAS_PATH } from "./routes";
import { AudienceProvider } from "./audience";
import { CoreDocumentationPage, GraphDocumentationPage } from "./pages/DocumentationPage";

export default function App() {
  return (
    <AudienceProvider>
    <Routes>
      <Route path="/" element={<Navigate to="/framework/core" replace />} />
      <Route path="/framework" element={<Navigate to="/framework/core" replace />} />
      <Route path="/framework/core" element={<CoreDocumentationPage />} />
      <Route path="/framework/tactics" element={<FrameworkPage />} />
      <Route path="/framework/graph" element={<GraphDocumentationPage />} />
      <Route path="/ct/:tacticId" element={<TacticPage />} />
      <Route path={ERDOS_GYARFAS_PATH} element={<ErdosGyarfasPage />} />
      <Route path="/examples" element={<ExamplesPage />} />
      <Route
        path="/examples/erdos-64"
        element={<Navigate to={ERDOS_GYARFAS_PATH} replace />}
      />
      <Route path="/examples/:exampleId" element={<ExamplePage />} />
      <Route path="*" element={<Navigate to="/framework/core" replace />} />
    </Routes>
    </AudienceProvider>
  );
}
