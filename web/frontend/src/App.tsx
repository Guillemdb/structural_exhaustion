import { Navigate, Route, Routes } from "react-router-dom";

import { FrameworkPage } from "./pages/FrameworkPage";
import { ErdosGyarfasPage } from "./pages/ErdosGyarfasPage";
import { ExamplePage } from "./pages/ExamplePage";
import { ExamplesPage } from "./pages/ExamplesPage";
import { TacticPage } from "./pages/TacticPage";
import { ERDOS_GYARFAS_PATH } from "./routes";

export default function App() {
  return (
    <Routes>
      <Route path="/" element={<Navigate to="/framework" replace />} />
      <Route path="/framework" element={<FrameworkPage />} />
      <Route path="/ct/:tacticId" element={<TacticPage />} />
      <Route path={ERDOS_GYARFAS_PATH} element={<ErdosGyarfasPage />} />
      <Route path="/examples" element={<ExamplesPage />} />
      <Route
        path="/examples/erdos-64"
        element={<Navigate to={ERDOS_GYARFAS_PATH} replace />}
      />
      <Route path="/examples/:exampleId" element={<ExamplePage />} />
      <Route path="*" element={<Navigate to="/framework" replace />} />
    </Routes>
  );
}
