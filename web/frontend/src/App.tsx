import { Navigate, Route, Routes } from "react-router-dom";

import { FrameworkPage } from "./pages/FrameworkPage";
import { ExamplePage } from "./pages/ExamplePage";
import { ExamplesPage } from "./pages/ExamplesPage";
import { TacticPage } from "./pages/TacticPage";

export default function App() {
  return (
    <Routes>
      <Route path="/" element={<Navigate to="/framework" replace />} />
      <Route path="/framework" element={<FrameworkPage />} />
      <Route path="/ct/:tacticId" element={<TacticPage />} />
      <Route path="/examples" element={<ExamplesPage />} />
      <Route path="/examples/:exampleId" element={<ExamplePage />} />
      <Route path="*" element={<Navigate to="/framework" replace />} />
    </Routes>
  );
}
