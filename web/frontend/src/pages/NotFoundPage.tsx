import { Link } from "react-router-dom";

import { useDocumentMetadata } from "../hooks/useDocumentMetadata";

export default function NotFoundPage() {
  useDocumentMetadata(
    "Page not found",
    "The requested Hypostructure documentation page does not exist.",
  );

  return (
    <section className="not-found">
      <p className="hero-eyebrow">404 · Uncharted residual</p>
      <h1>This route does not exist.</h1>
      <p>The requested page is not part of the published Hypostructure snapshot.</p>
      <div>
        <Link className="button-primary" to="/">Return home</Link>
        <Link className="button-secondary" to="/search">Search the reference</Link>
      </div>
    </section>
  );
}
