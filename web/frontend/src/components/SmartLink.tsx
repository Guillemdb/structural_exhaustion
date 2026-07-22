import type { ReactNode } from "react";
import { Link } from "react-router-dom";

export function SmartLink({
  href,
  children,
  className,
}: {
  href: string;
  children: ReactNode;
  className?: string;
}) {
  const sourceApiMatch = href.match(/^\/api\/v2\/sources\/([^/?]+)\/excerpt(\?.*)?$/);
  const applicationHref = sourceApiMatch
    ? `/source/${sourceApiMatch[1]}${sourceApiMatch[2] ?? ""}`
    : href;
  const isApplicationRoute = /^\/(?:$|start(?:\/|$)|core(?:\/|$)|graph(?:\/|$)|pde(?:\/|$)|examples(?:\/|$)|erdos(?:\/|$)|reference(?:\/|$)|source(?:\/|$)|search(?:\?|\/|$))/.test(applicationHref);
  if (!isApplicationRoute) {
    return (
      <a className={className} href={href} rel="noreferrer">
        {children}
      </a>
    );
  }
  return (
    <Link className={className} to={applicationHref}>
      {children}
    </Link>
  );
}
