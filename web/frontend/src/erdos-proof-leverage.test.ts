import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { describe, expect, it } from "vitest";

import {
  ERDOS_FRAMEWORK_GUIDED_TOURS,
  classifyErdosDeclarationOwnership,
  createErdosProofHistorySnapshot,
  deriveAllErdosNodeCausalEvidence,
  deriveErdosFrameworkLeverage,
  deriveErdosNodeCausalEvidence,
} from "./erdos-proof-leverage";
import type { ExampleDetail, ExampleResponse } from "./types";

function generatedErdosDetail(): ExampleDetail {
  return JSON.parse(readFileSync(
    resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
    "utf8",
  )) as ExampleDetail;
}

describe("Erdős framework leverage evidence", () => {
  it("classifies ownership from the declaration namespace", () => {
    expect(classifyErdosDeclarationOwnership("Erdos64EG.Internal.prefix")).toBe("author");
    expect(classifyErdosDeclarationOwnership("StructuralExhaustion.CT12.run")).toBe("framework");
    expect(classifyErdosDeclarationOwnership(
      "StructuralExhaustion.Graph.External.HegdeSandeepShashank.theorem",
    )).toBe("external");
    expect(classifyErdosDeclarationOwnership("Mathlib.Data.Finset.card")).toBe("external");
  });

  it("reports raw, deduplicated counts from the generated Lean artifact", () => {
    const detail = generatedErdosDetail();
    const summary = deriveErdosFrameworkLeverage(detail);
    const authorIds = new Set(detail.declarations
      .map((declaration) => declaration.declarationId)
      .filter((declarationId) => classifyErdosDeclarationOwnership(declarationId) === "author"));
    const frameworkIds = new Set(detail.declarations
      .map((declaration) => declaration.declarationId)
      .filter((declarationId) => classifyErdosDeclarationOwnership(declarationId) === "framework"));
    const externalIds = new Set(detail.declarations
      .map((declaration) => declaration.declarationId)
      .filter((declarationId) => classifyErdosDeclarationOwnership(declarationId) === "external"));
    const links = detail.workflows.flatMap((workflow) => workflow.links);

    expect(summary.counts).toMatchObject({
      authorOwnedDeclarations: authorIds.size,
      frameworkOwnedDeclarations: frameworkIds.size,
      externalDeclarations: externalIds.size,
      registeredTransitions: new Set(
        links.flatMap((link) =>
          link.transitionProfileId ? [link.transitionProfileId] : []),
      ).size,
      automationDeclarations: new Set(links.flatMap((link) => link.automationDeclarationIds)).size,
      interfaceBindings: new Set(detail.interfaceBindings.map((binding) => binding.bindingId)).size,
      proofSteps: new Set(detail.manuscript?.proofSteps.map((step) => step.stepId)).size,
      linksWithAutomation: links.filter((link) => link.automationDeclarationIds.length > 0).length,
    });
    expect(summary.authorOwnedDeclarationIds).toHaveLength(authorIds.size);
    expect(summary.frameworkOwnedDeclarationIds).toHaveLength(frameworkIds.size);
    expect(summary.externalDeclarationIds).toEqual([
      "StructuralExhaustion.Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle",
    ]);
    expect(summary.automationDeclarationIds).toEqual(
      [...new Set(summary.automationDeclarationIds)],
    );
    expect(summary.transitionProfileIds).toContain("CT1.terminal.c1->CT12");
    expect(summary.ctIds).toContain("CT15");
  });

  it("connects a paper node to its authored data, transition, CT, and work evidence", () => {
    const evidence = deriveErdosNodeCausalEvidence(generatedErdosDetail(), 17);

    expect(evidence.proofStepIds).toContain("erdos.p13-packing");
    expect(evidence.paperReferences.some((reference) =>
      reference.label === "def:p13-packing" && reference.nodeIds.includes(17))).toBe(true);
    expect(evidence.ctIds).toEqual(expect.arrayContaining(["CT1", "CT12"]));
    expect(evidence.transitionProfileIds).toContain("CT1.terminal.c1->CT12");
    expect(evidence.automationDeclarationIds).toContain(
      "StructuralExhaustion.Routes.CT1ToCT12.advance",
    );
    expect(evidence.bindings.some((binding) => binding.tacticId === "CT12")).toBe(true);
    expect(evidence.authorOwnedDeclarationIds.length).toBeGreaterThan(0);
    expect(evidence.frameworkOwnedDeclarationIds.length).toBeGreaterThan(0);
    expect(evidence.workBounds).toEqual([
      expect.objectContaining({ stepId: "erdos.p13-packing" }),
    ]);
    expect(new Set(evidence.frameworkOwnedDeclarationIds).size)
      .toBe(evidence.frameworkOwnedDeclarationIds.length);
  });

  it("keeps the external trust boundary and CT15 rank automation visible", () => {
    const detail = generatedErdosDetail();
    const inducedPath = deriveErdosNodeCausalEvidence(detail, 15);
    const targetRank = deriveErdosNodeCausalEvidence(detail, 31);

    expect(inducedPath.externalDeclarationIds).toContain(
      "StructuralExhaustion.Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle",
    );
    expect(targetRank.ctIds).toContain("CT15");
    expect(targetRank.automationDeclarationIds).toContain(
      "StructuralExhaustion.CT15.AdmissibleQuotient.Profile.targetRank",
    );
    expect(targetRank.workBounds[0]?.description).toContain("no subfamily powerset");
  });

  it("derives one causal record per cited original node", () => {
    const detail = generatedErdosDetail();
    const allEvidence = deriveAllErdosNodeCausalEvidence(detail);
    const expectedNodeIds = new Set(detail.manuscript?.proofSteps.flatMap((step) =>
      step.manuscriptRefs.flatMap((reference) => reference.nodeIds)));

    expect(allEvidence.map((evidence) => evidence.nodeId))
      .toEqual([...expectedNodeIds].sort((left, right) => left - right));
    expect(new Set(allEvidence.map((evidence) => evidence.nodeId)).size)
      .toBe(allEvidence.length);
  });

  it("creates a stable current snapshot suitable for an append-only history", () => {
    const detail = generatedErdosDetail();
    const response = {
      artifactType: "frameworkExplorerExample",
      artifactWarnings: [],
      catalogHash: "example-catalog-hash",
      frameworkCatalogHash: "framework-catalog-hash",
      verification: {},
      tactics: [],
      example: detail,
    } as unknown as ExampleResponse;
    const snapshot = createErdosProofHistorySnapshot(response, "2026-07-18T12:00:00Z");
    const second = createErdosProofHistorySnapshot(response, "2026-07-18T12:00:00Z");

    expect(snapshot).toEqual(second);
    expect(snapshot.recordedAt).toBe("2026-07-18T12:00:00Z");
    expect(snapshot.catalogHash).toBe("example-catalog-hash");
    expect(snapshot.frameworkCatalogHash).toBe("framework-catalog-hash");
    expect(snapshot.manuscriptSha256).toBe(detail.manuscript?.sha256);
    expect(snapshot.greenNodeIds).toEqual(detail.manuscript?.formalizedNodeIds);
    expect(snapshot.coverage.verifiedDiagramNodes)
      .toBe(detail.manuscript?.coverage.verifiedDiagramNodes);
    expect(snapshot.leverage).toEqual(deriveErdosFrameworkLeverage(detail).counts);
    expect(snapshot.yellowNodeIds.every((nodeId) =>
      !snapshot.greenNodeIds.includes(nodeId))).toBe(true);
  });

  it("provides guided tours covering exactly the two intended proof slices", () => {
    expect(ERDOS_FRAMEWORK_GUIDED_TOURS.map((tour) => tour.nodeIds)).toEqual([
      [15, 16, 17, 18],
      [31, 32, 33, 34],
    ]);
    for (const tour of ERDOS_FRAMEWORK_GUIDED_TOURS) {
      const stopNodeIds = tour.stops.flatMap((stop) => stop.nodeIds);
      expect(new Set(stopNodeIds)).toEqual(new Set(tour.nodeIds));
      expect(tour.stops.every((stop) =>
        stop.frameworkContribution.length > 0 && stop.evidenceFocus.length > 0)).toBe(true);
    }
  });
});
