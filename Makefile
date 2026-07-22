.PHONY: help lint build framework-build example-build even-cycle-example-build erdos-example-build greedy-coloring-example-build mantel-example-build mathlib-cache export example-export erdos-web-status-sync erdos-proof-history schemas generate validate kernel verify test manuscript checksums web web-data hypostructure-web-export web-build web-test web-backend-test web-frontend-test hypostructure-framework-build hypostructure-fixtures-build hypostructure-erdos-build hypostructure-pde-build hypostructure-parity-build hypostructure-mathlib-cache hypostructure-lint eg-source-authority-check hypostructure-test migration-test

.DEFAULT_GOAL := build

PYTHON ?= python3
UV ?= uv
NPM ?= npm
UV_CACHE_DIR ?= /tmp/uv-cache
LEAN_DIR := lean
HYPOSTRUCTURE_DIR := hypostructure
HYPOSTRUCTURE_ERDOS_EXAMPLE_DIR := examples/hypostructure_erdos_64_eg
HYPOSTRUCTURE_PDE_EXAMPLE_DIR := examples/hypostructure_pde
HYPOSTRUCTURE_PARITY_DIR := examples/hypostructure_parity
EVEN_CYCLE_EXAMPLE_DIR := examples/even_cycle
ERDOS_EXAMPLE_DIR := examples/erdos_64_eg
GREEDY_COLORING_EXAMPLE_DIR := examples/greedy_coloring
MANTEL_EXAMPLE_DIR := examples/mantel
CATALOG := generated/lean-machines.json
DOCUMENTATION_CATALOG := generated/framework-documentation.json
EXAMPLE_EXPORT_DIR := build/example-exports
WEB_FRONTEND_DIR := web/frontend
WEB_NODE_STAMP := $(WEB_FRONTEND_DIR)/node_modules/.package-lock.json
HYPOSTRUCTURE_WEB_RAW := generated/hypostructure/web/declarations.raw.json
HYPOSTRUCTURE_WEB_SNAPSHOT := generated/hypostructure/web/snapshot.json
HYPOSTRUCTURE_WEB_MANIFEST := generated/hypostructure/web/manifest.json
WEB_HOST ?= 127.0.0.1
WEB_PORT ?= 8000
WEB_WORKERS ?= 1
WEB_THREADS ?= 4
WEB_TIMEOUT ?= 60

help:
	@printf '%s\n' \
	  'Structural Exhaustion automation-first workflow' \
	  '' \
	  '  make lint        Reject legacy APIs, proof injection, admissions, and forbidden imports' \
	  '  make mathlib-cache  Download Mathlib oleans for the framework and external examples' \
	  '  make framework-build  Compile only the reusable Lean framework package' \
	  '  make hypostructure-framework-build  Compile the independent Hypostructure package' \
	  '  make hypostructure-fixtures-build  Compile cross-domain Core, Graph, and PDE fixtures' \
	  '  make hypostructure-erdos-build  Compile the Hypostructure-native EG registration and fixtures' \
	  '  make hypostructure-pde-build  Compile the independent PDE and NS2D example ladder' \
	  '  make hypostructure-parity-build  Prove normalized legacy/new EG parity fixtures' \
	  '  make hypostructure-lint  Enforce the Hypostructure production import firewall' \
	  '  make eg-source-authority-check  Verify the immutable EG original and diagram locator' \
	  '  make hypostructure-test  Build and lint the current Hypostructure migration slice' \
	  '  make even-cycle-example-build  Compile the external even-cycle example package' \
	  '  make erdos-example-build  Compile the partial Erdős Problem 64 example package' \
	  '  make greedy-coloring-example-build  Compile the external greedy-coloring example' \
	  '  make mantel-example-build  Compile the external Mantel/CT11 example' \
	  '  make example-build    Compile all external graph-problem example packages' \
	  '  make build       Compile the framework and all external examples' \
	  '  make export      Build Lean and export the compiled machine and example catalogs' \
	  '  make erdos-proof-history  Record the current Erdős artifact and framework-reuse facts' \
	  '  make schemas     Export Lean and regenerate all concrete JSON Schemas' \
	  '  make generate    Export Lean and regenerate every schema, diagram, index, and binding check' \
	  '  make validate    Validate the current catalog, transition contracts, schemas, and graph invariants' \
	  '  make kernel      Regenerate and kernel-check bindings, freshness, and absence of admissions' \
	  '  make verify      Run the complete linter, generation, kernel, validation, and checksum chain' \
	  '  make test        Run make verify plus Python and web regression checks' \
	  '  make web-data    Build the compiled Hypostructure documentation snapshot' \
	  '  make web         Build and serve the Flask + React documentation site' \
	  '  make web-test    Verify the data build, Flask API, React UI, and production bundle' \
	  '  make manuscript  Regenerate CT figures and compile the PDF manuscript'

lint:
	$(PYTHON) tools/lint_automation_first.py --root .

framework-build:
	cd $(LEAN_DIR) && lake build

hypostructure-framework-build:
	cd $(HYPOSTRUCTURE_DIR) && lake build

hypostructure-fixtures-build: hypostructure-framework-build
	cd $(HYPOSTRUCTURE_DIR) && lake build Hypostructure.PDE Hypostructure.Fixtures.PDEBasics Hypostructure.Fixtures.PDERows1To4 Hypostructure.Fixtures.PDERow5DirectedExhaustiveness Hypostructure.Fixtures.PDERow6DefectRoutingRaw Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment Hypostructure.Fixtures.PDERow6FinitePressureGaugeAlignment Hypostructure.Fixtures.ClosedLedger Hypostructure.Fixtures.CompactExtraction Hypostructure.Fixtures.LocalToGlobal Hypostructure.Fixtures.Response Hypostructure.Fixtures.Finite Hypostructure.Fixtures.ExecutionRouting Hypostructure.Fixtures.Decision Hypostructure.Fixtures.Focus Hypostructure.Fixtures.ProofProjection Hypostructure.Fixtures.NormalForms Hypostructure.Fixtures.GraphAssembly Hypostructure.Fixtures.GraphProgress Hypostructure.Fixtures.GraphMinimality Hypostructure.Fixtures.GraphDeletionCriticality Hypostructure.Fixtures.GraphBoundariedAtom Hypostructure.Fixtures.GraphAtomResponse Hypostructure.Fixtures.GraphBoundaryOverlap Hypostructure.Fixtures.GraphBoundaryOverlapCounterexample Hypostructure.Fixtures.GraphResponse Hypostructure.Fixtures.RootedReturn Hypostructure.Fixtures.CT1 Hypostructure.Fixtures.CT2 Hypostructure.Fixtures.CT3 Hypostructure.Fixtures.CT4 Hypostructure.Fixtures.CT5 Hypostructure.Fixtures.CT6 Hypostructure.Fixtures.CT7 Hypostructure.Fixtures.CT8 Hypostructure.Fixtures.CT9 Hypostructure.Fixtures.CT10 Hypostructure.Fixtures.CT11 Hypostructure.Fixtures.CT12 Hypostructure.Fixtures.CT13 Hypostructure.Fixtures.CT14 Hypostructure.Fixtures.CT15 Hypostructure.Fixtures.CT16 Hypostructure.Fixtures.CT17 Hypostructure.Fixtures.RouteRegistry

hypostructure-erdos-build: hypostructure-framework-build
	cd $(HYPOSTRUCTURE_ERDOS_EXAMPLE_DIR) && lake build
	cd $(HYPOSTRUCTURE_ERDOS_EXAMPLE_DIR) && lake build HypostructureErdos64EG.Node1
	cd $(HYPOSTRUCTURE_ERDOS_EXAMPLE_DIR) && lake build HypostructureErdos64EG.Fixtures.K4

hypostructure-pde-build: hypostructure-fixtures-build
	cd $(HYPOSTRUCTURE_PDE_EXAMPLE_DIR) && lake build

hypostructure-parity-build: hypostructure-erdos-build
	cd $(HYPOSTRUCTURE_PARITY_DIR) && lake build
	cd $(HYPOSTRUCTURE_PARITY_DIR) && lake build HypostructureParity.Erdos64EG.Node1

hypostructure-mathlib-cache:
	cd $(HYPOSTRUCTURE_DIR) && lake exe cache get
	cd $(HYPOSTRUCTURE_ERDOS_EXAMPLE_DIR) && lake exe cache get
	cd $(HYPOSTRUCTURE_PDE_EXAMPLE_DIR) && lake exe cache get
	cd $(HYPOSTRUCTURE_PARITY_DIR) && lake exe cache get

hypostructure-lint:
	$(PYTHON) tools/check_hypostructure_imports.py --root .

eg-source-authority-check:
	$(PYTHON) tools/extract_eg_original_node_anchors.py --root . --check

hypostructure-test: eg-source-authority-check hypostructure-lint hypostructure-fixtures-build hypostructure-erdos-build hypostructure-pde-build hypostructure-parity-build

migration-test: test hypostructure-test

even-cycle-example-build:
	cd $(EVEN_CYCLE_EXAMPLE_DIR) && lake build

erdos-example-build:
	cd $(ERDOS_EXAMPLE_DIR) && lake build

greedy-coloring-example-build:
	cd $(GREEDY_COLORING_EXAMPLE_DIR) && lake build

mantel-example-build:
	cd $(MANTEL_EXAMPLE_DIR) && lake build

example-build: even-cycle-example-build erdos-example-build greedy-coloring-example-build mantel-example-build

mathlib-cache:
	cd $(LEAN_DIR) && lake exe cache get
	cd $(EVEN_CYCLE_EXAMPLE_DIR) && lake exe cache get
	cd $(ERDOS_EXAMPLE_DIR) && lake exe cache get
	cd $(GREEDY_COLORING_EXAMPLE_DIR) && lake exe cache get
	cd $(MANTEL_EXAMPLE_DIR) && lake exe cache get

build: framework-build example-build

example-export: build
	mkdir -p $(EXAMPLE_EXPORT_DIR)
	rm -f $(EXAMPLE_EXPORT_DIR)/*.json
	cd $(EVEN_CYCLE_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/even-cycle.raw.json lake build EvenCycleExample.WebExport
	cd $(EVEN_CYCLE_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/even-cycle.raw.json lake env lean EvenCycleExample/WebExport.lean
	cd $(ERDOS_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/erdos-64.raw.json lake build Erdos64EG.WebExport
	cd $(ERDOS_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/erdos-64.raw.json lake env lean Erdos64EG/WebExport.lean
	cd $(GREEDY_COLORING_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/greedy-coloring.raw.json lake build GreedyColoringExample.WebExport
	cd $(GREEDY_COLORING_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/greedy-coloring.raw.json lake env lean GreedyColoringExample/WebExport.lean
	cd $(MANTEL_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/mantel.raw.json lake build MantelExample.WebExport
	cd $(MANTEL_EXAMPLE_DIR) && STRUCTURAL_EXHAUSTION_EXAMPLE_EXPORT=../../$(EXAMPLE_EXPORT_DIR)/mantel.raw.json lake env lean MantelExample/WebExport.lean

export: build example-export
	cd $(LEAN_DIR) && STRUCTURAL_EXHAUSTION_EXPORT=../$(CATALOG) STRUCTURAL_EXHAUSTION_DOCUMENTATION_EXPORT=../$(DOCUMENTATION_CATALOG) lake env lean StructuralExhaustion/Canonical/Export.lean
	$(PYTHON) tools/render_example_catalog.py --raw-root $(EXAMPLE_EXPORT_DIR) --root . --source-root . --catalog $(CATALOG)
	$(PYTHON) tools/update_erdos_proof_history.py

erdos-proof-history:
	$(PYTHON) tools/update_erdos_proof_history.py

erdos-web-status-sync:
	$(PYTHON) tools/sync_erdos_web_status.py --root .
	$(PYTHON) tools/render_single_example.py --raw $(EXAMPLE_EXPORT_DIR)/erdos-64.raw.json --root . --source-root . --catalog $(CATALOG) --status-only-existing

schemas: export
	$(PYTHON) tools/render_schemas.py

generate: export
	$(PYTHON) tools/render_artifacts.py

validate:
	$(PYTHON) tools/validate_repository.py

kernel: generate web-data
	$(PYTHON) tools/verify_lean.py

checksums:
	$(PYTHON) tools/generate_checksums.py

verify: lint kernel
	$(MAKE) validate
	$(MAKE) checksums

test: verify web-data
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run python -m pytest -q
	$(MAKE) web-test

hypostructure-web-export: hypostructure-framework-build
	cd $(HYPOSTRUCTURE_DIR) && lake build Hypostructure.PDE Hypostructure.PDE.NavierStokes
	cd $(HYPOSTRUCTURE_DIR) && HYPOSTRUCTURE_WEB_DECLARATIONS_EXPORT=../$(HYPOSTRUCTURE_WEB_RAW) lake env lean Hypostructure/Canonical/WebExport.lean

web-data: hypostructure-lint hypostructure-fixtures-build hypostructure-erdos-build hypostructure-pde-build hypostructure-web-export
	$(PYTHON) tools/build_hypostructure_web_data.py --skip-declaration-export
	@test -s $(HYPOSTRUCTURE_WEB_SNAPSHOT)
	@test -s $(HYPOSTRUCTURE_WEB_MANIFEST)

$(WEB_NODE_STAMP): $(WEB_FRONTEND_DIR)/package.json $(WEB_FRONTEND_DIR)/package-lock.json
	cd $(WEB_FRONTEND_DIR) && $(NPM) ci

web-build: web-data $(WEB_NODE_STAMP)
	cd $(WEB_FRONTEND_DIR) && $(NPM) run build

web-frontend-test: $(WEB_NODE_STAMP)
	cd $(WEB_FRONTEND_DIR) && $(NPM) run test
	cd $(WEB_FRONTEND_DIR) && $(NPM) run typecheck
	cd $(WEB_FRONTEND_DIR) && $(NPM) run build

web-backend-test: web-data
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run python -m pytest -q tests/test_web_api.py tests/test_hypostructure_web_data.py

web-test: web-backend-test $(WEB_NODE_STAMP)
	$(MAKE) web-frontend-test

web: web-build
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run gunicorn --preload --worker-class gthread --workers $(WEB_WORKERS) --threads $(WEB_THREADS) --timeout $(WEB_TIMEOUT) --bind $(WEB_HOST):$(WEB_PORT) 'web.backend.app.main:create_app()'

manuscript: generate
	mkdir -p build/framework
	cd framework && latexmk -pdf -silent -interaction=nonstopmode -halt-on-error -outdir=../build/framework branch_closure_methodology_extended.tex
