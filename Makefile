.PHONY: help lint build framework-build example-build even-cycle-example-build erdos-example-build greedy-coloring-example-build mantel-example-build mathlib-cache export example-export erdos-web-status-sync erdos-proof-history schemas generate validate kernel verify test manuscript checksums web web-build web-test web-frontend-test

.DEFAULT_GOAL := build

PYTHON ?= python3
UV ?= uv
NPM ?= npm
UV_CACHE_DIR ?= /tmp/uv-cache
LEAN_DIR := lean
EVEN_CYCLE_EXAMPLE_DIR := examples/even_cycle
ERDOS_EXAMPLE_DIR := examples/erdos_64_eg
GREEDY_COLORING_EXAMPLE_DIR := examples/greedy_coloring
MANTEL_EXAMPLE_DIR := examples/mantel
CATALOG := generated/lean-machines.json
DOCUMENTATION_CATALOG := generated/framework-documentation.json
EXAMPLE_EXPORT_DIR := build/example-exports
WEB_FRONTEND_DIR := web/frontend
WEB_NODE_STAMP := $(WEB_FRONTEND_DIR)/node_modules/.package-lock.json
WEB_HOST ?= 127.0.0.1
WEB_PORT ?= 8000

help:
	@printf '%s\n' \
	  'Structural Exhaustion automation-first workflow' \
	  '' \
	  '  make lint        Reject legacy APIs, proof injection, admissions, and forbidden imports' \
	  '  make mathlib-cache  Download Mathlib oleans for the framework and external examples' \
	  '  make framework-build  Compile only the reusable Lean framework package' \
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
	  '  make web         Build and serve the framework explorer on one local URL' \
	  '  make web-test    Run backend/frontend explorer tests and production build' \
	  '  make manuscript  Regenerate CT figures and compile the PDF manuscript'

lint:
	$(PYTHON) tools/lint_automation_first.py --root .

framework-build:
	cd $(LEAN_DIR) && lake build

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

kernel: generate
	$(PYTHON) tools/verify_lean.py

checksums:
	$(PYTHON) tools/generate_checksums.py

verify: lint kernel
	$(MAKE) validate
	$(MAKE) checksums

test: verify
	$(PYTHON) -m pytest -q
	$(MAKE) web-frontend-test

$(WEB_NODE_STAMP): $(WEB_FRONTEND_DIR)/package.json $(WEB_FRONTEND_DIR)/package-lock.json
	cd $(WEB_FRONTEND_DIR) && $(NPM) ci

web-build: $(WEB_NODE_STAMP)
	cd $(WEB_FRONTEND_DIR) && $(NPM) run build

web-frontend-test: $(WEB_NODE_STAMP)
	cd $(WEB_FRONTEND_DIR) && $(NPM) run test
	cd $(WEB_FRONTEND_DIR) && $(NPM) run typecheck
	cd $(WEB_FRONTEND_DIR) && $(NPM) run build

web-test: $(WEB_NODE_STAMP)
	UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run --with-requirements requirements.txt python -m pytest -q tests/test_web_api.py
	$(MAKE) web-frontend-test

web: web-build
	STRUCTURAL_EXHAUSTION_ALLOW_STALE_HASHES=1 UV_CACHE_DIR=$(UV_CACHE_DIR) $(UV) run --with-requirements requirements.txt uvicorn web.backend.app.main:app --host $(WEB_HOST) --port $(WEB_PORT)

manuscript: generate
	mkdir -p build/framework
	cd framework && latexmk -pdf -silent -interaction=nonstopmode -halt-on-error -outdir=../build/framework branch_closure_methodology_extended.tex
