.PHONY: help lint build framework-build example-build even-cycle-example-build erdos-example-build greedy-coloring-example-build mantel-example-build mathlib-cache export schemas generate validate kernel verify test manuscript checksums

.DEFAULT_GOAL := build

PYTHON ?= python3
LEAN_DIR := lean
EVEN_CYCLE_EXAMPLE_DIR := examples/even_cycle
ERDOS_EXAMPLE_DIR := examples/erdos_64_eg
GREEDY_COLORING_EXAMPLE_DIR := examples/greedy_coloring
MANTEL_EXAMPLE_DIR := examples/mantel
CATALOG := generated/lean-machines.json

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
	  '  make export      Build Lean and export the canonical compiled machine catalog' \
	  '  make schemas     Export Lean and regenerate all concrete JSON Schemas' \
	  '  make generate    Export Lean and regenerate every schema, diagram, index, and binding check' \
	  '  make validate    Validate the current catalog, contracts, routes, schemas, and graph invariants' \
	  '  make kernel      Regenerate and kernel-check bindings, freshness, and absence of admissions' \
	  '  make verify      Run the complete linter, generation, kernel, validation, and checksum chain' \
	  '  make test        Run make verify followed by the Python regression suite' \
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

export: build
	cd $(LEAN_DIR) && STRUCTURAL_EXHAUSTION_EXPORT=../$(CATALOG) lake env lean StructuralExhaustion/Canonical/Export.lean

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

manuscript: generate
	mkdir -p build/framework
	cd framework && latexmk -pdf -silent -interaction=nonstopmode -halt-on-error -outdir=../build/framework branch_closure_methodology_extended.tex
