.PHONY: validate build verify specs bindings catalog checksums test

PYTHON ?= python3

validate:
	$(PYTHON) tools/validate_repository.py
	$(PYTHON) ../framework/json_schemas/tools/validate_tactics.py ../framework/json_schemas/data/ct1-ct17.numbered.json
	$(PYTHON) ../framework/json_schemas/tools/validate_schema_descriptions.py ../framework/json_schemas/schemas

specs:
	$(PYTHON) tools/generate_ct1_spec.py
	$(PYTHON) tools/generate_ct3_ct5_spec.py
	$(PYTHON) tools/generate_ct6_ct10_spec.py
	$(PYTHON) tools/generate_ct11_ct17_spec.py
	$(PYTHON) tools/sync_manifest.py

bindings: specs
	$(PYTHON) tools/generate_binding_check.py

catalog: specs
	$(PYTHON) tools/sync_ct3_ct5_manuscript.py
	$(PYTHON) ../framework/json_schemas/tools/sync_ct1_semantic.py
	$(PYTHON) ../framework/json_schemas/tools/sync_ct3_ct5_semantic.py
	$(PYTHON) ../framework/json_schemas/tools/sync_semantic_manuscript_sections.py

checksums:
	$(PYTHON) tools/generate_checksums.py

build:
	lake build

verify: bindings catalog
	$(PYTHON) tools/verify_lean.py
	$(MAKE) validate
	$(MAKE) checksums

test: validate
	$(PYTHON) -m pytest -q
