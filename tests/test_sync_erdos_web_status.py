import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "sync_erdos_web_status", ROOT / "tools/sync_erdos_web_status.py"
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
extract_status = MODULE.extract_status


def test_extracts_current_lean_owned_erdos_status() -> None:
    source = (ROOT / "examples/erdos_64_eg/Erdos64EG/WebExport.lean").read_text()
    node_ids, obligations = extract_status(source)
    assert node_ids[-1] == 155
    assert 49 in node_ids and 50 in node_ids
    assert 154 in node_ids and 155 in node_ids
    by_id = {item["obligationId"]: item for item in obligations}
    assert by_id["N49-ENTROPY"]["status"] == "proved"
    assert by_id["N50-EXHAUSTIVE"]["status"] == "proved"
    assert by_id["N50-EXHAUSTIVE"]["evidenceStepIds"] == [
        "erdos.entropy-scale-split"
    ]
    for obligation_id in ("N154-PROV", "N154-DECIDE", "N154-NOG1", "N154-WORK"):
        assert by_id[obligation_id]["status"] == "proved"
        assert by_id[obligation_id]["evidenceStepIds"] == ["erdos.cold-g1-split"]
    for obligation_id in ("N155-PROV", "N155-CT1", "N155-CLOSE", "N155-WORK"):
        assert by_id[obligation_id]["status"] == "proved"
        assert by_id[obligation_id]["evidenceStepIds"] == ["erdos.cold-g1-terminal"]
