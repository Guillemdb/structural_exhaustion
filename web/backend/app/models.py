"""Pydantic contracts at the Flask API and generated-artifact boundaries."""

from __future__ import annotations

from typing import Any, ClassVar

from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator


class StrictModel(BaseModel):
    model_config = ConfigDict(extra="forbid")


class ManifestSourceModel(StrictModel):
    id: str = Field(min_length=1, max_length=240)
    path: str = Field(min_length=1, max_length=1000)
    sha256: str = Field(pattern=r"^[0-9a-f]{64}$")


class ManifestModel(StrictModel):
    schema_version: str = Field(min_length=1)
    snapshot_sha256: str
    counts: dict[str, int]
    sources: list[ManifestSourceModel]

    @field_validator("counts")
    @classmethod
    def counts_are_natural(cls, value: dict[str, int]) -> dict[str, int]:
        if any(count < 0 for count in value.values()):
            raise ValueError("manifest counts must be nonnegative")
        return value


class SnapshotModel(StrictModel):
    schema_version: str = Field(min_length=1)
    site: dict[str, Any]
    pages: dict[str, dict[str, Any]]
    modules: list[dict[str, Any]] | dict[str, dict[str, Any]]
    declarations: list[dict[str, Any]] | dict[str, dict[str, Any]]
    cts: list[dict[str, Any]] | dict[str, dict[str, Any]]
    routes: list[dict[str, Any]] | dict[str, dict[str, Any]]
    examples: list[dict[str, Any]] | dict[str, dict[str, Any]]
    erdos: dict[str, Any]
    sources: list[dict[str, Any]] | dict[str, dict[str, Any]]
    search_documents: list[dict[str, Any]]
    trust: dict[str, Any]


class SearchQuery(StrictModel):
    q: str = Field(default="", max_length=200)
    kind: str | None = Field(default=None, min_length=1, max_length=100)
    module: str | None = Field(default=None, min_length=1, max_length=300)
    page: int = Field(default=1, ge=1)
    page_size: int = Field(default=20, ge=1, le=100)

    @field_validator("q")
    @classmethod
    def normalize_query(cls, value: str) -> str:
        return " ".join(value.split())


class SourceExcerptQuery(StrictModel):
    start: int | None = Field(default=None, ge=1)
    end: int | None = Field(default=None, ge=1)
    default_span: ClassVar[int] = 160
    maximum_span: ClassVar[int] = 400

    @model_validator(mode="after")
    def ordered_range(self) -> "SourceExcerptQuery":
        if self.start is not None and self.end is not None and self.end < self.start:
            raise ValueError("end line must not precede start line")
        return self
