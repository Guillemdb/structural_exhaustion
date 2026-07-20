# Finite certificate tables

Each subdirectory owns one independent finite exhaustive computation used by
the manuscript proof. A table directory keeps its semantic definition,
certificate representation, row/count shards, and aggregate audit together.

The separation is intentional: a cached `native_decide` audit can later be
replaced by a kernel-reduced certificate one table at a time without changing
the canonical node routing.

