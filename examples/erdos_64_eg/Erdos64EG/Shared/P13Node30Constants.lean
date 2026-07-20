import Mathlib

namespace Erdos64EG.Internal

/-! Paper-local numerical constants used by node `[30]`. -/

/-- Exact rational form of the sharper high-entropy deficiency rate. -/
noncomputable def p13Node30HighEntropyDeficiencyRate : ℝ :=
  21296321056 / 100000000000

/-- Exact sharper wedge coefficient printed in the manuscript. -/
noncomputable def p13Node30OmegaHighEntropy : ℝ :=
  257407357888 / 100000000000

theorem p13Node30OmegaHighEntropy_eq :
    p13Node30OmegaHighEntropy =
      3 - 2 * p13Node30HighEntropyDeficiencyRate := by
  norm_num [p13Node30OmegaHighEntropy,
    p13Node30HighEntropyDeficiencyRate]

end Erdos64EG.Internal
