import SGPT.PSH.HermitianComparisonCanonicalOneFactor
import SGPT.PSH.HermitianComparisonPureSuccessor

/-! # Actual adjacent pure traces from canonical one-factor comparison -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparison

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianGlobalProducts HermitianComparisonPureTraces
  HermitianComparisonGlobalOneFactor

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {omega : Background (m + 1) M}

/-- The literal canonical pure measures satisfy the one-factor step. The
constant distinguished factor gives the preceding pure trace and the
original potential gives its successor. -/
theorem pureTraceMass_le_succ_add_torsion (C : CompactPartition omega)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ x, max (c - (u x).toReal) 0 ≤ δ)
    (k : ℕ) (hk : k < m + 1) :
    pureTraceMass omega hu hb {x | u x < (c : EReal)} k ≤
      pureTraceMass omega hu hb {x | u x < (c : EReal)} (k + 1) +
        torsionDifference C (pureTuple m k u) (pureTuple_isHermitianPSH hu k)
          (pureTuple_bounded hb k) u (fun _ => (c : EReal)) := by
  have h := canonical_strict_onefactor_const C (pureTuple m k u)
    (pureTuple_isHermitianPSH hu k) (pureTuple_bounded hb k) hu hb c hδ hgap
  rw [cons_const_mass_eq_pureTraceMass hu hb k (by omega) c,
    cons_self_mass_eq_pureTraceMass_succ hu hb k] at h
  linarith

end SGPT.PSH.HermitianComparison
