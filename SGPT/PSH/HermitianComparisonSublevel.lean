import SGPT.PSH.HermitianPSH
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The genuine comparison sublevel used to obtain positive bounded mass

A bounded upper semicontinuous potential has a nonempty open strict
sublevel with arbitrarily small positive gap from a constant competitor.
This is the geometry needed to use full support of the smooth Hermitian
volume in the small-gap comparison principle.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonSublevel

open Set Filter TopologicalSpace
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [Nonempty X]

/-- The lower comparison set is produced from the actual bounded potential;
neither attainment of its infimum nor positivity of its mass is assumed. -/
theorem exists_small_nonempty_open_sublevel {u : X → EReal}
    (hu : UpperSemicontinuous u) {a b : ℝ}
    (hbound : ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, IsOpen {x | u x < (c : EReal)} ∧
      {x | u x < (c : EReal)}.Nonempty ∧
      ∀ x, u x < (c : EReal) → 0 < c - (u x).toReal ∧ c - (u x).toReal ≤ δ := by
  have hfinite (x : X) : u x ≠ ⊤ ∧ u x ≠ ⊥ :=
    ⟨ne_of_lt ((hbound x).2.trans_lt (EReal.coe_lt_top b)),
      ne_of_gt ((EReal.bot_lt_coe a).trans_le (hbound x).1)⟩
  have hcoe (x : X) : ((u x).toReal : EReal) = u x :=
    EReal.coe_toReal (hfinite x).1 (hfinite x).2
  let v : X → ℝ := fun x => (u x).toReal
  have hbelow : BddBelow (range v) := by
    refine ⟨a, ?_⟩
    rintro t ⟨x, rfl⟩
    exact EReal.coe_le_coe_iff.mp (by rw [hcoe]; exact (hbound x).1)
  let c : ℝ := sInf (range v) + δ
  have hne : (range v).Nonempty := range_nonempty v
  obtain ⟨t, ⟨x, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne
    (show sInf (range v) < c by dsimp [c]; linarith)
  refine ⟨c, hu.isOpen_preimage (c : EReal), ?_, ?_⟩
  · refine ⟨x, ?_⟩
    change u x < (c : EReal)
    rw [← hcoe x]
    exact EReal.coe_lt_coe_iff.mpr hx
  · intro y hy
    have hyv : v y < c := EReal.coe_lt_coe_iff.mp (by rw [hcoe]; exact hy)
    have hinf : sInf (range v) ≤ v y := csInf_le hbelow (mem_range_self y)
    change 0 < c - v y ∧ c - v y ≤ δ
    dsimp [c] at *
    exact ⟨by linarith, by linarith⟩

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Upper semicontinuity comes from the original local-QPSH member of the
native Hermitian PSH definition, without a closed background. -/
theorem hermitianPSH_upperSemicontinuous {omega : Hermitian.Background (m + 1) M}
    {u : M → EReal} (hu : Hermitian.IsHermitianPSH omega u) : UpperSemicontinuous u :=
  ManifoldQuasiPlurisubharmonic.upperSemicontinuous hu.choose.1

/-- The native bounded Hermitian potential itself supplies the exact open
comparison set required to prove its Monge--Ampère mass is positive. -/
theorem exists_small_hermitian_sublevel [Nonempty M]
    {omega : Hermitian.Background (m + 1) M} {u : M → EReal}
    (hu : Hermitian.IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, IsOpen {x | u x < (c : EReal)} ∧
      {x | u x < (c : EReal)}.Nonempty ∧
      ∀ x, u x < (c : EReal) → 0 < c - (u x).toReal ∧ c - (u x).toReal ≤ δ := by
  obtain ⟨a, b, hab⟩ := hb
  exact exists_small_nonempty_open_sublevel (hermitianPSH_upperSemicontinuous hu) hab hδ

end SGPT.PSH.HermitianComparisonSublevel
