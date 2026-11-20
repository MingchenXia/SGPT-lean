import SGPT.Envelopes.MADirichletComparison
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity

/-!
# Capacity of sublevel sets from the comparison principle

Xia, *Foundations of pluripotential theory* (FPT), `lem:local-comparison-capacity-sublevels`:
let `D ⊆ ℂⁿ` be open, `u, v` locally bounded plurisubharmonic on `D`, `s ∈ ℝ`, `t > 0`, and
suppose `{u < v - s} ⋐ D`. Then

  `tⁿ Cap_D({u < v - s - t}) ≤ ∫_{u < v - s} (ddᶜu)ⁿ`

(`pow_mul_relCapacity_le`). Here `Cap_D` is TN's relative Monge–Ampère capacity
(`relCapacity`, the supremum of `(ddᶜw)ⁿ(E)` over psh `w` on `D` with `-1 ≤ w ≤ 0`, which is FPT's
`def:monge-ampere-capacity` after the shift `w ↦ w + 1`), and `{u < v - s} ⋐ D` is expressed by
a compact `K ⊆ D` containing it (FPT's `D` is bounded; boundedness is not needed in this form).

Proof (FPT): for a competitor `w`, `{u < v - s - t} ⊆ {u < v - s + t w} ⊆ {u < v - s}`; the
comparison principle (compact form, `SGPT.PSH.BookDeepDomination.measure_lt_le_of_subset_compact`)
applied to `u` and `v - s + t w`, together with
`(ddᶜ(v - s + t w))ⁿ ≥ tⁿ (ddᶜw)ⁿ` (superadditivity, `isBTLimit_add_ge`, and homogeneity), gives
`tⁿ (ddᶜw)ⁿ({u < v - s - t}) ≤ (ddᶜu)ⁿ({u < v - s})`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- **Capacity of sublevel sets** (FPT `lem:local-comparison-capacity-sublevels`). -/
theorem pow_mul_relCapacity_le (hn : 0 < n) {D : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn D u) (hv : IsLocallyBoundedPshOn D v)
    (s : ℝ) {t : ℝ} (ht : 0 < t) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKD : K ⊆ D) (hsub : {z | z ∈ D ∧ u z < v z - s} ⊆ K) :
    ENNReal.ofReal t ^ n * relCapacity D {z | z ∈ D ∧ u z < v z - s - t} ≤
      canonicalBedfordTaylorMeasure D u hu {z | z ∈ D ∧ u z < v z - s} := by
  unfold relCapacity
  simp only [ENNReal.mul_iSup]
  refine iSup₂_le fun w hw => iSup_le fun hwb => ?_
  set g : ComplexModel n → ℝ := fun z => (v z + -s) + t * w z with hgdef
  have hvs : IsLocallyBoundedPshOn D fun z => v z + -s := IsLocallyBoundedPshOn.add_const hv _
  have htw : IsLocallyBoundedPshOn D fun z => t * w z := isLocallyBoundedPshOn_const_mul hw ht.le
  have hg : IsLocallyBoundedPshOn D g :=
    SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add hvs htw
  set A : Set (ComplexModel n) := {z | z ∈ D ∧ u z < g z} with hAdef
  have hsub1 : {z | z ∈ D ∧ u z < v z - s - t} ⊆ A := by
    rintro z ⟨hzD, hz⟩
    refine ⟨hzD, ?_⟩
    have := (hwb z hzD).1
    simp only [hgdef]
    nlinarith
  have hsub2 : A ⊆ {z | z ∈ D ∧ u z < v z - s} := by
    rintro z ⟨hzD, hz⟩
    refine ⟨hzD, ?_⟩
    have := (hwb z hzD).2
    simp only [hgdef] at hz
    nlinarith
  -- the comparison principle on the relatively compact contact set
  have hcomp := SGPT.PSH.BookDeepDomination.measure_lt_le_of_subset_compact hn hu hg
    (isBTLimit_canonicalBedfordTaylorMeasure hu) (isBTLimit_canonicalBedfordTaylorMeasure hg)
    hK hKD (hsub2.trans hsub)
  -- `(ddᶜg)ⁿ ≥ tⁿ (ddᶜw)ⁿ`
  have hhom : IsBTLimit D (fun _ => fun z => t * w z)
      (ENNReal.ofReal t ^ n • canonicalBedfordTaylorMeasure D w hw) :=
    (isBTLimit_canonicalBedfordTaylorMeasure hw).const_mul_all ht.le
  have hadd := isBTLimit_add_ge hn hvs htw (isBTLimit_canonicalBedfordTaylorMeasure hg)
    (isBTLimit_canonicalBedfordTaylorMeasure hvs) hhom
  have hlow : ENNReal.ofReal t ^ n * canonicalBedfordTaylorMeasure D w hw A ≤
      canonicalBedfordTaylorMeasure D g hg A := by
    have := hadd A
    rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at this
    exact le_trans le_add_self this
  calc ENNReal.ofReal t ^ n * canonicalBedfordTaylorMeasure D w hw {z | z ∈ D ∧ u z < v z - s - t}
      ≤ ENNReal.ofReal t ^ n * canonicalBedfordTaylorMeasure D w hw A := by
        gcongr
    _ ≤ canonicalBedfordTaylorMeasure D g hg A := hlow
    _ ≤ canonicalBedfordTaylorMeasure D u hu A := hcomp
    _ ≤ canonicalBedfordTaylorMeasure D u hu {z | z ∈ D ∧ u z < v z - s} := measure_mono hsub2

end SGPT.Envelopes.MADirichlet
