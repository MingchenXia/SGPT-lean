import SGPT.NPP.NonPluripolarCurrent3Currents

/-!
# The non-pluripolar product in degree one: well-definedness and the upper bound

Source: `chapter_npp.tex`, `ex:1Dnpp` (`(dd^c φ)^1 = 1_{φ > -∞} dd^c φ`); Xia, *Foundations of
pluripotential theory*, `prop:nonpluripolar-degree-one-restriction`, first step of the proof
("Upper bound": for `l ≥ k`, `1_{u>-k} dd^c u_k = 1_{u>-k} dd^c u_l ≤ dd^c u_l`, and letting
`l → ∞`, `1_{u>-k} dd^c u_k ≤ dd^c u`; hence the product is locally finite,
`0 ≤ ⟨dd^c u⟩ ≤ dd^c u`, and since `⟨dd^c u⟩` gives no mass to the pole set,
`⟨dd^c u⟩ ≤ 1_{u > -∞} dd^c u`).

Let `U ⊆ ℂ^{m+1}` be open and `u` psh and locally integrable on `U`; `dd^c u` is TN's
`ddcL1 U u`.  We prove

* `isPositive_ddcL1_sub_truncatedProduct_one` — `1_{O_k} dd^c(u ∨ (-k)) ≤ dd^c u`;
* `isWellDefinedOn_one` — **the degree-one non-pluripolar product of every psh function is well
  defined** (`eq:welldefinepluri` holds for `p = 1`);
* `isPositive_indicator_ddcL1_sub_nonPluripolarProduct_one` — **`⟨dd^c u⟩ ≤ 1_{u > -∞} dd^c u`**,
  the inequality `≤` in `eq:1dimnpp`;
* `isNonPluripolarWellDefined_one`, `isPositive_indicator_ddcCurrent_sub_nonPluripolarProduct_one`
  — the same on a complex manifold, in every chart.

The reverse inequality `1_{φ > -∞} dd^c φ ≤ (dd^c φ)^1` (one-variable Riesz decomposition and the
continuity principle, then the fibre disintegration of `dd^c u ∧ dV_z` and
`lma:boundedfibrefubini`) is **not** formalized.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))} {u : ComplexModel (m + 1) → EReal}

/-- In degree one the truncated Bedford–Taylor product is `dd^c(u ∨ (-k))`. -/
theorem truncatedBT_one (hqp : m + 1 = m + 1) (k : ℕ) :
    truncatedBT hqp U (fun _ : Fin 1 => u) k = ddcMul (oneCurrent U) (truncationReal u k) := rfl

/-- `1_A T + 1_{Aᶜ} T = T` for a positive current `T` and a Borel set `A`. -/
theorem mulBorel_indicator_add_compl {q : ℕ} {T : LocalProductCurrent (m + 1) U q}
    (hT : IsPositive T) {A : Set (ComplexModel (m + 1))} (hA : MeasurableSet A) :
    mulBorel T (A.indicator fun _ => (1 : ℝ)) + mulBorel T (Aᶜ.indicator fun _ => (1 : ℝ)) = T := by
  have e : (fun _ : ComplexModel (m + 1) => (1 : ℝ)) =
      A.indicator (fun _ => (1 : ℝ)) + Aᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [← mulBorel_add hT (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _)
    (measurable_const.indicator hA.compl) (isLocallyBoundedOn_indicator_one _), ← e,
    mulBorel_const hT 1, one_smul]

/-- **`1_{O_k} dd^c(u ∨ (-k)) ≤ dd^c u`** (FPT, proof of
`prop:nonpluripolar-degree-one-restriction`, upper bound). -/
theorem isPositive_ddcL1_sub_truncatedProduct_one (hu : IsL1PshOn U u) (hqp : m + 1 = m + 1)
    (k : ℕ) :
    IsPositive (ddcL1 U u - BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k) := by
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn u U := fun _ => hu.psh
  set hF := isTruncationFamily hqp hψ
  set O := BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u)
  -- for `l ≥ k`, `dd^c u_l - 1_{O_k} dd^c u_k = 1_{O_kᶜ} dd^c u_l ≥ 0`
  have hstep : ∀ l, k ≤ l → IsPositive
      (truncatedBT hqp U (fun _ : Fin 1 => u) l -
        BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k) := by
    intro l hkl
    have hc := hF.consistent hkl
    have hsplit := mulBorel_indicator_add_compl (hF.isPositive l) (hF.measurableSet k)
    have e : truncatedBT hqp U (fun _ : Fin 1 => u) l -
        BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k =
        mulBorel (truncatedBT hqp U (fun _ : Fin 1 => u) l) ((O k)ᶜ.indicator fun _ => (1 : ℝ)) := by
      rw [← truncAt_eq_truncatedProduct, truncAt]
      conv_lhs => rw [← hsplit]
      rw [hc]
      abel
    rw [e]
    exact SGPT.NPP.NonPluripolarCurrent.isPositive_mulBorel_indicator (hF.isPositive l)
      (hF.measurableSet k).compl
  have hlim : LocalBedfordTaylorContinuity.WeakTendsto
      (fun l => truncatedBT hqp U (fun _ : Fin 1 => u) (l + k) -
        BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k)
      (ddcL1 U u - BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k) := by
    intro γ φ
    have h := (hu.weakTendsto_ddcMul_truncation γ φ).comp (tendsto_add_atTop_nat k)
    simp only [LinearMap.sub_apply, _root_.sub_apply]
    exact h.sub_const _
  exact LocalBedfordTaylorContinuity.isPositive_of_weakTendsto
    (fun l => hstep (l + k) (Nat.le_add_left k l)) hlim

/-- **The degree-one non-pluripolar product of a psh function is well defined.** -/
theorem isWellDefinedOn_one (hu : IsL1PshOn U u) (hqp : m + 1 = m + 1) :
    IsWellDefinedOn hqp U (fun _ : Fin 1 => u) := by
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn u U := fun _ => hu.psh
  set hF := isTruncationFamily hqp hψ
  rw [isWellDefinedOn_iff hqp hψ, hF.hasLocallyFiniteMass_iff]
  intro K hK hKU
  have hD := hu.isPositive_ddcL1
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (hD.traceMeasure_lt_top hK hKU)
  have hS := SGPT.NPP.NonPluripolarCurrent.isPositive_mulBorel_indicator (hF.isPositive k)
    (hF.measurableSet k)
  rw [← traceMeasure_mulBorel_indicator_apply (hF.isPositive k) (hF.measurableSet k) hS
    hK.measurableSet]
  exact LocalBedfordTaylorCalculus.traceMeasure_le_of_isPositive_sub hS hD
    (isPositive_ddcL1_sub_truncatedProduct_one hu hqp k) K

/-- `0 ≤ ⟨dd^c u⟩ ≤ dd^c u`. -/
theorem isPositive_ddcL1_sub_nonPluripolarProduct_one (hu : IsL1PshOn U u) (hqp : m + 1 = m + 1) :
    IsPositive (ddcL1 U u - nonPluripolarProduct hqp U (fun _ : Fin 1 => u)) := by
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn u U := fun _ => hu.psh
  have hlim := weakTendsto_truncatedProduct hqp hψ (isWellDefinedOn_one hu hqp)
  refine LocalBedfordTaylorContinuity.isPositive_of_weakTendsto
    (isPositive_ddcL1_sub_truncatedProduct_one hu hqp) fun γ φ => ?_
  simp only [LinearMap.sub_apply, _root_.sub_apply]
  exact (hlim γ φ).const_sub _

/-- The union of the strict loci is the complement of the pole set in `U`. -/
theorem iUnion_strictLocus_one :
    (⋃ k, BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k) =
      {z | z ∈ U ∧ u z ≠ ⊥} := by
  ext z
  simp only [mem_iUnion, BedfordTaylorTopDegree.strictLocus, Set.mem_ofPred_eq, forall_const]
  constructor
  · rintro ⟨k, hz, hk⟩
    exact ⟨hz, ne_bot_of_gt hk⟩
  · rintro ⟨hz, hb⟩
    obtain ⟨k, hk⟩ := exists_nat_neg_lt hb
    exact ⟨k, hz, hk⟩

/-- **`ex:1Dnpp`, the inequality `≤`**: for `u` psh on `U`, the degree-one non-pluripolar product
is well defined and `0 ≤ (dd^c u)^1 ≤ 1_{u > -∞} dd^c u`. -/
theorem isPositive_indicator_ddcL1_sub_nonPluripolarProduct_one (hu : IsL1PshOn U u)
    (hqp : m + 1 = m + 1) :
    IsWellDefinedOn hqp U (fun _ : Fin 1 => u) ∧
      IsPositive (nonPluripolarProduct hqp U (fun _ : Fin 1 => u)) ∧
      IsPositive (mulBorel (ddcL1 U u) ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ)) -
        nonPluripolarProduct hqp U (fun _ : Fin 1 => u)) := by
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn u U := fun _ => hu.psh
  have hW := isWellDefinedOn_one hu hqp
  have hN := isPositive_nonPluripolarProduct hqp hψ hW
  refine ⟨hW, hN, ?_⟩
  set A := ⋃ k, BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k
  have hA : MeasurableSet A :=
    MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus hψ)
  rw [← iUnion_strictLocus_one]
  have hD := isPositive_ddcL1_sub_nonPluripolarProduct_one hu hqp
  -- `⟨dd^c u⟩ = 1_A ⟨dd^c u⟩`
  have hNA : mulBorel (nonPluripolarProduct hqp U (fun _ : Fin 1 => u))
      (A.indicator fun _ => (1 : ℝ)) = nonPluripolarProduct hqp U (fun _ : Fin 1 => u) := by
    have h := mulBorel_indicator_add_compl hN hA
    rwa [mulBorel_nonPluripolarProduct_compl hqp hψ hW, add_zero] at h
  have hsum : ddcL1 U u = (1 : ℝ) • (ddcL1 U u - nonPluripolarProduct hqp U (fun _ : Fin 1 => u)) +
      (1 : ℝ) • nonPluripolarProduct hqp U (fun _ : Fin 1 => u) := by
    rw [one_smul, one_smul, sub_add_cancel]
  rw [hsum, mulBorel_smul_add_smul hD hN zero_le_one zero_le_one (measurable_const.indicator hA)
    (isLocallyBoundedOn_indicator_one _), one_smul, one_smul, hNA, add_sub_cancel_right]
  exact SGPT.NPP.NonPluripolarCurrent.isPositive_mulBorel_indicator hD hA

end SGPT.NPP.NonPluripolarCurrent

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-- **The degree-one non-pluripolar product of a psh function on `M` is well defined.** -/
theorem isNonPluripolarWellDefined_one {φ : M → EReal} (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ)
    (hqp : m + 1 = m + 1) : IsNonPluripolarWellDefined hqp (fun _ : Fin 1 => φ) := fun e =>
  isWellDefinedOn_one (isL1PshOn_chart hφ e) hqp

/-- **`ex:1Dnpp`, the inequality `≤`, on `M`**: in every chart,
`(dd^c φ)^1 ≤ 1_{φ > -∞} dd^c φ`, where `(dd^c φ)^1` is the non-pluripolar product
(`def:npp:L69`) and `dd^c φ` the current `SGPT.NPP.ddcCurrent`. -/
theorem isPositive_indicator_ddcCurrent_sub_nonPluripolarProduct_one {φ : M → EReal}
    (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ) (hqp : m + 1 = m + 1) (e : ComplexChart (m + 1) M) :
    IsPositive (mulBorel ((ddcCurrent m φ hφ).inChart e)
        ({z | z ∈ chartTarget e ∧ φ (e.val.symm z) ≠ ⊥}.indicator fun _ => (1 : ℝ)) -
      (nonPluripolarProduct hqp (fun _ : Fin 1 => φ) (fun _ => hφ)
        (isNonPluripolarWellDefined_one hφ hqp)).inChart e) :=
  (isPositive_indicator_ddcL1_sub_nonPluripolarProduct_one (isL1PshOn_chart hφ e) hqp).2.2

end SGPT.NPP
