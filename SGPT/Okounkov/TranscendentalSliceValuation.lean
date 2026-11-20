import SGPT.Okounkov.TranscendentalSliceClasses
import SGPT.Okounkov.TranscendentalCoreValuationAnalytic
import SGPT.Okounkov.TranscendentalCoreValuationBounded
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Okounkov.TranscendentalBodyConvex
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Okounkov.TranscendentalDensityTheorem
import SGPT.Okounkov.TranscendentalExtensionMain
import SGPT.Okounkov.TranscendentalPoleExtension
import SGPT.Okounkov.DivisorResidualGenericZero
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole

/-!
# Valuations of extended Kähler currents

Source: blueprint node `tok:slice-kahler` (sub-lemmas `tok-slice:lelong-zero`,
`tok-slice:weight-valuation`, `tok-slice:extension-valuation` of `claude-tok-slice.tex`); this
is also the "in particular `ν(S̃, V) = 0`" clause of DRWNXZ Theorem 6.4 (remark
`ext:gentle-lelong` of `claude-tok-ext.tex`) for a hypersurface `V = Y₁`.

Let `X` be a connected compact Kähler manifold of dimension `m + 1` with a smooth flag, `Y₁` its
first member and `E` a unit metric of `Y₁` (weight `ψ_E = log |s_{Y₁}|²_E`, curvature `Θ_E`).

* `flagValuation_eq_cons_zero_of_ne_bot`: if `φ ∈ 𝒜(θ)` is finite at some point of `Y₁`, then
  `ν(φ) = (0, ν_{Y₁ ⊇ ⋯}(φ|_{Y₁}))`: the generic Lelong number along `Y₁` vanishes (a positive
  Lelong number forces a pole), and the residual with coefficient `0` is `φ` itself.
* `flagValuation_weight`: `ν(ψ_E) = (1, 0, …, 0)`, i.e. `ν([Y₁]) = e₁`.
* `flagValuation_add_smul_weight`: `ν(φ + t ψ_E) = (t, ν(φ|_{Y₁}))` for such `φ` and `t ≥ 0`.
* `cons_mem_tradOkounkovBody_of_extension` (the extension step of `tok:slice-kahler`): for a
  Kähler form `κ`, a rational `t ≥ 0` and a gentle Kähler current `κ|_{Y₁} + dd^c w` on `Y₁`,
  `(t, ν(w)) ∈ Δ(κ + t Θ_E)`. The extension `φ̃` of `w` (DRWNXZ Theorem 6.4, package EXT) gives
  `φ̃ + t ψ_E ∈ 𝒜({κ} + t{Y₁})` with valuation `(t, ν(w))`, which lies in the body by
  `tok:density`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalSlice

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Okounkov.TranscendentalCore

section Local

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The squared-logarithmic Lelong number (the normalization of `sourceGenericLelongNumber`) of
a `θ`-psh function finite at `x` vanishes (positive dimension): a positive Lelong number forces
a pole (`eq_bot_of_lelongNumber_pos`). -/
theorem squaredLogLelongNumber_eq_zero_of_ne_bot (hn : 0 < n) {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) {x : M} (hx : u x ≠ ⊥) :
    squaredLogLelongNumber (n := n) u x = 0 := by
  have hl : lelongNumber (n := n) u x = 0 :=
    le_antisymm (le_of_not_gt fun h => hx (eq_bot_of_lelongNumber_pos hn hu h)) bot_le
  have h := lelongNumber_eq_two_mul_squaredLog (n := n) hn.ne' u x
  rw [hl] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

end Local

section Cut

variable {X : Type*} [TopologicalSpace X]

open scoped Classical in
/-- The upper regularization of a function continuous at `x`, cut to `-∞` on a set `K` with
empty interior, is the function itself at `x`. -/
theorem uscRegularization_cut_eq {K : Set X} (hK : interior K = ∅) {φ : X → EReal} {x : X}
    (hφ : ContinuousAt φ x) :
    uscRegularization (fun y => if y ∈ K then ⊥ else φ y) x = φ x := by
  apply le_antisymm
  · refine uscRegularization_le_of_eventually_le hφ.upperSemicontinuousAt
      (Eventually.of_forall fun y => ?_)
    split_ifs
    · exact bot_le
    · exact le_rfl
  · refine le_iInf₂ fun U hU => ?_
    refine le_of_forall_lt fun a ha => ?_
    have hS : {y | a < φ y} ∈ 𝓝 x := hφ.eventually (lt_mem_nhds ha)
    have hUS : U ∩ {y | a < φ y} ∈ 𝓝 x := Filter.inter_mem hU hS
    have hnot : ¬ U ∩ {y | a < φ y} ⊆ K := by
      intro hsub
      have hx : x ∈ interior K := interior_mono hsub (mem_interior_iff_mem_nhds.mpr hUS)
      rw [hK] at hx
      exact hx
    obtain ⟨y, ⟨hyU, hya⟩, hyK⟩ := not_subset.mp hnot
    refine lt_of_lt_of_le hya ?_
    refine le_iSup₂_of_le (f := fun y (_ : y ∈ U) => if y ∈ K then (⊥ : EReal) else φ y) y hyU ?_
    simp [hyK]

end Cut

section Valuation

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **The first coordinate vanishes and the tail is the restriction** (blueprint
`tok-slice:lelong-zero`): if `φ ∈ 𝒜(θ)` is finite at a point of `Y₁`, then
`ν(φ) = (0, ν_{Y₁ ⊇ ⋯ ⊇ Yₙ}(φ|_{Y₁}))`. This is the "in particular `ν(S̃, Y₁) = 0`" clause of
DRWNXZ Theorem 6.4 together with the successive-restriction description of `ν`. -/
theorem flagValuation_eq_cons_zero_of_ne_bot {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : φ ∈ analyticCurrents θ) {y₀ : F.carrier}
    (hy₀ : y₀ ∈ F.flag (1 : Fin (m + 2))) (hφy₀ : φ y₀ ≠ ⊥) :
    flagValuation F φ =
      Fin.cons 0 (flagValuation F.tail (fun y : F.tail.carrier => φ y.val)) := by
  obtain ⟨D, hDI, E, hEW, hmetric, -, -⟩ :=
    SGPT.Okounkov.exists_normalized_smooth_divisor_residual_generic_zero hφ.1 F.firstDivisor
  have hsg : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ = 0 :=
    le_antisymm ((iInf_le (fun y : F.flag (1 : Fin (m + 2)) =>
      squaredLogLelongNumber (n := m + 1) φ y.val) ⟨y₀, hy₀⟩).trans
        (squaredLogLelongNumber_eq_zero_of_ne_bot (Nat.succ_pos m) hφ.1.1 hφy₀).le) bot_le
  have hcz : (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toNNReal = 0 := by
    rw [hsg]; rfl
  obtain ⟨-, hc0, -, htail⟩ := flagValuation_of_analytic F hφ D hDI E hEW hmetric
  have hv := SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hφ.1
    F.firstDivisor D hDI E hEW hmetric
  simp only [hcz, NNReal.coe_zero] at hc0 htail hv
  have hrec := SGPT.Okounkov.smooth_divisor_residual_recompose hφ.1 F.firstDivisor E hEW 0
    (by simpa using hv)
  have hext : ∀ y, extensionAcross (F.flag (1 : Fin (m + 2)))
      (smoothDivisorOffResidual E 0 φ) y = φ y := by
    intro y
    have := congrFun hrec y
    simpa using this
  have htail' : (fun i => flagValuation F φ i.succ) =
      flagValuation F.tail (fun y : F.tail.carrier => φ y.val) := by
    rw [htail]
    congr 1
    funext y
    exact hext y.val
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]; exact hc0
  · rw [Fin.cons_succ]; exact congrFun htail' j

variable {F}

/-- The weight `ψ_E` of a unit metric of `Y₁` is a potential of `[Y₁] = Θ_E + dd^c ψ_E` with
analytic singularities: `ψ_E ∈ 𝒜({Y₁})`. -/
theorem weight_mem_analyticCurrents {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) :
    E.weight ∈ analyticCurrents E.curvature := by
  obtain ⟨D, -, hEW, hmetric⟩ := hE
  exact ⟨SGPT.Okounkov.isThetaPshPotential_divisor_weight_of_smooth_support F.firstDivisor E hEW,
    SGPT.Okounkov.TranscendentalPole.hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hmetric)⟩

/-- **`ν([Y₁]) = e₁`** (blueprint `tok-slice:weight-valuation`): the weight of a unit metric of
`Y₁` has valuation `(1, 0, …, 0)`. -/
theorem flagValuation_weight {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) :
    flagValuation F E.weight = Fin.cons 1 0 := by
  classical
  have hA := weight_mem_analyticCurrents hE
  obtain ⟨D, hDI, hEW, hmetric⟩ := hE
  have hone := SGPT.Okounkov.sourceGeneric_divisor_metric_eq_one F.firstDivisor D hDI E hmetric
  have hc1 : (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) E.weight).toNNReal = 1 := by
    rw [hone]; rfl
  obtain ⟨-, hc0, -, htail⟩ := flagValuation_of_analytic F hA D hDI E hEW hmetric
  simp only [hc1, NNReal.coe_one] at hc0 htail
  have hint : interior (F.flag (1 : Fin (m + 2))) = ∅ :=
    SGPT.Okounkov.smooth_divisor_interior_eq_empty F.firstDivisor
  have hres : ∀ y, extensionAcross (F.flag (1 : Fin (m + 2)))
      (smoothDivisorOffResidual E 1 E.weight) y = 0 := by
    intro y
    rw [extensionAcross]
    have hfun : (fun z => if z ∈ F.flag (1 : Fin (m + 2)) then (⊥ : EReal) else
        smoothDivisorOffResidual E 1 E.weight z) =
        fun z => if z ∈ F.flag (1 : Fin (m + 2)) then (⊥ : EReal) else (fun _ => (0 : EReal)) z := by
      funext z
      by_cases hz : z ∈ F.flag (1 : Fin (m + 2))
      · simp [hz]
      · have hzE : z ∉ E.support := by rw [hEW]; exact hz
        obtain ⟨G, -, hGeq⟩ :=
          MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hzE
        have hG := Filter.Eventually.self_of_nhds hGeq
        simp only [hz, if_false, smoothDivisorOffResidual, hzE, hG, EReal.coe_one, one_mul]
        rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
    rw [hfun]
    exact uscRegularization_cut_eq hint continuousAt_const
  have htail' : (fun i : Fin m => flagValuation F E.weight i.succ) = 0 := by
    rw [htail]
    have : (fun y : F.tail.carrier => extensionAcross (F.flag (1 : Fin (m + 2)))
        (smoothDivisorOffResidual E 1 E.weight) y.val) = fun _ => (0 : EReal) := by
      funext y; exact hres y.val
    rw [this]
    exact SGPT.Okounkov.TranscendentalBody.flagValuation_zero_potential F.tail
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]; exact hc0
  · rw [Fin.cons_succ]; exact congrFun htail' j

/-- **`ν(φ + t ψ_E) = (t, ν(φ|_{Y₁}))`** (blueprint `tok-slice:extension-valuation`): for
`φ ∈ 𝒜(θ)` finite at a point of `Y₁` and `t ≥ 0`. -/
theorem flagValuation_add_smul_weight {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : φ ∈ analyticCurrents θ) {y₀ : F.carrier}
    (hy₀ : y₀ ∈ F.flag (1 : Fin (m + 2))) (hφy₀ : φ y₀ ≠ ⊥)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {t : ℝ} (ht : 0 ≤ t) :
    flagValuation F (fun x => ((1 : ℝ) : EReal) * φ x + (t : EReal) * E.weight x) =
      Fin.cons t (flagValuation F.tail (fun y : F.tail.carrier => φ y.val)) := by
  rw [flagValuation_add_smul hφ.1 (weight_mem_analyticCurrents hE).1 zero_le_one ht,
    flagValuation_eq_cons_zero_of_ne_bot F hφ hy₀ hφy₀, flagValuation_weight hE, one_smul]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

end Valuation

section Extension

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- The restriction of a Kähler form to `Y₁`, as a Kähler form of the tail flag geometry. -/
abbrev restrictedKahlerForm (κ : KahlerBackground (m + 1) F.carrier) :
    KahlerBackground m F.tail.carrier :=
  SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ m) F.firstDivisor.2.2 κ

theorem restrictedKahlerForm_form (κ : KahlerBackground (m + 1) F.carrier) :
    (restrictedKahlerForm κ).form = TranscendentalMain.firstFlagRestriction F κ.form := rfl

/-- **The extension step of `tok:slice-kahler`**: let `κ` be a Kähler form on `X`, `E` a unit
metric of `Y₁`, `t ≥ 0` rational with `Ω({κ} + t{Y₁}) ≠ ∅`, and `κ|_{Y₁} + dd^c w` a gentle
Kähler current on `Y₁`. Then `(t, ν(w)) ∈ Δ(κ + t Θ_E)`. -/
theorem cons_mem_tradOkounkovBody_of_extension (κ : KahlerBackground (m + 1) F.carrier)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : TranscendentalMain.IsFirstDivisorUnitMetric F E) {t : ℚ} (ht : 0 ≤ t)
    (hΩ : (gentleKahlerCurrents (κ.form + (t : ℝ) • E.curvature)).Nonempty)
    {w : F.tail.carrier → EReal}
    (hw : w ∈ gentleKahlerCurrents (TranscendentalMain.firstFlagRestriction F κ.form)) :
    Fin.cons (t : ℝ) (flagValuation F.tail w) ∈
      tradOkounkovBody F (κ.form + (t : ℝ) • E.curvature) := by
  obtain ⟨φ', hK, hA, hres, -, -⟩ :=
    SGPT.Okounkov.TranscendentalExtension.hasGentleKahlerCurrentExtension κ F.firstDivisor w hw.2
      hw.1.2
  obtain ⟨ω', hω'⟩ := hK
  have hpsh : IsThetaPshPotential κ.form.val φ' := by
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hω' ?_
    rw [sub_sub_cancel]
    exact ω'.isSemipositive
  have hφ' : φ' ∈ analyticCurrents κ.form := ⟨hpsh, hA⟩
  -- a point of `Y₁` where `w` is finite
  obtain ⟨x₀, hx₀⟩ := F.firstDivisor.2.1.nonempty
  obtain ⟨y₀, -, hy₀⟩ := hw.1.1.2 (⟨x₀, hx₀⟩ : F.tail.carrier) univ isOpen_univ (mem_univ _)
  have hφ'y₀ : φ' y₀.val ≠ ⊥ := by rw [hres y₀]; exact hy₀
  -- the current `φ̃ + t ψ_E`
  have hΦ := add_smul_mem_analyticCurrents hφ' (weight_mem_analyticCurrents hE)
    (a := 1) (b := t) zero_le_one ht
  simp only [Rat.cast_one, one_smul] at hΦ
  have hν := flagValuation_add_smul_weight hφ' y₀.2 hφ'y₀ hE (t := (t : ℝ))
    (by exact_mod_cast ht)
  have htail : (fun y : F.tail.carrier => φ' y.val) = w := funext hres
  rw [htail] at hν
  have hmem := SGPT.Okounkov.TranscendentalDensity.densityStatement (m + 1) F _ hΩ _ hΦ
  rw [hν] at hmem
  exact closure_minimal (image_gentleKahlerCurrents_subset_tradOkounkovBody _)
    (isClosed_tradOkounkovBody _) hmem

end Extension

end SGPT.Okounkov.TranscendentalSlice
