import SGPT.Envelopes.RelativeCYUniqueness
import SGPT.Envelopes.RelativeMADimZero

/-!
# The relative Calabi–Yau theorem

Source `thm:Yau_rel` (`author/chapter_envelopes.tex`, lines 1021–1027): let `X` be a connected
compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form in a big class and `φ` a model
potential with positive mass (standing hypotheses of `subsec:fullmass`). For every
non-pluripolar measure `μ` with `μ(X) = ∫_X θ_φ^n` there is a unique `u ∈ E(X, θ; φ)` with
`θ_u^n = μ` and `sup_X u = 0`.

* Existence (`source_relative_calabiYau_exists`) is proved unconditionally, in every dimension
  (`RelativeCYExistence`; on a point the solution is `0`).
* Uniqueness (`source_relative_calabiYau_unique`, and up to constants without normalization,
  `source_relative_calabiYau_eq_add_const`) is proved from Dinew's lower bound for convex
  combinations against a common measure, the explicit hypothesis
  `SGPT.Envelopes.RelativeCY.CommonMeasureConvexLowerBound` (`RelativeCYDinew`), which is not yet
  available in the project. In dimension `0` no hypothesis is needed.

The book refers to Darvas–Di Nezza–Lu; the proofs follow Xia, *Foundations of pluripotential
theory*, `thm:nonpluripolar-relative-prescribed-measure-existence` and
`thm:relative-prescribed-measure-uniqueness`. Non-pluripolar measures are as in `thm:AY_rel`
(`SourceNonPluripolarMeasure`: Radon, and outer measure zero on pluripolar sets).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.RelativeMA SGPT.Envelopes.RelativeCY

theorem ereal_iSup_add_coe {X : Type*} (f : X → EReal) (C : ℝ) :
    (⨆ x, (f x + (C : EReal))) = (⨆ x, f x) + (C : EReal) := by
  have h1 : ∀ (g : X → EReal) (c : ℝ), (⨆ x, (g x + (c : EReal))) ≤ (⨆ x, g x) + (c : EReal) :=
    fun g c => iSup_le fun x => add_le_add (le_iSup g x) le_rfl
  refine le_antisymm (h1 f C) ?_
  have h2 := h1 (fun x => f x + (C : EReal)) (-C)
  rw [RelativePreceqClasses.translate_translate_neg f C] at h2
  calc (⨆ x, f x) + (C : EReal) ≤ (⨆ x, (f x + (C : EReal))) + ((-C : ℝ) : EReal) + (C : EReal) :=
        add_le_add h2 le_rfl
    _ = ⨆ x, (f x + (C : EReal)) := ereal_add_neg_add_cancel _ _

section Defs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The Monge–Ampère equation `θ_u^n = μ` for a source potential: `u` is `θ`-psh and its
non-pluripolar Monge–Ampère measure is `μ`. -/
def SourceSolvesMeasureEquation (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (μ : Measure M) (u : M → EReal) : Prop :=
  ∃ hu : (ofFixedModel n M).IsThetaPSH θ u, sourcePotentialNonPluripolarMeasure θ u hu = μ

end Defs

section DimZero

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)} {φ : M → EReal}

/-- Source `thm:Yau_rel`, existence, in dimension `0`: the solution is the constant `0`. -/
theorem source_relative_calabiYau_exists_dim_zero (hφ : SourceModelPotential θ φ) {μ : Measure M}
    (hmass : μ univ = sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ) :
    ∃ u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧
      (⨆ x, u x) = 0 := by
  have : Subsingleton M := SGPT.NPP.subsingleton_of_dim_zero
  obtain ⟨x₀⟩ := ModelRaySupremum.nonempty_of_modelPotential hφ.toNative
  let u : M → EReal := fun _ => ((0 : ℝ) : EReal)
  have hu : (ofFixedModel 0 M).IsThetaPSH θ u := SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0
  have hφfin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ φ).mp hφ.thetaPSH
  have hufin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ u).mp hu
  have hφ1 := SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ φ hφ.thetaPSH
  refine ⟨u, ⟨hu, (singularityEquiv_of_subsingleton hufin hφfin).1, ?_⟩, ⟨hu, ?_⟩, ?_⟩
  · rw [SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ u hu, hφ1]
  · rw [SGPT.NPP.sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero θ u hu x₀,
      measure_eq_smul_dirac_of_subsingleton μ x₀, hmass, hφ1, one_smul]
  · simp only [u, EReal.coe_zero, ciSup_const]

end DimZero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [BorelSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- **Source `thm:Yau_rel`, existence** (unconditional, every dimension). For a model potential
`φ` with positive mass in a big class and a non-pluripolar measure `μ` with
`μ(X) = ∫_X θ_φ^n`, there is `u ∈ E(X, θ; φ)` with `θ_u^n = μ` and `sup_X u = 0`. -/
theorem source_relative_calabiYau_exists (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {μ : Measure M} (hμ : SourceNonPluripolarMeasure (n := n) μ)
    (hmass : μ univ = sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ) :
    ∃ u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧
      (⨆ x, u x) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact source_relative_calabiYau_exists_dim_zero hφ hmass
  have := hμ.isFiniteMeasure
  obtain ⟨u, hu, hmeas, hsup, -⟩ := exists_relativeFullMass_measure_solution (hφ := hφ.toNative)
    ω hn hbig hμ.doesNotCharge hmass
  exact ⟨u, (sourceRelativeFullMass_iff_native θ φ u hφ).mpr hu,
    ⟨(isThetaPSH_iff_nativeThetaPotential θ u).mpr hu.1, hmeas⟩, hsup⟩

/-- **Uniqueness up to an additive constant** (conditional on Dinew's lower bound
`CommonMeasureConvexLowerBound`; Xia, *Foundations of pluripotential theory*,
`thm:relative-prescribed-measure-uniqueness`): two potentials of `E(X, θ; φ)` with the same
non-pluripolar Monge–Ampère measure differ by a real constant. -/
theorem source_relative_calabiYau_eq_add_const (ω : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) (hD : CommonMeasureConvexLowerBound n M) {u v : M → EReal}
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ)
    (heq : sourcePotentialNonPluripolarMeasure θ u hu.1 =
      sourcePotentialNonPluripolarMeasure θ v hv.1) :
    ∃ C : ℝ, u = fun x => v x + (C : EReal) :=
  eq_add_const_of_measure_eq hD ω hn hbig hφ.toNative
    ((sourceRelativeFullMass_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFullMass_iff_native θ φ v hφ).mp hv) heq

/-- **Source `thm:Yau_rel`, uniqueness** (conditional on `CommonMeasureConvexLowerBound`, which
is void in dimension `0`): two normalized solutions in `E(X, θ; φ)` coincide. -/
theorem source_relative_calabiYau_unique (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) (hD : CommonMeasureConvexLowerBound n M) {μ : Measure M}
    {u v : M → EReal}
    (hu : SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧ (⨆ x, u x) = 0)
    (hv : SourceRelativeFullMass θ φ v hφ ∧ SourceSolvesMeasureEquation θ μ v ∧ (⨆ x, v x) = 0) :
    u = v := by
  obtain ⟨huF, ⟨hu₁, hum⟩, hus⟩ := hu
  obtain ⟨hvF, ⟨hv₁, hvm⟩, hvs⟩ := hv
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton M := SGPT.NPP.subsingleton_of_dim_zero
    have hval : ∀ (w : M → EReal), (⨆ x, w x) = 0 → ∀ x, w x = 0 := fun w hw x =>
      le_antisymm (hw ▸ le_iSup w x)
        (hw ▸ iSup_le fun y => (Subsingleton.elim y x ▸ le_rfl : w y ≤ w x))
    funext x
    rw [hval u hus x, hval v hvs x]
  obtain ⟨C, hC⟩ := source_relative_calabiYau_eq_add_const ω hn hbig hφ hD huF hvF
    (hum.trans hvm.symm)
  have hC0 : (C : EReal) = 0 := by
    have h := congrArg (fun w : M → EReal => ⨆ x, w x) hC
    simp only [hus, ereal_iSup_add_coe, hvs, zero_add] at h
    exact h.symm
  rw [hC, hC0]
  funext x
  exact add_zero _

/-- **Source `thm:Yau_rel`** (relative Calabi–Yau theorem). Let `X` be a connected compact
Kähler manifold, `θ` represent a big class and `φ` be a model potential with positive mass.
For every non-pluripolar measure `μ` with `μ(X) = ∫_X θ_φ^n` there is a unique
`u ∈ E(X, θ; φ)` with `θ_u^n = μ` and `sup_X u = 0`. Existence is unconditional; uniqueness
uses Dinew's lower bound `CommonMeasureConvexLowerBound` as an explicit hypothesis. -/
theorem source_relative_calabiYau (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) (hD : CommonMeasureConvexLowerBound n M) {μ : Measure M}
    (hμ : SourceNonPluripolarMeasure (n := n) μ)
    (hmass : μ univ = sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ) :
    ∃! u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧
      (⨆ x, u x) = 0 := by
  obtain ⟨u, hu⟩ := source_relative_calabiYau_exists ω hbig hφ hμ hmass
  exact ⟨u, hu, fun v hv => source_relative_calabiYau_unique ω hbig hφ hD hv hu⟩

end SGPT.PSH.VariableComplexAtlas
