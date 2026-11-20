import SGPT.Okounkov.DivisorMetricPullback
import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.BDivisor.Modification
import SGPT.Okounkov.TranscendentalCoreDivisorGenerators
import SGPT.Foundations.Analysis.Pending.MeteredDivisorScaling
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.ActualDivisorCurrentMetricIndependence
import SGPT.Foundations.Analysis.Pending.BlowupSequenceTotalTransform

/-!
# The Néron–Severi space of a model, as the image of the cycle class map

Lane DF-ALG, blueprint `claude-df-alg.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`):
"The algebraic nef b-divisors are introduced by Dang--Favre [DF20], as their intersection
theory. [...] our transcendental intersection theory coincides with theirs in the algebraic
setting."

Dang–Favre work with the real Néron–Severi spaces `N¹(Y)_ℝ` of the models `Y` of a projective
variety: real numerical classes of `ℝ`-divisors. Over `ℂ`, the cycle class map
`Div(Y)_ℝ → H^{1,1}(Y, ℝ)`, `D ↦ {[D]}`, sends `N¹(Y)_ℝ` onto the subspace of `H^{1,1}(Y, ℝ)`
spanned by the classes of divisors. Every divisor on a complex manifold is a difference of two
effective divisors, so this subspace is spanned by the cycle classes of **effective** divisors.
This file defines that subspace and the cycle class map on effective divisors.

* `SGPT.BDivisor.DFAlg.neronSeveri n Y` — the `ℝ`-span in `H^{1,1}_{BC}(Y, ℝ)` of the classes
  `{Θ_E}` of the curvature forms of the smooth metrics `E` on `𝒪(D)`, `D` an effective divisor of
  `Y`. By Lelong–Poincaré `[D] = Θ_E + ddᶜ ψ_E`, so `{Θ_E} = {[D]}` is the cycle class of `D`.
* `cycleClass D` (`Y` compact of positive dimension) — the Bott–Chern class of the integration
  current `[D]`; `cycleClass_eq_of_isDivisorMetric`: it is `{Θ_E}` for **every** smooth metric `E`
  on `𝒪(D)` (metric independence); `neronSeveri_eq_span_cycleClass`: the Néron–Severi space is
  the span of the cycle classes.
* `curvature_smul_mem_neronSeveri`: the classes of nonnegative rational multiples `c · E` of
  metered divisors (the `ℚ`-divisors of analytic singularities) lie in the Néron–Severi space.
* `classPullback_mem_neronSeveri`: pull-back along a holomorphic map whose exceptional locus has
  empty interior (in particular along modifications, `classPullbackOfLE_mem_neronSeveri`)
  preserves the Néron–Severi spaces: `g^*{[D]} = {[g^*D]}` (total transform).

Not formalized here: the identification of the numerical space `N¹(Y)_ℝ` with this image
(well-definedness and injectivity of the cycle class map on numerical classes: Lefschetz `(1,1)`
and the Hodge index theorem), and the compatibility of the cycle class map with push-forward of
divisors along modifications.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor.DFAlg

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending

section Definition

variable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The real Néron–Severi space** `NS(Y)_ℝ ⊆ H^{1,1}_{BC}(Y, ℝ)`: the image of the cycle class
map on real divisors, i.e. the `ℝ`-span of the curvature classes `{Θ_E} = {[D]}` of the smooth
metrics `E` on `𝒪(D)`, `D` an effective divisor of `Y`. -/
def neronSeveri : Submodule ℝ (RealBottChern n Y) :=
  Submodule.span ℝ {α | ∃ (D : EffectiveDivisor n Y) (E : MeteredEffectiveQDivisor n Y),
    DivisorMetric.IsDivisorMetric D E ∧ α = RealBottChern.ofRepresentative E.curvature}

end Definition

section Basic

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The curvature class of a smooth metric on `𝒪(D)` lies in the Néron–Severi space. -/
theorem curvature_mem_neronSeveri {D : EffectiveDivisor n Y} {E : MeteredEffectiveQDivisor n Y}
    (hE : DivisorMetric.IsDivisorMetric D E) :
    RealBottChern.ofRepresentative E.curvature ∈ neronSeveri n Y :=
  Submodule.subset_span ⟨D, E, hE, rfl⟩

/-- The curvature class of a nonnegative rational multiple `c · E` of a metric `E` on `𝒪(D)`
(the metered `ℚ`-divisor `c D`) lies in the Néron–Severi space. -/
theorem curvature_smul_mem_neronSeveri {D : EffectiveDivisor n Y}
    {E : MeteredEffectiveQDivisor n Y} (hE : DivisorMetric.IsDivisorMetric D E) {c : ℚ}
    (hc : 0 ≤ c) :
    RealBottChern.ofRepresentative (MeteredDivisorScaling.smul hc E).curvature ∈
      neronSeveri n Y := by
  rw [MeteredDivisorScaling.curvature_smul, RealBottChern.ofRepresentative_smul]
  exact Submodule.smul_mem _ _ (curvature_mem_neronSeveri hE)

end Basic

section Pullback

variable {n : ℕ} {M Z : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Pull-back preserves the Néron–Severi spaces.** For a holomorphic map `g : Z → M` whose
exceptional locus has empty interior, `g^*` maps `NS(M)_ℝ` into `NS(Z)_ℝ`: on generators,
`g^*{Θ_E}` is the curvature class of the pulled-back metric on `𝒪(g^*D)` (total transform). -/
theorem classPullback_mem_neronSeveri {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) {α : RealBottChern n M}
    (hα : α ∈ neronSeveri n M) : classPullback hg α ∈ neronSeveri n Z := by
  induction hα using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨D, E, hE, rfl⟩ := hx
      rw [classPullback_ofRepresentative]
      exact curvature_mem_neronSeveri
        (SGPT.Okounkov.isDivisorMetric_meteredPullback hg hint D E hE)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end Pullback

section Models

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The exceptional locus of a holomorphic map dominated by a modification has empty interior. -/
theorem interior_exceptionalLocus_homOfLE_eq_empty {π π' : Modification n X} (h : π ≤ π') :
    interior (exceptionalLocus n (Modification.homOfLE h)) = ∅ :=
  SGPT.Okounkov.TranscendentalCore.interior_exceptionalLocus_eq_empty_of_isAnalyticModification
    (Modification.Dominates.isAnalyticModification h)

/-- **Pull-back along a domination of models preserves the Néron–Severi spaces.** -/
theorem classPullbackOfLE_mem_neronSeveri {π π' : Modification n X} (h : π ≤ π')
    {α : RealBottChern n π.carrier} (hα : α ∈ neronSeveri n π.carrier) :
    Modification.classPullbackOfLE h α ∈ neronSeveri n π'.carrier :=
  classPullback_mem_neronSeveri (Modification.contMDiff_homOfLE h)
    (interior_exceptionalLocus_homOfLE_eq_empty h) hα

/-- Pull-back from the root `X` to a model preserves the Néron–Severi spaces. -/
theorem classPullback_map_mem_neronSeveri (π : Modification n X) {α : RealBottChern n X}
    (hα : α ∈ neronSeveri n X) :
    classPullback π.isAnalyticModification.1 α ∈ neronSeveri n π.carrier :=
  classPullback_mem_neronSeveri π.isAnalyticModification.1
    (SGPT.Okounkov.TranscendentalCore.interior_exceptionalLocus_eq_empty_of_isAnalyticModification
      π.isAnalyticModification) hα

end Models

section CycleClass

open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  NaturalThetaPshGeometricCurrent CanonicalCurrentFrame

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y]

/-- The integration current `[D] = Θ_E + ddᶜ ψ_E` of an effective divisor `D` of a compact
complex manifold, as a closed `(1,1)`-current (computed with a chosen smooth metric `E` on
`𝒪(D)`; it does not depend on the metric, `divisorCurrent_val_eq`). -/
def divisorCurrent (D : EffectiveDivisor (m + 1) Y) :
    ClosedOneOneCurrent (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
  thetaClosedCurrent (DivisorMetric.exists_divisorMetric D).choose.curvature
    (DivisorMetric.exists_divisorMetric D).choose.weight
    (SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric D _
      (DivisorMetric.exists_divisorMetric D).choose_spec.2)

/-- The integration current of `D` is `Θ_E + ddᶜ ψ_E` for **every** smooth metric `E` on `𝒪(D)`
(Lelong–Poincaré, with the metric independence of the integration current). -/
theorem divisorCurrent_val_eq (D : EffectiveDivisor (m + 1) Y)
    (E : MeteredEffectiveQDivisor (m + 1) Y) (hE : DivisorMetric.IsDivisorMetric D E) :
    (divisorCurrent D).val = thetaPotentialCurrent E.curvature.val E.weight
      (SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric D E hE) := by
  have h₀ := (DivisorMetric.exists_divisorMetric D).choose_spec.2
  change thetaPotentialCurrent _ _
    (SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric D _ h₀) = _
  rw [SGPT.Okounkov.thetaPotentialCurrent_effectiveDivisorMetric_eq D _ h₀,
    SGPT.Okounkov.thetaPotentialCurrent_effectiveDivisorMetric_eq D E hE]
  exact ActualDivisorCurrentMetricIndependence.integrationCurrent_eq_of_isDivisorMetric
    (canonicalBasis (m + 1)) D _ E h₀ hE

/-- **The cycle class** `cl(D) = {[D]} ∈ H^{1,1}_{BC}(Y, ℝ)` of an effective divisor: the
Bott–Chern class of its integration current. -/
def cycleClass (D : EffectiveDivisor (m + 1) Y) : RealBottChern (m + 1) Y :=
  bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (divisorCurrent D)

/-- **The cycle class is the first Chern class** `c₁(𝒪(D)) = {Θ_E}`, for every smooth metric `E`
on `𝒪(D)`. -/
theorem cycleClass_eq_of_isDivisorMetric (D : EffectiveDivisor (m + 1) Y)
    (E : MeteredEffectiveQDivisor (m + 1) Y) (hE : DivisorMetric.IsDivisorMetric D E) :
    cycleClass D = RealBottChern.ofRepresentative E.curvature := by
  have hu := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric D E hE
  have hc : divisorCurrent D = thetaClosedCurrent E.curvature E.weight hu :=
    Subtype.ext (divisorCurrent_val_eq D E hE)
  rw [cycleClass, hc, bottChernClass_thetaClosedCurrent]

/-- The curvature classes of two smooth metrics on `𝒪(D)` agree. -/
theorem ofRepresentative_curvature_eq_of_isDivisorMetric {D : EffectiveDivisor (m + 1) Y}
    {E E' : MeteredEffectiveQDivisor (m + 1) Y} (hE : DivisorMetric.IsDivisorMetric D E)
    (hE' : DivisorMetric.IsDivisorMetric D E') :
    RealBottChern.ofRepresentative E.curvature = RealBottChern.ofRepresentative E'.curvature := by
  rw [← cycleClass_eq_of_isDivisorMetric D E hE, cycleClass_eq_of_isDivisorMetric D E' hE']

theorem cycleClass_mem_neronSeveri (D : EffectiveDivisor (m + 1) Y) :
    cycleClass D ∈ neronSeveri (m + 1) Y := by
  obtain ⟨E, -, hE⟩ := DivisorMetric.exists_divisorMetric D
  rw [cycleClass_eq_of_isDivisorMetric D E hE]
  exact curvature_mem_neronSeveri hE

/-- **The Néron–Severi space is the span of the cycle classes of effective divisors.** -/
theorem neronSeveri_eq_span_cycleClass :
    neronSeveri (m + 1) Y = Submodule.span ℝ (range (cycleClass (Y := Y))) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro α ⟨D, E, hE, rfl⟩
    rw [← cycleClass_eq_of_isDivisorMetric D E hE]
    exact Submodule.subset_span ⟨D, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro α ⟨D, rfl⟩
    exact cycleClass_mem_neronSeveri D

end CycleClass

end SGPT.BDivisor.DFAlg
