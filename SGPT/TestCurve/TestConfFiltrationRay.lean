import SGPT.LineBundle.Misc2FiltrationObstacle
import SGPT.PSH.SourceMaximalGeodesicRays
import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourceTestCurveBackgroundProjection
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Okounkov.SchemeProjectiveTNKahler
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay

/-!
# The geodesic ray of a filtration is maximal (`rmk:max_filt`)

Source `rmk:max_filt` (chapter *Test curves*): *"We deduce from `ex:RWN` that the ray
`Γ^{𝓕*}` induced by a filtration `𝓕` is maximal."*

`ex:RWN` claims that for a filtration `𝓕` of `R(X, L)` (`L` big, `h` a smooth metric,
`θ = c₁(L, h)`) the family `Γ^𝓕_τ = P_θ[usc sup_k k⁻¹ Γ^{𝓕,k}_τ]`, `τ < τ(𝓕)`, is a bounded
`𝓘`-model test curve, `Γ^𝓕 ∈ 𝓔^{NA}(X, θ)`. The remark is the deduction: a ray is maximal
(`def:maximalgeoray`) exactly when its inverse Legendre transform is `𝓘`-model, and the
Ross–Witt Nyström correspondence (`thm:Legenbij`) inverts the Legendre transform.

The existing formalization of `ex:RWN` (`SGPT.LineBundle.SectionFiltration.testCurvePotential`
and the `Misc2` files) proves that `τ ↦ Γ^𝓕_τ` is a decreasing concave family of `θ`-psh
functions on `(-∞, τ(𝓕))`, but two clauses of `ex:RWN` are open there:

* (a) `RWNIModelClause`: each `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model;
* (b) `RWNMinimalClause` (`eq:Gammatautheta`): `Γ^𝓕_τ = V_θ` for `τ ≤ -C`.

This file proves `rmk:max_filt` conditionally on exactly these two clauses. It connects the
scheme-side family of `ex:RWN` (on the analytic space `X^{an}` of a smooth projective complex
variety) to the test-curve and geodesic-ray API of chapter *Test curves*
(`SGPT.PSH.VariableComplexAtlas.SourceTestCurve`, `sourceMaximalGeodesicRays`):

* `filtrationTestCurve`: the actual family `(Γ^𝓕_τ)_{τ < τ(𝓕)}` as a test curve
  (`def:testcur`) with `Γ_max = τ(𝓕)`; concavity and monotonicity come from the proved part of
  `ex:RWN`, the fixed-point clause `P_θ[Γ_τ] = Γ_τ` from (a) (an `𝓘`-model potential is
  `P`-model), the positive mass of `Γ_{-∞} = V_θ` from (b) and bigness;
* `filtrationTestCurve_mem_iModel`, `filtrationTestCurve_isBounded`: under (a), (b) the curve
  lies in `𝓔^{NA}(X, θ)` and is bounded (the conclusion of `ex:RWN`);
* **`filtrationRay_mem_maximal`** (`rmk:max_filt`): the Legendre transform
  `Γ^{𝓕*}_t = usc sup_τ (Γ^𝓕_τ + tτ)` is a maximal geodesic ray emanating from `V_θ`.

The slope `τ(𝓕)` is finite: clause (b) forces `H⁰(X, L^k) ≠ 0` for some `k > 0`
(`slope_ne_bot_of_minimalClause`).

## Standing hypotheses

As in `ex:RWN`: `X` is an integral smooth projective complex scheme (`E` a closed projective
embedding; `IsSeparated`, `QuasiCompact` and compactness of `X^{an}` follow from `E`), the
book's `X` is *connected* (hypothesis `ConnectedSpace` of the analytic space) and `L` is big
in the book's sense that `c₁(L) = {θ}` is a big class (hypothesis `IsBigClass`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TestConf

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.VariableComplexAtlas

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance testConfTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance testConfCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance testConfManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance testConfMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance testConfBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

section Main

variable [IsSeparated f] [QuasiCompact f]
variable {L : X.Modules} {a : LineBundleAtlas L}
variable (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)

/-- `θ = c₁(L, h)` on the original atlas of `X^{an}` (the dictionary
`nativeClosedFormToAtlas` keeps the same coefficients). -/
def curvatureAtlasForm : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f)) :=
  nativeClosedFormToAtlas (H.curvature a)

/-- The native form of `curvatureAtlasForm` is `c₁(L, h)` itself. -/
theorem curvatureAtlasForm_native :
    atlasClosedFormToNative (curvatureAtlasForm (a := a) H) = H.curvature a :=
  sourceNativeAtlasForm_roundTrip _

/-- Open clause (a) of `ex:RWN`: for every `τ < τ(𝓕)`, `Γ^𝓕_τ` is `𝓘`-model,
`Γ^𝓕_τ = P_θ[Γ^𝓕_τ]_𝓘`. -/
def RWNIModelClause : Prop :=
  ∀ τ : ℝ, (τ : EReal) < F.slope →
    IsIModelPotential (H.curvature a).val (F.testCurvePotential H τ)

/-- Open clause (b) of `ex:RWN`, `eq:Gammatautheta`: `Γ^𝓕_τ = V_θ` for every `τ ≤ -C`, where
`C` is the constant of the linear boundedness `eq:Flinearlybdd` of `𝓕`. -/
def RWNMinimalClause : Prop :=
  ∀ τ : ℝ, τ ≤ -(F.bound : ℝ) → F.testCurvePotential H τ = thetaPshSupremum (H.curvature a).val

/-! ### Degenerate filtrations -/

omit [IsSeparated f] [QuasiCompact f] in
/-- If `H⁰(X, L^k) = 0`, then `Γ^{𝓕,k}_τ ≡ -∞`. -/
theorem sectionPotential_eq_bot_of_subsingleton {k : ℕ}
    (hk : Subsingleton (SectionSpace f L k)) (τ : ℝ) :
    F.sectionPotential H k τ = fun _ => ⊥ := by
  have h : (fun x => ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x) =
      fun _ => (⊥ : EReal) := by
    funext x
    refine le_antisymm (iSup_le fun s => ?_) bot_le
    have h0 : s.1 = 0 := Subsingleton.elim _ _
    have hz := H.sectionLogNormSq_zero a k
    change H.sectionLogNormSq a k s.1 x ≤ ⊥
    rw [h0, show H.sectionLogNormSq a k (0 : bundlePowerGlobalSections L k) x = ⊥ from
      congrFun hz x]
  change uscRegularization (fun x =>
    ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x) = _
  rw [h, uscRegularization_const]

omit [IsSeparated f] [QuasiCompact f] in
/-- If `τ(𝓕) = -∞` (no nonzero section in positive degree), the obstacle is `-∞`. -/
theorem obstacle_eq_bot_of_slope_eq_bot (hs : F.slope = ⊥) (τ : ℝ) :
    F.obstacle H τ = fun _ => ⊥ := by
  have hsub : ∀ k : ℕ, 0 < k → Subsingleton (SectionSpace f L k) := by
    intro k hk
    by_contra hn
    have : Nontrivial (SectionSpace f L k) := not_subsingleton_iff_nontrivial.mp hn
    exact F.slope_ne_bot hk hs
  have hraw : F.rawObstacle H τ = fun _ => ⊥ := by
    funext x
    refine le_antisymm (iSup₂_le fun k hk => ?_) bot_le
    change F.sectionPotential H k τ x / ((k : ℝ) : EReal) ≤ ⊥
    rw [sectionPotential_eq_bot_of_subsingleton F H (hsub k hk) τ]
    exact (EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr (Nat.cast_pos.mpr hk))
      (EReal.coe_ne_top _)).le
  change uscRegularization (F.rawObstacle H τ) = _
  rw [hraw, uscRegularization_const]

/-- The `P`-envelope of the constant `-∞` is `-∞`: it has no competitor. -/
theorem singularityEnvelope_bot [Nonempty (SchemeComplexPoint f)]
    (θ : SmoothRealForm n (SchemeComplexPoint f) 2) :
    singularityEnvelope θ (fun _ => (⊥ : EReal)) = fun _ => ⊥ := by
  apply singularityEnvelope_of_empty
  refine Set.eq_empty_of_forall_notMem fun u hu => ?_
  obtain ⟨⟨hu, -⟩, C, hC⟩ := hu
  obtain ⟨x⟩ := (inferInstance : Nonempty (SchemeComplexPoint f))
  obtain ⟨y, -, hy⟩ := hu.2 x univ isOpen_univ (mem_univ x)
  exact hy (le_bot_iff.mp (by simpa using hC y (mem_univ y)))

/-- Clause (b) of `ex:RWN` forces `τ(𝓕) > -∞` when `{θ}` is big. -/
theorem slope_ne_bot_of_minimalClause [Nonempty (SchemeComplexPoint f)]
    [CompactSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hb : RWNMinimalClause F H) : F.slope ≠ ⊥ := by
  intro hs
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    (H.curvature a) hbig
  have h := hb (-(F.bound : ℝ)) le_rfl
  have hbot : F.testCurvePotential H (-(F.bound : ℝ)) = fun _ => ⊥ := by
    change singularityEnvelope (H.curvature a).val (F.obstacle H _) = _
    rw [obstacle_eq_bot_of_slope_eq_bot F H hs]
    exact singularityEnvelope_bot _
  rw [hbot] at h
  obtain ⟨x⟩ := (inferInstance : Nonempty (SchemeComplexPoint f))
  obtain ⟨y, -, hy⟩ := hV.2 x univ isOpen_univ (mem_univ x)
  exact hy (congrFun h y).symm

/-! ### The test curve of a filtration -/

variable [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
variable [IsIntegral X]

/-- The real number `τ(𝓕)` (finite under clause (b) and bigness). -/
def slopeReal : ℝ := F.slope.toReal

omit [IsIntegral X] in
/-- `τ < τ(𝓕)` in `ℝ` gives `τ < τ(𝓕)` in `[-∞, ∞]`. -/
theorem coe_lt_slope_of_lt {hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))}
    {hb : RWNMinimalClause F H} {τ : ℝ} (hτ : τ < slopeReal F) : (τ : EReal) < F.slope := by
  have hne := slope_ne_bot_of_minimalClause F H hbig hb
  rw [← EReal.coe_toReal F.slope_ne_top hne]
  exact EReal.coe_lt_coe_iff.mpr hτ

omit [IsIntegral X] in
/-- `τ(𝓕)` is the real number `slopeReal F`. -/
theorem coe_slopeReal (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hb : RWNMinimalClause F H) : ((slopeReal F : ℝ) : EReal) = F.slope :=
  EReal.coe_toReal F.slope_ne_top (slope_ne_bot_of_minimalClause F H hbig hb)

omit [IsIntegral X] in
set_option linter.unusedSectionVars false in
/-- Under clause (a), `Γ^𝓕_τ` is a `P`-model potential: `P_θ[Γ^𝓕_τ] = Γ^𝓕_τ`. -/
theorem singularityEnvelope_testCurvePotential (ha : RWNIModelClause F H) {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) :
    singularityEnvelope (H.curvature a).val (F.testCurvePotential H τ) =
      F.testCurvePotential H τ := by
  have hI := ha τ hτ
  have hpsh : IsThetaPshPotential (H.curvature a).val (F.testCurvePotential H τ) := hI.1
  conv_lhs => rw [hI.2]
  rw [singularityEnvelope_iSingularityEnvelope (H.curvature a).val (H.curvature a).property.1
    (H.curvature a).property.2 (LocalPotentials.closedRealOneOne_hasLocalPotentials _) _ hpsh]
  exact hI.2.symm

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- Chords of the family `τ ↦ Γ^𝓕_τ` in both orders. -/
theorem testCurvePotential_chord {p q τ₀ : ℝ} (hp : (p : EReal) < τ₀) (hq : (q : EReal) < τ₀)
    (hτ₀ : (τ₀ : EReal) ≤ F.slope) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t (F.testCurvePotential H p)
        (F.testCurvePotential H q) ≤ F.testCurvePotential H (t * p + (1 - t) * q) := by
  have hps : (p : EReal) < F.slope := hp.trans_le hτ₀
  have hqs : (q : EReal) < F.slope := hq.trans_le hτ₀
  rcases lt_trichotomy q p with hlt | heq | hgt
  · exact F.testCurvePotential_concave H hlt hps ht0 ht1
  · subst heq
    intro x
    rw [ThetaPshConvexCombination.convexComb_apply, show t * q + (1 - t) * q = q by ring]
    induction F.testCurvePotential H q x with
    | bot =>
      rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr ht0),
        EReal.mul_bot_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ht1))]
      exact bot_le
    | top =>
      rw [EReal.mul_top_of_pos (EReal.coe_pos.mpr ht0),
        EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ht1))]
      exact le_top
    | coe r =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by ring_nf; exact le_rfl)
  · have h := F.testCurvePotential_concave H hgt hqs (sub_pos.mpr ht1)
      (by linarith : 1 - t < 1)
    intro x
    have hx := h x
    rw [ThetaPshConvexCombination.convexComb_apply] at hx ⊢
    rw [show 1 - (1 - t) = t by ring] at hx
    rw [show t * p + (1 - t) * q = (1 - t) * q + t * p by ring, add_comm]
    exact hx

variable (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
  (ha : RWNIModelClause F H) (hb : RWNMinimalClause F H)

/-- The family `(Γ^𝓕_τ)_{τ < τ(𝓕)}` of `ex:RWN` as test-curve data (`def:testcur`, without the
mass clause). -/
def filtrationTestCurvePredata : SourceTestCurvePredata (curvatureAtlasForm (a := a) H) where
  max := slopeReal F
  potential τ := F.testCurvePotential H τ.1
  thetaPSH τ := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [curvatureAtlasForm_native]
    exact F.testCurvePotential_isThetaPshPotential H (coe_lt_slope_of_lt F H (hbig := hbig)
      (hb := hb) τ.2)
  antitone x := fun τ τ' h => F.testCurvePotential_anti H h x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords
    intro p q t ht0 ht1
    exact testCurvePotential_chord F H (EReal.coe_lt_coe_iff.mpr p.2)
      (EReal.coe_lt_coe_iff.mpr q.2) (coe_slopeReal F H hbig hb).le ht0 ht1
  fixedPoint τ := by
    rw [sourceSingularityEnvelope_eq_native, curvatureAtlasForm_native]
    exact singularityEnvelope_testCurvePotential F H ha
      (coe_lt_slope_of_lt F H (hbig := hbig) (hb := hb) τ.2)

@[simp] theorem filtrationTestCurvePredata_max :
    (filtrationTestCurvePredata F H hbig ha hb).max = slopeReal F := rfl

@[simp] theorem filtrationTestCurvePredata_potential (τ : Iio (slopeReal F)) :
    (filtrationTestCurvePredata F H hbig ha hb).potential τ = F.testCurvePotential H τ.1 := rfl

omit [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  [IsIntegral X] in
/-- `V_θ` of the original atlas is the native `V_θ` of `θ = c₁(L, h)`. -/
theorem sourceMinimalEnvelope_curvatureAtlasForm :
    sourceMinimalEnvelope (curvatureAtlasForm (a := a) H) =
      thetaPshSupremum (H.curvature a).val := by
  rw [sourceMinimalEnvelope_eq_native, curvatureAtlasForm_native]

/-- `Γ_{-∞} = usc sup_{τ < τ(𝓕)} Γ^𝓕_τ = V_θ`. -/
theorem filtrationTestCurvePredata_limit :
    sourceTestCurveLimit (filtrationTestCurvePredata F H hbig ha hb) =
      sourceMinimalEnvelope (curvatureAtlasForm (a := a) H) := by
  rw [sourceMinimalEnvelope_curvatureAtlasForm]
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    (H.curvature a) hbig
  let τ₀ : ℝ := min (slopeReal F - 1) (-(F.bound : ℝ))
  have hτ₀ : τ₀ < slopeReal F := (min_le_left _ _).trans_lt (by linarith)
  have hsup : (fun x => ⨆ τ : Iio (slopeReal F),
      (filtrationTestCurvePredata F H hbig ha hb).potential τ x) =
      thetaPshSupremum (H.curvature a).val := by
    funext x
    apply le_antisymm
    · refine iSup_le fun τ => ?_
      have hpsh := F.testCurvePotential_isThetaPshPotential H
        (coe_lt_slope_of_lt F H (hbig := hbig) (hb := hb) τ.2)
      exact le_thetaPshSupremum hpsh (singularityEnvelope_le_zero _ _) x
    · refine le_trans (le_of_eq ?_) (le_iSup (fun τ : Iio (slopeReal F) =>
        (filtrationTestCurvePredata F H hbig ha hb).potential τ x) ⟨τ₀, hτ₀⟩)
      rw [filtrationTestCurvePredata_potential, hb τ₀ (min_le_right _ _)]
  exact (congrArg uscRegularization hsup).trans
    (uscRegularization_eq hV.1.quasiPlurisubharmonic.upperSemicontinuous)

omit [IsIntegral X] in
/-- `V_θ` is a model potential of positive mass (bigness of `{θ}`). -/
theorem sourceMinimalEnvelope_curvatureAtlasForm_model
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    SourceModelPotential (curvatureAtlasForm (a := a) H)
      (sourceMinimalEnvelope (curvatureAtlasForm (a := a) H)) := by
  apply sourceMinimalEnvelope_model (schemeProjectiveTNKahlerBackground f n E)
  rw [curvatureAtlasForm_native]
  exact hbig

/-- **The test curve `Γ^𝓕` of `ex:RWN`** (conditional on the open clauses (a), (b)): the actual
family `(Γ^𝓕_τ)_{τ < τ(𝓕)}` with `Γ_max = τ(𝓕)`; the mass of `Γ_{-∞} = V_θ` is positive. -/
def filtrationTestCurve : SourceTestCurve (curvatureAtlasForm (a := a) H) where
  toSourceTestCurvePredata := filtrationTestCurvePredata F H hbig ha hb
  positiveLimitMass := by
    obtain ⟨hV, -, hmass⟩ := sourceMinimalEnvelope_curvatureAtlasForm_model H hbig
    have hlim := filtrationTestCurvePredata_limit F H hbig ha hb
    have key : ∀ (u : SchemeComplexPoint f → EReal)
        (hu : (ofFixedModel n (SchemeComplexPoint f)).IsThetaPSH
          (curvatureAtlasForm (a := a) H) u),
        u = sourceMinimalEnvelope (curvatureAtlasForm (a := a) H) →
        0 < sourcePotentialNonPluripolarMeasure (curvatureAtlasForm (a := a) H) u hu univ := by
      rintro u hu rfl
      exact hmass
    exact key _ _ hlim

@[simp] theorem filtrationTestCurve_max :
    (filtrationTestCurve F H hbig ha hb).max = slopeReal F := rfl

@[simp] theorem filtrationTestCurve_potential (τ : Iio (slopeReal F)) :
    (filtrationTestCurve F H hbig ha hb).potential τ = F.testCurvePotential H τ.1 := rfl

/-- `Γ_max = τ(𝓕)` in `[-∞, ∞]`. -/
theorem coe_filtrationTestCurve_max :
    (((filtrationTestCurve F H hbig ha hb).max : ℝ) : EReal) = F.slope :=
  coe_slopeReal F H hbig hb

/-- `Γ^𝓕 ∈ TC(X, θ; V_θ)`. -/
theorem filtrationTestCurve_mem_based :
    filtrationTestCurve F H hbig ha hb ∈ SourceTestCurvesBased (curvatureAtlasForm (a := a) H)
      (sourceMinimalEnvelope (curvatureAtlasForm (a := a) H))
      (sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) :=
  filtrationTestCurvePredata_limit F H hbig ha hb

/-- **Conclusion of `ex:RWN`** (from its clauses (a), (b)): `Γ^𝓕` is an `𝓘`-model test curve
based at `V_θ`, i.e. `Γ^𝓕 ∈ 𝓔^{NA}(X, θ)`. -/
theorem filtrationTestCurve_mem_iModel :
    filtrationTestCurve F H hbig ha hb ∈ SourceIModelTestCurves (curvatureAtlasForm (a := a) H)
      (sourceMinimalEnvelope (curvatureAtlasForm (a := a) H))
      (sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) := by
  refine ⟨filtrationTestCurve_mem_based F H hbig ha hb, fun τ => ?_⟩
  rw [curvatureAtlasForm_native]
  exact ha τ.1 (coe_lt_slope_of_lt F H (hbig := hbig) (hb := hb) τ.2)

/-- **Conclusion of `ex:RWN`** (from clause (b)): `Γ^𝓕` is bounded, `Γ^𝓕_τ = V_θ` for all
`τ` near `-∞`. -/
theorem filtrationTestCurve_isBounded :
    SourceTestCurveIsBounded (sourceMinimalEnvelope (curvatureAtlasForm (a := a) H))
      (filtrationTestCurve F H hbig ha hb) := by
  rw [sourceMinimalEnvelope_curvatureAtlasForm]
  have hne : Nonempty (Iio (filtrationTestCurve F H hbig ha hb).max) :=
    ⟨⟨slopeReal F - 1, by change slopeReal F - 1 < slopeReal F; linarith⟩⟩
  rw [SourceTestCurveIsBounded, Filter.eventually_atBot]
  refine ⟨⟨min (slopeReal F - 1) (-(F.bound : ℝ)),
    (min_le_left _ _).trans_lt (by change slopeReal F - 1 < slopeReal F; linarith)⟩,
    fun τ hτ => ?_⟩
  exact hb τ.1 (le_trans (Subtype.coe_le_coe.mpr hτ) (min_le_right _ _))

/-- **Source `rmk:max_filt`** (conditional on the open clauses (a), (b) of `ex:RWN`): the ray
`Γ^{𝓕*}` induced by the filtration `𝓕` — the Legendre transform of the actual family
`(Γ^𝓕_τ)_{τ < τ(𝓕)}` — is a maximal geodesic ray emanating from `V_θ`, for every Kähler
background `ω` of `X^{an}`. -/
theorem filtrationRay_mem_maximal (omega : KahlerBackground n (SchemeComplexPoint f)) :
    sourceTestCurveLegendreRay (filtrationTestCurvePredata F H hbig ha hb) ∈
      sourceMaximalGeodesicRays omega (curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (curvatureAtlasForm (a := a) H))
        (sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) := by
  have hbased := filtrationTestCurve_mem_based F H hbig ha hb
  refine ⟨(source_test_curve_legendre_geodesic_whole omega _ hbased).1, ?_⟩
  exact (sourceTestCurveLegendreRay_isMaximal_iff omega _ hbased).mpr
    (filtrationTestCurve_mem_iModel F H hbig ha hb).2

end Main

section Projective

variable {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]
  [ConnectedSpace (SchemeComplexPoint f)]

/-- **Source `rmk:max_filt`**, with the separatedness, quasi-compactness and compactness of
`X^{an}` supplied by the projective embedding `E` (no hypothesis beyond the book's standing
ones — `X` connected, `{c₁(L, h)}` big — and the open clauses (a), (b) of `ex:RWN`). -/
theorem filtrationRay_mem_maximal_of_projective (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
      (ha : RWNIModelClause F H) (hb : RWNMinimalClause F H)
      (omega : KahlerBackground n (SchemeComplexPoint f)),
      sourceTestCurveLegendreRay (filtrationTestCurvePredata F H hbig ha hb) ∈
        sourceMaximalGeodesicRays omega (curvatureAtlasForm (a := a) H)
          (sourceMinimalEnvelope (curvatureAtlasForm (a := a) H))
          (sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro hbig ha hb omega
  exact filtrationRay_mem_maximal F H hbig ha hb omega

end Projective

end SGPT.TestCurve.TestConf
