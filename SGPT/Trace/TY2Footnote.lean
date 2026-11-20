import SGPT.Trace.TY2Final
import SGPT.Unibranch.KS2KahlerFootnote
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

/-!
# The footnote of `def:traceop`: `d_{S, ω̃}` on the normalization

Source: `chapter_trace.tex`, footnote of `def:traceop`: "We can find a closed smooth real
`(1,1)`-form `θ` on `X` such that `φ ∈ PSH(X, θ)`. Then there is a Kähler form such that
`ω + θ + dd^c φ_j ≥ 0` for all `j ≥ 1`. Take a Kähler form `ω̃` on `Ỹ` so that
`ω̃ ≥ (θ + ω)|_Ỹ` and `ψ ∈ PSH(Ỹ, ω̃)`. Then our condition means that `φ_j|_Ỹ → ψ` in
`d_{S, ω̃}`. This condition is independent of the choices of `θ`, `ω` and `ω̃` by
`cor:dSconv_changetheta`."

`d_{S, ω̃}` on `Ỹ` is computed with the non-pluripolar products on `Ỹ`, i.e. on a resolution
`F : (V, 𝒪_V) → Ỹ` (`sec:unib_ext`), with the background `F^*ω̃` (`footnoteForm`). The condition of the
footnote, read on a resolution of `Ỹ` given by a proper bimeromorphic morphism `F`
(`FootnoteCondition`): `F^*ω̃` is big, the restrictions `φ_j|_Ỹ ∘ ν = φ_j ∘ ι` and `ψ ∘ ν` are
`F^*ω̃`-psh and `φ_j ∘ ι → ψ ∘ ν` in `d_{S, F^*ω̃}`.

* `KSManifoldForm.manifoldPullback_isSemipositive`, `manifoldPullback_le_of_dominates`: the
  manifold pull-back of a semipositive form, resp. of a domination `ω̃ ≥ θ'`, along a morphism
  `F : (V, 𝒪_V) → X` (the ambient local representatives are pulled back along the holomorphic
  lifts of `F`);
* `isTraceOn_iff_footnoteCondition`: for every choice of `θ` (`φ ∈ PSH(X, θ)`, a
  quasi-equisingular approximation `(φ_j)` of `φ`), of a Kähler form `ω` on `X` with
  `φ_j ∈ PSH(X, θ + ω)` for all `j`, and of a Kähler form `ω̃` on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ` and
  `ψ ∈ PSH(Ỹ, ω̃)`, the trace condition on the resolution holds iff the footnote's condition does
  (`F^*ω̃` is then big automatically);
* `footnoteCondition_congr`: hence the condition is independent of the choices of `θ`, `(φ_j)`, `ω`
  and `ω̃`;
* `isTrace_iff_footnoteCondition`: for `ψ` in some `PSH(Ỹ, θ'|_Ỹ)` (e.g. every trace operator
  produced by `def:traceop`, `Normalization.exists_isTrace`), `ψ` is a trace operator of `φ` along
  `Y` iff the footnote's condition holds; `IsTrace.footnoteCondition`: every trace operator
  satisfies the footnote's condition for all choices;
* `exists_footnote_choices`: the choices exist: a Kähler form `ω` with `φ_j ∈ PSH(X, θ + ω)` for all
  `j` (here `ω = (ε_0 + 1) ω'` for the approximation with errors `ε_j ω'`), and (lane KS2,
  `exists_kahler_footnote`) a Kähler `ω̃` on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ` and `ψ ∈ PSH(Ỹ, ω̃)` for any
  given quasi-psh `ψ` on `Ỹ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

/-! ### Pull-backs of positivity to manifolds -/

namespace SGPT.Unibranch.KSManifoldForm

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SourceReducedComplexSpace OriginalNativeModification

variable {X : SourceReducedComplexSpace} {m : ℕ} {V : Type} [TopologicalSpace V]
  [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]

/-- **The manifold pull-back on complex tangent lines.** Near every point of every chart of `V`,
for every local embedding `E` of `X` at the image point there are a point `p` of the ambient
space of `E` and a real-linear map `L` such that, for every form `θ` on `X` restricting to `v`
on `E`, `(F^*θ)(u, iu) = v_p(L u, i L u)`. -/
theorem exists_manifoldPullback_coeff_complexLine (F : wholeModel (n := m) V ⟶ X)
    (e : ComplexChart m V) {z : ComplexModel m} (hz : z ∈ e.val.target) {E : LocalEmbedding X}
    (hE : F.hom.left.base ⟨e.val.symm z, mem_univ _⟩ ∈ range E.toPoint) :
    ∃ p : ComplexModel E.dim, p ∈ E.ambient ∧ ∃ L : ComplexModel m →L[ℝ] ComplexModel E.dim,
      ∀ (θ : SpaceForm X 2) (v : AmbientForm E.dim 2), θ.RestrictsTo E v →
        ∀ u : ComplexModel m,
          (manifoldPullback θ F).coeff e z ![u, Complex.I • u] =
            v p ![L u, Complex.I • L u] := by
  obtain ⟨A, hA⟩ := SpaceForm.morphismChartLift_cover F E ⟨e.val.symm z, mem_univ _⟩ hE
  obtain ⟨W, hW, hzW, hWU, G, hG, hGmaps, hfac⟩ := exists_chartInverse_factor e A.source hz hA
  have hGd : DifferentiableAt ℂ G z :=
    (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hzW)
  have hLd : DifferentiableAt ℂ A.lift (G z) :=
    (A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.source.ambient.isOpen.mem_nhds (hGmaps hzW))
  refine ⟨A.lift (G z), A.maps (hGmaps hzW),
    (fderiv ℝ A.lift (G z)).comp (fderiv ℝ G z), fun θ v hres u => ?_⟩
  have h1 := SpaceForm.pullback_restrictsTo_of_lift θ F hres A.source A.holomorphic A.maps
    A.factor
  have h2 := toManifoldForm_coeff_eq_of_restrictsTo (SpaceForm.pullback θ F) e h1 hW hWU
    (hG.differentiableOn (by simp)) hfac hzW
  change (toManifoldForm (SpaceForm.pullback θ F)).coeff e z ![u, Complex.I • u] = _
  rw [h2, pullbackForm_apply_complexLine hGd, pullbackForm_apply_complexLine hLd]
  rfl

/-- The manifold pull-back of a semipositive form on a complex space is semipositive. -/
theorem manifoldPullback_isSemipositive {θ : SpaceForm X 2} (h : θ.IsSemipositive)
    (F : wholeModel (n := m) V ⟶ X) : (manifoldPullback θ F).IsSemipositive := by
  intro e z hz u
  obtain ⟨E, hE, v, -, hres, hpos⟩ := h (F.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨p, hp, L, hL⟩ := exists_manifoldPullback_coeff_complexLine F e hz hE
  rw [hL θ v hres u]
  exact hpos p hp (L u)

/-- **Domination pulls back**: if `ω ≥ θ` on the complex space `X` (`SpaceForm.Dominates`), then
`F^*θ ≤ F^*ω` on every complex tangent line of `V`. -/
theorem manifoldPullback_le_of_dominates {om θ : SpaceForm X 2} (h : om.Dominates θ)
    (F : wholeModel (n := m) V ⟶ X) (e : ComplexChart m V) {z : ComplexModel m}
    (hz : z ∈ e.val.target) (u : ComplexModel m) :
    (manifoldPullback θ F).coeff e z ![u, Complex.I • u] ≤
      (manifoldPullback om F).coeff e z ![u, Complex.I • u] := by
  obtain ⟨E, hE, v, w, -, -, resv, resw, hpt⟩ :=
    h (F.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨p, hp, L, hL⟩ := exists_manifoldPullback_coeff_complexLine F e hz hE
  rw [hL θ w resw u, hL om v resv u]
  exact (hpt p hp).2.2 (L u)

end SGPT.Unibranch.KSManifoldForm

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification

/-- A big class plus a semipositive form is big. -/
private theorem isBigClass_add_semipositive' {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] {θ η : ClosedRealOneOneForm k V}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hη : η.val.IsSemipositive) :
    IsBigClass (RealBottChern.ofRepresentative (θ + η)) := by
  obtain ⟨T⟩ := hbig
  refine ⟨{
    representative := T.representative + η
    represents := by
      rw [RealBottChern.ofRepresentative_add, T.represents, RealBottChern.ofRepresentative_add]
    potential := T.potential
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have hform : T.representative + η - T.lowerBound.form =
      (T.representative - T.lowerBound.form) + η := by abel
  rw [hform]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hη

private theorem isSemipositive_add {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] {a b : ClosedRealOneOneForm k V}
    (ha : a.val.IsSemipositive) (hb : b.val.IsSemipositive) : (a + b).val.IsSemipositive := by
  intro e z hz u
  simp only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
  exact add_nonneg (ha e z hz u) (hb e z hz u)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

namespace Normalization

variable (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)

/-- `ν^*ω̃ = F^*ω̃`: the reading on the resolution `F : (V, 𝒪_V) → Ỹ` of a Kähler form `ω̃` on `Ỹ`. -/
def footnoteForm {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler) :
    ClosedRealOneOneForm Y.dim N.R.V :=
  KSManifoldForm.manifoldPullbackClosed omt hK.isClosed hK.isOneOne F

/-- **The condition of the footnote of `def:traceop`**, read on the resolution
`F : (V, 𝒪_V) → Ỹ`: `φ_j|_Ỹ → ψ` in `d_{S, ω̃}`, i.e. `F^*ω̃` is big, `φ_j|_Ỹ ∘ ν = φ_j ∘ ι` and
`ψ ∘ ν` are `F^*ω̃`-psh, and `φ_j ∘ ι → ψ ∘ ν` in `d_{S, F^*ω̃}`. -/
def FootnoteCondition {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (φSeq : ℕ → X → EReal) (ψ : (normalizationTildeY omega Y).space.obj.left → EReal) : Prop :=
  ∃ (hbig : IsBigClass (RealBottChern.ofRepresentative (footnoteForm omega Y F hK)))
    (hterms : ∀ j, IsThetaPshPotential (footnoteForm omega Y F hK).val
      (fun v => φSeq j (N.R.ι v)))
    (hψ : IsThetaPshPotential (footnoteForm omega Y F hK).val (ψ ∘ N.ν)),
    Tendsto (fun j => (⟨fun v => φSeq j (N.R.ι v), hterms j⟩ :
        ThetaPshL1 (footnoteForm omega Y F hK).val))
      atTop (@nhds (ThetaPshL1 (footnoteForm omega Y F hK).val)
        (singularityPseudoMetricSpace N.R.kahler (footnoteForm omega Y F hK)
          hbig).toUniformSpace.toTopologicalSpace ⟨ψ ∘ N.ν, hψ⟩)

/-- **The footnote of `def:traceop`.** Let `F : (V, 𝒪_V) → Ỹ` be a resolution of the
normalization given by a proper bimeromorphic morphism, `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0`, `(φ_j)`
a quasi-equisingular approximation of `φ`, `ω` a Kähler form on `X` with `φ_j ∈ PSH(X, θ + ω)` for
all `j` ("`ω + θ + dd^c φ_j ≥ 0`"), and `ω̃` a Kähler form on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ` and
`ψ ∈ PSH(Ỹ, ω̃)`. Then `ψ ∘ ν` is a trace operator of `φ` on the resolution iff
`φ_j|_Ỹ → ψ` in `d_{S, ω̃}`. -/
theorem isTraceOn_iff_footnoteCondition {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} {omega' : KahlerBackground n X}
    {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    (om : KahlerBackground n X) (hom : ∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j))
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (hdom : omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)))
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ) :
    TildeY.IsTraceOn N φ (ψ ∘ N.ν) ↔ FootnoteCondition omega Y F hK φSeq ψ := by
  set σ := footnoteForm omega Y F hK with hσdef
  set κ := ClosedRealOneOneForm.pullback N.R.contMDiff (θ + om.form) with hκdef
  -- `F^*((θ + ω)|_Ỹ) = ι^*(θ + ω)`
  have hF' : ∀ y : N.R.V, ((KSNormalizedSubvariety.normalizationMap Y.carrier Y.analytic).hom.left.base
      (F.hom.left.base ⟨y, mem_univ y⟩)).val = N.R.ι y := by
    intro y
    rw [hFN y]
    exact N.toX_comp y
  have hgeo := KSNormalizedSubvariety.manifoldPullback_restrictForm Y.carrier Y.analytic
    (θ + om.form).val F N.R.contMDiff hF'
  -- `F^*ω̃ - ι^*(θ + ω) ≥ 0` and `F^*ω̃ ≥ 0`
  have hσκ : (σ - κ).val.IsSemipositive := by
    intro e z hz u
    have h1 := KSManifoldForm.manifoldPullback_le_of_dominates hdom F e hz u
    have h2 := hgeo e hz
    rw [sub_eq_add_neg]
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply]
    have h3 : κ.val.coeff e z = (KSManifoldForm.manifoldPullback
        ((normalizationTildeY omega Y).restrict (θ + om.form)) F).coeff e z := h2.symm
    rw [h3]
    change 0 ≤ (KSManifoldForm.manifoldPullback omt F).coeff e z ![u, Complex.I • u] +
      -(KSManifoldForm.manifoldPullback ((normalizationTildeY omega Y).restrict (θ + om.form))
        F).coeff e z ![u, Complex.I • u]
    linarith
  have hσ0 : σ.val.IsSemipositive :=
    KSManifoldForm.manifoldPullback_isSemipositive hK.isSemipositive F
  have hσeq : σ = κ + (σ - κ) := by abel
  -- `ψ ∘ ν` is `F^*ω̃`-psh (forward `cor:PSH`)
  have hψσ : IsThetaPshPotential σ.val (ψ ∘ N.ν) := by
    have h := KSUnibranchIEnvelope.isThetaPshPotential_pullback
      (KSNormalizedSubvariety.normalization_isUnibranch Y.carrier Y.analytic) hψ hF
    have hfun : (fun y => ψ (KSUnibranchIEnvelope.pt F y)) = ψ ∘ N.ν := by
      funext y
      exact congrArg ψ (hFN y)
    rw [hfun] at h
    exact h
  -- `κ`-psh restrictions are `F^*ω̃`-psh
  have hκσ : ∀ {w : N.R.V → EReal}, IsThetaPshPotential κ.val w → IsThetaPshPotential σ.val w := by
    intro w hw
    rw [hσeq]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hw hσκ
  -- an admissible Kähler background `β = F^*ω̃ + C ω_V`
  obtain ⟨C, hC, hadm0, -⟩ := AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
    N.R.contMDiff omega' N.R.kahler θ happ.2.1.2.1
  let βC : KahlerBackground Y.dim N.R.V := ⟨C • N.R.kahler.form, hadm0.1⟩
  let β : KahlerBackground Y.dim N.R.V := SGPT.Trace.RIsoB.kahlerAddSemipositive hσ0 βC
  have hβform : β.form = σ + βC.form := rfl
  have hadm : IsAdmissibleTraceBackground N.R.contMDiff omega' θ ε β.form := by
    refine ⟨β.isKahler, fun j => ?_⟩
    have hsplit : β.form - ClosedRealOneOneForm.pullback N.R.contMDiff (θ + ε j • omega'.form) =
        σ + (βC.form - ClosedRealOneOneForm.pullback N.R.contMDiff (θ + ε j • omega'.form)) := by
      rw [hβform]
      abel
    change (β.form - ClosedRealOneOneForm.pullback N.R.contMDiff (θ + ε j • omega'.form)).val.IsSemipositive
    rw [hsplit]
    exact isSemipositive_add hσ0 (hadm0.2 j)
  have hσβ : ∀ {w : N.R.V → EReal}, IsThetaPshPotential σ.val w → IsThetaPshPotential β.form.val w := by
    intro w hw
    rw [hβform]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hw βC.isSemipositive
  have hψβ : IsThetaPshPotential β.form.val (ψ ∘ N.ν) := hσβ hψσ
  constructor
  · -- trace ⟹ footnote
    intro hT
    have htrace := hT.retarget omega' N.R.kahler
    obtain ⟨hv, hlim, -⟩ := trace_independent_of_qea N.R htrace happ β hadm hψβ
    have hterms : ∀ j, IsThetaPshPotential σ.val (fun v => φSeq j (N.R.ι v)) := fun j =>
      hκσ ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp N.R.contMDiff (hom j).1, (hv j).2⟩
    -- `F^*ω̃` is big: it dominates `ι^*(θ + ω)`, which carries a positive-mass trace
    have hκbig : IsBigClass (RealBottChern.ofRepresentative κ) := by
      rcases Nat.eq_zero_or_pos Y.dim with h0 | hpos
      · exact NonBigPotentialMass.isBigClass_of_dim_zero h0 N.R.kahler _
      · obtain ⟨τ, -, hτ, hmass⟩ := SGPT.Trace.RIsoB.hasPositiveSourceTraceAlong_add_kahler N.R
          om om N.R.kahler happ.1 hν
        exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hpos N.R.kahler κ hτ
          hmass
    have hσbig : IsBigClass (RealBottChern.ofRepresentative σ) := by
      have h := isBigClass_add_semipositive' hκbig hσκ
      rwa [← hσeq] at h
    have hnative := SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
      N.R.kahler β.form σ (PluripolarCapacityDichotomy.isBigClass_kahler β) hσbig atTop
      hv hψβ hterms hψσ
    exact ⟨hσbig, hterms, hψσ, hnative.mp hlim⟩
  · -- footnote ⟹ trace
    rintro ⟨hσbig, hterms, hψσ', hlim⟩
    have hterms' : ∀ j, IsThetaPshPotential β.form.val (fun v => φSeq j (N.R.ι v)) :=
      fun j => hσβ (hterms j)
    have hnative := SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
      N.R.kahler σ β.form hσbig (PluripolarCapacityDichotomy.isBigClass_kahler β) atTop
      hterms hψσ' hterms' hψβ
    refine ⟨omega', N.R.kahler, ?_, θ, ε, φSeq, happ, β, hadm, hψβ, hterms', hnative.mp hlim⟩
    exact (sourceGenericLelongNumber_eq_sourceGenericLelong N.R.isResolutionOf.range_eq φ).trans hν

end Normalization

namespace Normalization

variable (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)

/-- `ψ ∈ PSH(Ỹ, ω̃)` gives `ψ ∘ ν ∈ PSH(V, F^*ω̃)` (forward `cor:PSH`). -/
theorem isThetaPshPotential_footnoteForm {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ) :
    IsThetaPshPotential (footnoteForm omega Y F hK).val (ψ ∘ N.ν) := by
  have h := KSUnibranchIEnvelope.isThetaPshPotential_pullback
    (KSNormalizedSubvariety.normalization_isUnibranch Y.carrier Y.analytic) hψ hF
  have hfun : (fun y => ψ (KSUnibranchIEnvelope.pt F y)) = ψ ∘ N.ν := by
    funext y
    exact congrArg ψ (hFN y)
  rw [hfun] at h
  exact h

/-- **The footnote's condition is independent of the choices of `θ`, `(φ_j)`, `ω` and `ω̃`.** -/
theorem footnoteCondition_congr {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {φ : X → EReal}
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    {θ₁ : ClosedRealOneOneForm n X} {omega₁ : KahlerBackground n X} {ε₁ : ℕ → ℝ}
    {φSeq₁ : ℕ → X → EReal} (happ₁ : IsQuasiEquisingularApproximation omega₁ θ₁ φ ε₁ φSeq₁)
    (om₁ : KahlerBackground n X) (hom₁ : ∀ j, IsThetaPshPotential (θ₁ + om₁.form).val (φSeq₁ j))
    {omt₁ : SpaceForm (normalizationTildeY omega Y).space 2} (hK₁ : omt₁.IsKahler)
    (hdom₁ : omt₁.Dominates ((normalizationTildeY omega Y).restrict (θ₁ + om₁.form)))
    (hψ₁ : (normalizationTildeY omega Y).space.IsThetaPSH omt₁ ψ)
    {θ₂ : ClosedRealOneOneForm n X} {omega₂ : KahlerBackground n X} {ε₂ : ℕ → ℝ}
    {φSeq₂ : ℕ → X → EReal} (happ₂ : IsQuasiEquisingularApproximation omega₂ θ₂ φ ε₂ φSeq₂)
    (om₂ : KahlerBackground n X) (hom₂ : ∀ j, IsThetaPshPotential (θ₂ + om₂.form).val (φSeq₂ j))
    {omt₂ : SpaceForm (normalizationTildeY omega Y).space 2} (hK₂ : omt₂.IsKahler)
    (hdom₂ : omt₂.Dominates ((normalizationTildeY omega Y).restrict (θ₂ + om₂.form)))
    (hψ₂ : (normalizationTildeY omega Y).space.IsThetaPSH omt₂ ψ) :
    FootnoteCondition omega Y F hK₁ φSeq₁ ψ ↔ FootnoteCondition omega Y F hK₂ φSeq₂ ψ :=
  (isTraceOn_iff_footnoteCondition omega Y F hF hFN happ₁ hν om₁ hom₁ hK₁ hdom₁ hψ₁).symm.trans
    (isTraceOn_iff_footnoteCondition omega Y F hF hFN happ₂ hν om₂ hom₂ hK₂ hdom₂ hψ₂)

/-- **The footnote's condition does not depend on the resolution** of `Ỹ` (among resolutions given
by proper bimeromorphic morphisms). -/
theorem footnoteCondition_resolution_congr {N₁ N₂ : (normalizationTildeY omega Y).Resolution}
    (F₁ : wholeModel (n := Y.dim) N₁.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF₁ : IsProperBimeromorphic F₁) (hFN₁ : ∀ v, F₁.hom.left.base ⟨v, mem_univ v⟩ = N₁.ν v)
    (F₂ : wholeModel (n := Y.dim) N₂.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF₂ : IsProperBimeromorphic F₂) (hFN₂ : ∀ v, F₂.hom.left.base ⟨v, mem_univ v⟩ = N₂.ν v)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} {omega' : KahlerBackground n X}
    {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    (om : KahlerBackground n X) (hom : ∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j))
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (hdom : omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)))
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ) :
    FootnoteCondition omega Y F₁ hK φSeq ψ ↔ FootnoteCondition omega Y F₂ hK φSeq ψ := by
  rw [← isTraceOn_iff_footnoteCondition omega Y F₁ hF₁ hFN₁ happ hν om hom hK hdom hψ,
    ← isTraceOn_iff_footnoteCondition omega Y F₂ hF₂ hFN₂ happ hν om hom hK hdom hψ]
  exact ⟨fun h => TildeY.transfer N₁ N₂ h
      (isThetaPshPotential_footnoteForm omega Y F₂ hF₂ hFN₂ hK hψ),
    fun h => TildeY.transfer N₂ N₁ h
      (isThetaPshPotential_footnoteForm omega Y F₁ hF₁ hFN₁ hK hψ)⟩

/-- **Every trace operator satisfies the footnote's condition**, for every choice of `θ`, `(φ_j)`,
`ω`, `ω̃` and every resolution of `Ỹ` given by a proper bimeromorphic morphism. -/
theorem IsTrace.footnoteCondition {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} {omega' : KahlerBackground n X}
    {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (om : KahlerBackground n X) (hom : ∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j))
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (hdom : omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)))
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ)
    (h : (normalizationTildeY omega Y).IsTrace φ ψ) :
    FootnoteCondition omega Y F hK φSeq ψ :=
  (isTraceOn_iff_footnoteCondition omega Y F hF hFN happ h.sourceGenericLelong_eq_zero om hom hK
    hdom hψ).mp (h.2 N)

/-- **`def:traceop` with the footnote**: for `ψ ∈ PSH(Ỹ, θ'|_Ỹ)` (`θ'` a closed real
`(1,1)`-form on `X`; e.g. every trace operator produced by `exists_isTrace`) and every choice of
`θ`, `(φ_j)`, `ω`, `ω̃` with `ψ ∈ PSH(Ỹ, ω̃)`, `ψ` is a trace operator of `φ` along `Y` iff
`φ_j|_Ỹ → ψ` in `d_{S, ω̃}`. -/
theorem isTrace_iff_footnoteCondition {N : (normalizationTildeY omega Y).Resolution}
    (F : wholeModel (n := Y.dim) N.R.V ⟶ (normalizationTildeY omega Y).space)
    (hF : IsProperBimeromorphic F) (hFN : ∀ v, F.hom.left.base ⟨v, mem_univ v⟩ = N.ν v)
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} {omega' : KahlerBackground n X}
    {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong φ Y.carrier = 0)
    (om : KahlerBackground n X) (hom : ∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j))
    {omt : SpaceForm (normalizationTildeY omega Y).space 2} (hK : omt.IsKahler)
    (hdom : omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)))
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH omt ψ)
    {θ' : ClosedRealOneOneForm n X}
    (hψ' : (normalizationTildeY omega Y).space.IsThetaPSH
      ((normalizationTildeY omega Y).restrict θ') ψ) :
    (normalizationTildeY omega Y).IsTrace φ ψ ↔ FootnoteCondition omega Y F hK φSeq ψ := by
  rw [Normalization.isTrace_iff_exists omega Y hψ',
    ← isTraceOn_iff_footnoteCondition omega Y F hF hFN happ hν om hom hK hdom hψ]
  exact ⟨fun ⟨N', h'⟩ => TildeY.transfer N' N h'
      (isThetaPshPotential_footnoteForm omega Y F hF hFN hK hψ), fun h => ⟨N, h⟩⟩

/-- **The choices of the footnote exist.** For a quasi-equisingular approximation `(φ_j)` of
`φ ∈ PSH(X, θ)` (with errors `ε_j ω'`) there is a Kähler form `ω` on `X` with `φ_j ∈ PSH(X, θ + ω)`
for all `j` (`ω + θ + dd^c φ_j ≥ 0`), and for every quasi-psh `ψ` on `Ỹ` (`ψ ∈ PSH(Ỹ, η)`) a Kähler
form `ω̃` on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ`, `PSH(Ỹ, (θ + ω)|_Ỹ) ⊆ PSH(Ỹ, ω̃)` and `ψ ∈ PSH(Ỹ, ω̃)`
. -/
theorem exists_footnote_choices {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    {omega' : KahlerBackground n X} {ε : ℕ → ℝ} {φSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega' θ φ ε φSeq)
    (η : SpaceForm (normalizationTildeY omega Y).space 2)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).space.IsThetaPSH η ψ) :
    ∃ om : KahlerBackground n X, (∀ j, IsThetaPshPotential (θ + om.form).val (φSeq j)) ∧
      ∃ omt : SpaceForm (normalizationTildeY omega Y).space 2, omt.IsKahler ∧
        omt.Dominates ((normalizationTildeY omega Y).restrict (θ + om.form)) ∧
        (∀ u, (normalizationTildeY omega Y).space.IsThetaPSH
          ((normalizationTildeY omega Y).restrict (θ + om.form)) u →
            (normalizationTildeY omega Y).space.IsThetaPSH omt u) ∧
        (normalizationTildeY omega Y).space.IsThetaPSH omt ψ := by
  have hε := happ.2.1
  have hc : (0 : ℝ) < ε 0 + 1 := by linarith [hε.1 0]
  refine ⟨KahlerBackground.smul hc omega', fun j => ?_, ?_⟩
  · have hsemi : ((ε 0 + 1 - ε j) • omega'.form).val.IsSemipositive := by
      intro e z hz u
      simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      have hj : ε j ≤ ε 0 := hε.2.1 (Nat.zero_le j)
      exact mul_nonneg (by linarith) (omega'.isSemipositive e z hz u)
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (happ.2.2.1 j) hsemi
    have hform : θ + ε j • omega'.form + (ε 0 + 1 - ε j) • omega'.form =
        θ + (KahlerBackground.smul hc omega').form := by
      change θ + ε j • omega'.form + (ε 0 + 1 - ε j) • omega'.form = θ + (ε 0 + 1) • omega'.form
      module
    rw [hform] at h
    exact h
  · exact SGPT.Unibranch.KS2NormalizationKahler.exists_kahler_footnote Y.carrier Y.analytic omega
      (θ + (KahlerBackground.smul hc omega').form) η hψ

end Normalization


end SGPT.Trace.TY
