import SGPT.Trace.Trace2Resolution
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Foundations.Analysis.Pending.SmoothDDCHessianPositivity
import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
import Mathlib.MeasureTheory.Function.Jacobian
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

/-!
# A resolution of `Y` sees the restricted Kähler form with positive volume

Source: `chapter_trace.tex`, the observations after `def:traceop2` and `ex:tracedefinedposmass`
for a singular `Y`. On the normalization `Ỹ` of `Y` the restriction `ω|_Ỹ` of a Kähler form is
Kähler; on a resolution `ι : Y' → Y` (`Trace2Resolution.ResolutionTarget`) the pullback `ι^*ω` is
only semipositive. What the trace theory on `Y'` needs instead is that `ι^*ω` is *big*, i.e.
`∫_{Y'} (ι^*ω)^{dim Y} > 0`. This file proves it for every resolution target.

* `diagonalPotentialMass_zero_pos_of_isStrictlyPositive_at`: a semipositive closed `(1,1)`-form
  on a compact complex manifold that is strictly positive at one point has positive volume
  (`∫ κ^k > 0`; same proof as `KahlerVolumePositive.diagonalPotentialMass_zero_pos`, with the
  density positive near the point by continuity).
* `isStrictlyPositive_pullback_coeff`: the pullback of a Kähler form along a holomorphic map is
  strictly positive at every point where the differential is injective.
* `exists_injective_fderiv` (**a resolution is generically an immersion**): for every resolution
  target `(Y', ι)` of an irreducible `Y`, `ι` has an injective differential somewhere. Proof
  (Sard): near a point `y₀ ∈ Y \ B` (`B ⊇ Y_sing` the analytic set of `IsResolutionOf`), `Y` is
  flattened to `ℂ^k × {0}` and `ι⁻¹(N)` (`N` the flattening neighbourhood minus `B`) maps onto a
  non-empty open subset of `ℂ^k`; if every differential were singular, Sard's lemma (in equal
  dimension, `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) on finitely many
  charts would make this image Lebesgue-null.
* `diagonalPotentialMass_pullback_kahler_pos`: `∫_{Y'} (ι^*ω)^{dim Y} > 0`, and
  `isBigClass_pullback_kahler`: `{ι^*ω}` is big (Boucksom).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ENNReal ContDiff ComplexOrder

universe u

namespace SGPT.Trace.RIsoB

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.Pending

/-! ### Positive volume from strict positivity at one point -/

section Volume

open FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] [CompactSpace V]

/-- A semipositive closed real `(1,1)`-form which is strictly positive at one point (in some
chart) has positive volume `∫ κ^k > 0`. -/
theorem diagonalPotentialMass_zero_pos_of_isStrictlyPositive_at
    {κ : ClosedRealOneOneForm k V} (hκ : κ.val.IsSemipositive)
    (e : ComplexChart k V) {z0 : ComplexModel k} (hz0 : z0 ∈ e.val.target)
    (hpos : IsStrictlyPositive (κ.val.coeff e z0)) :
    0 < diagonalPotentialMass κ (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff κ).mpr hκ) := by
  classical
  have h0 := (LocalPotentials.isThetaPshPotential_zero_iff κ).mpr hκ
  obtain ⟨W0, ρ, hzW0, hρ, hpsh⟩ := h0.1 e z0 hz0
  set D : TopologicalSpace.Opens (ComplexModel k) :=
    ⟨e.val.target ∩ W0, e.val.open_target.inter hρ.1⟩ with hD
  have hDV : (D : Set (ComplexModel k)) ⊆ W0 := inter_subset_right
  have hzD : z0 ∈ D := ⟨hz0, hzW0⟩
  let Q : Patch (fun _ : Fin k => κ) (fun _ => (fun _ : V => (0 : EReal))) :=
    { chart := e
      domain := D
      domain_le_target := inter_subset_left
      potential := fun _ => ρ
      localPotential := fun _ => hρ.mono D.isOpen hDV
      plurisubharmonic := fun _ => hpsh.mono hDV }
  have hcorr : ∀ i y, Q.corrected i y = ((ρ y : ℝ) : EReal) := fun i y => by
    simp [Patch.corrected, Q, chartFunction]
  have hρD : ContDiffOn ℝ ∞ ρ D := hρ.2.2.1.mono hDV
  have hρ2 : ∀ y ∈ D, ContDiffAt ℝ 2 ρ y := fun y hy =>
    ((hρD y hy).contDiffAt (D.isOpen.mem_nhds hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcH : ContinuousOn (fun z => complexHessian ρ z) D :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun l =>
      BedfordTaylor.IsSmoothPsdOn.continuousOn_complexHessian hρD j l
  have hdensc : ContinuousOn (fun z => smoothDensity ρ z) D :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn hcH))
  have hdz0 : 0 < smoothDensity ρ z0 :=
    KahlerVolumePositive.smoothDensity_pos_of_isStrictlyPositive (hρ2 z0 hzD)
      (by rw [hρ.2.2.2 (hDV hzD)]; exact hpos)
  have hρcont : ContinuousAt ρ z0 := hρD.continuousOn.continuousAt (D.isOpen.mem_nhds hzD)
  have hnhds : ((D : Set (ComplexModel k)) ∩ {y | ρ z0 - 1 < ρ y}) ∩
      {y | 0 < smoothDensity ρ y} ∈ 𝓝 z0 :=
    Filter.inter_mem (Filter.inter_mem (D.isOpen.mem_nhds hzD)
      (hρcont.eventually (lt_mem_nhds (by linarith : ρ z0 - 1 < ρ z0))))
      ((hdensc.continuousAt (D.isOpen.mem_nhds hzD)).eventually (lt_mem_nhds hdz0))
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  set W : TopologicalSpace.Opens (ComplexModel k) := ⟨ball z0 r, isOpen_ball⟩ with hW
  have hWD : W ≤ Q.domain := fun y hy => (hball (ball_subset_closedBall hy)).1.1
  have hWrel : RelativelyCompactIn W Q.domain := by
    refine ⟨(isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
      (closure_ball_subset_closedBall), fun y hy => ?_⟩
    exact (hball (closure_ball_subset_closedBall hy)).1.1
  obtain ⟨m, hm⟩ := exists_nat_gt (1 - ρ z0)
  have hWk : (W : Set (ComplexModel k)) ⊆ commonStrictLocus Q.domain Q.corrected m := by
    intro y hy
    refine ⟨hWD hy, fun i => ?_⟩
    rw [hcorr]
    have h1 : ρ z0 - 1 < ρ y := (hball (ball_subset_closedBall hy)).1.2
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hρW : ContDiffOn ℝ ∞ ρ W := hρD.mono fun y hy => hWD hy
  have hf : IsSmoothPshOn W ρ := by
    refine ⟨hρW, ?_, fun y hy => ?_⟩
    · have := hpsh.mono fun y hy => hDV (hWD hy)
      simpa [chartFunction] using this
    · have hyD := hWD hy
      exact SmoothDDCHessianPositivity.complexHessian_posSemidef_of_coefficientSemipositive
        (hρ2 y hyD) (by rw [hρ.2.2.2 (hDV hyD)]; exact fun v => hκ e y hyD.1 v)
  have hcorrected : ∀ i, EqOn (fun z => (Q.corrected i z).toReal) ρ W := fun i y _ => by
    simp only [hcorr, EReal.toReal_coe]
  have heq :=
    FullSpacePatchMeasure.globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal
      h0.1 Q W hWD m hWrel hWk hf hcorrected (subset_refl _)
  have hdens : ContinuousOn (fun z => ENNReal.ofReal (smoothDensity ρ z)) W :=
    ENNReal.continuous_ofReal.comp_continuousOn (hdensc.mono fun y hy => hWD hy)
  have hpos' : 0 < smoothMeasure W ρ hf W := by
    rw [smoothMeasure, pos_iff_ne_zero, Ne,
      withDensity_apply_eq_zero' (hdens.aemeasurable W.isOpen.measurableSet)]
    rw [Measure.restrict_apply' W.isOpen.measurableSet]
    have hsub : (W : Set (ComplexModel k)) ⊆
        {y | ENNReal.ofReal (smoothDensity ρ y) ≠ 0} ∩ W ∩ W := fun y hy =>
      ⟨⟨by simpa using (hball (ball_subset_closedBall hy)).2, hy⟩, hy⟩
    intro h0'
    have : volume (W : Set (ComplexModel k)) = 0 := measure_mono_null hsub h0'
    exact (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hr)) this
  calc (0 : ℝ≥0∞) < smoothMeasure W ρ hf W := hpos'
    _ = globalMixedMeasure (fun _ : Fin k => κ) (fun _ => fun _ : V => (0 : EReal))
          (fun _ => h0.1) (Q.chart.val.symm '' W) := heq.symm
    _ ≤ globalMixedMeasure (fun _ : Fin k => κ) (fun _ => fun _ : V => (0 : EReal))
          (fun _ => h0.1) univ := measure_mono (subset_univ _)
    _ = diagonalPotentialMass κ (fun _ => 0) h0 := rfl

end Volume

/-! ### Strict positivity of a pulled-back Kähler form at an immersive point -/

section Pullback

variable {n k : ℕ} {X V : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V]

/-- The pullback of a Kähler form along a holomorphic map is strictly positive at every point
where (a coordinate representative of) the map has an injective differential. -/
theorem isStrictlyPositive_pullback_coeff {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (omega : KahlerBackground n X) (e : ComplexChart k V) (d : ComplexChart n X)
    {z : ComplexModel k} (hzd : z ∈ coordinateDomain ι e d)
    (hinj : Function.Injective (fderiv ℝ (coordinateMap ι e d) z)) :
    IsStrictlyPositive ((ClosedRealOneOneForm.pullback hι omega.form).val.coeff e z) := by
  set D := fderiv ℝ (coordinateMap ι e d) z with hD
  have hDI : ∀ v, D (Complex.I • v) = Complex.I • D v := fun v =>
    coordinateMap_fderiv_map_smul_complex hι e d hzd Complex.I v
  have hvec : ∀ a b : ComplexModel k, (⇑D ∘ ![a, b]) = ![D a, D b] := by
    intro a b
    funext i
    fin_cases i <;> rfl
  have hpos := (omega.isKahler.1 d _ (coordinateMap_mem_target hzd)).2
  rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hι _ e d hzd]
  intro a ha
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← hD]
  rw [hvec, hDI]
  refine hpos (D a) ?_
  intro h0
  exact ha (hinj (h0.trans (map_zero D).symm))

end Pullback

/-! ### A resolution is generically an immersion -/

section Immersion

open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Trace.Trace2Resolution

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- **A resolution is generically an immersion.** For every resolution target `(Y', ι)` of an
irreducible analytic subset `Y`, some coordinate representative of `ι` has an injective
differential. (Sard's lemma in equal dimension, near a regular point of `Y` outside the
analytic set `B` of `IsResolutionOf`.) -/
theorem exists_injective_fderiv (R : ResolutionTarget Y) :
    ∃ (e : ComplexChart Y.dim R.V) (d : ComplexChart n X) (z : ComplexModel Y.dim),
      z ∈ coordinateDomain R.ι e d ∧
        Function.Injective (fderiv ℝ (coordinateMap R.ι e d) z) := by
  classical
  obtain ⟨B, hBan, hsing, -, hdense⟩ := R.isResolutionOf.exists_isoLocus
  obtain ⟨v0, hv0⟩ := hdense.nonempty
  have hy0Y : R.ι v0 ∈ Y.carrier := by
    rw [← R.isResolutionOf.range_eq]
    exact mem_range_self v0
  have hreg : RegularAtDim (n := n) Y.carrier (R.ι v0) Y.dim := by
    by_contra h
    exact hv0 (hsing ⟨hy0Y, h⟩)
  obtain ⟨hk, -, Φ, -, hΦ0, hflat⟩ := hreg
  let d := complexChartAt (n := n) (R.ι v0)
  set N : Set X := (d.val.source ∩ d.val ⁻¹' Φ.source) ∩ Bᶜ with hN
  have hNopen : IsOpen N :=
    (d.val.isOpen_inter_preimage Φ.isOpen_source).inter hBan.isClosed.isOpen_compl
  have hy0N : R.ι v0 ∈ N :=
    ⟨⟨mem_complexChartAt_source _, Φ.center_mem_source⟩, hv0⟩
  -- the flattened image `T ⊆ ℂ^k` of `Y ∩ N`, a non-empty open set
  set Ψ := Φ.toOpenPartialHomeomorph with hΨ
  have hdN : d.val '' N ⊆ Ψ.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.1.2
  have hOopen : IsOpen (Ψ '' (d.val '' N)) :=
    Ψ.isOpen_image_of_subset_source
      (d.val.isOpen_image_of_subset_source hNopen fun y hy => hy.1.1) hdN
  set T : Set (ComplexModel Y.dim) :=
    coordinateInclusion n Y.dim ⁻¹' (Ψ '' (d.val '' N)) with hT
  have hTopen : IsOpen T := hOopen.preimage (coordinateInclusion n Y.dim).continuous
  have hT0 : (0 : ComplexModel Y.dim) ∈ T := by
    show coordinateInclusion n Y.dim 0 ∈ Ψ '' (d.val '' N)
    rw [map_zero]
    exact ⟨d.val (R.ι v0), ⟨R.ι v0, hy0N, rfl⟩, hΦ0⟩
  -- every point of `T` is the flattened image of a point `ι v` with `v ∈ ι⁻¹ N`
  set G : R.V → ComplexModel Y.dim :=
    fun v => coordinateProjection n Y.dim (Φ.toFun (d.val (R.ι v))) with hG
  have hTG : T ⊆ G '' (R.ι ⁻¹' N) := by
    rintro w ⟨_, ⟨y, hyN, rfl⟩, hyw⟩
    have hyw' : Φ.toFun (d.val y) = coordinateInclusion n Y.dim w := hyw
    have hyY : y ∈ Y.carrier := (hflat hyN.1.1 hyN.1.2).mpr
      (hyw' ▸ coordinateInclusion_mem_complexCoordinatePlane w)
    rw [← R.isResolutionOf.range_eq] at hyY
    obtain ⟨v, rfl⟩ := hyY
    exact ⟨v, hyN, by simp only [hG, hyw', coordinateProjection_coordinateInclusion hk]⟩
  -- finitely many charts of `Y'`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun v : R.V => (complexChartAt (n := Y.dim) v).val.source)
    (fun v => (complexChartAt (n := Y.dim) v).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  by_contra hne
  simp only [not_exists, not_and] at hne
  let S : R.V → Set (ComplexModel Y.dim) := fun v =>
    (complexChartAt (n := Y.dim) v).val.target ∩
      (complexChartAt (n := Y.dim) v).val.symm ⁻¹' (R.ι ⁻¹' N)
  let g : R.V → ComplexModel Y.dim → ComplexModel Y.dim := fun v z =>
    coordinateProjection n Y.dim
      (Φ.toFun (coordinateMap R.ι (complexChartAt (n := Y.dim) v) d z))
  have hSdom : ∀ v, S v ⊆ coordinateDomain R.ι (complexChartAt (n := Y.dim) v) d :=
    fun v z hz => ⟨hz.1, hz.2.1.1⟩
  -- on each chart the coordinate expression of `G` has singular differential: null image
  have hnull : ∀ v, volume (g v '' S v) = 0 := by
    intro v
    set e := complexChartAt (n := Y.dim) v with he
    have hd1 : ∀ z ∈ S v, DifferentiableAt ℝ (coordinateMap R.ι e d) z := fun z hz =>
      (coordinateMap_contDiffAt_real R.contMDiff e d (hSdom v hz)).differentiableAt (by simp)
    have hd2 : ∀ z ∈ S v, DifferentiableAt ℝ Φ.toFun (coordinateMap R.ι e d z) := fun z hz =>
      (Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds hz.2.1.2)).restrictScalars ℝ
    have hd3 : ∀ z ∈ S v, DifferentiableAt ℝ (g v) z := fun z hz =>
      ((coordinateProjection n Y.dim).restrictScalars ℝ).differentiableAt.comp z
        ((hd2 z hz).comp z (hd1 z hz))
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun z => fderiv ℝ (g v) z)
      (fun z hz => (hd3 z hz).hasFDerivAt.hasFDerivWithinAt) ?_
    intro z hz
    by_contra hdet
    apply hne e d z (hSdom v hz)
    have hu : IsUnit ((fderiv ℝ (g v) z : ComplexModel Y.dim →L[ℝ] ComplexModel Y.dim) :
        ComplexModel Y.dim →ₗ[ℝ] ComplexModel Y.dim) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hginj : Function.Injective (fderiv ℝ (g v) z) :=
      ((Module.End.isUnit_iff _).mp hu).1
    have hchain : fderiv ℝ (g v) z =
        (((coordinateProjection n Y.dim).restrictScalars ℝ).comp
          (fderiv ℝ Φ.toFun (coordinateMap R.ι e d z))).comp
          (fderiv ℝ (coordinateMap R.ι e d) z) := by
      have h := fderiv_comp z ((coordinateProjection n Y.dim).restrictScalars ℝ).differentiableAt
        ((hd2 z hz).comp z (hd1 z hz))
      rw [show g v = ((coordinateProjection n Y.dim).restrictScalars ℝ) ∘
          (Φ.toFun ∘ coordinateMap R.ι e d) from rfl, h, fderiv_comp z (hd2 z hz) (hd1 z hz),
        ContinuousLinearMap.fderiv]
      rfl
    intro a b hab
    apply hginj
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, hab]
  have hcover : G '' (R.ι ⁻¹' N) ⊆ ⋃ v ∈ t, g v '' S v := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨v, hv, hpv⟩ := mem_iUnion₂.mp (ht (mem_univ p))
    refine mem_iUnion₂.mpr ⟨v, hv, (complexChartAt (n := Y.dim) v).val p,
      ⟨(complexChartAt (n := Y.dim) v).val.map_source hpv, ?_⟩, ?_⟩
    · show R.ι ((complexChartAt (n := Y.dim) v).val.symm
        ((complexChartAt (n := Y.dim) v).val p)) ∈ N
      rw [(complexChartAt (n := Y.dim) v).val.left_inv hpv]
      exact hp
    · show coordinateProjection n Y.dim (Φ.toFun (d.val (R.ι
        ((complexChartAt (n := Y.dim) v).val.symm ((complexChartAt (n := Y.dim) v).val p))))) = _
      rw [(complexChartAt (n := Y.dim) v).val.left_inv hpv]
  have hTnull : volume T = 0 := by
    apply measure_mono_null (hTG.trans hcover)
    refine le_antisymm ((measure_biUnion_finset_le t _).trans ?_) bot_le
    simp only [hnull, Finset.sum_const_zero, le_refl]
  exact (hTopen.measure_ne_zero volume ⟨0, hT0⟩) hTnull

end Immersion

/-! ### The restricted Kähler form on a resolution is big -/

section Big

open SGPT.Trace.Trace2Resolution SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- The pullback `ι^*ω` of a Kähler form to a resolution target is semipositive. -/
theorem pullback_kahler_isSemipositive (R : ResolutionTarget Y) (omega : KahlerBackground n X) :
    (ClosedRealOneOneForm.pullback R.contMDiff omega.form).val.IsSemipositive :=
  ClosedRealOneOneForm.pullback_isSemipositive R.contMDiff omega.isSemipositive

/-- **`∫_{Y'} (ι^*ω)^{dim Y} > 0`** for every resolution target `(Y', ι)` of `Y` and every
Kähler form `ω`: the restricted Kähler form has positive volume on every resolution. -/
theorem diagonalPotentialMass_pullback_kahler_pos (R : ResolutionTarget Y)
    (omega : KahlerBackground n X) :
    0 < diagonalPotentialMass (ClosedRealOneOneForm.pullback R.contMDiff omega.form) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (pullback_kahler_isSemipositive R omega)) := by
  obtain ⟨e, d, z, hz, hinj⟩ := exists_injective_fderiv R
  exact diagonalPotentialMass_zero_pos_of_isStrictlyPositive_at
    (pullback_kahler_isSemipositive R omega) e hz.1
    (isStrictlyPositive_pullback_coeff R.contMDiff omega e d hz hinj)

/-- The class `{ι^*ω}` of the restricted Kähler form on a resolution target is big. -/
theorem isBigClass_pullback_kahler (R : ResolutionTarget Y) (omega : KahlerBackground n X) :
    IsBigClass (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback R.contMDiff omega.form)) := by
  rcases Nat.eq_zero_or_pos Y.dim with h0 | hpos
  · exact NonBigPotentialMass.isBigClass_of_dim_zero h0 R.kahler _
  · exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hpos R.kahler _ _
      (diagonalPotentialMass_pullback_kahler_pos R omega)

end Big

end SGPT.Trace.RIsoB

end
