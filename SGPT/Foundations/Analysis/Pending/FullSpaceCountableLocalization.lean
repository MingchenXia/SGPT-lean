import SGPT.Foundations.Analysis.Pending.FullSpaceMeasurablePiece

set_option autoImplicit false

/-!
# The countable-cover localization of the full-space restricted mass

`Pending.FullSpaceMeasurablePiece` proves that around every pole-free regular
full-space parameter point there is one radius `r` such that **every**
measurable subset of the closed ball of that radius is measured exactly by the
global diagonal non-pluripolar measure of its image.  This module upgrades that
local uniform statement to an arbitrary measurable parameter piece, which is
the localization interface
`FullSpaceAmbientComparison.lintegral_patchDensity_eq_globalMixedMeasure_image`
was named for.

The passage is the classical three-step one and uses no new analysis:

* `ComplexModel n` is second countable, so the cover of the piece by those
  balls has a **countable subcover** (`TopologicalSpace.isOpen_iUnion_countable`);
* mathlib's `disjointed` turns the countable cover into a countable *pairwise
  disjoint* measurable refinement with the same union;
* both sides are countably additive — the left one because `lintegral_iUnion`
  splits a set integral along a disjoint countable union, the right one because
  the parametrization is injective on the parameter domain, so the images of the
  refinement are pairwise disjoint measurable sets.

Measurability of the image of a measurable piece is
`FullSpaceMeasurablePiece.measurableSet_coordinateImage` followed by
`measurableSet_chartSymm_image`; no compactness occurs anywhere.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceCountableLocalization

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches
open FullSpaceRegularPatch FullSpaceClosedBallDomains FullSpaceClosedBallTransport
  GlobalNonPluripolar FullSpaceMeasurablePiece

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
  {hcarrier : V.carrier = univ} {hdim : V.dim = n}

section Pointwise

/-- The full-space patch parametrization into the manifold, with its ambient
source type made explicit.  Exactly as for
`FullSpaceClosedBallTransport.fullSpaceCoordinateParametrization`, this unfolds
the certified equality of the subvariety dimension with `n` once, so no later
statement has to solve that reduction implicitly. -/
def fullSpaceToManifold (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    ComplexModel n → M := fun w => P.toManifold w

@[simp] theorem fullSpaceToManifold_apply
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) (w : ComplexModel n) :
    fullSpaceToManifold P w = P.toManifold w := rfl

/-- The parametrization factors as the inverse chart applied to the coordinate
parametrization. -/
theorem fullSpaceToManifold_image
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (K : Set (ComplexModel n)) :
    fullSpaceToManifold P '' K = (complexChartAt (n := n) P.center).val.symm ''
      (fullSpaceCoordinateParametrization P '' K) := by
  rw [Set.image_image]
  rfl

/-- The coordinate parametrization lands in the target of the chart at the
centre, so the inverse chart may be applied to its image. -/
theorem coordinateImage_subset_chartTarget
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {K : Set (ComplexModel n)} (hKA : K ⊆ (fullParameterDomain P : Set (ComplexModel n))) :
    fullSpaceCoordinateParametrization P '' K ⊆
      (complexChartAt (n := n) P.center).val.target := by
  rintro z ⟨w, hw, rfl⟩
  exact P.source_subset (P.flattening.mapsTo_invFun (hKA hw))

/-- **The full-space patch parametrization is injective on its parameter
domain.**  The coordinate half is injective because it is one leg of a
biholomorphic pair; the chart half is injective on its target. -/
theorem fullSpaceToManifold_injOn
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    InjOn (fullSpaceToManifold P) (fullParameterDomain P : Set (ComplexModel n)) := by
  have h := fullSpaceCoordinateParametrization_isBiholomorphic P
  intro x hx y hy hxy
  have hxT : fullSpaceCoordinateParametrization P x ∈
      (complexChartAt (n := n) P.center).val.target :=
    coordinateImage_subset_chartTarget P (subset_refl _) ⟨x, hx, rfl⟩
  have hyT : fullSpaceCoordinateParametrization P y ∈
      (complexChartAt (n := n) P.center).val.target :=
    coordinateImage_subset_chartTarget P (subset_refl _) ⟨y, hy, rfl⟩
  have hxy' : (complexChartAt (n := n) P.center).val.symm
        (fullSpaceCoordinateParametrization P x) =
      (complexChartAt (n := n) P.center).val.symm
        (fullSpaceCoordinateParametrization P y) := hxy
  have hcoord : fullSpaceCoordinateParametrization P x =
      fullSpaceCoordinateParametrization P y := by
    have hchart := congrArg (complexChartAt (n := n) P.center).val hxy'
    rwa [(complexChartAt (n := n) P.center).val.right_inv hxT,
      (complexChartAt (n := n) P.center).val.right_inv hyT] at hchart
  calc
    x = P.flattening.toFun (fullSpaceCoordinateParametrization P x) := (h.left_inv x hx).symm
    _ = P.flattening.toFun (fullSpaceCoordinateParametrization P y) := by rw [hcoord]
    _ = y := h.left_inv y hy

variable [MeasurableSpace M] [BorelSpace M]

/-- The image in the manifold of a measurable parameter piece is measurable. -/
theorem measurableSet_fullSpaceToManifold_image
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKA : K ⊆ (fullParameterDomain P : Set (ComplexModel n))) :
    MeasurableSet (fullSpaceToManifold P '' K) := by
  rw [fullSpaceToManifold_image P K]
  exact measurableSet_chartSymm_image (complexChartAt (n := n) P.center)
    (measurableSet_coordinateImage P hK hKA) (coordinateImage_subset_chartTarget P hKA)

end Pointwise

section Localization

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The localization theorem, full-space form.**  On the full space the
parameter density integral over an arbitrary measurable pole-free piece of a
regular patch is exactly the ambient diagonal non-pluripolar measure of its
image.  Only measurability and the pole-free condition are used; neither
compactness nor a bound on the ambient mass appears. -/
theorem lintegral_patchDensity_eq_globalMixedMeasure_image
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {S : Set (ComplexModel n)} (hS : MeasurableSet S)
    (hSdom : S ⊆ (fullParameterDomain P : Set (ComplexModel n)))
    (hSpole : Disjoint (fullSpaceToManifold P '' S) (poleSet p.potential)) :
    ∫⁻ w in S, ENNReal.ofReal (patchDensity p P w) ∂volume =
      globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
        (fun _ => p.potential) (fun _ => p.potential_psh.1)
        (fullSpaceToManifold P '' S) := by
  classical
  set mu : Measure M := globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
    (fun _ => p.potential) (fun _ => p.potential_psh.1) with hmu
  -- The local uniform statement at each point of the piece.
  have hlocal : ∀ x : S, ∃ r : ℝ, 0 < r ∧ ∀ K : Set (ComplexModel n), MeasurableSet K →
      K ⊆ closedBall (x : ComplexModel n) r →
      ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
        mu (fullSpaceToManifold P '' K) := by
    rintro ⟨x, hx⟩
    have hxA : x ∈ fullParameterDomain P := hSdom hx
    have hxpole : (complexChartAt (n := n) P.center).val.symm
        (fullSpaceCoordinateParametrization P x) ∉ poleSet p.potential :=
      Set.disjoint_left.mp hSpole ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hkey⟩ :=
      exists_radius_forall_measurableSet_lintegral_eq_globalMixedMeasure p P hxA hxpole
    refine ⟨r, hr, fun K hK hKball => ?_⟩
    rw [hkey K hK hKball, hmu, fullSpaceToManifold_image P K]
  choose r hrpos hkey using hlocal
  rcases Set.eq_empty_or_nonempty S with rfl | hSne
  · rw [Set.image_empty, measure_empty, Measure.restrict_empty, lintegral_zero_measure]
  -- A countable subcover of the piece by those balls.
  obtain ⟨T, hTcount, hTunion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x : S => ball (x : ComplexModel n) (r x))
      fun x => isOpen_ball
  have hcover : S ⊆ ⋃ x ∈ T, ball ((x : S) : ComplexModel n) (r x) := by
    intro w hw
    rw [hTunion]
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, mem_ball_self (hrpos ⟨w, hw⟩)⟩
  have hTne : T.Nonempty := by
    obtain ⟨w, hw⟩ := hSne
    obtain ⟨x, hxT, -⟩ := mem_iUnion₂.mp (hcover hw)
    exact ⟨x, hxT⟩
  obtain ⟨f, hf⟩ := hTcount.exists_eq_range hTne
  -- The countable cover, indexed by the naturals, and its disjoint refinement.
  set A : ℕ → Set (ComplexModel n) :=
    fun k => S ∩ ball ((f k : S) : ComplexModel n) (r (f k)) with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k => hS.inter measurableSet_ball
  have hAunion : (⋃ k, A k) = S := by
    apply Subset.antisymm (iUnion_subset fun k => inter_subset_left)
    intro w hw
    obtain ⟨x, hxT, hxb⟩ := mem_iUnion₂.mp (hcover hw)
    rw [hf] at hxT
    obtain ⟨k, rfl⟩ := hxT
    exact mem_iUnion.mpr ⟨k, hw, hxb⟩
  set D : ℕ → Set (ComplexModel n) := disjointed A with hD
  have hDmeas : ∀ k, MeasurableSet (D k) := MeasurableSet.disjointed hAmeas
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed A
  have hDunion : (⋃ k, D k) = S := by rw [hD, iUnion_disjointed, hAunion]
  have hDball : ∀ k, D k ⊆ closedBall ((f k : S) : ComplexModel n) (r (f k)) := fun k =>
    (disjointed_le A k).trans (inter_subset_right.trans ball_subset_closedBall)
  have hDS : ∀ k, D k ⊆ S := fun k => (disjointed_le A k).trans inter_subset_left
  -- Both sides are countably additive along the refinement.
  have hpiece : ∀ k, ∫⁻ w in D k, ENNReal.ofReal (patchDensity p P w) ∂volume =
      mu (fullSpaceToManifold P '' D k) := fun k => hkey (f k) (D k) (hDmeas k) (hDball k)
  have hinj : InjOn (fullSpaceToManifold P) (fullParameterDomain P : Set (ComplexModel n)) :=
    fullSpaceToManifold_injOn P
  have himagedisj :
      Pairwise (Function.onFun Disjoint fun k => fullSpaceToManifold P '' D k) := by
    intro i j hij
    have hinter := hinj.image_inter ((hDS i).trans hSdom) ((hDS j).trans hSdom)
    show Disjoint (fullSpaceToManifold P '' D i) (fullSpaceToManifold P '' D j)
    rw [Set.disjoint_iff_inter_eq_empty, ← hinter,
      Set.disjoint_iff_inter_eq_empty.mp (hDdisj hij), Set.image_empty]
  have himagemeas : ∀ k, MeasurableSet (fullSpaceToManifold P '' D k) := fun k =>
    measurableSet_fullSpaceToManifold_image P (hDmeas k) ((hDS k).trans hSdom)
  calc
    ∫⁻ w in S, ENNReal.ofReal (patchDensity p P w) ∂volume
        = ∫⁻ w in ⋃ k, D k, ENNReal.ofReal (patchDensity p P w) ∂volume := by rw [hDunion]
    _ = ∑' k, ∫⁻ w in D k, ENNReal.ofReal (patchDensity p P w) ∂volume :=
        lintegral_iUnion hDmeas hDdisj _
    _ = ∑' k, mu (fullSpaceToManifold P '' D k) := tsum_congr hpiece
    _ = mu (⋃ k, fullSpaceToManifold P '' D k) := (measure_iUnion himagedisj himagemeas).symm
    _ = mu (fullSpaceToManifold P '' S) := by rw [← Set.image_iUnion, hDunion]

/-- The localization theorem together with the measurability of the image: the
exact shape the named interface asks for. -/
theorem measurableSet_and_lintegral_patchDensity_eq_globalMixedMeasure
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {S : Set (ComplexModel n)} (hS : MeasurableSet S)
    (hSdom : S ⊆ (fullParameterDomain P : Set (ComplexModel n)))
    (hSpole : Disjoint (fullSpaceToManifold P '' S) (poleSet p.potential)) :
    MeasurableSet (fullSpaceToManifold P '' S) ∧
      ∫⁻ w in S, ENNReal.ofReal (patchDensity p P w) ∂volume =
        globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
          (fun _ => p.potential) (fun _ => p.potential_psh.1)
          (fullSpaceToManifold P '' S) :=
  ⟨measurableSet_fullSpaceToManifold_image P hS hSdom,
    lintegral_patchDensity_eq_globalMixedMeasure_image p P hS hSdom hSpole⟩

end Localization

end SGPT.Foundations.Analysis.Pending.FullSpaceCountableLocalization
