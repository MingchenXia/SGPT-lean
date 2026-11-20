import SGPT.Foundations.Analysis.Pending.FullSpaceGeneralClosedBall

set_option autoImplicit false

/-!
# From closed parameter balls to arbitrary measurable parameter pieces

`Pending.FullSpaceGeneralClosedBall` measures a *closed parameter ball* of a
full-space regular patch by the global diagonal non-pluripolar measure of its
image, in every complex dimension.  The compactness of the ball is used in
exactly one place in that chain: to know that the coordinate image is a
measurable set (`FullSpaceClosedBallTransport.measurableSet_coordinateImage_closedBall`).
Every other ingredient — the mathlib change-of-variables formula
`lintegral_coordinateImage_eq_lintegral_abs_det_fderiv_mul`, the `withDensity`
evaluation, the holomorphic density covariance, and the patch identification
`globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal` —
already accepts an arbitrary measurable (respectively arbitrary) set.

This module removes that single obstruction.  The full-space patch
parametrization is one half of an `IsBiholomorphicPair`, so its image is a
*preimage* under the other half:

  `τ '' K = flatteningSource ∩ σ ⁻¹' K`   (`IsBiholomorphicPair.image_eq`),

and `σ` is continuous on the open set `flatteningSource`.  Hence the image of a
measurable parameter piece is measurable, with no compactness anywhere.  Every
statement of `FullSpaceGeneralClosedBall` is then repeated with `IsCompact K`
weakened to `MeasurableSet K`, and the local data is packaged once as

  `exists_radius_forall_measurableSet_lintegral_eq_globalMixedMeasure`,

which fixes, around one pole-free regular parameter point, a radius that works
*simultaneously for every measurable subset* of the corresponding closed ball.
That uniformity is what the countable-cover localization consumes.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceMeasurablePiece

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches
open FullSpaceRegularPatch FullSpaceClosedBallDomains FullSpaceClosedBallTransport
  FullSpaceLocalCurrent FullSpaceGeneralDensity FullSpacePatchMeasure BedfordTaylor
  MixedNonPluripolar GlobalNonPluripolar FullSpaceGeneralClosedBall

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

section ContinuousOnPreimage

variable {alpha' beta' : Type*} [TopologicalSpace alpha'] [MeasurableSpace alpha']
  [BorelSpace alpha'] [TopologicalSpace beta'] [MeasurableSpace beta'] [BorelSpace beta']

/-- A set on which a map is only *continuous there* still pulls measurable sets
back to measurable sets, provided one keeps the intersection with that set and
the set itself is measurable.  This is the only measure-theoretic ingredient
needed to drop compactness from the full-space patch chain. -/
theorem measurableSet_inter_preimage_of_continuousOn {f : alpha' → beta'} {s : Set alpha'}
    (hs : MeasurableSet s) (hf : ContinuousOn f s) {A : Set beta'} (hA : MeasurableSet A) :
    MeasurableSet (s ∩ f ⁻¹' A) := by
  have hres : Measurable (s.domRestrict f) := hf.domRestrict.measurable
  have hset : s ∩ f ⁻¹' A = Subtype.val '' (s.domRestrict f ⁻¹' A) := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨⟨z, hz⟩, hzA, rfl⟩
    · rintro ⟨⟨z, hz⟩, hzA, rfl⟩
      exact ⟨hz, hzA⟩
  rw [hset]
  exact (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 (hres hA)

end ContinuousOnPreimage

section ChartImage

variable [MeasurableSpace M] [BorelSpace M]

omit [IsComplexManifold n M] in
/-- The inverse chart image of a measurable subset of the chart target is
measurable.  `PartialHomeomorph.symm_image_eq_source_inter_preimage` turns the
image into a preimage, and the chart is continuous on its open source. -/
theorem measurableSet_chartSymm_image (e : ComplexChart n M) {A : Set (ComplexModel n)}
    (hA : MeasurableSet A) (hAt : A ⊆ e.val.target) :
    MeasurableSet (e.val.symm '' A) := by
  rw [e.val.symm_image_eq_source_inter_preimage hAt]
  exact measurableSet_inter_preimage_of_continuousOn e.val.open_source.measurableSet
    e.val.continuousOn hA

end ChartImage

section Measurability

variable {hcarrier : V.carrier = univ} {hdim : V.dim = n}

/-- **The coordinate image of a measurable parameter piece is measurable.**
No compactness: the parametrization is half of a biholomorphic pair, so its
image is the preimage of `K` under the flattening, intersected with the open
flattening source. -/
theorem measurableSet_coordinateImage
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKA : K ⊆ (fullParameterDomain P : Set (ComplexModel n))) :
    MeasurableSet (fullSpaceCoordinateParametrization P '' K) := by
  have h := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hB : MeasurableSet (flatteningSource P : Set (ComplexModel n)) :=
    (flatteningSource P).isOpen.measurableSet
  have hcont : ContinuousOn P.flattening.toFun
      (flatteningSource P : Set (ComplexModel n)) := h.holo_inv.continuousOn
  rw [h.image_eq hKA]
  exact measurableSet_inter_preimage_of_continuousOn hB hcont hK

end Measurability

section Transport

variable {hcarrier : V.carrier = univ} {hdim : V.dim = n}

/-- The Jacobian evaluation of `smoothMeasure` on a coordinate image, for an
arbitrary **measurable** parameter piece.  This is
`FullSpaceClosedBallTransport.smoothMeasure_coordinateImage_eq_lintegral_jacobian`
with compactness replaced by `measurableSet_coordinateImage`. -/
theorem smoothMeasure_coordinateImage_eq_lintegral_jacobian_of_measurableSet
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {K : Set (ComplexModel n)}
    (hK : MeasurableSet K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    {f : ComplexModel n → ℝ} (hf : IsSmoothPshOn (regularPotentialDomain P U) f) :
    smoothMeasure (regularPotentialDomain P U) f hf
        (fullSpaceCoordinateParametrization P '' K) =
      ∫⁻ w in K,
        ENNReal.ofReal |(fderiv ℝ (fullSpaceCoordinateParametrization P) w).det| *
          ENNReal.ofReal (smoothDensity f
            (fullSpaceCoordinateParametrization P w)) ∂volume := by
  have h := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hKA : K ⊆ (fullParameterDomain P : Set (ComplexModel n)) := fun w hw =>
    (mem_regularParameterDomain_iff P U w).mp (hKU hw) |>.1
  have himage : MeasurableSet (fullSpaceCoordinateParametrization P '' K) :=
    measurableSet_coordinateImage P hK hKA
  have himageU : fullSpaceCoordinateParametrization P '' K ⊆
      (regularPotentialDomain P U : Set (ComplexModel n)) := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨hwA, hwU⟩ := (mem_regularParameterDomain_iff P U w).mp (hKU hw)
    exact ⟨hwU, h.mapsTo hwA⟩
  unfold FirstPass.MongeAmpere.smoothMeasure
  calc
    _ = ∫⁻ z in fullSpaceCoordinateParametrization P '' K,
        ENNReal.ofReal (smoothDensity f z) ∂
          (volume.restrict (regularPotentialDomain P U : Set (ComplexModel n))) := by
      exact @MeasureTheory.withDensity_apply (ComplexModel n) _
        (volume.restrict (regularPotentialDomain P U : Set (ComplexModel n)))
        (fun z => ENNReal.ofReal (smoothDensity f z))
        (fullSpaceCoordinateParametrization P '' K) himage
    _ = ∫⁻ z in fullSpaceCoordinateParametrization P '' K,
        ENNReal.ofReal (smoothDensity f z) ∂volume := by
      rw [Measure.restrict_restrict_of_subset himageU]
    _ = _ := lintegral_coordinateImage_eq_lintegral_abs_det_fderiv_mul P U hK hKU
      (fun z => ENNReal.ofReal (smoothDensity f z))

/-- The smooth mass of the coordinate image of a **measurable** regular
parameter piece is the smooth top-density integral of the pulled-back
potential. -/
theorem smoothMeasure_coordinateImage_eq_lintegral_smoothDensity_comp_of_measurableSet
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {K : Set (ComplexModel n)}
    (hK : MeasurableSet K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    {f : ComplexModel n → ℝ} (hf : IsSmoothPshOn (regularPotentialDomain P U) f) :
    smoothMeasure (regularPotentialDomain P U) f hf
        (fullSpaceCoordinateParametrization P '' K) =
      ∫⁻ w in K, ENNReal.ofReal (smoothDensity
          (fun x => f (fullSpaceCoordinateParametrization P x)) w) ∂volume := by
  refine (smoothMeasure_coordinateImage_eq_lintegral_jacobian_of_measurableSet
    P U hK hKU hf).trans ?_
  refine setLIntegral_congr_fun hK fun w hw => ?_
  exact jacobian_smoothDensity_eq_smoothDensity_comp_coordinateParametrization P U hf.1
    (hKU hw)

end Transport

section Density

variable {hcarrier : V.carrier = univ} {hdim : V.dim = n}

/-- A **measurable** pole-free parameter piece has exactly the smooth mass of
its coordinate image, in every complex dimension.  This is
`FullSpaceGeneralClosedBall.lintegral_patchDensity_eq_smoothMeasure_coordinateImage`
with compactness weakened to measurability. -/
theorem lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_measurableSet
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y)) :
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' K) := by
  calc
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
        ∫⁻ w in K, ENNReal.ofReal
          (smoothDensity (fun x => g (fullSpaceCoordinateParametrization P x) +
            rho (fullSpaceCoordinateParametrization P x)) w) ∂volume := by
      refine setLIntegral_congr_fun hK fun w hw => ?_
      rw [patchDensity_eq_smoothDensity_corrected p P U hrho hg hpot (hKU hw)]
    _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' K) :=
      (smoothMeasure_coordinateImage_eq_lintegral_smoothDensity_comp_of_measurableSet
        P U hK hKU hsmooth).symm

end Density

section GlobalMeasure

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
variable {hcarrier : V.carrier = univ} {hdim : V.dim = n}

/-- **A measurable full-space parameter piece is measured exactly by the global
diagonal non-pluripolar measure.**  Identical to
`FullSpaceGeneralClosedBall.closedBall_lintegral_patchDensity_eq_globalMixedMeasure`,
except that the piece is only assumed measurable. -/
theorem lintegral_patchDensity_eq_globalMixedMeasure_of_measurableSet
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential (perturbedRepresentative p).val
      (complexChartAt (n := n) P.center) U rho)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hpot : EqOn (chartFunction p.potential (complexChartAt (n := n) P.center))
      (fun y => (g y : EReal)) U)
    {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (hsmooth : IsSmoothPshOn (regularPotentialDomain P U) (fun y => g y + rho y))
    (Q : Patch (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential))
    (hchart : Q.chart = complexChartAt (n := n) P.center)
    (W : Opens (ComplexModel n)) (hWD : W ≤ regularPotentialDomain P U)
    (hWQ : W ≤ Q.domain) (k : ℕ) (hW : RelativelyCompactIn W Q.domain)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k)
    (hcorrected : ∀ i, EqOn (fun z => (Q.corrected i z).toReal)
      (fun z => g z + rho z) W)
    (himage : fullSpaceCoordinateParametrization P '' K ⊆ W) :
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
      globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
        (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' K)) := by
  have hsmoothW : IsSmoothPshOn W (fun y => g y + rho y) :=
    ⟨hsmooth.1.mono hWD, hsmooth.2.1.mono hWD,
      fun z hz => hsmooth.2.2 z (hWD hz)⟩
  have hsmooth_restrict :
      smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
        (fullSpaceCoordinateParametrization P '' K) =
      smoothMeasure W (fun y => g y + rho y) hsmoothW
        (fullSpaceCoordinateParametrization P '' K) := by
    symm
    calc
      smoothMeasure W (fun y => g y + rho y) hsmoothW
          (fullSpaceCoordinateParametrization P '' K) =
        (smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth).restrict
          (W : Set (ComplexModel n))
          (fullSpaceCoordinateParametrization P '' K) :=
        congrArg (fun mu : Measure (ComplexModel n) =>
          mu (fullSpaceCoordinateParametrization P '' K))
          (smoothMeasure_restrict hWD (fun y => g y + rho y) hsmooth hsmoothW).symm
      _ = smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' K) := by
        rw [Measure.restrict_apply' W.isOpen.measurableSet,
          inter_eq_self_of_subset_left himage]
  calc
    ∫⁻ w in K, ENNReal.ofReal (patchDensity p P w) ∂volume =
        smoothMeasure (regularPotentialDomain P U) (fun y => g y + rho y) hsmooth
          (fullSpaceCoordinateParametrization P '' K) :=
      lintegral_patchDensity_eq_smoothMeasure_coordinateImage_of_measurableSet
        p P U hrho hg hpot hK hKU hsmooth
    _ = smoothMeasure W (fun y => g y + rho y) hsmoothW
          (fullSpaceCoordinateParametrization P '' K) := hsmooth_restrict
    _ = globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p) (fun _ => p.potential)
          (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' K)) := by
      simpa only [hchart, perturbedRepresentative] using
        (globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal
          p.potential_psh.1 Q W hWQ k hW hWk hsmoothW hcorrected himage).symm

/-- **The uniform local statement.**  Around a regular full-space parameter
point off the pole set there is one radius `r` such that *every* measurable
subset of the closed ball of that radius is measured exactly by the global
diagonal non-pluripolar measure of its image.  All local data is chosen from
the presentation by `FullSpaceAutomaticPatch.exists_fullSpace_closedBall_patch_data`;
the point is that the same data serves all measurable subsets at once. -/
theorem exists_radius_forall_measurableSet_lintegral_eq_globalMixedMeasure
    (p : AdmissibleRestrictedCurrentPresentation omega alpha
      (fullSpaceSubvariety V hcarrier hdim) epsilon)
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    {w : ComplexModel n} (hw : w ∈ fullParameterDomain P)
    (hpole : (complexChartAt (n := n) P.center).val.symm
      (fullSpaceCoordinateParametrization P w) ∉ poleSet p.potential) :
    ∃ r > 0, ∀ K : Set (ComplexModel n), MeasurableSet K → K ⊆ closedBall w r →
      ∫⁻ x in K, ENNReal.ofReal (patchDensity p P x) ∂volume =
        globalMixedMeasure (fun _ : Fin n => perturbedRepresentative p)
          (fun _ => p.potential) (fun _ => p.potential_psh.1)
          ((complexChartAt (n := n) P.center).val.symm ''
            (fullSpaceCoordinateParametrization P '' K)) := by
  obtain ⟨U, rho, g, Q, W, k, r, hrho, hg, hpot, hsmooth, hchart, hWD, hWQ,
      hWrel, hWstrict, hcorrected, hr, hball, himage⟩ :=
    FullSpaceAutomaticPatch.exists_fullSpace_closedBall_patch_data p P hw hpole
  refine ⟨r, hr, ?_⟩
  intro K hK hKball
  refine lintegral_patchDensity_eq_globalMixedMeasure_of_measurableSet
    p P U hrho hg hpot hK (hKball.trans hball) hsmooth Q hchart W hWD hWQ k hWrel
    hWstrict hcorrected ?_
  exact (Set.image_mono hKball).trans himage

end GlobalMeasure

end SGPT.Foundations.Analysis.Pending.FullSpaceMeasurablePiece
