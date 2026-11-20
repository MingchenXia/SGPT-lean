import SGPT.Unibranch.HironakaG10ActualPointCentreExceptionalSaturation
import SGPT.Foundations.Analysis.Pending.HironakaActualRelativeNormalizedSaturation
import SGPT.Foundations.Analysis.Pending.HironakaActualFixedFlatteningBlowupCoordinates
import SGPT.Foundations.Analysis.Pending.HironakaActualControlledNeighborhoodGenerators

/-!
# One pivot of a general admissible blowup: whole exceptional ideal and full saturation (G10-02-07.a)

Lane G10SB, run 0081, plan item G10-02-07 (sub-item 07.a, research gate `G10SB/G10-02-07r-general-centre-pivot.md`).
PR #272 proved, for a genuine manifold blowup with a POINT centre, that one chart identifies the whole exceptional
stalk ideal with the pivot governing the full nonreduced pullback saturation and quotient regularity
(`HironakaG10ActualPointCentreExceptionalSaturation.exists_actual_point_centre_exceptional_stalk_saturation`).
Here the centre is a regular submanifold of ANY dimension `d` along which the coherent (possibly nonreduced)
ideal has constant Hilbert–Samuel function (normal flatness: Hironaka 1975 Def. 4.4.3 (1), p. 537; for a point
it is automatic).  The same chart then:

* identifies the WHOLE exceptional-divisor stalk ideal with the principal ideal of the transported pivot;
* identifies the whole native pullback stalk ideal with the adapted chart pullback;
* makes the normalized strict ideal the FULL pivot saturation of the native pullback, with the pivot a
  non-zero-divisor modulo it and one finite colon.

No named input.  This is a statement on a smooth ambient manifold (ideal-theoretic strict transform); the
singular-base version is G10-02-07.b.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG10SbGeneralCentreSaturation

noncomputable section

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences HolGerm BlowupFlatCoordinates
  BlowupExceptionalDivisor HironakaActualHistoricalMovingCentreChart
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualRelativeNormalizedSaturation HironakaActualFixedFlatteningBlowupCoordinates
  HironakaActualControlledNeighborhoodGenerators HironakaActualNativeAdaptedPullbackSquare
  SGPT.Unibranch.HironakaG10AdaptedStalkIdeal
  SGPT.Unibranch.HironakaG10NativeStalkSaturationTransport
  SGPT.Unibranch.HironakaG10ActualExceptionalStalkPivot

/-- Translation by the literal zero does not change the origin ideal of a sheaf coherent near `0`. -/
theorem zero_translated_origin_ideal_eq {n : ℕ}
    (F : GermIdeal n (ComplexModel n)) (W : Set (ComplexModel n))
    (hF : CoherentOn F W) (h0W : (0 : ComplexModel n) ∈ W) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F 0) =
      originalCoherentOriginIdeal F := by
  obtain ⟨V, hV, h0V, _hVW, N, H, hH, hgen⟩ := hF 0 h0W
  have hsame : (fun i : Fin N => H i ∘ actualAffineTranslation n 0) = H := by
    funext i z
    simp only [Function.comp_apply, actualAffineTranslation, zero_add]
  have hmem (f : ComplexModel n → ℂ) :
      (actualTranslatedOriginalSheaf F 0).mem 0 f ↔ F.mem 0 f := by
    have h := translated_sheaf_mem_iff_of_real_generators F H hV hH hgen h0V f
    rw [hsame] at h
    exact h.trans (hgen 0 h0V f).symm
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hIf, rfl⟩
    exact Ideal.subset_span ⟨f, hf, (hmem f).mp hIf, rfl⟩
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hIf, rfl⟩
    exact Ideal.subset_span ⟨f, hf, (hmem f).mpr hIf, rfl⟩

/-- The normal variables of a dimension-`d` centre are the indices `≥ d`. -/
theorem tangentCentreVariables_eq (d t : ℕ) :
    actualTangentCentreVariables d t = {i : Fin (d+t) | d ≤ i.val} := by
  ext i
  simp only [actualTangentCentreVariables, mem_range, mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl⟩
    show d ≤ d + k.val
    omega
  · intro hi
    have hlt := i.isLt
    refine ⟨⟨i.val - d, by omega⟩, Fin.ext ?_⟩
    show d + (i.val - d) = i.val
    omega

theorem complexCoordinatePlane_eq_coordinateSubsetPlane (d t : ℕ) :
    complexCoordinatePlane (d+t) d = coordinateSubsetPlane (actualTangentCentreVariables d t) := by
  rw [tangentCentreVariables_eq]
  ext z
  simp only [complexCoordinatePlane, coordinateSubsetPlane, mem_ofPred_eq]

variable {d t : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]

/-- **G10-02-07.a.**  A genuine manifold blowup along a regular centre of dimension `d`, along which the
coherent ideal `I` (possibly nonreduced) has constant Hilbert–Samuel function: one chart produces the pivot
generating the WHOLE exceptional stalk ideal, the whole native pullback stalk ideal, its FULL pivot
saturation (the normalized strict ideal), pivot regularity and one finite colon. -/
theorem exists_actual_hs_centre_exceptional_stalk_saturation
    (I : GermIdeal (d+t) X) (hI : I.IsCoherent) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (d+t) C π) (y : Y)
    (hCy : RegularAtDim (n := d+t) C (π y) d)
    (hhs : ∀ c ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt I c ℓ = hilbertSamuelAt I (π y) ℓ) :
    ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π y) (π y)))
      (j : Fin t) (b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π y)) = 0)
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y) = 0),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) (π y)).target ∧
      Θ.source ⊆ (chartAt (ComplexModel (d+t)) y).target ∧ b (j.natAdd d) = 0 ∧
      (∀ {x : X}, x ∈ (chartAt (ComplexModel (d+t)) (π y)).source →
        chartAt (ComplexModel (d+t)) (π y) x ∈ Φ.source →
        (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) x) ∈
          complexCoordinatePlane (d+t) d)) ∧
      (∀ z : Y, z ∈ (chartAt (ComplexModel (d+t)) y).source →
        chartAt (ComplexModel (d+t)) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z)) =
          actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
            (Θ.toFun (chartAt (ComplexModel (d+t)) y z))) ∧
      let E := adaptedStalkEquiv y Θ hΘ0
      let p := E.symm (coordinateGerm (j.natAdd d))
      let Ip := actualWholeSheafStalkIdeal (GermIdeal.pullback (m := d+t) π I) y
      let T := adaptedIdeal (GermIdeal.pullback (m := d+t) π I) y Θ hΘ0
      let J₀ := adaptedIdeal I (π y) Φ hΦ0
      let N := actualAnalyticNormalizedMemberIdeal J₀ (actualTangentCentreVariables d t) (j.natAdd d) b
      let J := N.comap E.toRingHom
      E p = coordinateGerm (j.natAdd d) ∧
      actualWholeSheafStalkIdeal (exceptionalDivisor hπ).ideal y = Ideal.span {p} ∧
      Ideal.map E.toRingHom Ip = T ∧
      Ideal.map E.toRingHom J = N ∧
      (∀ v, v ∈ J ↔ ∃ q : ℕ, p^q * v ∈ Ip) ∧
      (∀ v, p*v ∈ J ↔ v ∈ J) ∧
      IsRegular (Ideal.Quotient.mk J p) ∧
      (∃ D : ℕ, T.colon {coordinateGerm (j.natAdd d)^D} = N) := by
  obtain ⟨Φ, hΦsrc, hΦ0, hflat, hrest⟩ :=
    exists_original_hs_centre_normalized_saturation C (π y) hCy I hI hhs
  obtain ⟨_P, _hPG, _hpower, hsat⟩ := hrest
  -- the origin ideal of the canonical family is the adapted ideal of `I`
  have hI0 : originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf I (π y) Φ) 0) = adaptedIdeal I (π y) Φ hΦ0 := by
    rw [zero_translated_origin_ideal_eq _ Φ.target
      (coherentOn_actualFlattenedOriginalSheaf I hI (π y) Φ hΦsrc)
      (actualFlattening_target_zero_mem (π y) Φ hΦ0)]
    exact actual_flattened_origin_eq_adapted I hI (π y) Φ hΦ0
  -- blowup coordinates in the SAME flattening chart
  obtain ⟨j₀, b, Θ, hΘsrc, hΘ0, hj₀, _hbt, hbj, hSquare⟩ :=
    exists_actual_fixed_flattening_blowup_coordinates hπ y d Φ hΦsrc hΦ0 hflat
  have hj₀lt := j₀.isLt
  let j : Fin t := ⟨j₀.val - d, by omega⟩
  have hj : j.natAdd d = j₀ := by
    apply Fin.ext
    show d + (j₀.val - d) = j₀.val
    omega
  have hA := tangentCentreVariables_eq d t
  have hSquare' : ∀ z : Y, z ∈ (chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z)) =
        actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z)) := by
    rw [hA, hj]
    exact hSquare
  have hFlat' : ∀ {x : X}, x ∈ (chartAt (ComplexModel (d+t)) (π y)).source →
      chartAt (ComplexModel (d+t)) (π y) x ∈ Φ.source →
      (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) x) ∈
        coordinateSubsetPlane (actualTangentCentreVariables d t)) := by
    intro x hx hxΦ
    rw [← complexCoordinatePlane_eq_coordinateSubsetPlane]
    exact hflat hx hxΦ
  have hmemA : j.natAdd d ∈ actualTangentCentreVariables d t := ⟨j, rfl⟩
  have hExceptional := actual_exceptional_stalk_ideal_eq_span_transported_pivot
    hπ y (actualTangentCentreVariables d t) (j.natAdd d) hmemA b Φ hFlat' Θ hΘsrc hΘ0 hSquare'
  -- the whole pullback in the adapted charts
  have hpull := actual_native_adapted_pullback_square I hI π hπ.contMDiff y
    (actualTangentCentreVariables d t) (j.natAdd d) b Φ hΦsrc hΦ0 Θ hΘsrc hΘ0 hSquare'
  -- the relative saturation law, read on the adapted ideal
  have hlaw := hsat j b
  simp only [hI0] at hlaw
  obtain ⟨hwhole, _hpivot, hcolon⟩ := hlaw
  let E := adaptedStalkEquiv y Θ hΘ0
  let p := E.symm (coordinateGerm (j.natAdd d))
  let Ip := actualWholeSheafStalkIdeal (GermIdeal.pullback (m := d+t) π I) y
  let T := adaptedIdeal (GermIdeal.pullback (m := d+t) π I) y Θ hΘ0
  let J₀ := adaptedIdeal I (π y) Φ hΦ0
  let N := actualAnalyticNormalizedMemberIdeal J₀ (actualTangentCentreVariables d t) (j.natAdd d) b
  have hmap : Ideal.map E.toRingHom Ip = T :=
    map_actualWholeSheafStalkIdeal_adapted (GermIdeal.pullback (m := d+t) π I) y Θ hΘsrc hΘ0
  have hN : ∀ g, g ∈ N ↔ ∃ q : ℕ, (E p)^q * g ∈ T := by
    intro g
    have h := hwhole g
    rw [← hpull] at h
    simpa only [p, RingEquiv.apply_symm_apply] using h
  have htransport := actual_structure_stalk_saturation_quotient_regular y E Ip T N p hmap hN
  have hcolon' : ∃ D : ℕ, T.colon {coordinateGerm (j.natAdd d)^D} = N := by
    obtain ⟨D, hD⟩ := hcolon
    rw [← hpull] at hD
    exact ⟨D, hD⟩
  refine ⟨Φ, j, b, Θ, hΦ0, hΘ0, hΦsrc, hΘsrc, (by rw [hj]; exact hbj), hflat, hSquare', ?_⟩
  exact ⟨E.apply_symm_apply _, hExceptional.2, hmap, htransport.1, htransport.2.1,
    htransport.2.2.1, htransport.2.2.2, hcolon'⟩

end

end SGPT.Unibranch.HironakaG10SbGeneralCentreSaturation
