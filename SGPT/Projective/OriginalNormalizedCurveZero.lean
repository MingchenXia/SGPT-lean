import SGPT.Projective.OriginalNormalizationCurveDimension
import SGPT.Projective.OriginalNormalizationLineUnit
import SGPT.Projective.OriginalIntegralCurveZeroEuler
import SGPT.Projective.OriginalOpenSectionZero
import SGPT.Projective.OriginalFiniteArtinianCech
import SGPT.Projective.AlgebraicCurveZeroArtinian

/-! ENTIRE actual ordinary zero geometry on the SAME original normalization.
No closed embedding of the normalizer is supplied. Blueprint:
original-normalized-curve-zero.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open scoped nonZeroDivisors

/-- Genuine proper curve geometry suffices for the ENTIRE zero scheme;
no chosen source projective embedding or zero-dimension output is needed. -/
theorem originalProperSmoothCurveSectionZero_isArtinian
    {Y : Scheme.{0}} [IsIntegral Y] (g : Y ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 g] [QuasiCompact g]
    {L : Y.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) :
    IsArtinianScheme (sectionZeroSubscheme a s) := by
  classical
  let : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let Z := sectionZeroSubscheme a s
  let ι := sectionZeroι a s
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian ι
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace ι
  have hlocal : ∀ x : Y, ∃ (V : Y.Opens) (_hV : IsAffineOpen V) (_hxV : x ∈ V)
      (i : a.I), V ≤ a.opens i := by
    intro x
    obtain ⟨i,hi⟩ := a.covers x
    obtain ⟨V,hV,hxV,hVi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨V,hV,hxV,i,hVi⟩
  choose V hV hxV idx hVi using hlocal
  let W : Y → Z.Opens := fun x => ι ⁻¹ᵁ V x
  have hcover : IsOpenCover W := by
    apply top_unique
    intro z _
    exact Opens.mem_iSup.mpr ⟨ι z,hxV (ι z)⟩
  have hAff (x : Y) : IsAffineOpen (W x) := (hV x).preimage ι
  have hArt : IsLocallyArtinian Z := by
    apply (isLocallyArtinian_iff_of_isOpenCover hcover hAff).mpr
    intro x
    let : IsNoetherianRing Γ(Z,W x) := IsLocallyNoetherian.component_noetherian ⟨W x,hAff x⟩
    let : Nonempty (V x) := ⟨⟨x,hxV x⟩⟩
    let j : V x ⟶ a.opens (idx x) := homOfLE (hVi x)
    have hrN : (show Γ(Y,V x) from (a.frame (idx x)).coefficients j
        (L.presheaf.map (V x).leTop.op s)) ∈ nonZeroDivisors Γ(Y,V x) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (sectionCoefficient_ne_zero a s hs (a.frame (idx x)) j)
    have hd := sectionZeroAffine_ringKrullDim_succ_le_of_regular a s ⟨V x,hV x⟩ (a.frame (idx x)) j hrN
    rw [affineCurve_ringKrullDim_eq_one g (hV x)] at hd
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ring.krullDimLE_iff.mpr
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_one,Nat.cast_zero,zero_add] using hd
  exact { toIsLocallyArtinian := hArt, toCompactSpace := inferInstance }

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

/-- Actual ORIGINAL nonzero section stays nonzero under the SAME genuine
normalization pullback. No nonzero/reader certificate for the output. -/
theorem originalNormalizedSection_ne_zero {L : X.Modules} (a : LineBundleAtlas L)
    (s : Γ(L,⊤)) (hs : s ≠ 0) : originalPulledSection (originalNormalizationMap X) s ≠ 0 := by
  intro h
  apply hs
  apply originalNormalizationLineUnit_injective X a ⊤
  exact h.trans (map_zero _).symm

include E hcurve in
/-- ENTIRE actual pulled original section-zero scheme on the SAME
normalizer is genuinely Artinian; no new normalized projective embedding. -/
theorem originalNormalizedCurveSectionZero_isArtinian
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) :
    IsArtinianScheme (sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
      (originalPulledSection (originalNormalizationMap X) s)) := by
  let := originalNormalizationMap_finite X f E
  let := E.isProper
  let := originalNormalizationCurve_smoothOfRelativeDimension f E hcurve
  exact originalProperSmoothCurveSectionZero_isArtinian (originalNormalizationMap X ≫ f)
    (matePullbackAtlas (originalNormalizationMap X) a)
    (originalPulledSection (originalNormalizationMap X) s) (originalNormalizedSection_ne_zero a s hs)

/-- Actual SAME whole normalized zero is mapped FINITELY to the original
ambient projective space, NEVER asserted to be a closed immersion there. -/
def originalNormalizedZeroProjectiveMap {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) :
    sectionZeroSubscheme (matePullbackAtlas (originalNormalizationMap X) a)
      (originalPulledSection (originalNormalizationMap X) s) ⟶ polynomialProj ℂ E.ambientDimension :=
  sectionZeroι (matePullbackAtlas (originalNormalizationMap X) a)
    (originalPulledSection (originalNormalizationMap X) s) ≫ originalNormalizationMap X ≫ E.map

include f in
/-- The true finite map is PRODUCED from actual zero closed immersion,
actual finite normalization, and the ORIGINAL closed projective embedding. -/
theorem originalNormalizedZeroProjectiveMap_finite
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) :
    IsFinite (originalNormalizedZeroProjectiveMap f E a s) := by
  let := originalNormalizationMap_finite X f E
  let := E.closedImmersion
  exact inferInstanceAs (IsFinite (sectionZeroι (matePullbackAtlas (originalNormalizationMap X) a)
    (originalPulledSection (originalNormalizationMap X) s) ≫ originalNormalizationMap X ≫ E.map))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
