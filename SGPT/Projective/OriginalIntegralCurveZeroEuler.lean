import SGPT.Projective.OriginalNormalizationCurveDVR
import SGPT.Projective.OriginalArtinianLineEuler
import SGPT.Projective.AlgebraicArtinianCycleDegree
import SGPT.Foundations.Schemes.RegularZeroEvaluationMono
import SGPT.Foundations.Schemes.RegularSectionDimensionDrop
import Mathlib.AlgebraicGeometry.Artinian

/-! ENTIRE actual ordinary zero schemes and independent INTEGER structural
cycle/Euler degree for arbitrary integral ORIGINAL projective curves.
No original smoothness or period comparison. Blueprint: original-integral-curve-zero-euler.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open scoped nonZeroDivisors

/-- Actual original integrality and ordinary nonzero section give TRUE
original dual evaluation injectivity on EVERY open, without smoothness. -/
theorem originalIntegralSectionZeroEvaluation_injective
    {X : Scheme.{0}} [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L)
    (s : Γ(L,⊤)) (hs : s ≠ 0) (V : X.Opens) :
    Function.Injective (sectionZeroEvaluation L s V) := by
  intro α β h
  apply TopCat.Presheaf.IsSheaf.section_ext (F := (bundleDual L).val.presheaf) (bundleDual L).isSheaf
  intro x hx
  obtain ⟨j,hj⟩ := a.covers x
  let W := V ⊓ a.opens j
  let i : W ⟶ a.opens j := homOfLE inf_le_right
  let : Nonempty W := ⟨⟨x,hx,hj⟩⟩
  refine ⟨W,inf_le_left,⟨hx,hj⟩,?_⟩
  apply ((a.frame j).dual.coefficients i).injective
  apply sectionCoefficient_mul_injective a s hs (a.frame j) i
  have hh := congrArg (X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op) h
  rw [← sectionZeroEvaluation_restrict L s (show W ≤ V from inf_le_left),
    ← sectionZeroEvaluation_restrict L s (show W ≤ V from inf_le_left)] at hh
  rw [sectionZeroEvaluation_frame s (a.frame j) i,sectionZeroEvaluation_frame s (a.frame j) i] at hh
  exact hh

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1)

include f E hcurve in
/-- ENTIRE original section-zero scheme on an arbitrary integral ORIGINAL
projective curve is Artinian, all nilpotents/empty zero retained, no smoothness. -/
theorem originalIntegralCurveSectionZero_isArtinian
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) :
    IsArtinianScheme (sectionZeroSubscheme a s) := by
  classical
  let Z := sectionZeroSubscheme a s
  let ι := sectionZeroι a s
  let EZ := E.sectionZero a s
  let : IsNoetherian Z := EZ.isNoetherian
  have hlocal : ∀ x : X, ∃ (V : X.Opens) (_hV : IsAffineOpen V) (_hxV : x ∈ V)
      (i : a.I), V ≤ a.opens i := by
    intro x
    obtain ⟨i,hi⟩ := a.covers x
    obtain ⟨V,hV,hxV,hVi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨V,hV,hxV,i,hVi⟩
  choose V hV hxV idx hVi using hlocal
  let W : X → Z.Opens := fun x => ι ⁻¹ᵁ V x
  have hcover : IsOpenCover W := by
    apply top_unique
    intro z _
    exact Opens.mem_iSup.mpr ⟨ι z,hxV (ι z)⟩
  have hAff (x : X) : IsAffineOpen (W x) := (hV x).preimage ι
  have hArt : IsLocallyArtinian Z := by
    apply (isLocallyArtinian_iff_of_isOpenCover hcover hAff).mpr
    intro x
    let : IsNoetherianRing Γ(Z,W x) := EZ.affineSections_isNoetherian (hAff x)
    let : Nonempty (V x) := ⟨⟨x,hxV x⟩⟩
    let j : V x ⟶ a.opens (idx x) := homOfLE (hVi x)
    have hrN : (show Γ(X,V x) from (a.frame (idx x)).coefficients j
        (L.presheaf.map (V x).leTop.op s)) ∈ nonZeroDivisors Γ(X,V x) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (sectionCoefficient_ne_zero a s hs (a.frame (idx x)) j)
    have hd := sectionZeroAffine_ringKrullDim_succ_le_of_regular a s ⟨V x,hV x⟩ (a.frame (idx x)) j hrN
    rw [originalIntegralCurve_affine_ringKrullDim_one f E hcurve (hV x)] at hd
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ring.krullDimLE_iff.mpr
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_one,Nat.cast_zero,zero_add] using hd
  exact { toIsLocallyArtinian := hArt, toCompactSpace := inferInstance }

/-- INDEPENDENT TRUE original structural pushforward of the ENTIRE actual
ordinary section-zero cycle, before Euler or analytic comparisons. -/
def originalIntegralCurveSectionZeroDegree {L : X.Modules} (a : LineBundleAtlas L)
    (s : Γ(L,⊤)) (hs : s ≠ 0) : AlgebraicCycle (Spec (.of ℂ)) ℤ := by
  let := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
  exact artinianStructuralPushforward (E.sectionZero a s)

/-- TRUE entire local-ring lengths of the SAME original zero scheme,
including every nilpotent length and empty scheme; no comparison input. -/
theorem originalIntegralCurveSectionZeroDegree_eq_fullLength
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) (p : Spec (.of ℂ)) :
    letI := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
    originalIntegralCurveSectionZeroDegree f E hcurve a s hs p =
      ((originalArtinianStalkLengthSum (sectionZeroSubscheme a s)).toNat : ℤ) := by
  let := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
  exact artinianStructuralPushforward_apply (E.sectionZero a s) p

/-- Arbitrary DISTINCT original line Cartier Euler difference equals the
INDEPENDENT full original section-zero degree on an arbitrary integral
original projective curve. No smoothness or period/Euler premise. -/
theorem originalIntegralCurve_twistedEuler_eq_sectionZeroDegree
    {L B : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas B)
    (s : Γ(L,⊤)) (hs : s ≠ 0) (p : Spec (.of ℂ)) :
    originalProjectiveLineCechEuler f E (bundleTensor B L) =
      originalProjectiveLineCechEuler f E B + originalIntegralCurveSectionZeroDegree f E hcurve a s hs p := by
  let := originalIntegralCurveSectionZero_isArtinian f E hcurve a s hs
  have h := originalTwistedCartierEuler_eq_restricted f E a b s
    (originalIntegralSectionZeroEvaluation_injective a s hs)
  have hD : (originalSectionZeroRestrictedCechComplex f E a s (bundleTensor B L)).homologyEulerChar =
      originalIntegralCurveSectionZeroDegree f E hcurve a s hs p := by
    change originalProjectiveLineCechEuler (sectionZeroι a s ≫ f) (E.sectionZero a s)
      ((Scheme.Modules.pullback (sectionZeroι a s)).obj (bundleTensor B L)) = _
    exact (originalArtinianLineCechEuler_eq_fullLength (sectionZeroι a s ≫ f) (E.sectionZero a s)
      (matePullbackAtlas (sectionZeroι a s) (b.tensor a))).trans
        (originalIntegralCurveSectionZeroDegree_eq_fullLength f E hcurve a s hs p).symm
  exact h.trans (congrArg (fun z : ℤ => originalProjectiveLineCechEuler f E B + z) hD)

/-- PURE original effective Euler degree is the INDEPENDENT ENTIRE
original zero-cycle structural degree, with no original smoothness. -/
theorem originalIntegralCurve_eulerDifference_eq_sectionZeroDegree
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L,⊤)) (hs : s ≠ 0) (p : Spec (.of ℂ)) :
    originalProjectiveLineCechEuler f E L -
        originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) =
      originalIntegralCurveSectionZeroDegree f E hcurve a s hs p := by
  have h := originalIntegralCurve_twistedEuler_eq_sectionZeroDegree f E hcurve a
    (trivialIntrinsicLineBundle X).atlas s hs p
  change originalProjectiveLineCechEuler f E (bundleTensor (SheafOfModules.unit X.ringCatSheaf) L) =
    originalProjectiveLineCechEuler f E (SheafOfModules.unit X.ringCatSheaf) +
      originalIntegralCurveSectionZeroDegree f E hcurve a s hs p at h
  rw [originalProjectiveLineCechEuler_eq_of_iso f E (bundleTensorLeftUnitIso L)] at h
  omega

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
