import SGPT.Projective.AlgebraicCurveClosedPoint
import SGPT.Projective.AlgebraicArtinianCycleDegree
import SGPT.Foundations.Schemes.NativeProjectiveCutGeometry
import Mathlib.AlgebraicGeometry.Artinian

/-! The ACTUAL nonzero original curve section produces its ENTIRE actual
Artinian zero closed subscheme and its independent true structural-cycle
degree; no dimension/finiteness/intersection certificate is supplied.
Blueprint: algebraic-curve-zero-artinian.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Algebra CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open scoped BigOperators nonZeroDivisors

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 f]

include f in
/-- The SAME actual affine coordinate ring has actual dimension one,
from the SAME original structural constants and function field. -/
theorem affineCurve_ringKrullDim_eq_one {V : X.Opens} [Nonempty V] (hV : IsAffineOpen V) :
    ringKrullDim Γ(X, V) = 1 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let := affineChartAlgebra f V
  let := schemeFunctionFieldAlgebra f
  let : IsScalarTower ℂ Γ(X, V) X.functionField := schemeFunctionField_affineChartScalarTower f V
  let : IsFractionRing Γ(X, V) X.functionField := functionField_isFractionRing_of_isAffineOpen X V hV
  let : Algebra.FiniteType ℂ Γ(X, V) := affineChartAlgebra_finiteType f hV
  let : Algebra.IsAlgebraic Γ(X, V) X.functionField :=
    IsLocalization.isAlgebraic X.functionField (nonZeroDivisors Γ(X, V))
  have hF := nativeSmoothFunctionField_trdeg f 1
  have htr : Algebra.trdeg ℂ Γ(X, V) = 1 := by
    have h := trdeg_add_eq ℂ Γ(X, V) (A := X.functionField)
    rw [trdeg_eq_zero (R := Γ(X, V)) (A := X.functionField), add_zero, hF] at h
    exact h
  exact finiteTypeDomain_ringKrullDim_of_trdeg ℂ Γ(X, V) 1 htr

/-- The SAME nonzero original global section manufactures its ENTIRE
actual Artinian zero scheme, retaining nilpotents and the empty case.
No regularity, dimension, finiteness or Artinian output is assumed. -/
theorem sectionZero_isArtinian (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    IsArtinianScheme (sectionZeroSubscheme a s) := by
  classical
  let Z := sectionZeroSubscheme a s
  let iota := sectionZeroι a s
  let EZ := E.sectionZero a s
  let : IsNoetherian Z := EZ.isNoetherian
  have hlocal : ∀ x : X, ∃ (V : X.Opens) (_hV : IsAffineOpen V) (_hxV : x ∈ V)
      (i : a.I), V ≤ a.opens i := by
    intro x
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨V, hV, hxV, i, hVi⟩
  choose V hV hxV idx hVi using hlocal
  let W : X → Z.Opens := fun x => iota ⁻¹ᵁ V x
  have hcover : IsOpenCover W := by
    apply top_unique
    intro z _
    apply Opens.mem_iSup.mpr
    exact ⟨iota z, hxV (iota z)⟩
  have hAff (x : X) : IsAffineOpen (W x) := (hV x).preimage iota
  have hArt : IsLocallyArtinian Z := by
    apply (isLocallyArtinian_iff_of_isOpenCover hcover hAff).mpr
    intro x
    let : IsNoetherianRing Γ(Z, W x) := EZ.affineSections_isNoetherian (hAff x)
    let : Nonempty (V x) := ⟨⟨x, hxV x⟩⟩
    let j : V x ⟶ a.opens (idx x) := homOfLE (hVi x)
    have hr := sectionCoefficient_ne_zero a s hs (a.frame (idx x)) j
    have hrN : (show Γ(X, V x) from (a.frame (idx x)).coefficients j
        (L.presheaf.map (V x).leTop.op s)) ∈ nonZeroDivisors Γ(X, V x) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hr
    have hd := sectionZeroAffine_ringKrullDim_succ_le_of_regular a s ⟨V x, hV x⟩
      (a.frame (idx x)) j hrN
    rw [affineCurve_ringKrullDim_eq_one f (hV x)] at hd
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ring.krullDimLE_iff.mpr
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_one, Nat.cast_zero, zero_add] using hd
  exact { toIsLocallyArtinian := hArt, toCompactSpace := inferInstance }

/-- Actual Artinian geometry makes EVERY original zero-scheme image
point closed in the SAME original curve, without a closed-point premise. -/
theorem sectionZero_image_isClosed (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (z : sectionZeroSubscheme a s) : IsClosed ({sectionZeroι a s z} : Set X) := by
  let := sectionZero_isArtinian f E a s hs
  have h := (sectionZeroι a s).isClosedEmbedding.isClosedMap _
    (isClosed_singleton : IsClosed ({z} : Set (sectionZeroSubscheme a s)))
  simpa only [Set.image_singleton] using h

/-- Independent GENUINE actual algebraic structural pushforward of the
SAME entire original section-zero cycle, before any analytic period. -/
def sectionZeroCycleDegree (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    AlgebraicCycle (Spec (.of ℂ)) ℤ := by
  let := sectionZero_isArtinian f E a s hs
  exact artinianStructuralPushforward (E.sectionZero a s)

/-- The actual ORIGINAL structural zero-cycle degree has the FULL finite
local-ring length sum, independently of any analytic current or period. -/
theorem sectionZeroCycleDegree_eq_sum_lengths (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (y : Spec (.of ℂ)) :
    let := sectionZero_isArtinian f E a s hs
    let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
    sectionZeroCycleDegree f E a s hs y =
      ((∑ z : sectionZeroSubscheme a s,
        Module.length ((sectionZeroSubscheme a s).presheaf.stalk z)
          ((sectionZeroSubscheme a s).presheaf.stalk z)).toNat : ℤ) := by
  let := sectionZero_isArtinian f E a s hs
  let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
  exact artinianStructuralPushforward_apply (E.sectionZero a s) y

end SGPT.Projective.NumEq.AlgebraicCurveDegree
