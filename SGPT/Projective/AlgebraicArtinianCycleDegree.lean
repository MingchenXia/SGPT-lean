import SGPT.Foundations.Schemes.ArtinianProjectiveStalkLength
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Topology.Specialization
import Mathlib.Order.KrullDimension

/-!
The genuine structural algebraic zero-cycle degree, independently of every
analytic period. Source port of the GENERIC definitions/proofs in
`SGPT.Foundations.Schemes/ArtinianFundamentalCycle.lean` (schemePointDimension,
artinianFundamentalCycle and full-length sum) and
`SGPT.Foundations.Schemes/ArtinianCycleStructuralDegree.lean` (actual residue degrees
and structural pushforward), excluding their unrelated Fano-volume tails.

These are FRESH uniquely owned SGPT declarations. Their literal formulas
use the SAME actual AlgebraicCycle.map, full actual local-ring lengths,
original structural morphism and actual residue degrees. The old BWE API
is not imported or relabelled; an equation to those old named constants
remains separate until that upstream import cone is available.
Blueprint: algebraic-artinian-structural-degree.tex.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open scoped BigOperators

/-- Actual specialization-order point dimension, not a supplied weight. -/
def pointDimension (X : Scheme.{0}) (x : X) : ℕ∞ :=
  Order.height (Specialization.toEquiv x)

/-- The genuine discrete specialization order gives actual dimension0. -/
theorem pointDimension_eq_zero_of_discrete (X : Scheme.{0})
    [DiscreteTopology X] (x : X) : pointDimension X x = 0 := by
  apply Order.height_eq_zero.mpr
  intro y hy
  have hxy : x ⤳ Specialization.ofEquiv y := hy
  have he : x = Specialization.ofEquiv y := specializes_iff_eq.mp hxy
  simpa only [Specialization.toEquiv_ofEquiv] using
    (le_of_eq (congrArg Specialization.toEquiv he))

/-- Every actual Artinian local ring has finite FULL self-module length. -/
theorem artinianLocalLength_ne_top (X : Scheme.{0}) [IsLocallyArtinian X] (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) ≠ ⊤ := by
  let U := discreteSingletonOpen X x
  have hU : IsAffineOpen U := IsAffineOpen.of_subsingleton Set.subsingleton_singleton
  let : IsArtinianRing Γ(X, U) := IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U, hU⟩
  let : IsArtinianRing (X.presheaf.stalk x) :=
    (discreteSingletonGermIso X x).commRingCatIsoToRingEquiv.isArtinianRing
  exact Module.length_ne_top (R := X.presheaf.stalk x) (M := X.presheaf.stalk x)

/-- The genuine algebraic zero-cycle of the ACTUAL scheme with FULL
local-ring multiplicities, including its actual nonreduced structure. -/
def artinianZeroCycle (X : Scheme.{0}) [IsArtinianScheme X] : AlgebraicCycle X ℤ where
  toFun x := ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' x _ := ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩

theorem artinianZeroCycle_apply (X : Scheme.{0}) [IsArtinianScheme X] (x : X) :
    artinianZeroCycle X x =
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := rfl

/-- Actual finiteness of every full local-ring length identifies the full
finite cycle coefficient sum, with no truncation of infinity. -/
theorem artinianZeroCycle_sum (X : Scheme.{0}) [IsArtinianScheme X] :
    let : Fintype X := Fintype.ofFinite X
    ∑ x : X, artinianZeroCycle X x =
      ((∑ x : X, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have h : ((∑ x : X, (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℕ) : ℕ∞) =
      ∑ x : X, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact ENat.natCast_toNat (artinianLocalLength_ne_top X x)
  have ht := congrArg ENat.toNat h
  simp only [ENat.toNat_natCast] at ht
  simp only [artinianZeroCycle_apply, ← Nat.cast_sum, ht]

/-- Actual original scalar evaluation proves bijectivity of the ACTUAL
original structural residue-field map, not of a replacement base field. -/
theorem artinianStructuralResidueMap_bijective {X : Scheme.{0}}
    {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] (x : X) : Function.Bijective (p.residueFieldMap x) := by
  refine ⟨(p.residueFieldMap x).hom.injective, ?_⟩
  intro z
  let := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants p) x
  obtain ⟨c, hc⟩ := (P.artinian_stalk_residue_bijective x).surjective z
  refine ⟨(Spec (.of ℂ)).Γevaluation (p x) ((Scheme.ΓSpecIso (.of ℂ)).inv c), ?_⟩
  rw [Scheme.Γevaluation_naturality_apply]
  exact hc

/-- The ACTUAL structural residue-field extension has degree one. -/
theorem artinianStructuralResidueDegree_eq_one {X : Scheme.{0}}
    {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] (x : X) : p.residueDegree x = 1 := by
  let := (p.residueFieldMap x).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap (artinianStructuralResidueMap_bijective P x)

/-- GENUINE actual structural AlgebraicCycle.map with true point
dimensions, original morphism and actual residue extension degrees. -/
def artinianStructuralPushforward {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)}
    (P : ClosedProjectiveEmbedding p) [IsArtinianScheme X] :
    AlgebraicCycle (Spec (.of ℂ)) ℤ := by
  let := P.isProper
  exact AlgebraicCycle.map p (pointDimension X) (pointDimension (Spec (.of ℂ))) (artinianZeroCycle X)

/-- The ACTUAL algebraic structural degree is the SAME full local-ring
length sum. Its definition and proof use no analytic form or period. -/
theorem artinianStructuralPushforward_apply {X : Scheme.{0}}
    {p : X ⟶ Spec (.of ℂ)} (P : ClosedProjectiveEmbedding p)
    [IsArtinianScheme X] (y : Spec (.of ℂ)) :
    let : Fintype X := Fintype.ofFinite X
    artinianStructuralPushforward P y =
      ((∑ x : X, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have hf : p ⁻¹' {y} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hw (x : X) : AlgebraicCycle.mapCoeff p (pointDimension X)
      (pointDimension (Spec (.of ℂ))) x = 1 := by
    simp only [AlgebraicCycle.mapCoeff, pointDimension_eq_zero_of_discrete,
      ↓reduceIte, artinianStructuralResidueDegree_eq_one P x]
  change (∑ᶠ x ∈ p ⁻¹' {y}, artinianZeroCycle X x *
    (AlgebraicCycle.mapCoeff p (pointDimension X)
      (pointDimension (Spec (.of ℂ))) x : ℤ)) = _
  simpa [hf, hw, finsum_eq_sum_of_fintype] using artinianZeroCycle_sum X

end SGPT.Projective.NumEq.AlgebraicCurveDegree
