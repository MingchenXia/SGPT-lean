import SGPT.NAPotential.AlgPrimes3Algebra

/-!
# The actual original divisorial centre without a proper structural base

Complete blueprint: `divisor-valuation-center.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.DivisorValuationCenter

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich
open SGPT.NAPotential.AlgPrimes3.PrimeDivisorOver'

variable {X : Scheme.{0}} (D : PrimeDivisorOver X)

/-- The original divisor pullback and original specialization map have the SAME
actual stalk coefficient square. -/
theorem pullback_specializationMap (g : X.presheaf.stalk (D.π D.point)) :
    D.pullback ((BerkovichPoint.specializationMap
      ((genericPoint_specializes D.point).map D.π.continuous)).hom g) =
      algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField
        ((D.π.stalkMap D.point) g) := by
  apply D.residueEquiv.injective
  have hmaps : BerkovichPoint.specializationMap
        ((genericPoint_specializes D.point).map D.π.continuous) ≫
      D.π.residueFieldMap (genericPoint D.Y) =
      D.π.stalkMap D.point ≫
        D.Y.presheaf.stalkSpecializes (genericPoint_specializes D.point) ≫
          D.Y.residue (genericPoint D.Y) := by
    dsimp only [BerkovichPoint.specializationMap]
    rw [Category.assoc, Scheme.residue_residueFieldMap, ← Category.assoc,
      D.π.stalkSpecializes_stalkMap (genericPoint D.Y) D.point
        (genericPoint_specializes D.point), Category.assoc]
  have h := congrArg
    (fun k : X.presheaf.stalk (D.π D.point) ⟶ D.Y.residueField (genericPoint D.Y) => k g)
    hmaps
  change D.residueEquiv
    (D.residueEquiv.symm ((D.π.residueFieldMap (genericPoint D.Y)).hom
      ((BerkovichPoint.specializationMap
        ((genericPoint_specializes D.point).map D.π.continuous)).hom g))) = _
  rw [D.residueEquiv.apply_symm_apply]
  exact h

/-- The original image point is the ACTUAL centre of every positive multiple of the
original divisor order; no properness of the structural base or centre certificate is used. -/
theorem ordVal_isCenter_image (f : X ⟶ Spec (.of ℂ)) (t : ℝ) (ht : 0 < t) :
    (D.ordVal f t ht).IsCenter (D.π D.point) := by
  let h := (genericPoint_specializes D.point).map D.π.continuous
  have hordNonneg (g : X.presheaf.stalk (D.π D.point))
      (hg : (BerkovichPoint.specializationMap h).hom g ≠ 0) :
      0 ≤ D.ord ((BerkovichPoint.specializationMap h).hom g) :=
    (ord_nonneg_iff_mem_range D hg).mpr
      ⟨(D.π.stalkMap D.point) g, (pullback_specializationMap D g).symm⟩
  refine ⟨h, ?_, ?_⟩
  · intro g
    let q := (BerkovichPoint.specializationMap h).hom g
    change 0 ≤ (D.ordVal f t ht).valAt q
    by_cases hq : q = 0
    · rw [hq, BerkovichPoint.valAt_zero]
      exact le_top
    rw [D.ordVal_valAt t ht hq]
    have hg : (0 : ℝ) ≤ D.ord q := by exact_mod_cast hordNonneg g hq
    exact_mod_cast mul_nonneg ht.le hg
  · intro g hg
    let q := (BerkovichPoint.specializationMap h).hom g
    change 0 < (D.ordVal f t ht).valAt q
    by_cases hq : q = 0
    · rw [hq, BerkovichPoint.valAt_zero]
      exact WithTop.coe_lt_top (0 : ℝ)
    have hne : D.ord q ≠ 0 := by
      intro hzord
      have hnorm := (Scheme.ord_eq_iff D.coheight_point
        ((map_ne_zero_iff _ D.pullback_injective).mpr hq)).mp hzord
      change Ring.ordFrac (D.Y.presheaf.stalk D.point) (D.pullback q) = 1 at hnorm
      rw [show D.pullback q = _ from pullback_specializationMap D g] at hnorm
      have hu := (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
        (K := D.Y.functionField)).mpr hnorm
      exact (IsLocalRing.notMem_maximalIdeal.mpr hu)
        (map_nonunit (D.π.stalkMap D.point).hom g hg)
    have hpos : 0 < D.ord q := lt_of_le_of_ne (hordNonneg g hq) hne.symm
    have hpos' : (0 : ℝ) < D.ord q := by exact_mod_cast hpos
    rw [D.ordVal_valAt t ht hq]
    exact_mod_cast mul_pos ht hpos'

end SGPT.NAPotential.DivisorValuationCenter
