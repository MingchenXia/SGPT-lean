import SGPT.NAPotential.DivisorValuationCenter
import SGPT.NAPotential.AffineDivisorFlattening

/-!
# Produced native divisor normal order on a smooth graph neighbourhood

Complete blueprint: `smooth-divisor-normal-order.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.SmoothDivisorNormalOrder

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich
open SGPT.Foundations.Schemes SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open SGPT.Foundations.Analysis.Pending
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f] [IsIntegral X]

include f m in
omit [IsSeparated f] [QuasiCompact f] [IsIntegral X] in
private theorem nativeLocallyNoetherian : IsLocallyNoetherian X := by
  let : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  exact LocallyOfFiniteType.isLocallyNoetherian f

local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance pointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The actual smooth scheme, its identity proper map and its actual codimension-one
point manufacture a prime divisor over the SAME smooth open. -/
def identityPrimeDivisor (z : X) (hz : Order.coheight z = 1) : PrimeDivisorOver X := by
  let : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine
    { Y := X
      π := 𝟙 X
      normal := fun x => SGPT.NAPotential.AlgPrimes2.isIntegrallyClosed_stalk f (m + 1) x
      point := z
      coheight_point := hz
      birational := ?_ }
  simpa using (Function.bijective_id : Function.Bijective
    (id : X.residueField (genericPoint X) → X.residueField (genericPoint X)))

/-- The centre of the actual identity prime is PRODUCED, even on a nonproper smooth open. -/
theorem identityPrimeDivisor_isCenter (z : X) (hz : Order.coheight z = 1) :
    ((identityPrimeDivisor f m z hz).ordVal f 1 one_pos).IsCenter z :=
  DivisorValuationCenter.ordVal_isCenter_image (identityPrimeDivisor f m z hz) f 1 one_pos

/-- The original identity-prime pullback cancels the actual generic residue map and
returns the SAME native germ in the actual native function field. -/
theorem identityPrimeDivisor_pullback_specialization
    (z : X) (hz : Order.coheight z = 1) (y : X) (h : genericPoint X ⤳ y)
    (g : X.presheaf.stalk y) :
    (identityPrimeDivisor f m z hz).pullback ((BerkovichPoint.specializationMap h).hom g) =
      algebraMap (X.presheaf.stalk y) X.functionField g := by
  let E := identityPrimeDivisor f m z hz
  apply E.residueEquiv.injective
  change E.residueEquiv (E.residueEquiv.symm
    ((Scheme.Hom.residueFieldMap (𝟙 X) (genericPoint X)).hom
      ((BerkovichPoint.specializationMap h).hom g))) = _
  rw [E.residueEquiv.apply_symm_apply, Scheme.residueFieldMap_id]
  rfl

/-- Every actual smooth codimension-one point produces analytic divisor coordinates
comparing native scheme order for EVERY nonzero native regular germ. No centre,
flattening, or order-comparison certificate is an input. -/
theorem exists_nativeNormalOrder {z : X} (hz : Order.coheight z = 1) :
    letI : IsLocallyNoetherian X := nativeLocallyNoetherian f m
    ∃ y : SchemeComplexPoint f, z ⤳ schemeComplexPointImage f y ∧
      ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
        ∀ g : X.presheaf.stalk (schemeComplexPointImage f y), g ≠ 0 →
          Scheme.ord (algebraMap (X.presheaf.stalk (schemeComplexPointImage f y))
            X.functionField g) z =
            ((normalOrder Ψ (stalkToModel f (m + 1) y g)).toNat : ℤ) := by
  let : IsLocallyNoetherian X := nativeLocallyNoetherian f m
  let E := identityPrimeDivisor f m z hz
  obtain ⟨y, hzy, Ψ, hord⟩ := AffineDivisorFlattening.exists_order_comparison_at_center
    f m E (identityPrimeDivisor_isCenter f m z hz) hz
  refine ⟨y, hzy, Ψ, fun g hg => ?_⟩
  have h := hord g hg
  let hs := SGPT.NAPotential.AlgPrimes.ordVal_support_specializes f E (schemeComplexPointImage f y)
  change Scheme.ord (E.pullback ((BerkovichPoint.specializationMap hs).hom g)) z = _ at h
  have hp := identityPrimeDivisor_pullback_specialization f m z hz _ hs g
  change E.pullback ((BerkovichPoint.specializationMap hs).hom g) = _ at hp
  rw [hp] at h
  exact h

private theorem native_ord_div {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    (z : T) {a b : T.functionField} (ha : a ≠ 0) (hb : b ≠ 0) :
    Scheme.ord (a / b) z = Scheme.ord a z - Scheme.ord b z := by
  have h := Scheme.ord_mul (x := z) (div_ne_zero ha hb) hb
  rw [div_mul_cancel₀ a hb] at h
  omega

/-- The SAME produced analytic coordinates compare every regular native germ and give
the signed normal order of EVERY nonzero rational function by an actual native fraction. -/
theorem exists_nativeNormalOrder_withFractions {z : X} (hz : Order.coheight z = 1) :
    letI : IsLocallyNoetherian X := nativeLocallyNoetherian f m
    ∃ y : SchemeComplexPoint f, z ⤳ schemeComplexPointImage f y ∧
      ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
        (∀ g : X.presheaf.stalk (schemeComplexPointImage f y), g ≠ 0 →
          Scheme.ord (algebraMap (X.presheaf.stalk (schemeComplexPointImage f y))
            X.functionField g) z = ((normalOrder Ψ (stalkToModel f (m + 1) y g)).toNat : ℤ)) ∧
        ∀ r : X.functionField, r ≠ 0 →
          ∃ a b : X.presheaf.stalk (schemeComplexPointImage f y), a ≠ 0 ∧ b ≠ 0 ∧
            r = algebraMap _ X.functionField a / algebraMap _ X.functionField b ∧
            Scheme.ord r z = ((normalOrder Ψ (stalkToModel f (m + 1) y a)).toNat : ℤ) -
              ((normalOrder Ψ (stalkToModel f (m + 1) y b)).toNat : ℤ) := by
  let : IsLocallyNoetherian X := nativeLocallyNoetherian f m
  obtain ⟨y, hzy, Ψ, hreg⟩ := exists_nativeNormalOrder f m hz
  refine ⟨y, hzy, Ψ, hreg, fun r hr => ?_⟩
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk (schemeComplexPointImage f y)) r
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, map_zero, zero_div] at hfrac
    exact hr hfrac.symm
  refine ⟨a, b, ha, hb0, hfrac.symm, ?_⟩
  have haK : algebraMap _ X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr ha
  have hbK : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr hb0
  rw [← hfrac, native_ord_div z haK hbK, hreg a ha, hreg b hb0]

end SGPT.NAPotential.SmoothDivisorNormalOrder
