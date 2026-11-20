import SGPT.NAPotential.TowerAlgRealize
import SGPT.NAPotential.DivDictComparison

/-!
# The algebraic half of the dictionary of prime divisors: reduction to one local comparison


Source `chapter_NApotential.tex`: the sentence after `def:NApotential:L975`
(*when `v = t ord_E` for some prime divisor `E` over `X`, `φ^An(v) = -t ν(φ, E)`*), used again in
`lma:psieqpsiprimeondiv` and `prop:anpreinf`.  For an *algebraic* prime divisor `D` over `X`
(`SGPT.NAPotential.Berkovich.PrimeDivisorOver X`: a codimension one point of a normal proper
birational model) the formal proof needs an analytic presentation `p` of a prime divisor over
`X(ℂ)` realizing `D` (`PrimeDivisorOver.IsRealizedBy`); the statement that one always exists is
`SGPT.NAPotential.Berkovich.AlgebraicPrimesRealized`.

TOWER-ALG attached to every analytic presentation `p`, point `y₀` of its hypersurface and
flattening `Φ₀` the *analytic* divisorial valuation `anDivVal p Φ₀ t` of `ℂ(X)` (through the
analytic order `stalkOrd p Φ₀` along the hypersurface of germs of `𝒪_{X,P₀}`, `P₀` the scheme
point of `π(y₀)`) and proved that `D` is realized by `p` as soon as `ord_D = anDivVal p Φ₀ 1` as
points of `X^An` (`isRealizedBy_of_ordVal_eq`).  This file reduces that equality of valuations of
`ℂ(X)` to a comparison on the single local ring `𝒪_{X,P₀}`:

* `berkovichPoint_eq_of_valAt_specializationMap_eq`: two semi-valuations of `X^An` whose support
  is the generic point of the integral scheme `X` and which agree on the image of one stalk
  `𝒪_{X,c}` are equal (`ℂ(X)` is the fraction field of `𝒪_{X,c}`);
* **`ordVal_eq_anDivVal_of_ord_eq_stalkOrd`**: if `ord_D(g) = ord_{E,y₀}(g^an ∘ π)` for every
  nonzero germ `g ∈ 𝒪_{X,P₀}`, then `ord_D = anDivVal p Φ₀ 1`, and `D` is realized by `p`
  (`isRealizedBy_of_ord_eq_stalkOrd`);
* `LocalOrderRealizations`, `AlgebraicDivisorialValuationsAnalytic`: the local and the
  valuation-level forms of the algebraic half of the dictionary, and the implications
  `LocalOrderRealizations → AlgebraicDivisorialValuationsAnalytic → AlgebraicPrimesRealized`
  (`algebraicPrimesRealized_of_localOrderRealizations`).

What remains for `AlgebraicPrimesRealized` is the geometric statement `LocalOrderRealizations`:
for every algebraic prime divisor `D` over `X`, an analytic presentation `p` and a point `y₀` of
its hypersurface at which the analytic orders of the germs of `𝒪_{X,P₀}` are the algebraic orders
`ord_D`.  See `AlgPrimesHypersurface` for the next reduction (a possibly singular
hypersurface on a smooth compact model suffices).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.CompactPrimeOver SGPT.NAPotential.Berkovich SGPT.NAPotential.TowerAlg
open DemaillyApproximantDivisorialLelong

/-! ### Semi-valuations of `ℂ(X)` are determined on one stalk -/

section Ext

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsIntegral X]

/-- Every element of `κ(η) = ℂ(X)` (`η` the generic point) is a quotient of images of germs at an
arbitrary point `c`: `ℂ(X)` is the fraction field of `𝒪_{X,c}`. -/
theorem exists_specializationMap_mul_eq (c : X) (h : genericPoint X ⤳ c)
    (x : X.residueField (genericPoint X)) :
    ∃ a b : X.presheaf.stalk c, b ≠ 0 ∧
      x * (BerkovichPoint.specializationMap h).hom b = (BerkovichPoint.specializationMap h).hom a := by
  obtain ⟨y, rfl⟩ := X.residue_surjective (genericPoint X) x
  obtain ⟨a, b, hb, hy⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk c) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hspec : ∀ g : X.presheaf.stalk c, (BerkovichPoint.specializationMap h).hom g =
      (X.residue (genericPoint X)).hom (algebraMap (X.presheaf.stalk c) X.functionField g) := by
    intro g
    rfl
  have hbne : algebraMap (X.presheaf.stalk c) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk c) X.functionField)).mpr hb0
  refine ⟨a, b, hb0, ?_⟩
  rw [hspec, hspec, ← map_mul, ← hy, div_mul_cancel₀ _ hbne]

/-- **Semi-valuations with generic support are determined on one stalk**: two points `v, w` of
`X^An` whose support is the generic point of the integral scheme `X` (valuations of `ℂ(X)`) and
which agree on the image of `𝒪_{X,c}` in `ℂ(X)` are equal. -/
theorem berkovichPoint_eq_of_valAt_specializationMap_eq {v w : BerkovichPoint f}
    (hv : v.support = genericPoint X) (hw : w.support = genericPoint X) {c : X}
    (hvc : v.support ⤳ c) (hwc : w.support ⤳ c)
    (h : ∀ g : X.presheaf.stalk c,
      v.valAt ((BerkovichPoint.specializationMap hvc).hom g) =
        w.valAt ((BerkovichPoint.specializationMap hwc).hom g)) :
    v = w := by
  obtain ⟨s, val⟩ := v
  obtain ⟨s', val'⟩ := w
  dsimp only at hv hw hvc hwc h
  subst hv hw
  congr 1
  let := residueComplexAlgebra f (genericPoint X)
  refine @SourceRealValuation.ext _ _ (residueComplexAlgebra f (genericPoint X)) val val'
    fun x => ?_
  obtain ⟨a, b, hb, hab⟩ := exists_specializationMap_mul_eq c hvc x
  have hinj : Function.Injective (BerkovichPoint.specializationMap hvc).hom := by
    intro g g' hgg
    have h1 : algebraMap (X.presheaf.stalk c) X.functionField g =
        algebraMap (X.presheaf.stalk c) X.functionField g' :=
      (X.residue (genericPoint X)).hom.injective hgg
    exact IsFractionRing.injective (X.presheaf.stalk c) X.functionField h1
  have hsb : (BerkovichPoint.specializationMap hvc).hom b ≠ 0 := by
    intro h0
    exact hb (hinj (h0.trans (map_zero _).symm))
  have hv1 := val.map_mul' x ((BerkovichPoint.specializationMap hvc).hom b)
  have hw1 := val'.map_mul' x ((BerkovichPoint.specializationMap hvc).hom b)
  rw [hab] at hv1 hw1
  have ha : val.toFun ((BerkovichPoint.specializationMap hvc).hom a) =
      val'.toFun ((BerkovichPoint.specializationMap hvc).hom a) := h a
  have hb' : val.toFun ((BerkovichPoint.specializationMap hvc).hom b) =
      val'.toFun ((BerkovichPoint.specializationMap hvc).hom b) := h b
  have hfin : val'.toFun ((BerkovichPoint.specializationMap hvc).hom b) ≠ ⊤ := fun htop =>
    hsb ((val'.eq_top_iff' _).mp htop)
  rw [← ha, hv1, hb'] at hw1
  exact WithTop.add_right_cancel hfin hw1

variable (f) in
/-- The support `π(η_Y)` of `ord_D` specializes to every point of `X`. -/
theorem ordVal_support_specializes (D : PrimeDivisorOver X) (c : X) :
    (D.ordVal f 1 one_pos).support ⤳ c := by
  rw [D.ordVal_support_eq_genericPoint 1 one_pos]
  exact TowerAlg.genericPoint_specializes c

end Ext

/-! ### The local comparison criterion -/

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance algPrimesValPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimesValPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPrimesValPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X]

/-- **The local comparison criterion.**  Let `D` be an algebraic prime divisor over `X` and `p` an
analytic presentation of a prime divisor `E` over `X(ℂ)`, with a point `y₀ ∈ E` and a flattening
`Φ₀` there.  If for every nonzero germ `g ∈ 𝒪_{X,P₀}` (`P₀` the scheme point of `π(y₀)`) the
algebraic order `ord_D(g)` is the analytic order of `g^an ∘ π` along `E` at `y₀`, then `ord_D` is
the analytic divisorial valuation `anDivVal p Φ₀ 1` as points of `X^An`. -/
theorem ordVal_eq_anDivVal_of_ord_eq_stalkOrd (D : PrimeDivisorOver X)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) {y₀ : p.model}
    (Φ₀ : DivisorFlattening (m := m) p.divisor y₀)
    (h : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀)), g ≠ 0 →
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f (p.projection y₀)))).hom g) : ℤ) =
        ((stalkOrd p Φ₀ g).toNat : ℤ)) :
    D.ordVal f 1 one_pos = anDivVal p Φ₀ 1 one_pos := by
  set c := schemeComplexPointImage f (p.projection y₀) with hc
  refine berkovichPoint_eq_of_valAt_specializationMap_eq (D.ordVal_support_eq_genericPoint 1 one_pos)
    (anDivVal_support p Φ₀ 1 one_pos) (ordVal_support_specializes f D c)
    (TowerAlg.genericPoint_specializes c) fun g => ?_
  -- injectivity of the specialization maps
  have hinj : ∀ {y : X} (hy : y ⤳ c), y = genericPoint X →
      Function.Injective (BerkovichPoint.specializationMap hy).hom := by
    intro y hy hyη
    subst hyη
    intro g g' hgg
    have h1 : algebraMap (X.presheaf.stalk c) X.functionField g =
        algebraMap (X.presheaf.stalk c) X.functionField g' :=
      (X.residue (genericPoint X)).hom.injective hgg
    exact IsFractionRing.injective (X.presheaf.stalk c) X.functionField h1
  by_cases hg : g = 0
  · subst hg
    rw [map_zero, map_zero]
    exact (D.ordVal f 1 one_pos).valAt_zero.trans (anDivVal p Φ₀ 1 one_pos).valAt_zero.symm
  · have hDg : (BerkovichPoint.specializationMap (ordVal_support_specializes f D c)).hom g ≠ 0 := by
      intro h0
      exact hg (hinj _ (D.ordVal_support_eq_genericPoint 1 one_pos) (h0.trans (map_zero _).symm))
    rw [D.ordVal_valAt 1 one_pos hDg, h g hg, one_mul]
    -- the analytic side
    have hval := toENNReal_valAt_anDivVal p Φ₀ 1 one_pos g
    have hnn := valAt_anDivVal_nonneg p Φ₀ 1 one_pos g
    have hfin := stalkOrd_ne_top p Φ₀ hg
    revert hval hnn
    generalize (anDivVal p Φ₀ 1 one_pos).valAt
      ((BerkovichPoint.specializationMap (TowerAlg.genericPoint_specializes c)).hom g) = a
    intro hval hnn
    induction a using WithTop.recTopCoe with
    | top =>
      rw [toENNReal_top, ENNReal.ofReal_one, one_mul] at hval
      exact absurd (ENat.toENNReal_eq_top.mp hval.symm) hfin
    | coe r =>
      rw [toENNReal_coe, ENNReal.ofReal_one, one_mul] at hval
      have hr : 0 ≤ r := WithTop.coe_le_coe.mp hnn
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hk] at hval
      rw [← hk, ENat.toNat_natCast]
      have h2 : ENNReal.ofReal r = ((k : ℝ≥0∞)) := hval
      have h3 := congrArg ENNReal.toReal h2
      rw [ENNReal.toReal_ofReal hr, ENNReal.toReal_natCast] at h3
      rw [h3]
      norm_cast

/-- **`D` is realized by `p` as soon as the orders agree on one stalk**
(`PrimeDivisorOver.IsRealizedBy`, through `isRealizedBy_of_ordVal_eq`). -/
theorem isRealizedBy_of_ord_eq_stalkOrd (E : ClosedProjectiveEmbedding f) (D : PrimeDivisorOver X)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) {y₀ : p.model}
    (Φ₀ : DivisorFlattening (m := m) p.divisor y₀)
    (h : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀)), g ≠ 0 →
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f (p.projection y₀)))).hom g) : ℤ) =
        ((stalkOrd p Φ₀ g).toNat : ℤ)) :
    D.IsRealizedBy m E p :=
  isRealizedBy_of_ordVal_eq E p Φ₀ (ordVal_eq_anDivVal_of_ord_eq_stalkOrd D p Φ₀ h)

/-! ### The reductions of `AlgebraicPrimesRealized` -/

variable (m) in
/-- **The valuation-level form of the algebraic half of the dictionary**: the divisorial valuation
`ord_D` of every algebraic prime divisor `D` over `X` is an analytic divisorial valuation
`anDivVal p Φ₀ 1` (the order along a smooth connected hypersurface of a modification of `X(ℂ)`).
(A statement; not proved here.) -/
def AlgebraicDivisorialValuationsAnalytic : Prop :=
  ∀ D : PrimeDivisorOver X, ∃ (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) (y₀ : p.model)
    (Φ₀ : DivisorFlattening (m := m) p.divisor y₀), D.ordVal f 1 one_pos = anDivVal p Φ₀ 1 one_pos

variable (m) in
/-- **The local form of the algebraic half of the dictionary**: for every algebraic prime divisor
`D` over `X` there are an analytic presentation `p` and a point `y₀` of its hypersurface (with a
flattening `Φ₀`) at which the analytic order along the hypersurface of `g^an ∘ π` is `ord_D(g)`,
for every nonzero germ `g ∈ 𝒪_{X,P₀}`.  (A statement; not proved here.) -/
def LocalOrderRealizations : Prop :=
  ∀ D : PrimeDivisorOver X, ∃ (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) (y₀ : p.model)
    (Φ₀ : DivisorFlattening (m := m) p.divisor y₀),
    ∀ g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀)), g ≠ 0 →
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f (p.projection y₀)))).hom g) : ℤ) =
        ((stalkOrd p Φ₀ g).toNat : ℤ)

theorem algebraicDivisorialValuationsAnalytic_of_localOrderRealizations
    (h : LocalOrderRealizations (f := f) m) : AlgebraicDivisorialValuationsAnalytic (f := f) m := by
  intro D
  obtain ⟨p, y₀, Φ₀, hD⟩ := h D
  exact ⟨p, y₀, Φ₀, ordVal_eq_anDivVal_of_ord_eq_stalkOrd D p Φ₀ hD⟩

/-- **`AlgebraicPrimesRealized` reduces to the valuation-level statement.** -/
theorem algebraicPrimesRealized_of_algebraicDivisorialValuationsAnalytic
    (E : ClosedProjectiveEmbedding f) (h : AlgebraicDivisorialValuationsAnalytic (f := f) m) :
    AlgebraicPrimesRealized (f := f) m E := by
  intro D
  obtain ⟨p, y₀, Φ₀, hD⟩ := h D
  exact ⟨p, isRealizedBy_of_ordVal_eq E p Φ₀ hD⟩

/-- **`AlgebraicPrimesRealized` reduces to one local comparison of orders.** -/
theorem algebraicPrimesRealized_of_localOrderRealizations (E : ClosedProjectiveEmbedding f)
    (h : LocalOrderRealizations (f := f) m) : AlgebraicPrimesRealized (f := f) m E :=
  algebraicPrimesRealized_of_algebraicDivisorialValuationsAnalytic E
    (algebraicDivisorialValuationsAnalytic_of_localOrderRealizations h)

end SGPT.NAPotential.AlgPrimes

end
