import SGPT.Checks.Comparison.BJCharge2TcDiv
import SGPT.Checks.Comparison.ThinApprox.BJPairEnergy

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# `Scheme.ord` versus `ordPoint`, and components of the central fibre (lane BJ-CHARGE, R8)

Source: [BJ22] (`references/bj22-trivval`), §2.2 and Lemma `lem:tcdiv`; towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-charge3.tex`.

the Rees theorems (`reesCenter`, `exists_reesComponent`) describe a divisorial point
as `β · ord_c` with Mathlib's order of vanishing `Scheme.ord`; the divisorial points
`ordPoint fY z` are built from `IsDiscreteValuationRing.addVal`. This file identifies them.

* `ord_algebraMap_eq_addVal`, `dvrFracAddVal_eq_ord`: on a DVR stalk of codimension one,
  `Scheme.ord` is the normalized valuation `addVal` (Mathlib's `Ring.ord_eq_addVal`);
* `ordPoint_valAt_residue`: **`ord_z(F) = Scheme.ord F z`** for the point `ordPoint fY z`;
* `eq_rescalePoint_ordPoint`: a semi-valuation of the function field equal to
  `β · Scheme.ord(-, z)` is `rescalePoint (ordPoint fY z) β`;
* `eq_of_specializes_of_coheight_eq_one`, `closure_singleton_maximal_of_coheight_eq_one`,
  `closure_singleton_mem_components`: a point of codimension one
  of the normalized model lying in the central fibre is the generic point of an irreducible
  component of the central fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BerkovichPoint
open SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJModel3

/-! ### `Scheme.ord` on a DVR stalk -/

section ordMatch

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- On a DVR stalk of codimension one, `Scheme.ord` of a germ is its normalized valuation. -/
theorem ord_algebraMap_eq_addVal {z : Y} (hz : coheight z = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk z)] {r : Y.presheaf.stalk z} (hr : r ≠ 0) :
    natTop (IsDiscreteValuationRing.addVal _ r) =
      ((Scheme.ord (algebraMap _ Y.functionField r) z : ℝ) : WithTop ℝ) := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal (Y.presheaf.stalk z) r = k := by
    have h : IsDiscreteValuationRing.addVal (Y.presheaf.stalk z) r ≠ ⊤ :=
      fun h => hr (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h
    exact ⟨k, hk.symm⟩
  have hne : algebraMap _ Y.functionField r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hr
  have hord : Scheme.ord (algebraMap _ Y.functionField r) z = k := by
    rw [Scheme.ord_eq_iff hz hne]
    change Ring.ordFrac _ _ = _
    rw [Ring.ordFrac_eq_ord _ hr,
      Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hr) (n := k)
        (by rw [Ring.ord_eq_addVal, hk])]
  rw [hk, natTop_coe, hord]
  norm_cast

/-- On a DVR stalk of codimension one, BJ-PAIR's `ord_z` on the function field is `Scheme.ord`. -/
theorem dvrFracAddVal_eq_ord {z : Y} (hz : coheight z = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk z)] {F : Y.functionField} (hF : F ≠ 0) :
    dvrFracAddVal z F = ((Scheme.ord F z : ℝ) : WithTop ℝ) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Y.presheaf.stalk z) F
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap _ Y.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have haK : algebraMap _ Y.functionField a ≠ 0 := fun h => hF (by rw [h, zero_div])
  have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
  have hmul : algebraMap _ Y.functionField a / algebraMap _ Y.functionField b *
      algebraMap _ Y.functionField b = algebraMap _ Y.functionField a := div_mul_cancel₀ _ hbK
  have h1 := congrArg (dvrFracAddVal z) hmul
  rw [AddValuation.map_mul, dvrFracAddVal_algebraMap, dvrFracAddVal_algebraMap, dvrAddVal_apply,
    dvrAddVal_apply, ord_algebraMap_eq_addVal hz ha0, ord_algebraMap_eq_addVal hz hb0] at h1
  have h2 := Scheme.ord_mul (x := z) (div_ne_zero haK hbK) hbK
  rw [hmul] at h2
  cases hv : dvrFracAddVal z (algebraMap _ Y.functionField a / algebraMap _ Y.functionField b) with
  | top => rw [hv, WithTop.top_add] at h1; exact absurd h1.symm WithTop.coe_ne_top
  | coe r =>
    rw [hv, ← WithTop.coe_add, WithTop.coe_eq_coe] at h1
    rw [WithTop.coe_eq_coe, h2] at *
    push_cast at h1
    linarith

variable (fY : Y ⟶ Spec (.of ℂ))

/-- **`ord_z = Scheme.ord(-, z)`**: the values of BJ-PAIR's divisorial point `ordPoint fY z` on
the function field are Mathlib's orders of vanishing. -/
theorem ordPoint_valAt_residue {z : Y} (hz : coheight z = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk z)] {F : Y.functionField} (hF : F ≠ 0) :
    (ordPoint fY z).valAt ((Y.residue (genericPoint Y)).hom F) =
      ((Scheme.ord F z : ℝ) : WithTop ℝ) := by
  change dvrFracAddVal z (genericResidueEquiv.symm (genericResidueEquiv F)) = _
  rw [RingEquiv.symm_apply_apply]
  exact dvrFracAddVal_eq_ord hz hF

/-- **A multiple of `Scheme.ord(-, z)` is a rescaling of `ordPoint`**: a semi-valuation supported
at the generic point whose values on `ℂ(Y)^×` are `β · Scheme.ord(-, z)` is
`rescalePoint (ordPoint fY z) β`. -/
theorem eq_rescalePoint_ordPoint {z : Y} (hz : coheight z = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk z)] (val : ResidueValuation fY (genericPoint Y))
    {β : ℝ} (hβ : 0 < β)
    (h : ∀ F : Y.functionField, F ≠ 0 → val ((Y.residue (genericPoint Y)).hom F) =
      ((β * (Scheme.ord F z : ℝ) : ℝ) : WithTop ℝ)) :
    (⟨genericPoint Y, val⟩ : BerkovichPoint fY) = rescalePoint (ordPoint fY z) hβ := by
  let := residueComplexAlgebra fY (genericPoint Y)
  have hval : val = @SourceRealValuation.rescale _ _ (residueComplexAlgebra fY (genericPoint Y))
      (ordPoint fY z).val β hβ := by
    ext g
    obtain ⟨F, rfl⟩ := (genericResidueEquiv (Y := Y)).surjective g
    by_cases hF : F = 0
    · subst hF
      rw [map_zero, SourceRealValuation.map_zero, SourceRealValuation.map_zero]
    · rw [genericResidueEquiv_apply, h F hF, SourceRealValuation.rescale_apply]
      change _ = scaleTop β ((ordPoint fY z).valAt _)
      rw [ordPoint_valAt_residue fY hz hF, scaleTop_coe]
  change BerkovichPoint.mk (genericPoint Y) val = BerkovichPoint.mk (genericPoint Y) _
  rw [hval]

end ordMatch

/-! ### Components of the central fibre -/

section component

/-- **A codimension-one point is a maximal point of every set avoiding the generic point**: on an
integral scheme, a point of a set `S` not containing the generic point that specializes to a point
of coheight one is equal to it. -/
theorem eq_of_specializes_of_coheight_eq_one {Y : Scheme.{0}} [IsIntegral Y] {S : Set Y}
    (hS : genericPoint Y ∉ S) {z : Y} (hz : coheight z = 1) {y : Y} (hy : y ∈ S)
    (hyz : y ⤳ z) : y = z := by
  by_contra hne
  have hlt : z < y := by
    refine lt_of_le_not_ge ?_ fun hle => hne ?_
    · rw [Scheme.le_iff_specializes]
      exact hyz
    · rw [Scheme.le_iff_specializes] at hle
      exact (hyz.antisymm hle).eq
  have h1 := coheight_add_one_le hlt
  rw [hz] at h1
  have h0 : coheight y = 0 := by
    by_contra h0
    have h2 : (1 : ℕ∞) ≤ coheight y := Order.one_le_iff_ne_zero.mpr h0
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h2 le_rfl).trans h1
    exact absurd h3 (by norm_num)
  have hgen : y = genericPoint Y := eq_genericPoint_of_coheight_eq_zero h0
  exact hS (hgen ▸ hy)

/-- **On an integral scheme, a point of coheight one of a closed set `S` avoiding the generic
point is the generic point of an irreducible component of `S`**: `closure {z}` is a maximal
irreducible subset of `S`. -/
theorem closure_singleton_maximal_of_coheight_eq_one {Y : Scheme.{0}} [IsIntegral Y] {S : Set Y}
    (hSc : IsClosed S) (hS : genericPoint Y ∉ S) {z : Y} (hz : coheight z = 1) (hzS : z ∈ S) :
    closure ({z} : Set Y) ⊆ S ∧
      ∀ T : Set Y, IsIrreducible T → closure {z} ⊆ T → T ⊆ S → T = closure {z} := by
  have hsub : closure ({z} : Set Y) ⊆ S := closure_minimal (Set.singleton_subset_iff.mpr hzS) hSc
  refine ⟨hsub, fun T hT hzT hTS => le_antisymm ?_ hzT⟩
  obtain ⟨y, hy⟩ := QuasiSober.sober hT.closure isClosed_closure
  have hyS : y ∈ S := closure_minimal hTS hSc hy.mem
  have hyz : y ⤳ z := by
    rw [specializes_iff_mem_closure, hy.def]
    exact subset_closure (hzT (subset_closure (Set.mem_singleton z)))
  have hyz' := eq_of_specializes_of_coheight_eq_one hS hz hyS hyz
  subst hyz'
  calc T ⊆ closure T := subset_closure
    _ = closure {y} := hy.def.symm

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable {𝔠 : FlagIdeal X} {c₀ : ℤ}

/-- **A codimension-one point of the central fibre is the generic point of an irreducible
component of the central fibre** of the normalized model `ν : 𝒳̃ → 𝒳`: `closure {z}` is a
maximal irreducible subset of `ν⁻¹(𝒳₀)`. -/
theorem closure_singleton_mem_components {z : normModel p 𝔠 c₀} (hz : coheight z = 1)
    (hzc : normModelν p 𝔠 c₀ z ∈ centralFibre p 𝔠 c₀) :
    closure ({z} : Set (normModel p 𝔠 c₀)) ⊆ normModelν p 𝔠 c₀ ⁻¹' centralFibre p 𝔠 c₀ ∧
      ∀ T : Set (normModel p 𝔠 c₀), IsIrreducible T →
        closure {z} ⊆ T → T ⊆ normModelν p 𝔠 c₀ ⁻¹' centralFibre p 𝔠 c₀ →
          T = closure {z} :=
  closure_singleton_maximal_of_coheight_eq_one
    (((centralIdeal p).support.isClosed.preimage (flagModelπ p 𝔠 c₀).continuous).preimage
      (normModelν p 𝔠 c₀).continuous)
    (genericPoint_normModel_not_mem 𝔠 c₀) hz hzc

end component

end SGPT.NAPotential.ThinApprox.BJ
