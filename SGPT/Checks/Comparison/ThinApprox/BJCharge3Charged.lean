import SGPT.Checks.Comparison.ThinApprox.BJCharge3Model
import SGPT.Checks.Comparison.ThinApprox.BJPair3Comparison
import SGPT.Foundations.Envelope.Berkovich.SchemeNormalizationDominantLift

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
# Charging divisorial points modulo the cycle formula and relative ampleness (BJ-CHARGE, R8(e))

Source: [BJ22] (`references/bj22-trivval`), `equ:mixedMAPL` (the Monge–Ampère measure of a PL
function `φ_D` is `Σ_E b_E ((ω + D)|_E)^n δ_{v_E}`), `lem:relamp` and the proof of
`thm:BJappseq` (Corollary 12.18) of `chapter_NApotential.tex`. Blueprint: `claude-bj-charge3.tex`.

Lane BJ-PAIR reduced `thm:BJappseq` to the charging of the divisorial points by the energy pairings
of ample classes (`bjAppSeq_of_charging`). This file proves that charging from two standard facts
of intersection theory, stated as hypotheses:

* `CycleLowerBound n`: on an integral projective `Y` of dimension `≤ n + 1`, for an effective
  Cartier divisor `K`, a class `θ` pulled back along `ρ : Y ⟶ Y₀` and nef on `K`, and a point `z`
  of codimension one with a DVR as local ring, `(𝒪(K) ⋅ (ρ^*θ)^n) ≥ ord_z(K) · (θ|_Z)^n` for the
  closure `Z` of `ρ(z)` (the cycle formula `[K] = Σ ord_E(K) [E]`, nonnegativity of the other terms
  and the projection formula for `closure {z} ⟶ Z`);
* `RelAmplePositive p n ω`: every good model carries a vertical divisor `D` with `π^*ω + D` nef on
  the central fibre and of positive top self-intersection on every component of the central fibre
  of the normalized model ([BJ22, `lem:relamp`]: `π^*ω + D` relatively ample).

Main results:

* `fn_mem_plSubmodule`, `exists_bound_fn`: functions of combinations of flag data are bounded PL
  functions;
* `normLift_eq`: lifts of a field-valued point to the normalized model are unique when they hit
  the generic point;
* `exists_effective_ordPoint`: the `FDiv.exists_effective` with the divisorial value of
  the effective divisor `K` at a Rees point: `ord_z(K) = β⁻¹ N φ_D(v)`;
* `isCharged_of_cycleLowerBound`: **every divisorial point is charged** by the energy pairing of
  every ample class;
* `bjAppSeq_of_cycleLowerBound`: **`thm:BJappseq`** from the two hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BerkovichPoint
open SGPT.NAPotential.BJCharge SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJEnergy SGPT.NAPotential.BJHodge
open FlagIdealBound
open scoped ENNReal

/-! ### The cycle lower bound -/

/-- **The cycle lower bound** (Kleiman's intersection theory: `[K] = Σ_E ord_E(K) [E]` for an
effective Cartier divisor on an integral scheme, nonnegativity of the terms against classes nef
on `K`, and the projection formula): on an integral projective `Y` of dimension `≤ n + 1` with
a morphism `ρ : Y ⟶ Y₀`, an invertible ideal sheaf `K`, a class `θ` of `Y₀` with `ρ^*θ` nef on
`V(K)`, a point `z` of codimension one with a DVR as local ring and a closed integral subscheme
`Z ⊆ Y₀` with generic point `ρ(z)`: `ord_z(K) · (θ|_Z)^n ≤ (𝒪(K) ⋅ (ρ^*θ)^n)_Y`. -/
def CycleLowerBound (n : ℕ) : Prop :=
  ∀ (Y Y₀ : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [Y.IsSeparated] [CompactSpace Y₀]
    [Y₀.IsSeparated] (q : Y ⟶ Spec (.of ℂ)) [IsProjective q] (q₀ : Y₀ ⟶ Spec (.of ℂ))
    [IsProjective q₀] (ρ : Y ⟶ Y₀), ρ ≫ q₀ = q →
    ∀ (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ)) (K : Y.IdealSheafData) (hK : K.IsInvertible)
      (θ : PicQ Y₀), picPullbackQ ρ θ ∈ relNefCone q (K.support : Set Y) →
    ∀ (z : Y) [IsDiscreteValuationRing (Y.presheaf.stalk z)], coheight z = 1 →
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated] (ι : Z ⟶ Y₀)
      [IsClosedImmersion ι] [IsProjective (ι ≫ q₀)], Set.range ι = closure {ρ z} →
    ∀ hdimZ : topologicalKrullDim Z ≤ n,
      (ordIdeal (K.stalkIdeal z)).toReal *
          ((interFormQ (ι ≫ q₀) n hdimZ (Scheme.Modules.unitObj Z)
            (Multiset.replicate n (picPullbackQ ι θ)) : ℚ) : ℝ) ≤
        ((interFormQ q (n + 1) hdim (Scheme.Modules.unitObj Y)
          (picQ ⟨cartierLine K, cartierLine_isInvertible hK⟩ ::ₘ
            Multiset.replicate n (picPullbackQ ρ θ)) : ℚ) : ℝ)

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable (p) in
/-- **Relatively ample vertical divisors** ([BJ22, `lem:relamp`] and the positivity of ample
classes on subvarieties): every good model `(𝔠, c₀)` carries a combination `D` of flag data with
`π^*ω + D` nef on the central fibre and with positive top self-intersection on (an integral closed
subscheme supported on) the closure of every codimension-one point of the central fibre of the
normalized model. -/
def RelAmplePositive (n : ℕ) (ω : PicQ X) : Prop :=
  ∀ (𝔠 : FlagIdeal X) (c₀ : ℤ), IsGoodModel p 𝔠 c₀ → ∃ D : FDiv p 𝔠 c₀,
    omegaPullback 𝔠 c₀ ω + FDiv.cls D ∈
      relNefCone (flagModelStructure p 𝔠 c₀) (centralFibre p 𝔠 c₀) ∧
    ∀ z : normModel p 𝔠 c₀, coheight z = 1 → normModelν p 𝔠 c₀ z ∈ centralFibre p 𝔠 c₀ →
      ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : CompactSpace Z) (_ : Z.IsSeparated)
        (ι : Z ⟶ normModel p 𝔠 c₀) (_ : IsClosedImmersion ι)
        (_ : IsProjective (ι ≫ normModelStructure p 𝔠 c₀)) (hdimZ : topologicalKrullDim Z ≤ n),
        Set.range ι = closure {z} ∧
        0 < interFormQ (ι ≫ normModelStructure p 𝔠 c₀) n hdimZ (Scheme.Modules.unitObj Z)
          (Multiset.replicate n (picPullbackQ ι (picPullbackQ (normModelν p 𝔠 c₀)
            (omegaPullback 𝔠 c₀ ω + FDiv.cls D))))

/-! ### Functions of flag data -/

section fdiv

variable {𝔠 : FlagIdeal X} {c₀ : ℤ}

omit [IsIntegral X] in
/-- The function of a combination of flag data is PL. -/
theorem fn_mem_plSubmodule (D : FDiv p 𝔠 c₀) : FDiv.fn D ∈ plSubmodule p := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add D₁ D₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | single e q =>
    rw [FDiv.fn_single]
    refine Submodule.smul_mem _ q ?_
    have h : e.vert.fn = (fun _ => ((e.bound : ℚ) : ℝ)) - e.ideal.phi := by
      funext v
      rw [FlagDatum.fn_vert, Pi.sub_apply]
      push_cast
      rfl
    rw [h]
    exact Submodule.sub_mem _ (const_mem_plSubmodule (f := p) (e.bound : ℚ))
      (phi_mem_plSubmodule (f := p) e.ideal)

omit [IsIntegral X] in
/-- The function of a combination of flag data is bounded. -/
theorem exists_bound_fn (D : FDiv p 𝔠 c₀) :
    ∃ R : ℚ, ∀ v : BerkovichPoint p, |FDiv.fn D v| ≤ R := by
  induction D using Finsupp.induction_linear with
  | zero => exact ⟨0, fun v => by simp⟩
  | add D₁ D₂ h₁ h₂ =>
    obtain ⟨R₁, hR₁⟩ := h₁
    obtain ⟨R₂, hR₂⟩ := h₂
    refine ⟨R₁ + R₂, fun v => ?_⟩
    rw [map_add, Pi.add_apply]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add (hR₁ v) (hR₂ v))
  | single e q =>
    obtain ⟨a, ha⟩ := e.ideal.exists_eq_top
    refine ⟨|q| * (e.bound - a), fun v => ?_⟩
    rw [FDiv.fn_single, Pi.smul_apply, Rat.smul_def, abs_mul]
    have h0 := FlagDatum.fn_vert_nonneg e v
    have h1 : e.vert.fn v ≤ e.bound - a := by
      rw [FlagDatum.fn_vert]
      have := e.ideal.le_phi v (ha a le_rfl)
      linarith
    rw [abs_of_nonneg h0]
    push_cast
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

end fdiv

/-! ### Uniqueness of normalized lifts -/

section lift

variable {𝔠 : FlagIdeal X} {c₀ : ℤ}

/-- **Lifts to the normalized model hitting the generic point are unique**: the normalization is
an isomorphism over a dense open subset. -/
theorem normLift_eq {L : Type} [Field L] (a b : Spec (.of L) ⟶ normModel p 𝔠 c₀)
    (hab : a ≫ normModelν p 𝔠 c₀ = b ≫ normModelν p 𝔠 c₀)
    (hb : normModelν p 𝔠 c₀ (fieldPt b) = genericPoint (flagModel p 𝔠 c₀)) : a = b := by
  let := productLine_isIntegral_of_isProjective p
  let ν := normModelν p 𝔠 c₀
  obtain ⟨V, hVne, hiso⟩ := exists_isIso_normModelν_restrict p 𝔠 c₀
  have hηV : genericPoint (flagModel p 𝔠 c₀) ∈ V :=
    ((genericPoint_spec (flagModel p 𝔠 c₀)).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  have hbV : fieldPt b ∈ ν ⁻¹ᵁ V := by
    change ν (fieldPt b) ∈ V
    rw [hb]
    exact hηV
  have haV : fieldPt a ∈ ν ⁻¹ᵁ V := by
    change (a ≫ ν) (closedPoint L) ∈ V
    rw [hab]
    exact hbV
  have hra : Set.range a ⊆ Set.range (ν ⁻¹ᵁ V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : x = closedPoint L := Subsingleton.elim _ _
    subst this
    exact haV
  have hrb : Set.range b ⊆ Set.range (ν ⁻¹ᵁ V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : x = closedPoint L := Subsingleton.elim _ _
    subst this
    exact hbV
  have ha := IsOpenImmersion.lift_fac (ν ⁻¹ᵁ V).ι a hra
  have hb' := IsOpenImmersion.lift_fac (ν ⁻¹ᵁ V).ι b hrb
  have h1 : IsOpenImmersion.lift (ν ⁻¹ᵁ V).ι a hra ≫ (ν ∣_ V) =
      IsOpenImmersion.lift (ν ⁻¹ᵁ V).ι b hrb ≫ (ν ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, ← Category.assoc, ha, hb']
    exact hab
  have h2 := (cancel_mono (ν ∣_ V)).mp h1
  rw [← ha, ← hb', h2]

end lift

/-! ### Effective divisors with their divisorial values -/

section effective

variable {𝔠 : FlagIdeal X} {c₀ : ℤ}

/-- Divisorial values of `ℕ`-combinations of flag data at a point where the values of flag ideals
are known. -/
theorem idealVal_idealN_of_formula (z : normModel p 𝔠 c₀)
    [IsDiscreteValuationRing ((normModel p 𝔠 c₀).presheaf.stalk z)] {C : ℝ≥0∞}
    {v : BerkovichPoint p}
    (hz : ∀ (𝔟 : FlagIdeal X) (b : ℤ), IsWeightBound 𝔟 b →
      (ordPoint (normModelStructure p 𝔠 c₀) z).idealVal
        ((flagSheaf p 𝔟 b).comap (normModelπ p 𝔠 c₀)) = C * ENNReal.ofReal (b - 𝔟.phi v))
    (n : FlagDatum p 𝔠 c₀ →₀ ℕ) :
    (ordPoint (normModelStructure p 𝔠 c₀) z).idealVal (idealN n) =
      C * ENNReal.ofReal (FDiv.fn (natToRat n) v) := by
  classical
  rw [idealN, fn_natToRat]
  have hnn : ∀ e ∈ n.support, 0 ≤ (n e : ℝ) * (e.bound - e.ideal.phi v) := fun e _ =>
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (e.ideal.phi_le v e.isWeightBound))
  rw [ENNReal.ofReal_sum_of_nonneg hnn, Finset.mul_sum]
  generalize n.support = s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, Scheme.IdealSheafData.one_eq_top,
      BerkovichPoint.idealVal_top]
  | insert e s he ih =>
    rw [Finset.prod_insert he, Finset.sum_insert he, BerkovichPoint.idealVal_mul, ih,
      idealVal_pow, vert_comap_eq, hz e.ideal e.bound e.isWeightBound,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    ring

/-- **Effective divisors with their values at a Rees point** (lane BJ-PAIR's
`FDiv.exists_effective`, with the value): if `φ_D ≥ 0`, a positive multiple `N • ν^*[𝒪(D)]` is
`-[K]` for an invertible ideal sheaf `K` supported in the central fibre, and at a point `z` where
`ord_z((t^b 𝔟) · 𝒪) = C (b - φ_𝔟(v))` for all flag ideals, `ord_z(K) = C · N φ_D(v)`. -/
theorem exists_effective_ordPoint
    (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c₀)).IsInvertible)
    (D : FDiv p 𝔠 c₀) (hD : 0 ≤ FDiv.fn D) (z : normModel p 𝔠 c₀)
    [IsDiscreteValuationRing ((normModel p 𝔠 c₀).presheaf.stalk z)] {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {v : BerkovichPoint p}
    (hz : ∀ (𝔟 : FlagIdeal X) (b : ℤ), IsWeightBound 𝔟 b →
      (ordPoint (normModelStructure p 𝔠 c₀) z).idealVal
        ((flagSheaf p 𝔟 b).comap (normModelπ p 𝔠 c₀)) = C * ENNReal.ofReal (b - 𝔟.phi v)) :
    ∃ (N : ℕ) (K : (normModel p 𝔠 c₀).IdealSheafData) (hK : K.IsInvertible), 0 < N ∧
      (K.support : Set (normModel p 𝔠 c₀)) ⊆ normModelν p 𝔠 c₀ ⁻¹' centralFibre p 𝔠 c₀ ∧
      (N : ℚ) • FDiv.ncls D = -picQ ⟨K.toModules, hK.isInvertibleModule_toModules⟩ ∧
      (ordPoint (normModelStructure p 𝔠 c₀) z).idealVal K =
        C * ENNReal.ofReal (N * FDiv.fn D v) := by
  obtain ⟨N, m, hN, hm⟩ := exists_nsmul_eq_intCast D
  rw [intCast_eq_sub] at hm
  set n := m.mapRange Int.toNat (by simp)
  set n' := (-m).mapRange Int.toNat (by simp)
  have hfnv : ∀ w : BerkovichPoint p, FDiv.fn (natToRat n) w - FDiv.fn (natToRat n') w =
      N * FDiv.fn D w := by
    intro w
    have h1 := congrFun (congrArg FDiv.fn hm) w
    rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, Rat.smul_def, Rat.cast_natCast] at h1
    linarith
  have hfn : FDiv.fn (natToRat n') ≤ FDiv.fn (natToRat n) := by
    intro w
    have h2 := hD w
    have h3 : (0 : ℝ) ≤ (N : ℝ) * FDiv.fn D w := mul_nonneg (Nat.cast_nonneg _) h2
    have := hfnv w
    simp only [Pi.zero_apply] at h2
    linarith
  have hle := idealN_le_of_fn_le h0 n n' hfn
  have hJ := idealN_isInvertible n
  have hJ' := idealN_isInvertible n'
  refine ⟨N, (idealN n).colon (idealN n'), colon_isInvertible hJ hJ' hle, hN,
    (support_colon_subset hJ hJ' hle).trans (support_idealN_subset n), ?_, ?_⟩
  · have hmul := eq_mul_colon hJ hJ' hle
    have hcls : FDiv.ncls ((N : ℚ) • D) =
        -picQ ⟨(idealN n).toModules, hJ.isInvertibleModule_toModules⟩ +
          picQ ⟨(idealN n').toModules, hJ'.isInvertibleModule_toModules⟩ := by
      rw [hm, map_sub, ncls_natToRat, ncls_natToRat, sub_neg_eq_add]
    rw [← map_smul, hcls]
    have key : picQ ⟨(idealN n).toModules, hJ.isInvertibleModule_toModules⟩ =
        picQ ⟨(idealN n').toModules, hJ'.isInvertibleModule_toModules⟩ +
          picQ ⟨((idealN n).colon (idealN n')).toModules,
            (colon_isInvertible hJ hJ' hle).isInvertibleModule_toModules⟩ := by
      have e1 : picQ ⟨(idealN n).toModules, hJ.isInvertibleModule_toModules⟩ =
          picQ ⟨((idealN n') * (idealN n).colon (idealN n')).toModules,
            (hJ'.mul (colon_isInvertible hJ hJ' hle)).isInvertibleModule_toModules⟩ :=
        picQ_toModules_congr hmul _ _
      rw [e1, picQ, picQ, picQ, lineCls_toModules_mul hJ' (colon_isInvertible hJ hJ' hle),
        TensorProduct.tmul_add]
    rw [key]
    abel
  · have hmul := eq_mul_colon hJ hJ' hle
    have hval := congrArg (ordPoint (normModelStructure p 𝔠 c₀) z).idealVal hmul
    rw [BerkovichPoint.idealVal_mul, idealVal_idealN_of_formula z hz,
      idealVal_idealN_of_formula z hz] at hval
    have hn0 : 0 ≤ FDiv.fn (natToRat n') v := fn_natToRat_nonneg n' v
    have hdiff : 0 ≤ (N : ℝ) * FDiv.fn D v := mul_nonneg (Nat.cast_nonneg _) (hD v)
    have hsplit : C * ENNReal.ofReal (FDiv.fn (natToRat n) v) =
        C * ENNReal.ofReal (FDiv.fn (natToRat n') v) + C * ENNReal.ofReal (N * FDiv.fn D v) := by
      rw [← mul_add, ← ENNReal.ofReal_add hn0 hdiff, ← hfnv v]
      ring_nf
    rw [hsplit] at hval
    exact ((ENNReal.add_right_inj (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)).mp hval).symm

end effective

/-! ### The charging inequality -/

section charging

/-- At a Rees point `z` of the central fibre of a good model, the scale satisfies `β⁻¹ ≥ 1`:
`β⁻¹ = ord_z(𝒳₀)` is a positive integer. -/
theorem one_le_inv_of_rees {𝔠 : FlagIdeal X} {c₀ : ℤ}
    (h0 : ((centralIdeal p).comap (flagModelπ p 𝔠 c₀)).IsInvertible) (z : normModel p 𝔠 c₀)
    [IsDiscreteValuationRing ((normModel p 𝔠 c₀).presheaf.stalk z)]
    (hzc : normModelπ p 𝔠 c₀ z ∈ ((centralIdeal p).support : Set (productLine p)))
    {β : ℝ} {v : BerkovichPoint p}
    (hz : ∀ (𝔟 : FlagIdeal X) (b : ℤ), IsWeightBound 𝔟 b →
      (ordPoint (normModelStructure p 𝔠 c₀) z).idealVal
        ((flagSheaf p 𝔟 b).comap (normModelπ p 𝔠 c₀)) =
          ENNReal.ofReal β⁻¹ * ENNReal.ofReal (b - 𝔟.phi v)) : 1 ≤ β⁻¹ := by
  have hw : IsWeightBound (FlagIdeal.monomial X 0) 1 :=
    (isWeightBound_monomial 0).mono (by norm_num)
  have h := hz _ 1 hw
  rw [flagSheaf_monomial_zero_one, FlagIdeal.phi_monomial] at h
  have hinv : ((centralIdeal p).comap (normModelπ p 𝔠 c₀)).IsInvertible := by
    rw [normModelπ, Scheme.IdealSheafData.comap_comp]
    exact isInvertible_comap_normModelν p 𝔠 c₀ h0
  have hmem : z ∈ ((centralIdeal p).comap (normModelπ p 𝔠 c₀)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hzc
  have hpos := idealVal_ordPoint_pos (normModelStructure p 𝔠 c₀) z hmem
  have hfin := idealVal_ordPoint_ne_top (normModelStructure p 𝔠 c₀) z hinv
  rw [idealVal_ordPoint, ordIdeal_eq] at hpos hfin h
  cases ha : IsDiscreteValuationRing.addVal ((normModel p 𝔠 c₀).presheaf.stalk z)
      (Submodule.IsPrincipal.generator
        (((centralIdeal p).comap (normModelπ p 𝔠 c₀)).stalkIdeal z)) with
  | top => rw [ha] at hfin; exact absurd rfl hfin
  | coe k =>
    rw [ha] at hpos h
    have hk : k ≠ 0 := by
      rintro rfl
      simp at hpos
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal β⁻¹ := by
      have : (1 : ℝ≥0∞) ≤ ((k : ℕ∞) : ℝ≥0∞) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      rw [h] at this
      simpa using this
    exact ENNReal.one_le_ofReal.mp h1

variable [CompactSpace X] [X.IsSeparated]

/-- **Every divisorial point is charged** ([BJ22, `equ:mixedMAPL`], step R8(e)): granted the
cycle lower bound and relatively ample vertical divisors, for every ample rational class `ω` of
`X` of dimension `n ≥ 1` and every `v ∈ X^Div`, the energy pairing of `ω` charges `v`: there are a
bounded `ω`-psh PL function `χ` (`φ_D` for a relatively ample `π^*ω + D` on a model of the valuation
ideals of `v`) and `c > 0` with `(0, f) ⋅ (ω, χ)^n ≥ c f(v)` for every PL `f ≥ 0`. -/
theorem isCharged_of_cycleLowerBound (n : ℕ) (hX : topologicalKrullDim X ≤ n)
    (hXn : topologicalKrullDim X = n) (hn : 0 < n) (ω : SGPT.NAPotential.BJ.NativePicard.RationalPicardSpace X)
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p)
    (hcyc : CycleLowerBound n) (hamp : RelAmplePositive p n ω) (v : BerkovichPoint p)
    (hv : v ∈ divisorialSet p) : (energyPairingOfAmple n hX hXn hn ω hω).IsCharged v := by
  have hvs : v.support = genericPoint X := by
    obtain ⟨E, s, hs, rfl⟩ := hv
    exact E.isGenericPoint_image
  let := residueComplexAlgebra p v.support
  obtain ⟨𝔞, N, hwb, hrees⟩ := exists_reesPoint_of_divisorial v hv
  obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial (p := p) hwb
  obtain ⟨D, hθ, hpos⟩ := hamp _ _ hgood
  obtain ⟨gb, hgb, zb, hgbν, hgbη, hzb, hzbc, hzb1, hdvrb, βb, hβb, hrescb, hflagb⟩ :=
    hrees _ _ hdom.1
  obtain ⟨Z, hZi, hZc, hZs, ι, hι, hιp, hdimZ, hrange, hκ⟩ := hpos zb hzb1 hzbc
  obtain ⟨R, hR⟩ := exists_bound_fn D
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℚ, interFormQ (ι ≫ normModelStructure p _ _) n hdimZ
      (Scheme.Modules.unitObj Z) (Multiset.replicate n (picPullbackQ ι (picPullbackQ
        (normModelν p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1))
          (omegaPullback _ _ ω + FDiv.cls D)))) = κ := ⟨_, rfl⟩
  rw [hκdef] at hκ
  refine ⟨⟨FDiv.fn D, fn_mem_plSubmodule D⟩,
    show IsFlagPsh p ω (FDiv.fn D) from ⟨_, _, hgood, D, rfl, hθ⟩, ⟨R, fun s => hR s⟩,
    (κ : ℝ), (by exact_mod_cast hκ), fun f hf => ?_⟩
  change _ ≤ plPair n hX ω (((0 : ℚ), f) ::ₘ Multiset.replicate n ((1 : ℚ), ⟨FDiv.fn D, _⟩))
  simp only [plPair, Multiset.map_cons, Multiset.map_replicate]
  -- a common good model for `f` and the model of `χ`
  obtain ⟨𝔠f, cf, hgoodf, hfrep⟩ := exists_goodModel_flagRep f.2
  obtain ⟨g₀, g, hg₀, hg⟩ := exists_common_dominating p hgoodf.1 hgood.1
  have hP : IsGoodModel p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) :=
    ⟨hgoodf.1.mul hgood.1, hgoodf.2.of_comp g₀ hg₀⟩
  have hfrep' := hfrep.pullback g₀ hg₀
  have hD' : FDiv.fn (FDiv.pullback g hg D) = FDiv.fn D := FDiv.fn_pullback g hg D
  have hχrep : IsFlagRep p _ _ (FDiv.fn D) := ⟨FDiv.pullback g hg D, hD'⟩
  rw [flagPair_eq n hX ω hP _ (fun x hx => by
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hfrep'
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hχrep)]
  -- the Rees point on the common model
  obtain ⟨g', hg', z', hg'ν, hg'η, hz', hz'c, hz'1, hdvr', β', hβ', hresc', hflag'⟩ :=
    hrees _ _ (hdom.of_comp g hg).1
  -- the effective divisor of `f`
  have hDf : FDiv.fn (flagRep (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1))
      (f : BerkovichPoint p → ℝ)) = f := fn_flagRep hfrep'
  obtain ⟨Nf, K, hK, hNf, hKsupp, hNK, hKval⟩ := exists_effective_ordPoint hP.central_isInvertible
    (flagRep _ _ (f : BerkovichPoint p → ℝ)) (by rw [hDf]; exact fun s => hf s) z'
    ENNReal.ofReal_ne_top hflag'
  have hβ1 := one_le_inv_of_rees hP.central_isInvertible z' hz'c hflag'
  -- the lift `ρ` of `ν' ≫ g` to the normalized model of `χ`
  have : IsDominant g := isDominant_of_comp_eq g hg
  have : IsDominant (normModelν p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1))) :=
    ⟨(normModelν_surjective p _ _).denseRange⟩
  obtain ⟨ρ, hρ0, -⟩ :=
    SGPT.Foundations.Envelope.IntegralSchemeNormalization.existsUnique_dominant_normalization_lift
      (normModelν p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) ≫ g)
      (normModel_stalk_isIntegrallyClosed p _ _)
  have hρ : ρ ≫ normModelν p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1) =
      normModelν p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) ≫ g := hρ0
  have hρs : ρ ≫ normModelStructure p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1) =
      normModelStructure p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) := by
    rw [normModelStructure, ← Category.assoc, hρ, Category.assoc, comp_flagModelStructure g hg]
  -- `ρ` maps the Rees point `z'` to the Rees point `zb`
  have hadm : ((flagSheaf p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1)).comap
      (gaussMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
        (fromSpecResidueField_structure v))).IsInvertible := by
    rw [comap_gaussMap_flagSheaf]
    exact Scheme.IdealSheafData.isInvertible_top
  have hlift : g' ≫ ρ = gb := by
    apply normLift_eq
    · rw [Category.assoc, hρ, ← Category.assoc, hg'ν, hgbν]
      exact (flagModel_isBlowUp p _ _).hom_ext _ hadm _ _
        (by rw [Category.assoc, hg, gaussModelMap_π]) (gaussModelMap_π _ _ _ _ _)
    · change fieldPt (gb ≫ normModelν p _ _) = _
      rw [hgbν]
      exact fieldPt_gaussModelMap_eq_genericPoint v hvs _ _
  have hρz : ρ z' = zb := by
    have h := center_fieldBerkovichPoint_comp g' hg' ρ hρs (berkovichGaussExtension v)
    rw [hz', fieldBerkovichPoint_congr hlift _ hgb, hzb] at h
    exact h.symm
  -- the class of `χ` pulled back along `ρ`
  have hθ' : picPullbackQ ρ (picPullbackQ (normModelν p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1))
      (omegaPullback _ _ ω + FDiv.cls D)) =
      normOmega ω _ _ + FDiv.ncls (FDiv.pullback g hg D) := by
    rw [← picPullbackQ_comp, hρ, picPullbackQ_comp, map_add, omegaPullback_comp g hg,
      ← FDiv.cls_pullback g hg D, map_add]
    rfl
  have hnef : picPullbackQ ρ (picPullbackQ (normModelν p (𝔞 * FlagIdeal.monomial X 0)
      ((N : ℤ) + 1)) (omegaPullback _ _ ω + FDiv.cls D)) ∈
        relNefCone (normModelStructure p _ _) (K.support : Set _) := by
    have : IsProjective ((normModelν p (𝔠f * (𝔞 * FlagIdeal.monomial X 0))
        (cf + ((N : ℤ) + 1)) ≫ g) ≫ flagModelStructure p (𝔞 * FlagIdeal.monomial X 0)
          ((N : ℤ) + 1)) := by
      rw [Category.assoc, comp_flagModelStructure g hg]
      infer_instance
    have h1 := picPullbackQ_mem_relNefCone (flagModelStructure p _ _)
      (normModelν p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) ≫ g) hθ
    rw [Category.assoc, comp_flagModelStructure g hg] at h1
    rw [← picPullbackQ_comp, hρ]
    refine relNefCone_mono _ ?_ h1
    intro x hx
    have h2 := hKsupp hx
    have e : ∀ y, flagModelπ p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1) (g y) =
        flagModelπ p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) y := fun y => by
      rw [← hg]
      rfl
    show flagModelπ p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1)
      (g (normModelν p (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1)) x)) ∈
        ((centralIdeal p).support : Set (productLine p))
    rw [e]
    exact h2
  -- the cycle lower bound
  have hc := hcyc _ _ (normModelStructure p _ _) (normModelStructure p _ _) ρ hρs
    (topologicalKrullDim_normModel_le p _ _ n hX) K hK _ hnef z' hz'1 Z ι
    (by rw [hrange, hρz]) hdimZ
  -- the left side: `ord_{z'}(K) = β'⁻¹ N f(v)`
  have hord : (ordIdeal (K.stalkIdeal z')).toReal =
      β'⁻¹ * (Nf * (f : BerkovichPoint p → ℝ) v) := by
    rw [← idealVal_ordPoint (normModelStructure p (𝔠f * (𝔞 * FlagIdeal.monomial X 0))
      (cf + ((N : ℤ) + 1))), hKval, hDf, ← ENNReal.ofReal_mul (inv_nonneg.mpr hβ'.le),
      ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hβ'.le)
        (mul_nonneg (Nat.cast_nonneg _) (hf v)))]
  -- the right side: `N` times the pairing
  have hcart : picQ ⟨cartierLine K, cartierLine_isInvertible hK⟩ =
      (Nf : ℚ) • FDiv.ncls (flagRep _ _ (f : BerkovichPoint p → ℝ)) := by
    rw [hNK, picQ, picQ, lineCls_cartierLine hK, TensorProduct.tmul_neg]
  have hmv : interFormQ (normModelStructure p (𝔠f * (𝔞 * FlagIdeal.monomial X 0))
      (cf + ((N : ℤ) + 1))) (n + 1)
      (topologicalKrullDim_normModel_le p _ _ n hX) (Scheme.Modules.unitObj _)
        (picQ ⟨cartierLine K, cartierLine_isInvertible hK⟩ ::ₘ
          Multiset.replicate n (picPullbackQ ρ (picPullbackQ
            (normModelν p (𝔞 * FlagIdeal.monomial X 0) ((N : ℤ) + 1))
              (omegaPullback _ _ ω + FDiv.cls D)))) =
      (Nf : ℚ) * modelValue n hX ω (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1))
        (((0 : ℚ), (f : BerkovichPoint p → ℝ)) ::ₘ Multiset.replicate n ((1 : ℚ), FDiv.fn D)) := by
    rw [hcart, hθ', MultisetForm.map_smul, modelValue, Multiset.map_cons, Multiset.map_replicate]
    congr 3
    · rw [modelClass, zero_smul, zero_add]
    · rw [modelClass_eq ω hP _ (FDiv.pullback g hg D) hD', one_smul]
  rw [hord, hmv, hκdef] at hc
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hNf' : (0 : ℝ) < Nf := by exact_mod_cast hNf
  have hfv : 0 ≤ (f : BerkovichPoint p → ℝ) v := hf v
  push_cast at hc
  set M := (modelValue n hX ω (𝔠f * (𝔞 * FlagIdeal.monomial X 0)) (cf + ((N : ℤ) + 1))
    (((0 : ℚ), (f : BerkovichPoint p → ℝ)) ::ₘ Multiset.replicate n ((1 : ℚ), FDiv.fn D)) : ℝ)
  have h3 : (Nf : ℝ) * ((κ : ℝ) * (f : BerkovichPoint p → ℝ) v) ≤ Nf * M := by
    have h4 : (κ : ℝ) * (f : BerkovichPoint p → ℝ) v ≤
        β'⁻¹ * ((κ : ℝ) * (f : BerkovichPoint p → ℝ) v) :=
      le_mul_of_one_le_left (mul_nonneg hκ'.le hfv) hβ1
    nlinarith
  exact le_of_mul_le_mul_left h3 hNf'

end charging

/-- **`thm:BJappseq` from the cycle lower bound and relatively ample vertical divisors**
([BJ22, Corollary 12.18]): for an integral projective `X` of dimension `n ≥ 1`, the comparison
theorem, the energy pairings of ample classes and the charging of divisorial
points (`isCharged_of_cycleLowerBound`) give `thm:BJappseq`. -/
theorem bjAppSeq_of_cycleLowerBound (n : ℕ) (hXn : topologicalKrullDim X = n) (hn : 0 < n)
    (hcyc : CycleLowerBound n)
    (hamp : ∀ ω : SGPT.NAPotential.BJ.NativePicard.RationalPicardSpace X,
      SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p →
        RelAmplePositive p n ω) :
    SGPT.NAPotential.ThinApprox.BJ.AppSeq.BJAppSeqStatement.{u} p := by
  let := compactSpace_of_projective p
  let := isSeparated_of_projective p
  exact bjAppSeq_of_charging p n hXn hn fun ω hω v hv =>
    isCharged_of_cycleLowerBound n hXn.le hXn hn ω hω hcyc (hamp ω hω) v hv

end SGPT.NAPotential.ThinApprox.BJ
