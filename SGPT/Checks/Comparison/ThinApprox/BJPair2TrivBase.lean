import SGPT.Checks.Comparison.ThinApprox.BJPairEnergy
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionSectionIntersections
import SGPT.Checks.Comparison.SourceNumericalAmpleness
run_cmd Lean.logInfo "THIN_TRIV_BASE: imports-ready"

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
# The volume, the central fibre and `equ:mixedMA0` for the energy pairing (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), §3.2: `(ω^n) > 0` for an ample class,
`(𝒳₀ ⋅ (π^*ω)^n) = (ω^n)` and `equ:mixedMA0`, `(0, f) ⋅ (ω, 0)^n = (ω^n) f(v_triv)`. Towards
`thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

* `volQ_pos`: `(ω^n) > 0` when `dim X = n` and `ω` has ample numerical class (SGPT.Foundations.Envelope's
  `mixedEulerDifference_replicate_pos_of_isAmple` for an ample representative);
* `isIso_subscheme_productFst`: the subscheme `X × {0}` of `X × ℙ¹` maps isomorphically to `X`;
* `interFormQ_central_omega`: `(𝒳₀ ⋅ (π^*ω)^n)_𝒳 = (ω^n)_X` on every blow-up model (cut formula
  along `X × {0}` on `X × ℙ¹`, birational invariance);
* `interFormQ_flagVert_omega_eq_zero`: `(E ⋅ (π^*ω)^n) = 0` for the divisor `E = (t^{λ} 𝔞) · 𝒪`
  of a flag ideal with `𝔞_λ ≠ 0`: `E` maps into the proper closed subset `V(𝔞_λ)` of `X` (cut
  formula, BJ-INTERSECT's pull-back vanishing);
* `phi_trivial_eq`: `φ_𝔞(v_triv) = max {λ : 𝔞_λ ≠ 0}`;
* `pairTriv` (**[BJ22, `equ:mixedMA0`]**): the axiom `PairTriv` of lane BJ-PAIR holds when
  `dim X = n ≥ 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge SGPT.NAPotential.BJ.NativePicard
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open FlagIdealBound

/-! ### Scalars in multilinear forms -/

theorem MultisetForm.map_replicate_smul {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Φ : MultisetForm ℚ V) (c : ℚ) (x : V) :
    ∀ (k : ℕ) (t : Multiset V),
      Φ (Multiset.replicate k (c • x) + t) = c ^ k * Φ (Multiset.replicate k x + t) := by
  intro k
  induction k with
  | zero => intro t; simp
  | succ k ih =>
    intro t
    rw [Multiset.replicate_succ, Multiset.replicate_succ, Multiset.cons_add, Multiset.cons_add,
      Φ.map_smul, ← Multiset.add_cons, ih, ← Multiset.add_cons, pow_succ]
    ring

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

run_cmd Lean.logInfo "THIN_TRIV_BASE: volume-next"

/-! ### The volume -/

section vol

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n)

omit [IsIntegral X] [CompactSpace X] [X.IsSeparated] in
theorem picQ_atlas_presentation (ω : RationalPicardSpace X) :
    ∃ (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ), 0 < m ∧
      ω = (1 / (m : ℚ)) • picQ ⟨L, hL⟩ ∧
      SGPT.NAPotential.BJ.NativePicard.numericalClass p ω =
        (1 / (m : ℚ)) • SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass p L hL := by
  obtain ⟨L, a, m, hm, rfl⟩ := exists_actual_line_presentation ω
  refine ⟨L, isInvertible_of_atlas a, m, hm, by rw [rationalPicardClass_eq_picQ a], ?_⟩
  rw [numericalClass_rat_smul, numericalClass_line]

run_cmd Lean.logInfo "THIN_TRIV_BASE: positivity-next"

/-- **`(ω^n) > 0`** for a rational class with ample numerical class on an integral projective `X`
of dimension `n` (an ample representative of a multiple of `ω` and SGPT.Foundations.Envelope's positivity
of top self-intersections of ample bundles). -/
theorem volQ_pos (hXn : topologicalKrullDim X = n) (ω : RationalPicardSpace X)
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p) :
    0 < volQ p n hX ω := by
  obtain ⟨L, hL, m, hm, rfl, hnum⟩ := picQ_atlas_presentation (p := p) ω
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hclass : SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass p L hL ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p := by
    have h2 := (SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p).smul_mem hmR hω
    rw [hnum, ← Rat.cast_smul_eq_qsmul ℝ, smul_smul] at h2
    have h3 : (m : ℝ) * (((1 / (m : ℚ)) : ℚ) : ℝ) = 1 := by
      push_cast
      field_simp
    rwa [h3, one_smul] at h2
  have hample := SGPT.NAPotential.BJ.SourceNumericalAmpleness.isAmple_of_lineClass_mem_ampleCone p L hL hclass
  have hpos := SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.mixedEulerDifference_replicate_pos_of_isAmple
    p n hXn L hample
  have hval : interFormQ p n hX (Scheme.Modules.unitObj X)
      (Multiset.replicate n (picQ ⟨L, hL⟩)) =
      SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.mixedEulerDifference p
        (List.replicate n L) (Scheme.Modules.unitObj X) := by
    have := interFormQ_picQ p n hX (Scheme.Modules.unitObj X) (List.replicate n ⟨L, hL⟩)
      (by simp)
    simpa [List.map_replicate, Multiset.coe_replicate] using this
  have hsc := MultisetForm.map_replicate_smul (interFormQ p n hX (Scheme.Modules.unitObj X))
    (1 / (m : ℚ)) (picQ ⟨L, hL⟩) n 0
  simp only [add_zero] at hsc
  rw [volQ, hsc, hval]
  have hmq : (0 : ℚ) < 1 / (m : ℚ) := by positivity
  exact mul_pos (pow_pos hmq n) (by exact_mod_cast hpos)

end vol

run_cmd Lean.logInfo "THIN_TRIV_BASE: central-next"

/-! ### The central fibre maps isomorphically to `X` -/

section central

omit [IsProjective p] [IsIntegral X] in
theorem isIso_zeroIdeal_structure :
    IsIso ((zeroIdeal ℂ).subschemeι ≫ projectiveSpaceStructure ℂ 1) := by
  have h1 : (zeroPoint ℂ).toImage ≫ (zeroIdeal ℂ).subschemeι = zeroPoint ℂ :=
    (zeroPoint ℂ).toImage_imageι
  have h2 : (zeroIdeal ℂ).subschemeι ≫ projectiveSpaceStructure ℂ 1 =
      inv (zeroPoint ℂ).toImage := by
    rw [← cancel_epi (zeroPoint ℂ).toImage, ← Category.assoc, h1, zeroPoint_structure,
      IsIso.hom_inv_id]
  rw [h2]
  infer_instance

omit [IsProjective p] [IsIntegral X] in
/-- **`X × {0} ≅ X`**: the subscheme of the ideal of the central fibre maps isomorphically to `X`
under the first projection. -/
theorem isIso_subscheme_productFst (I : (productLine p).IdealSheafData)
    (hI : I = centralIdeal p) : IsIso (I.subschemeι ≫ productFst p) := by
  subst hI
  have := isIso_zeroIdeal_structure
  have e1 : (centralIdeal p).subschemeι =
      ((zeroIdeal ℂ).comapIso (productSnd p)).hom ≫ pullback.fst _ _ :=
    (Scheme.IdealSheafData.comapIso_hom_fst _ _).symm
  rw [e1, Category.assoc]
  change IsIso (((zeroIdeal ℂ).comapIso (productSnd p)).hom ≫
    pullback.fst (pullback.snd p (projectiveSpaceStructure ℂ 1)) (zeroIdeal ℂ).subschemeι ≫
      pullback.fst p (projectiveSpaceStructure ℂ 1))
  rw [← pullbackLeftPullbackSndIso_hom_fst p (projectiveSpaceStructure ℂ 1)
    (zeroIdeal ℂ).subschemeι]
  infer_instance

end central

/-! ### `(𝒳₀ ⋅ (π^*ω)^n) = (ω^n)` -/


end SGPT.NAPotential.ThinApprox.BJ
