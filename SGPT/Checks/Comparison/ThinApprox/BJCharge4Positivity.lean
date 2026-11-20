import SGPT.Checks.Comparison.ThinApprox.BJCharge3Charged

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
# Positivity of ample classes on closures of points (lane BJ-CHARGE, towards `RelAmplePositive`)

Source: Lazarsfeld, *Positivity I*, Thm. 1.2.23 (`(A^n ⋅ Z) > 0` for an ample `A` on an
`n`-dimensional integral projective `Z`); [BJ22, `lem:relamp`]. Towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-charge4.tex`.

The hypothesis `RelAmplePositive` of `bjAppSeq_of_cycleLowerBound` asks for positive top
self-intersections on the closures of codimension-one points of the central fibre. This file
provides the generic ingredients:

* `interFormQ_replicate_smul_pos_of_isAmple`: on an integral projective scheme of dimension `n`, a
  positive rational multiple of the class of an ample invertible sheaf has positive `n`-th power;
* `pointClosure`, `pointClosureι`: the reduced closed subscheme `closure {z}` with its inclusion,
  integral, separated, compact and projective over `ℂ` when the ambient scheme is;
* `range_pointClosureι`: its image is `closure {z}`;
* `topologicalKrullDim_pointClosure_le`: if `z` is not the generic point of an integral `Y` with
  `dim Y ≤ n + 1`, then `dim closure {z} ≤ n`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory TopologicalSpace
open SGPT.NAPotential.BJIntersect
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
open SGPT.Foundations.Envelope.SeshadriAmplenessCriterionNefAmpleMixedIntersections

/-! ### Positivity of ample classes -/

/-- **Ample classes have positive top self-intersection**: on an integral projective scheme `Z`
of dimension `n` over `ℂ`, for an ample invertible sheaf `A` and a rational `c > 0`,
`((c [A])^n) > 0`. -/
theorem interFormQ_replicate_smul_pos_of_isAmple {Z : Scheme.{0}} [IsIntegral Z] [CompactSpace Z]
    [Z.IsSeparated] (q : Z ⟶ Spec (.of ℂ)) [IsProjective q] (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ n) (hdimeq : topologicalKrullDim Z = n)
    (A : Z.Modules) (hA : SchemeLineAmpleness.IsAmple q A) {c : ℚ} (hc : 0 < c) :
    0 < interFormQ q n hdim (Scheme.Modules.unitObj Z)
      (Multiset.replicate n (c • picQ ⟨A, hA.isInvertible⟩)) := by
  have h := MultisetForm.map_replicate_smul (interFormQ q n hdim (Scheme.Modules.unitObj Z)) c
    (picQ ⟨A, hA.isInvertible⟩) n 0
  rw [add_zero, add_zero] at h
  rw [h]
  have hval : interFormQ q n hdim (Scheme.Modules.unitObj Z)
      (Multiset.replicate n (picQ ⟨A, hA.isInvertible⟩)) =
        mixedEulerDifference q (List.replicate n A) (Scheme.Modules.unitObj Z) := by
    have := interFormQ_picQ q n hdim (Scheme.Modules.unitObj Z)
      (List.replicate n ⟨A, hA.isInvertible⟩) (by simp)
    simpa [List.map_replicate, Multiset.coe_replicate] using this
  rw [hval]
  have hpos := SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.mixedEulerDifference_replicate_pos_of_isAmple
    q n hdimeq A hA
  have hpos' : (0 : ℚ) < (mixedEulerDifference q (List.replicate n A)
      (Scheme.Modules.unitObj Z) : ℚ) := by exact_mod_cast hpos
  exact mul_pos (pow_pos hc n) hpos'

/-! ### Closures of points as integral closed subschemes -/

section pointClosure

variable {Y : Scheme.{0}} (z : Y)

/-- The reduced closed subscheme `closure {z}`. -/
abbrev pointClosure : Scheme.{0} :=
  (Scheme.IdealSheafData.vanishingIdeal (⟨closure ({z} : Set Y), isClosed_closure⟩ : Closeds Y)).subscheme

/-- The inclusion of `closure {z}`. -/
abbrev pointClosureι : pointClosure z ⟶ Y :=
  (Scheme.IdealSheafData.vanishingIdeal (⟨closure ({z} : Set Y), isClosed_closure⟩ : Closeds Y)).subschemeι

instance pointClosure_isIntegral : IsIntegral (pointClosure z) :=
  SGPT.Foundations.Envelope.SchemePointClosureIntegral.isIntegral_pointClosure z

instance pointClosure_compactSpace [CompactSpace Y] : CompactSpace (pointClosure z) :=
  QuasiCompact.compactSpace_of_compactSpace (pointClosureι z)

instance pointClosure_isSeparated [Y.IsSeparated] : (pointClosure z).IsSeparated :=
  isSeparated_of_closed (pointClosureι z)

instance pointClosureι_isProjective (q : Y ⟶ Spec (.of ℂ)) [IsProjective q] :
    IsProjective (pointClosureι z ≫ q) :=
  isProjective_closed_comp (pointClosureι z) q

theorem range_pointClosureι : Set.range (pointClosureι z) = closure {z} := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- **The closure of a non-generic point has smaller dimension.** -/
theorem topologicalKrullDim_pointClosure_le [IsIntegral Y] {n : ℕ}
    (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ)) (hz : z ≠ genericPoint Y) :
    topologicalKrullDim (pointClosure z) ≤ n := by
  let W : Closeds Y := ⟨closure ({z} : Set Y), isClosed_closure⟩
  have hW : W ≠ ⊤ := by
    intro h
    apply hz
    have hmem : genericPoint Y ∈ closure ({z} : Set Y) := by
      have : genericPoint Y ∈ (W : Set Y) := by rw [h]; trivial
      exact this
    have h1 : genericPoint Y ⤳ z := (genericPoint_spec Y).specializes trivial
    have h2 : z ⤳ genericPoint Y := specializes_iff_mem_closure.mpr hmem
    exact (h2.antisymm h1).eq
  change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal W).support ≤ n
  have hs : (Scheme.IdealSheafData.vanishingIdeal W).support = W := by
    apply SetLike.coe_injective
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal W
  rw [hs]
  exact SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.properClosed_dimension_drop W hW n
    hdim

end pointClosure

end SGPT.NAPotential.ThinApprox.BJ
