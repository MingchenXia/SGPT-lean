import SGPT.Checks.Comparison.ThinApprox.BJCharge4Positivity
import SGPT.Checks.Comparison.BJRelAmpleDim
import SGPT.Checks.Comparison.ThinApprox.BJRelAmpleClass

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
# Relatively ample vertical divisors: `RelAmplePositive`

Source: [BJ22] (`references/bj22-trivval`), `lem:relamp` (on a blow-up model `π : 𝒳 ⟶ X × ℙ¹` of
a flag ideal, `π^*ω - ε E` is relatively ample for an ample `ω` and `0 < ε ≪ 1`, `E` the exceptional
divisor), and the positivity of ample classes on subvarieties (Lazarsfeld, *Positivity I*,
Thm. 1.2.23). This discharges the hypothesis `RelAmplePositive` of `bjAppSeq_of_cycleLowerBound`
(`thm:BJappseq` of `chapter_NApotential.tex`). Blueprint: `claude-bj-relample.tex`.

Proof. Write `m ω = [L]` with `L` ample and `L^r ≅ i^*𝒪(1)` for a closed embedding `i : X ⟶ ℙ^N`.
On `X × ℙ¹`, `H = pr₁^* i^*𝒪(1) ⊗ pr₂^*𝒪(1)` is ample (Segre), so on the blow-up `𝒳` of `t^c 𝔠`
the sheaf `A = 𝒪(-E) ⊗ π^*H^s` is ample for some `s > 0` (SGPT.Foundations.Envelope). With `M = s r m` and
`μ = [ρ^*𝒪_{ℙ¹}(1)]`, `M (π^*ω - M⁻¹ E) = [A] - s μ`, where `[A]` is nef and `-μ` is nef on the
central fibre, and `μ` vanishes on every subscheme of the central fibre. On the closure `Z` of a
codimension-one point of the central fibre of the normalized model, `dim Z = n` and the class is
`M⁻¹ [A|_Z]` with `A|_Z` ample (finite and closed pull-backs), whence `((π^*ω - M⁻¹E)|_Z)^n > 0`.

* `relAmplePositive`: **`RelAmplePositive p n ω`** for every rational class `ω` with ample numerical
  class on an integral projective `X` of dimension `n`;
* `bjAppSeq_of_cycleLowerBound_of_relAmple`: `thm:BJappseq` modulo `CycleLowerBound n` only.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Order Topology
open SGPT.Foundations.Envelope SGPT.NAPotential.BJIntersect SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel FlagIdealBound

attribute [local instance] Scheme.Modules.monoidalCategory

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- **Relatively ample vertical divisors with positive self-intersection on the components**
([BJ22, `lem:relamp`] and Lazarsfeld, Thm. 1.2.23): on an integral projective `X` of dimension `n`
over `ℂ`, for every rational class `ω` with ample numerical class, every good model `(𝔠, c₀)`
carries the vertical divisor `D = -M⁻¹ E` (`E` the exceptional divisor, `M > 0`) with `π^*ω + D`
nef on the central fibre and of positive top self-intersection on the closure of every
codimension-one point of the central fibre of the normalized model. -/
theorem relAmplePositive (n : ℕ) (hXn : topologicalKrullDim X = n)
    (ω : SGPT.NAPotential.BJ.NativePicard.RationalPicardSpace X)
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p) :
    RelAmplePositive p n ω := by
  intro 𝔠 c₀ hgood
  -- an ample representative `L` of `m ω` and an embedding `i` with `i^*𝒪(1) ≅ L^r`
  obtain ⟨m, L, hL, hm, hmω⟩ := exists_isAmple_smul_eq_picQ p ω hω
  obtain ⟨r, hr, N₀, i, hi, hip, ⟨eL⟩⟩ := hL.2
  let : IsClosedImmersion i := hi
  -- the Segre-ample sheaf `H` on `X × ℙ¹` and the ample sheaf `A = 𝒪(-E) ⊗ π^*H^s` on `𝒳`
  have hH : SchemeLineAmpleness.IsAmple (productStructure p) (segreLine p i) :=
    isAmple_segre p i hip
  obtain ⟨s, hs, hA⟩ :=
    Vanishing.NadelNefBigSingleExceptionalAmple.exists_positive_isAmple_exceptional_tensor_pullback
      (flagSheaf p 𝔠 c₀) (productStructure p) (segreLine p i) hH
  have hA' : SchemeLineAmpleness.IsAmple (flagModelStructure p 𝔠 c₀)
      (modelAmpleLine p i 𝔠 c₀ s) := hA
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℕ, Nn = s * r * m := ⟨_, rfl⟩
  have hN0 : (Nn : ℚ) ≠ 0 := by
    have : 0 < Nn := hNn ▸ Nat.mul_pos (Nat.mul_pos hs hr) hm
    exact_mod_cast this.ne'
  -- the class computation `Nn (π^*ω + D) = [A] - s μ`
  have hAcls : picQ ⟨modelAmpleLine p i 𝔠 c₀ s, hA'.isInvertible⟩ =
      picQ (exceptionalDatum p hgood.1).vert.line + (Nn : ℚ) • omegaPullback 𝔠 c₀ ω +
        (s : ℚ) • lineTwistClass p 𝔠 c₀ := by
    rw [picQ_modelAmpleLine p i hgood.1 s, picQ_segreLine p i hL.isInvertible eL, ← hmω,
      lineTwistClass_eq, omegaPullback, picPullbackQ_comp, hNn]
    simp only [map_add, map_smul]
    push_cast
    module
  have hθN : (Nn : ℚ) • (omegaPullback 𝔠 c₀ ω +
      FDiv.cls (Finsupp.single (exceptionalDatum p hgood.1) (-(1 / (Nn : ℚ))))) =
      picQ ⟨modelAmpleLine p i 𝔠 c₀ s, hA'.isInvertible⟩ + (s : ℚ) • -lineTwistClass p 𝔠 c₀ := by
    rw [hAcls, FDiv.cls_single, smul_add, neg_smul_neg, smul_smul, mul_one_div_cancel hN0,
      one_smul]
    module
  have hθ : omegaPullback 𝔠 c₀ ω +
      FDiv.cls (Finsupp.single (exceptionalDatum p hgood.1) (-(1 / (Nn : ℚ)))) =
      (1 / (Nn : ℚ)) • (picQ ⟨modelAmpleLine p i 𝔠 c₀ s, hA'.isInvertible⟩ +
        (s : ℚ) • -lineTwistClass p 𝔠 c₀) := by
    rw [← hθN, smul_smul, one_div_mul_cancel hN0, one_smul]
  refine ⟨Finsupp.single (exceptionalDatum p hgood.1) (-(1 / (Nn : ℚ))), ?_, ?_⟩
  · -- nef on the central fibre
    rw [hθ]
    refine Submodule.smul_mem _ (⟨1 / (Nn : ℚ), by positivity⟩ : {r : ℚ // 0 ≤ r})
      (add_mem (picQ_mem_relNefCone _ ⟨_, hA'.isInvertible⟩ (isNefOn_of_isAmple _ hA' _)) ?_)
    exact Submodule.smul_mem _ (⟨(s : ℚ), by positivity⟩ : {r : ℚ // 0 ≤ r})
      (neg_lineTwistClass_mem_relNefCone p 𝔠 c₀)
  · -- positivity on the components of the central fibre
    intro z hz hzc
    have hdim := topologicalKrullDim_normModel_le p 𝔠 c₀ n hXn.le
    have hdimZ := topologicalKrullDim_pointClosure_le z hdim
      (ne_genericPoint_of_coheight_eq_one hz)
    have hdimeq : topologicalKrullDim (pointClosure z) = n :=
      le_antisymm hdimZ (le_topologicalKrullDim_of_coheight_eq_one (normModelStructure p 𝔠 c₀)
        (topologicalKrullDim_normModel_eq p 𝔠 c₀ n hXn) hz (pointClosureι z)
        (range_pointClosureι z))
    refine ⟨pointClosure z, inferInstance, inferInstance, inferInstance, pointClosureι z,
      inferInstance, inferInstance, hdimZ, range_pointClosureι z, ?_⟩
    -- `Z = closure {z}` lies in the central fibre
    have hclosed : IsClosed ((normModelν p 𝔠 c₀) ⁻¹' centralFibre p 𝔠 c₀) :=
      ((centralIdeal p).support.isClosed.preimage (flagModelπ p 𝔠 c₀).continuous).preimage
        (normModelν p 𝔠 c₀).continuous
    have hrange : Set.range (pointClosureι z ≫ normModelν p 𝔠 c₀) ⊆ centralFibre p 𝔠 c₀ := by
      rintro _ ⟨x, rfl⟩
      have hx : pointClosureι z x ∈ closure ({z} : Set (normModel p 𝔠 c₀)) := by
        rw [← range_pointClosureι z]
        exact ⟨x, rfl⟩
      have hsub : closure ({z} : Set (normModel p 𝔠 c₀)) ⊆
          (normModelν p 𝔠 c₀) ⁻¹' centralFibre p 𝔠 c₀ :=
        hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzc)
      rw [Scheme.Hom.comp_apply]
      exact hsub hx
    -- the ample restriction of `A`
    have hAν := PLModelAuxiliaryPolarization.isAmple_finite_pullback
      (flagModelStructure p 𝔠 c₀) _ hA' (normModelν p 𝔠 c₀)
    have hAZ := SeshadriAmplenessCriterion.isAmple_closedPullback (pointClosureι z)
      (normModelStructure p 𝔠 c₀) _ hAν
    have hZcls : picPullbackQ (pointClosureι z) (picPullbackQ (normModelν p 𝔠 c₀)
        (omegaPullback 𝔠 c₀ ω +
          FDiv.cls (Finsupp.single (exceptionalDatum p hgood.1) (-(1 / (Nn : ℚ)))))) =
        (1 / (Nn : ℚ)) • picQ ⟨_, hAZ.isInvertible⟩ := by
      rw [hθ, map_smul, map_smul, map_add, map_add, map_smul, map_smul, map_neg, map_neg,
        ← picPullbackQ_comp (pointClosureι z) (normModelν p 𝔠 c₀) (lineTwistClass p 𝔠 c₀),
        picPullbackQ_lineTwistClass_eq_zero p _ hrange, neg_zero, smul_zero, add_zero,
        picPullbackQ_picQ, picPullbackQ_picQ]
    rw [hZcls]
    exact interFormQ_replicate_smul_pos_of_isAmple _ n hdimZ hdimeq _ hAZ (by positivity)

/-- **`thm:BJappseq` from the cycle lower bound alone**: `bjAppSeq_of_cycleLowerBound` with its
hypothesis `RelAmplePositive` discharged by `relAmplePositive`. -/
theorem bjAppSeq_of_cycleLowerBound_of_relAmple (n : ℕ) (hXn : topologicalKrullDim X = n)
    (hn : 0 < n) (hcyc : CycleLowerBound n) : SGPT.NAPotential.ThinApprox.BJ.AppSeq.BJAppSeqStatement.{u} p :=
  bjAppSeq_of_cycleLowerBound n hXn hn hcyc fun ω hω => relAmplePositive p n hXn ω hω

end SGPT.NAPotential.ThinApprox.BJ
