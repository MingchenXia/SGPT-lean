import SGPT.Projective.OriginalZeroFrameLength
import SGPT.Projective.OriginalClosedCyclePushforward

/-! SAME ENTIRE original Artinian zero cycle in the original ambient scheme:
actual AlgebraicCycle.map, all-frame quotient readers and independent structural sum.
Blueprint: original-section-zero-cycle.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open scoped BigOperators
variable {X : Scheme.{0}} {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤))
  [IsArtinianScheme (sectionZeroSubscheme a s)]

/-- ACTUAL original closed-immersion pushforward of ENTIRE FULL original zero cycle. -/
def originalSectionZeroAmbientCycle : AlgebraicCycle X ℤ :=
  AlgebraicCycle.map (sectionZeroι a s) (pointDimension (sectionZeroSubscheme a s))
    (pointDimension X) (artinianZeroCycle (sectionZeroSubscheme a s))

/-- SAME actual original ambient zero coefficient is SAME arbitrary-frame FULL original principal length. -/
theorem originalSectionZeroAmbientCycle_coeff {U : X.Opens} (e : LocalBundleFrame L U)
    (x : X) (hx : x ∈ U) :
    originalSectionZeroAmbientCycle a s x =
      ((Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
        Ideal.span {originalSectionFrameGerm e s x hx})).toNat : ℤ) := by
  by_cases hin : x ∈ Set.range (sectionZeroι a s)
  · obtain ⟨z, rfl⟩ := hin
    exact (originalClosedImmersion_artinianCycle_at_image (sectionZeroι a s) z).trans
      (congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) (originalZeroStalk_fullLength_anyFrame a s z e hx))
  · have hrange : Set.range (sectionZeroι a s) = ((sectionZeroIdealSheaf a s).support : Set X) :=
      Scheme.IdealSheafData.range_subschemeι _
    have hout := Eq.mp (congrArg (fun S : Set X => x ∉ S) hrange) hin
    have hz := originalFramePrincipalLength_zero_off_zeroSupport a s e x hx hout
    exact (originalClosedImmersion_artinianCycle_off_image (sectionZeroι a s) x hin).trans
      (congrArg (fun q : ℕ∞ => (q.toNat : ℤ)) hz.symm)

include a in
/-- Actual full principal quotient length is finite at EVERY original ambient point. -/
theorem originalFramePrincipalLength_ne_top {U : X.Opens} (e : LocalBundleFrame L U)
    (x : X) (hx : x ∈ U) :
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
      Ideal.span {originalSectionFrameGerm e s x hx}) ≠ ⊤ := by
  by_cases hin : x ∈ Set.range (sectionZeroι a s)
  · obtain ⟨z, rfl⟩ := hin
    rw [← originalZeroStalk_fullLength_anyFrame a s z e hx]
    exact artinianLocalLength_ne_top _ z
  · have hrange : Set.range (sectionZeroι a s) = ((sectionZeroIdealSheaf a s).support : Set X) :=
      Scheme.IdealSheafData.range_subschemeι _
    have hout := Eq.mp (congrArg (fun S : Set X => x ∉ S) hrange) hin
    rw [originalFramePrincipalLength_zero_off_zeroSupport a s e x hx hout]
    exact ENat.zero_ne_top

/-- Actual original ambient zero cycle is supported inside ENTIRE original actual zero-image. -/
theorem originalSectionZeroAmbientCycle_support_subset :
    Function.support (originalSectionZeroAmbientCycle a s) ⊆ Set.range (sectionZeroι a s) := by
  intro x hx
  by_contra hout
  exact hx (originalClosedImmersion_artinianCycle_off_image (sectionZeroι a s) x hout)

/-- All original ambient zero-cycle coefficients have genuine finite original support. -/
theorem originalSectionZeroAmbientCycle_support_finite :
    (Function.support (originalSectionZeroAmbientCycle a s)).Finite :=
  (Set.finite_range (sectionZeroι a s)).subset (originalSectionZeroAmbientCycle_support_subset a s)

/-- Independent ORIGINAL structural zero-cycle degree is ENTIRE original ambient zero-cycle sum. -/
theorem originalSectionZeroStructuralDegree_eq_finsum (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) (b : Spec (.of ℂ)) :
    artinianStructuralPushforward (E.sectionZero a s) b = ∑ᶠ x : X, originalSectionZeroAmbientCycle a s x := by
  classical
  let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
  rw [artinianStructuralPushforward_apply]
  symm
  calc
    _ = ∑ᶠ x ∈ Set.range (sectionZeroι a s), originalSectionZeroAmbientCycle a s x := by
      rw [← finsum_mem_univ]
      apply finsum_mem_inter_support_eq'
      intro x hx
      exact iff_of_true (Set.mem_univ x) (originalSectionZeroAmbientCycle_support_subset a s hx)
    _ = ∑ᶠ z : sectionZeroSubscheme a s, originalSectionZeroAmbientCycle a s (sectionZeroι a s z) :=
      finsum_mem_range (sectionZeroι a s).isClosedEmbedding.injective
    _ = ∑ z : sectionZeroSubscheme a s, artinianZeroCycle (sectionZeroSubscheme a s) z := by
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_congr rfl (fun z _ => originalClosedImmersion_artinianCycle_at_image (sectionZeroι a s) z)
    _ = _ := artinianZeroCycle_sum _

end SGPT.Projective.NumEq.AlgebraicCurveDegree
