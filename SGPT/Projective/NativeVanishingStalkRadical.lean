import SGPT.NAPotential.GAGAMultSiuGerms
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Actual FULL native vanishing-ideal stalk is radical, from actual
holomorphic combinations and actual pointwise zero germs, no radical
replacement. Blueprint: native-vanishing-stalk-radical.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open Set Filter
open SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold

/-- The FULL actual native ideal of holomorphic germs vanishing along ANY
actual subset is radical; neither coherence nor a radical equality is
supplied. The original span and every actual germ are retained. -/
theorem nativeVanishingStalk_isRadical {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (C : Set M) (p : M) :
    (stalkIdeal (vanishingIdeal (n := n) C) p).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro γ hγ
  obtain ⟨f,hf,rfl⟩ := NativeHolGerm.exists_eq_mk γ
  rw [pow_two] at hγ
  have hcomb := isInSpanAt_of_mk_mem_spanGerms (hf.mul hf) hγ
  obtain ⟨_,K,s,a,hs,_,heq⟩ := hcomb
  have hzero : ∀ᶠ y in 𝓝 p, y∈C → f y=0 := by
    filter_upwards [heq,eventually_all.mpr (fun k => (hs k).2)] with y hy hs' hyC
    have hsq : f y*f y=0 := by
      rw [hy]
      exact Finset.sum_eq_zero fun k _ => by rw [hs' k hyC,mul_zero]
    exact (mul_eq_zero.mp hsq).elim id id
  exact Ideal.subset_span ⟨f,hf,⟨hf,hzero⟩,rfl⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
