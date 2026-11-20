import SGPT.Okounkov.FlagValuationPrefixIdeals
import SGPT.GAGA.ChowBlImage

/-!
# Actual homogeneous Chow ideals of native valuation prefixes

Chow's existing actual image theorem manufactures homogeneous polynomial
ideals of each literal original flag member. Its native local generation
theorem and the proved prefix criterion identify those same polynomials
with the actual positive prefix ideal. No polynomial ideal or flag/centre
identification is supplied as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.GAGA.Core

/-- The actual homogeneous polynomials of every original projective flag
member generate its actual positive native prefix ideal in every affine
chart containing the original endpoint. -/
theorem exists_originalFlagPrefix_chow_generators {n N : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (Ψ : F.carrier → ComplexProjectiveSpace N) (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (k : ℕ) (hk : k ≤ n) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ K : ℕ, ∃ P : Fin K → MvPolynomial (Fin (N + 1)) ℂ,
      (∀ j, (P j).IsHomogeneous d) ∧
      (coneIdeal (Ψ '' F.flag ⟨k, Nat.lt_succ_of_le hk⟩)).GeneratedOn
        (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
        (fun j => SGPT.GAGA.PN.polyTuple (P j)) ∧
      Ψ '' F.flag ⟨k, Nat.lt_succ_of_le hk⟩ =
        {q | ∀ j, MvPolynomial.eval q.rep (P j) = 0} ∧
      ∀ (i : Fin (N + 1)), Ψ x.1 ∈ (affineChart i).source →
      ∀ (f : F.carrier → ℂ) (hf : HolomorphicAt n f x.1),
        (0 < ValCurr.prefixValuation hk (originalFlagGermValuation F x) (NativeHolGerm.mk f hf) ↔
          IsInSpanAt (n := n) (· ∈ range fun j => genFun Ψ i (P j)) x.1 f) := by
  classical
  have hsub : IsClosedSubmanifold n (F.flag ⟨k, Nat.lt_succ_of_le hk⟩) :=
    ⟨(F.smooth.2.2 _).1, fun y hy => ⟨n - k, (F.smooth.2.2 _).2.2 y hy⟩⟩
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hsub
  obtain ⟨d₀, hd₀⟩ := chow_image hΨ hC
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨μ, hμ, Q, hQ, hgen, hzero⟩ := hd₀ d hd
  let : Fintype μ := hμ
  let e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ
  let P : Fin (Fintype.card μ) → MvPolynomial (Fin (N + 1)) ℂ := fun j => Q (e.symm j)
  have hgenP : (coneIdeal (Ψ '' F.flag ⟨k, Nat.lt_succ_of_le hk⟩)).GeneratedOn
      (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun j => SGPT.GAGA.PN.polyTuple (P j)) := by
    apply hgen.of_generators
    · exact fun j b => hgen.1 (e.symm j) b
    · exact fun y hy j => hgen.gen_mem hy (e.symm j)
    · intro y hy j
      have hh := isCombinationAt_gen (fun a => SGPT.GAGA.PN.polyTuple (P a)) y (e j)
      simpa only [P, e.symm_apply_apply] using hh
  have hzeroP : Ψ '' F.flag ⟨k, Nat.lt_succ_of_le hk⟩ =
      {q | ∀ j, MvPolynomial.eval q.rep (P j) = 0} := by
    rw [hzero]
    ext q
    constructor
    · exact fun h j => h (e.symm j)
    · intro h j
      simpa only [P, e.symm_apply_apply] using h (e j)
  refine ⟨Fintype.card μ, P, fun j => hQ (e.symm j), hgenP, hzeroP, ?_⟩
  intro i hi f hf
  exact (originalFlagPrefixValuation_pos_iff_vanishingIdeal F x k hk f hf).trans
    (vanishingIdeal_mem_iff_isInSpanAt_genFun hΨ hgenP hi f)

end SGPT.Okounkov
