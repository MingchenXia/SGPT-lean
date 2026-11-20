import SGPT.Foundations.Analysis.Pending.NonzeroHolomorphicGermBoundaryPrincipalization

set_option autoImplicit false

/-! # The complete original finite holomorphic family supplies actual local principalization -/

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.FiniteHolomorphicFamilyLocalPrincipalization

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  NormalCrossings HironakaAdmissibleSequence

noncomputable section

/-- Every original generator is retained literally and all local
principalization hypotheses are produced from one nonzero family germ. -/
theorem exists_principalization_of_nonzero_family_germ {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    (hne : ∃ i, ∃ᶠ z in 𝓝 (0 : ComplexModel n), G i z ≠ 0) :
    ∃ B : Opens (ComplexModel n), (0 : ComplexModel n) ∈ B ∧
      IsPreconnected (B : Set (ComplexModel n)) ∧
      (∀ i, ∀ z ∈ B, DifferentiableAt ℂ (G i) z) ∧
    ∃ I : GermIdeal n B,
      (∀ y g, I.mem y g ↔
        IsInSpanAt (n := n) (· ∈ Set.range fun i => fun b : B => G i b.val) y g) ∧
      I.IsCoherent ∧
    ∃ U : Opens B, {b : B | b.val = 0} ⊆ U ∧ IsCompact (closure (U : Set B)) ∧
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → U) (D : EffectiveDivisor n Y)
      (E : List (Set Y)),
      IsAdmissibleBlowupSequence n U []
        ((Subtype.val : U → B) ⁻¹' I.zeroLocus) Y π E ∧
      GermIdeal.pullback (m := n) π (GermIdeal.pullback (m := n)
        (Subtype.val : U → B) I) = D.ideal ∧
      IsSNCDivisor n E ∧ D.support = ⋃ H ∈ E, H ∧
      D.support = π ⁻¹' ((Subtype.val : U → B) ⁻¹' I.zeroLocus) ∧
      IsIsomorphismOver n π ((Subtype.val : U → B) ⁻¹' I.zeroLocus)ᶜ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨r₁, hr₁, hrow⟩ :=
    NonzeroHolomorphicGermBoundaryPrincipalization.exists_ball_differentiable_frequently_ne_zero
      (hG i₀) hi₀
  obtain ⟨r₂, hr₂, hfamily⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_all.mpr hG)
  let B : Opens (ComplexModel n) := ⟨ball 0 (min r₁ r₂), isOpen_ball⟩
  have hB₁ : (B : Set (ComplexModel n)) ⊆ ball 0 r₁ :=
    ball_subset_ball (min_le_left _ _)
  have hB₂ : (B : Set (ComplexModel n)) ⊆ ball 0 r₂ :=
    ball_subset_ball (min_le_right _ _)
  have h0B : (0 : ComplexModel n) ∈ B := mem_ball_self (lt_min hr₁ hr₂)
  let g : Fin s → B → ℂ := fun i b => G i b.val
  have hd (i : Fin s) (b : B) :
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) b := by
    apply (mdifferentiableAt_comp_val_iff B).mpr
    simpa only [mdifferentiableAt_iff_differentiableAt] using
      hfamily b.val (hB₂ b.property) i
  have hg (i : Fin s) (b : B) : HolomorphicAt n (g i) b :=
    Eventually.of_forall (hd i)
  have hnon (b : B) : ∃ᶠ z in 𝓝 b, g i₀ z ≠ 0 := by
    by_contra hfreq
    have hb0 : ∀ᶠ z in 𝓝 b, g i₀ z = 0 := by
      simpa only [not_frequently, not_ne_iff] using hfreq
    have hf0 : ∀ᶠ z in 𝓝 b.val, G i₀ z = 0 :=
      (eventually_nhds_val_iff B).mpr hb0
    exact (hrow b.val (hB₁ b.property)).2 (hf0.mono fun z hz => not_not.mpr hz)
  let I : GermIdeal n B := ⟨fun y f => IsInSpanAt (n := n) (· ∈ Set.range g) y f⟩
  have hcoh : I.IsCoherent := by
    intro b
    exact ⟨univ, isOpen_univ, mem_univ b, s, g,
      fun i y _ => (hd i y).mdifferentiableWithinAt, fun _ _ _ => Iff.rfl⟩
  have hmembers : ∀ b, ∃ f, I.mem b f ∧ ∃ᶠ z in 𝓝 b, f z ≠ 0 := by
    intro b
    exact ⟨g i₀, InvertibleIdealQuotient.isInSpanAt_self ⟨i₀, rfl⟩ (hg i₀ b), hnon b⟩
  let b₀ : B := ⟨0, h0B⟩
  obtain ⟨U, hU, hUc, Y, hYt, hYc, hYm, π, D, E, hadm, hpb, hE, hsupp, hZ, hiso⟩ :=
    HironakaAPI.exists_principalization_local hcoh hmembers (isCompact_singleton (x := b₀))
  refine ⟨B, h0B, (convex_ball 0 (min r₁ r₂)).isPreconnected,
    (fun i z hz => hfamily z (hB₂ hz) i), I, (fun _ _ => Iff.rfl), hcoh,
    U, ?_, hUc, Y, hYt, hYc, hYm, π, D, E, hadm, hpb, hE, hsupp, hZ, hiso⟩
  intro b hb
  have hbb : b = b₀ := Subtype.ext hb
  exact hU (by simp only [mem_singleton_iff, hbb])

end
end SGPT.Foundations.Analysis.Pending.FiniteHolomorphicFamilyLocalPrincipalization
