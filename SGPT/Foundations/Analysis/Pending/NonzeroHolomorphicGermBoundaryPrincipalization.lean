import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin
import SGPT.Foundations.Analysis.Pending.HironakaAPI2
import SGPT.Foundations.Analysis.Pending.NormalCrossingsInvariance
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

set_option autoImplicit false

/-! # Natural nonzero holomorphic test germs and boundary-compatible local principalization -/

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.NonzeroHolomorphicGermBoundaryPrincipalization

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  NormalCrossings HironakaAdmissibleSequence

/-- One nonzero holomorphic germ supplies a ball whose germs are all nonzero. -/
theorem exists_ball_differentiable_frequently_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : V → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : V), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : V), F z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball (0 : V) r,
      DifferentiableAt ℂ F y ∧ ∃ᶠ z in 𝓝 y, F z ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hF
  have hd : DifferentiableOn ℂ F (ball (0 : V) r) :=
    fun z hz => (hball z hz).differentiableWithinAt
  refine ⟨r, hr, fun y hy => ⟨hball y hy, ?_⟩⟩
  by_contra hfreq
  have hy0 : ∀ᶠ z in 𝓝 y, F z = 0 := by
    simpa only [not_frequently, not_ne_iff] using hfreq
  have hzero := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero
    isOpen_ball (convex_ball (0 : V) r).isPreconnected hd hy hy0 0 (mem_ball_self hr)
  exact hne (hzero.mono fun z hz => not_not.mpr hz)

/-- Coherence and nonzero members for the literal test ideal are internal to the germ consumer. -/
theorem exists_principalization_boundary_of_nonzero_germ
    {n : ℕ} {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel n), F z ≠ 0)
    {E₀ : List (Set (ComplexModel n))} (hE₀ : IsSNCDivisor n E₀) :
    ∃ B : Opens (ComplexModel n), (0 : ComplexModel n) ∈ B ∧
      IsPreconnected (B : Set (ComplexModel n)) ∧
      (∀ z ∈ B, DifferentiableAt ℂ F z) ∧
    ∃ I : GermIdeal n B,
      (∀ y g, I.mem y g ↔ IsInSpanAt (n := n) (· = fun b : B => F b.val) y g) ∧
      I.IsCoherent ∧
    ∃ U : Opens B, {b : B | b.val = 0} ⊆ U ∧ IsCompact (closure (U : Set B)) ∧
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → U) (D : EffectiveDivisor n Y)
      (E : List (Set Y)),
      IsAdmissibleBlowupSequence n U
        ((E₀.map ((Subtype.val : B → ComplexModel n) ⁻¹' ·)).map
          ((Subtype.val : U → B) ⁻¹' ·))
        ((Subtype.val : U → B) ⁻¹' I.zeroLocus) Y π E ∧
      IsSNCDivisor n E ∧
      GermIdeal.pullback (m := n) π (GermIdeal.pullback (m := n)
        (Subtype.val : U → B) I) = D.ideal ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧
      D.support = π ⁻¹' ((Subtype.val : U → B) ⁻¹' I.zeroLocus) ∧
      IsIsomorphismOver n π ((Subtype.val : U → B) ⁻¹' I.zeroLocus)ᶜ := by
  classical
  obtain ⟨r, hr, hball⟩ := exists_ball_differentiable_frequently_ne_zero hF hne
  let B : Opens (ComplexModel n) := ⟨ball 0 r, isOpen_ball⟩
  let g : B → ℂ := fun b => F b.val
  have hd (b : B) : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g b := by
    apply (mdifferentiableAt_comp_val_iff B).mpr
    simpa only [mdifferentiableAt_iff_differentiableAt] using (hball b.val b.property).1
  have hg (b : B) : HolomorphicAt n g b := Eventually.of_forall hd
  have hnon (b : B) : ∃ᶠ z in 𝓝 b, g z ≠ 0 := by
    by_contra hfreq
    have hb0 : ∀ᶠ z in 𝓝 b, g z = 0 := by
      simpa only [not_frequently, not_ne_iff] using hfreq
    have hf0 : ∀ᶠ z in 𝓝 b.val, F z = 0 :=
      (eventually_nhds_val_iff B).mpr hb0
    exact (hball b.val b.property).2 (hf0.mono fun z hz => not_not.mpr hz)
  let I : GermIdeal n B := ⟨fun y f => IsInSpanAt (n := n) (· = g) y f⟩
  have hcoh : I.IsCoherent := by
    intro b
    refine ⟨univ, isOpen_univ, mem_univ b, 1, fun _ => g,
      fun _ y _ => (hd y).mdifferentiableWithinAt, fun y _ f => ?_⟩
    change IsInSpanAt (n := n) (· = g) y f ↔
      IsInSpanAt (n := n) (· ∈ range (fun _ : Fin 1 => g)) y f
    constructor
    · exact IsInSpanAt.mono fun s hs => ⟨0, hs.symm⟩
    · refine IsInSpanAt.mono fun s hs => ?_
      obtain ⟨i, hi⟩ := hs
      exact hi.symm
  have hself (b : B) : I.mem b g := by
    change IsInSpanAt (n := n) (fun f => f = g) b g
    exact InvertibleIdealQuotient.isInSpanAt_self rfl (hg b)
  have hmembers : ∀ b, ∃ f, I.mem b f ∧ ∃ᶠ z in 𝓝 b, f z ≠ 0 :=
    fun b => ⟨g, hself b, hnon b⟩
  have hEB : IsSNCDivisor n (E₀.map ((Subtype.val : B → ComplexModel n) ⁻¹' ·)) :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val B) continuous_subtype_val hE₀
  let b₀ : B := ⟨0, mem_ball_self hr⟩
  obtain ⟨U, hU, hUc, Y, hYt, hYc, hYm, π, D, E, hadm, hE, hpb, hsupp, hZ, hiso⟩ :=
    HironakaAPI2.exists_principalization_boundary_local hcoh hmembers hEB
      (isCompact_singleton (x := b₀))
  refine ⟨B, mem_ball_self hr, (convex_ball 0 r).isPreconnected,
    fun z hz => (hball z hz).1, I, fun _ _ => Iff.rfl, hcoh,
    U, ?_, hUc, Y, hYt, hYc, hYm, π, D, E, hadm, hE, hpb, ?_, hZ, hiso⟩
  · intro b hb
    have hbb : b = b₀ := Subtype.ext hb
    exact hU (by simp only [mem_singleton_iff, hbb])
  · simpa only [List.length_map] using hsupp

end SGPT.Foundations.Analysis.Pending.NonzeroHolomorphicGermBoundaryPrincipalization
