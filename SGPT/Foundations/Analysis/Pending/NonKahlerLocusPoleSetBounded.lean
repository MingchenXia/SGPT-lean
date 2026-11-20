import SGPT.Foundations.Analysis.Pending.QuasiEquisingularKahlerCurrent
import SGPT.Foundations.Analysis.Pending.AnalyticNoetherProperty
import SGPT.Foundations.Analysis.Pending.KahlerCurrentMax

set_option autoImplicit false

/-!
# Boucksom's theorem 3.17 in the bounded-remainder convention

Source: Boucksom, *Divisorial Zariski decompositions*, Theorem 3.17; Copy-4,
`sec:nK` (`main-Nulllocus.tex:505-510`, stated for analytic singularities of type
`(c, 𝔞)` with a merely BOUNDED remainder, as defined at `main-Nulllocus.tex:300-306`);
blueprint `ana:nonkahler-locus-analytic`.

This is the same minimality argument as `Pending.NonKahlerLocusPoleSet`, but run
entirely in the convention in which the source states the theorem: chartwise
logarithmic presentations with a bounded remainder
(`HasManifoldAnalyticSingularityType`).  Among the polar sets of Kähler currents
in a big class `α` with analytic singularity type (a nonempty family, by
`Pending.QuasiEquisingularKahlerCurrent`) pick a minimal one, `P(S)`.  It contains
`E_nK(α)`, since a positive Lelong number forces a pole.  Conversely, for any
Kähler current `T`, the maximum `R` of `S` and `T` (`Pending.KahlerCurrentMax`)
has Lelong numbers below both; its regularization `S'` has
`P(S') ⊆ {ν(R) > 0} ⊆ {ν(S) > 0} ⊆ P(S)`, so `P(S') = P(S)` by minimality, and
every point of `P(S)` has `ν(T) ≥ ν(R) > 0`.

Consequences: `E_nK(α)` is an analytic subset, with no appeal to CT22's
smooth-remainder convention.  The approximation step is
`Pending.QuasiEquisingularApproximation.exists_quasiEquisingularApproximation` (Xia SGPT
Theorem 1.6.2), proved from Demailly's approximation theorem in
`Pending.QuasiEquisingularApproximationDemailly`; everything here is sorry-free.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.QuasiEquisingularApproximation

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The polar set of a potential with chartwise analytic singularity type (bounded
remainder) is an analytic subset. -/
theorem isComplexAnalyticSubset_poleSet_of_analyticSingularityType {u : X → EReal}
    (hu : HasManifoldAnalyticSingularityType (n := n) u) :
    IsComplexAnalyticSubset (n := n) (poleSet u) := by
  intro x
  set e := complexChartAt (n := n) x with he
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxsrc
  obtain ⟨c, N, f, hc, ⟨U, hUo, hzU, hf⟩, b, -, heq⟩ := hu e (e.val x) hz
  obtain ⟨t, htp, hto, hzt⟩ := eventually_nhds_iff.mp heq
  refine ⟨{
    generatorCount := N
    generator := f
    coordinateNeighborhood := e.val.target ∩ (U ∩ t)
    isOpen_coordinateNeighborhood := e.val.open_target.inter (hUo.inter hto)
    center_mem_coordinateNeighborhood := ⟨hz, hzU, hzt⟩
    coordinateNeighborhood_subset_target := inter_subset_left
    generator_holomorphic := fun i => (hf i).mono (inter_subset_right.trans inter_subset_left)
    zeroLocus := ?_ }⟩
  intro y hysrc hymem
  have hyy : e.val.symm (e.val y) = y := e.val.left_inv hysrc
  have h1 := htp (e.val y) hymem.2.2
  simp only [chartFunction, hyy] at h1
  simp only [mem_poleSet, h1]
  exact scaled_generatorLog_add_eq_bot_iff f (e.val y) hc (b (e.val y))

variable [CompactSpace X]

/-- **Boucksom, Theorem 3.17, bounded convention.**  A big class contains a Kähler
current with chartwise analytic singularity type whose polar set is exactly
`E_nK(α)`. -/
theorem exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
    (hn : 0 < n) (alpha : RealBottChern n X) (hbig : IsBigClass alpha) :
    ∃ T : KahlerCurrent alpha,
      HasManifoldAnalyticSingularityType (n := n) T.potential ∧
        poleSet T.potential = nonKahlerLocus alpha := by
  classical
  set 𝒜 : Set (Set X) := {A | ∃ S : KahlerCurrent alpha,
    HasManifoldAnalyticSingularityType (n := n) S.potential ∧ poleSet S.potential = A}
    with h𝒜def
  have h𝒜 : ∀ A ∈ 𝒜, IsComplexAnalyticSubset (n := n) A := by
    rintro A ⟨S, hS, rfl⟩
    exact isComplexAnalyticSubset_poleSet_of_analyticSingularityType hS
  obtain ⟨T₀⟩ := hbig
  obtain ⟨S₀, hS₀, -⟩ :=
    QuasiEquisingularKahlerCurrent.exists_kahlerCurrent_analyticSingularityType_poleSet_subset T₀
  obtain ⟨A, ⟨S, hS, rfl⟩, hmin⟩ :=
    AnalyticNoetherProperty.exists_minimal_of_isComplexAnalyticSubset 𝒜 h𝒜 ⟨_, S₀, hS₀, rfl⟩
  refine ⟨S, hS, subset_antisymm ?_ ?_⟩
  · intro x hx T
    obtain ⟨R, hR⟩ := KahlerCurrentMax.exists_kahlerCurrent_lelongNumber_le_both S T
    obtain ⟨S', hS'a, hsub⟩ :=
      QuasiEquisingularKahlerCurrent.exists_kahlerCurrent_analyticSingularityType_poleSet_subset R
    have hS'S : poleSet S'.potential ⊆ poleSet S.potential := fun y hy =>
      eq_bot_of_lelongNumber_pos hn S.strictlyPsh.1 ((hsub hy).trans_le (hR y).1)
    have heq := hmin _ ⟨S', hS'a, rfl⟩ hS'S
    rw [← heq] at hx
    exact (hsub hx).trans_le (hR x).2
  · intro x hx
    exact eq_bot_of_lelongNumber_pos hn S.strictlyPsh.1 (hx S)

/-- The non-Kähler locus of a big class is an analytic subset, proved without the
smooth-remainder convention. -/
theorem isComplexAnalyticSubset_nonKahlerLocus (hn : 0 < n)
    (alpha : RealBottChern n X) (hbig : IsBigClass alpha) :
    IsComplexAnalyticSubset (n := n) (nonKahlerLocus alpha) := by
  obtain ⟨T, hsing, hpole⟩ :=
    exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus hn alpha hbig
  rw [← hpole]
  exact isComplexAnalyticSubset_poleSet_of_analyticSingularityType hsing

end

end SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded
