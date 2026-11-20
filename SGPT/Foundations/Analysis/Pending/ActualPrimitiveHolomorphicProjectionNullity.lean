import SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicCoordinates
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin

set_option autoImplicit false

/-! # Actual projection nullity for primitive holomorphic families

Only actual holomorphic functions and the natural all-centre algebraic
primitive germ condition are inputs.  Divisor bad projections, genuine
regular graphs and actual countable covers supply projection nullity.
Uniform primitive remainders after origin factorization remain separate.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicProjectionNullity

open DivisorRegularLocus ActualPrimitiveHolomorphicGraphProjection

private theorem projection_null_of_nonzero_member {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {m N : ℕ}
    (f : Fin N → V → ℂ) (j : Fin N) {Ω : Set V} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ (f j) Ω)
    (hg0 : ∀ x ∈ Ω, ∃ᶠ y in 𝓝 x, f j y ≠ 0)
    (hprim : ∀ x ∈ Ω, IsPrimitiveAt f x) {u : V} (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) :
    volume (S.π '' {x | x ∈ Ω ∧ ∀ i, f i x = 0}) = 0 := by
  classical
  let T : Set V := {x | x ∈ Ω ∧ ∀ i, f i x = 0}
  let R := transverseLocus (f j) u
  have hbad : volume (S.π '' (T \ R)) = 0 := by
    apply measure_mono_null (image_mono ?_)
      (DivisorSingularProjection.measure_image_bad_eq_zero volume hΩ hg hg0 hu S)
    intro x hx
    exact ⟨hx.1.1, hx.1.2 j, hx.2⟩
  have hreg : volume (S.π '' (T ∩ R)) = 0 := by
    apply DivisorSingularProjection.measure_image_null_of_local volume S.π
    intro x hx
    obtain ⟨P⟩ := hx.2.1
    have hxu := (P.mem_transverseLocus_iff P.mem (hx.1.2 j) u).mp hx.2
    obtain ⟨D, W, k, hVo, hxV, hVU, hVtr, hWo, hxW, hk, hgraph, hzero, horder⟩ :=
      P.exists_graph_slices hu S hxu
    let G : EuclideanSpace ℂ (Fin m) → V := fun w => k w • u + S.ι w
    let W' := W ∩ G ⁻¹' Ω
    have hGc : ContinuousOn G W :=
      (hk.continuousOn.smul continuousOn_const).add S.ι.continuous.continuousOn
    have hW'o : IsOpen W' := hGc.isOpen_inter_preimage hWo hΩ
    have hp : ∀ w ∈ W', IsPrimitiveAt f (k w • u + S.ι w) :=
      fun w hw => hprim (G w) hw.2
    have hnull := ActualPrimitiveHolomorphicCoordinates.volume_splitting_graph_common_zero_eq_zero
      f hu S hW'o (hk.mono inter_subset_left) hp
    refine ⟨D ∩ Ω, (hVo.inter hΩ).mem_nhds ⟨hxV, hx.1.1⟩, ?_⟩
    apply measure_mono_null ?_ hnull
    rintro w ⟨y, hy, rfl⟩
    have hd : ⟪u, y⟫_ℂ • u + S.ι (S.π y) = y := (S.decomp y).symm
    have hn : ⟪u, y⟫_ℂ • u + S.ι (S.π y) ∈ D := hd.symm ▸ hy.1.1
    have hz : f j (⟪u, y⟫_ℂ • u + S.ι (S.π y)) = 0 := hd.symm ▸ hy.2.1.2 j
    obtain ⟨hw, hky⟩ := (hzero (S.π y) ⟪u, y⟫_ℂ hn).mp hz
    have hGy : k (S.π y) • u + S.ι (S.π y) = y := hky ▸ hd
    refine ⟨⟨hw, ?_⟩, ?_⟩
    · change G (S.π y) ∈ Ω
      simpa only [G, hGy] using hy.2.1.1
    · intro i
      simpa only [hGy] using hy.2.1.2 i
  have hsub : T ⊆ (T \ R) ∪ (T ∩ R) := by
    intro x hx
    by_cases hr : x ∈ R
    · exact Or.inr ⟨hx, hr⟩
    · exact Or.inl ⟨hx, hr⟩
  apply measure_mono_null (image_mono hsub)
  rw [image_union]
  exact measure_union_null hbad hreg

/-- Genuine holomorphic functions and all-centre primitive germs internally
produce nullity of the actual projected common-zero set. -/
theorem volume_projection_common_zero_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {m N : ℕ}
    (f : Fin N → V → ℂ) {Ω : Set V} (hΩ : IsOpen Ω)
    (hf : ∀ i, DifferentiableOn ℂ (f i) Ω)
    (hprimitive : ∀ x ∈ Ω, IsPrimitiveAt f x) {u : V} (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) :
    volume (S.π '' {x | x ∈ Ω ∧ ∀ i, f i x = 0}) = 0 := by
  classical
  apply DivisorSingularProjection.measure_image_null_of_local volume S.π
  intro x hx
  obtain ⟨hF, hp⟩ := hprimitive x hx.1
  have hsome : ∃ j, HolGerm.mk (fun y => f j (y + x)) (hF j) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hunit : IsUnit (0 : HolGerm V) := hp 0 fun j => by
      rw [hnone j]
    exact not_isUnit_zero hunit
  obtain ⟨j, hj⟩ := hsome
  have hnex : ¬ ∀ᶠ y in 𝓝 x, f j y = 0 := by
    intro he
    apply hj
    rw [← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    have hc : Continuous (fun y : V => y + x) := continuous_id.add continuous_const
    have ht : Tendsto (fun y : V => y + x) (𝓝 0) (𝓝 x) := by
      simpa only [zero_add] using hc.tendsto (0 : V)
    exact ht.eventually he
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp hΩ x hx.1
  have hg : DifferentiableOn ℂ (f j) (ball x r) := (hf j).mono hB
  have hg0 : ∀ y ∈ ball x r, ∃ᶠ z in 𝓝 y, f j z ≠ 0 := by
    intro y hy
    apply Filter.not_eventually.mp
    intro hyzero
    exact hnex (RiemannExtension.eventually_eq_zero_of_eventually_eq_zero isOpen_ball
      (convex_ball x r).isPreconnected hg hy hyzero x (mem_ball_self hr))
  have hnull := projection_null_of_nonzero_member f j isOpen_ball hg hg0
    (fun y hy => hprimitive y (hB hy)) hu S
  refine ⟨ball x r, ball_mem_nhds x hr, measure_mono_null (image_mono ?_) hnull⟩
  intro y hy
  exact ⟨hy.1, hy.2.2⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicProjectionNullity
