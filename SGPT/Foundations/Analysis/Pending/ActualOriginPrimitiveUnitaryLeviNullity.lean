import SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicProjectionElimination
import SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicCoordinates
import SGPT.Foundations.Analysis.Pending.ActualUnitaryLeviProjectedNullity
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Foundations.Analysis.Pending.RegularDirectionDense

set_option autoImplicit false

/-! # Actual local Levi nullity from origin-only primitive germs

Actual original primitive germs and a genuine regular direction produce
local projection nullity and the actual directional Levi measure.
Nearby primitive germs or target mass-nullity are not supplied.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian ENNReal InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualOriginPrimitiveUnitaryLeviNullity
open FirstPass DivisorRegularLocus DivisorIntegrationCurrent LelongPoincareSlices
open ActualPrimitiveHolomorphicGraphProjection ActualPrimitiveHolomorphicCoordinates
open ActualPrimitiveHolomorphicProjectionElimination RegularDirectionDense

/-- Actual unitary coordinates transport origin-only primitivity and
produce a genuine local product with null transverse common-zero projection. -/
theorem exists_unitary_product_projection_common_zero_null {n m N : ℕ}
    {v : ComplexModel n} (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    (f : Fin N → ComplexModel n → ℂ) (hp : IsPrimitiveAt f 0)
    (k : Fin N) (haxis : RegularAlong (f k) v) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      volume (S.π '' {x : ComplexModel n |
        x ∈ splitHomeomorph hv S '' ((ball (0 : ℂ) ε) ×ˢ (ball (0 : ComplexModel m) δ)) ∧
          ∀ i, f i x = 0}) = 0 := by
  classical
  have hinner : (innerSL ℂ v) v ≠ 0 := by
    simp [innerSL_apply_apply, inner_self_eq_norm_sq_to_K, hv]
  let B := S.equiv (innerSL ℂ v) hinner
  let A : (ComplexModel m × ℂ) ≃L[ℂ] ComplexModel n :=
    (ContinuousLinearEquiv.prodComm ℂ (ComplexModel m) ℂ).trans B.symm
  have hA : ∀ z : ComplexModel m × ℂ, A z = z.2 • v + S.ι z.1 := by
    intro z
    apply B.injective
    simp [A, B, Splitting.equiv_apply, S.inner_smul_add hv, S.π_smul_add, Prod.swap]
  let F : Fin N → ComplexModel m × ℂ → ℂ := fun i z => f i (A z)
  have hpF : IsPrimitiveAt F 0 := isPrimitiveAt_comp_equiv A f 0 (by simpa using hp)
  obtain ⟨hF, hP⟩ := hpF
  have hF' : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel m × ℂ), DifferentiableAt ℂ (F i) z := by
    simpa only [add_zero] using hF
  have hP' : ∀ q : HolGerm (ComplexModel m × ℂ),
      (∀ i, q ∣ HolGerm.mk (F i) (hF' i)) → IsUnit q := by
    simpa only [add_zero] using hP
  have haxisF : ¬ ∀ᶠ t : ℂ in 𝓝 0, F k (0, t) = 0 := by
    simpa only [F, hA, map_zero, add_zero, RegularAlong] using haxis
  obtain ⟨δ, hδ, ε, hε, hnull⟩ :=
    exists_product_projection_common_zero_null F hF' k haxisF hP'
  refine ⟨δ, hδ, ε, hε, measure_mono_null ?_ hnull⟩
  rintro _ ⟨x, ⟨⟨z, hz, hzx⟩, hzero⟩, rfl⟩
  have hAx : A (z.2, z.1) = x := by
    simpa only [hA, splitHomeomorph_apply, splitMap_apply] using hzx
  refine ⟨(z.2, z.1), ⟨hz.2, hz.1, ?_⟩, ?_⟩
  · intro i
    change f i (A (z.2, z.1)) = 0
    rw [hAx]
    exact hzero i
  · change z.2 = S.π x
    rw [← hzx, splitHomeomorph_apply, splitMap_apply, S.π_smul_add]

/-- The original unbounded noncollapsed psh potential and origin-primitive
germs internally produce a local carried Levi measure killing their common zeros. -/
theorem exists_local_directional_measure_null_origin_primitive_common_zeros {n m N : ℕ}
    {v : ComplexModel n} (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    (f : Fin N → ComplexModel n → ℂ) (hprimitive : IsPrimitiveAt f 0)
    (k : Fin N) (haxis : RegularAlong (f k) v)
    (Ω : Opens (ComplexModel n)) (hΩ : IsPreconnected (Ω : Set (ComplexModel n)))
    (h0 : (0 : ComplexModel n) ∈ Ω) (p : ComplexModel n → EReal)
    (hp : PlurisubharmonicOn p Ω) (hne : ∃ a ∈ Ω, p a ≠ ⊥) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      let Q : Opens (ComplexModel n) :=
        ⟨splitHomeomorph hv S '' ((ball (0 : ℂ) ε) ×ˢ (ball (0 : ComplexModel m) δ)),
          (splitHomeomorph hv S).isOpenMap _ (isOpen_ball.prod isOpen_ball)⟩
      ∃ (hsub : (Q : Set (ComplexModel n)) ⊆ Ω)
        (hQ : IsPreconnected (Q : Set (ComplexModel n)))
        (hneQ : ∃ a ∈ Q, p a ≠ ⊥) (μ : Measure (ComplexModel n)),
        μ (Q : Set (ComplexModel n))ᶜ = 0 ∧
        (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Q → μ K < ⊤) ∧
        (∀ φ : 𝓓(Q, ℝ), (∫ x, φ x ∂μ) =
          distributionalLeviCLM v (pshRegularDistribution (hp.mono hsub) volume hQ hneQ) φ) ∧
        μ {x : ComplexModel n | x ∈ Q ∧ ∀ i, f i x = 0} = 0 := by
  classical
  obtain ⟨δ₀, hδ₀, ε₀, hε₀, hnull₀⟩ :=
    exists_unitary_product_projection_common_zero_null hv S f hprimitive k haxis
  have hopen : IsOpen ((splitHomeomorph hv S) ⁻¹' (Ω : Set (ComplexModel n))) :=
    Ω.isOpen.preimage (splitHomeomorph hv S).continuous
  have hzero : (0 : ℂ × ComplexModel m) ∈
      (splitHomeomorph hv S) ⁻¹' (Ω : Set (ComplexModel n)) := by
    change splitMap S 0 ∈ Ω
    rw [map_zero]
    exact h0
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  let δ := min δ₀ ρ
  let ε := min ε₀ ρ
  have hδ : 0 < δ := lt_min hδ₀ hρ
  have hε : 0 < ε := lt_min hε₀ hρ
  let U : Opens ℂ := ⟨ball 0 ε, isOpen_ball⟩
  let V : Opens (ComplexModel m) := ⟨ball 0 δ, isOpen_ball⟩
  let Q : Opens (ComplexModel n) :=
    ⟨splitHomeomorph hv S '' ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))),
      (splitHomeomorph hv S).isOpenMap _ (U.isOpen.prod V.isOpen)⟩
  have hQsub : (Q : Set (ComplexModel n)) ⊆ Ω := by
    rintro _ ⟨z, hz, rfl⟩
    apply hρsub
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    exact ⟨(mem_ball_zero_iff.mp hz.1).trans_le (min_le_right _ _),
      (mem_ball_zero_iff.mp hz.2).trans_le (min_le_right _ _)⟩
  have hQnonempty : (Q : Set (ComplexModel n)).Nonempty := by
    refine ⟨splitHomeomorph hv S 0, ?_⟩
    exact ⟨0, ⟨mem_ball_self hε, mem_ball_self hδ⟩, rfl⟩
  have hneQ : ∃ a ∈ Q, p a ≠ ⊥ :=
    OpensRestrictionMeasure.exists_ne_bot_of_isOpen_subset hp hΩ hne
      Q.isOpen hQnonempty hQsub
  have hprod : IsPreconnected ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))) :=
    (convex_ball (0 : ℂ) ε).isPreconnected.prod
      (convex_ball (0 : ComplexModel m) δ).isPreconnected
  obtain ⟨hQ, μ, hcarry, hfinite, hrep, hnull⟩ :=
    ActualUnitaryLeviProjectedNullity.exists_unitary_directional_measure_null_projection
      hv S U V p (hp.mono hQsub) hprod hneQ
  have hproj : volume (S.π '' {x : ComplexModel n |
      x ∈ Q ∧ ∀ i, f i x = 0}) = 0 := by
    apply measure_mono_null _ hnull₀
    apply Set.image_mono
    rintro x ⟨⟨z, hz, hzx⟩, hzero⟩
    refine ⟨⟨z, ⟨ball_subset_ball (min_le_left _ _) hz.1,
      ball_subset_ball (min_le_left _ _) hz.2⟩, hzx⟩, hzero⟩
  exact ⟨δ, hδ, ε, hε, hQsub, hQ, hneQ, μ, hcarry, hfinite, hrep, hnull _ hproj⟩

end SGPT.Foundations.Analysis.Pending.ActualOriginPrimitiveUnitaryLeviNullity
