import SGPT.Foundations.Analysis.Pending.HolomorphicGermReducednessBridge
import SGPT.Foundations.Analysis.Pending.CoordinatePlaneDivision
import Mathlib.RingTheory.Ideal.Maps

set_option autoImplicit false

/-! # Actual nonlinear holomorphic pullback preserves genuine point truncations -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.HolomorphicPointTruncationPullback

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

private theorem holomorphic_comp {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ (F ∘ η) z := by
  have ht : Tendsto η (𝓝 0) (𝓝 0) := by
    simpa only [hη0] using hη.self_of_nhds.continuousAt.tendsto
  filter_upwards [hη, ht.eventually hF] with z hz hFz
  exact hFz.comp z hz

private def compHom {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) : HolGerm (ComplexModel n) →+* HolGerm (ComplexModel m) where
  toFun g := ⟨(g : Germ (𝓝 (0 : ComplexModel n)) ℂ).compTendsto η
    (by simpa only [hη0] using hη.self_of_nhds.continuousAt.tendsto), by
      obtain ⟨_, F, hF, rfl⟩ := g
      exact ⟨F ∘ η, holomorphic_comp η hη hη0 hF, rfl⟩⟩
  map_one' := rfl
  map_mul' g h := by
    induction g using HolGerm.induction_on with
    | h F hF =>
      induction h using HolGerm.induction_on with
      | h G hG => rfl
  map_zero' := rfl
  map_add' g h := by
    induction g using HolGerm.induction_on with
    | h F hF =>
      induction h using HolGerm.induction_on with
      | h G hG => rfl

private theorem compHom_mk {m n : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    compHom η hη hη0 (HolGerm.mk F hF) =
      HolGerm.mk (F ∘ η) (holomorphic_comp η hη hη0 hF) := rfl

private theorem mem_coordinate_span_of_zero {n : ℕ} {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) (hF0 : F 0 = 0) :
    HolGerm.mk F hF ∈ Ideal.span (Set.range fun j : Fin n => HolGerm.mk
      (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j)) := by
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      z ∈ complexCoordinatePlane n 0 → F z = 0 := by
    filter_upwards [] with z hz
    have hz0 : z = 0 := by
      ext j
      exact hz j (Nat.zero_le _)
    simpa only [hz0] using hF0
  obtain ⟨H, _hH0, hH, heq⟩ := CoordinatePlaneDivision.exists_eq_sum_coord_mul
    n 0 (by omega) (fun _ _ => rfl) hF hvan
  have hsum := eventually_differentiableAt_sum Finset.univ fun j =>
    eventually_differentiableAt_mul (eventually_differentiableAt_coordinate j) (hH j)
  have hmk : HolGerm.mk F hF = ∑ j : Fin n,
      HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) *
        HolGerm.mk (H j) (hH j) := by
    calc
      HolGerm.mk F hF = HolGerm.mk (fun z => ∑ j : Fin n, z j * H j z) hsum :=
        HolGerm.mk_eq_mk_iff.mpr heq
      _ = _ := by
        rw [HolGerm.mk_sum Finset.univ (fun j z => z j * H j z)
          (fun j => eventually_differentiableAt_mul
            (eventually_differentiableAt_coordinate j) (hH j))]
        exact Finset.sum_congr rfl fun j _ => HolGerm.mk_mul _ _ _ _
  rw [hmk]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _
    (Ideal.subset_span ⟨j, rfl⟩)

/-- Genuine nonlinear holomorphic pullback transports the complete original
family and actual point-power membership in every pair of dimensions. -/
theorem mem_truncation_of_holomorphic_comp {m n r : ℕ}
    (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) (G : Fin r → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    (N : ℕ) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hmem : HolGerm.mk F hF ∈
      Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) ⊔
      (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
        (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) :
    ∃ (hFc : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ (F ∘ η) z)
      (hGc : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ (G i ∘ η) z),
      HolGerm.mk (F ∘ η) hFc ∈
        Ideal.span (Set.range fun i => HolGerm.mk (G i ∘ η) (hGc i)) ⊔
        (Ideal.span (Set.range fun j : Fin m => HolGerm.mk
          (fun z : ComplexModel m => z j) (eventually_differentiableAt_coordinate j))) ^ N := by
  let φ := compHom η hη hη0
  let hFc := holomorphic_comp η hη hη0 hF
  let hGc := fun i => holomorphic_comp η hη hη0 (hG i)
  refine ⟨hFc, hGc, ?_⟩
  have hfamily : Ideal.map φ (Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i))) ≤
      Ideal.span (Set.range fun i => HolGerm.mk (G i ∘ η) (hGc i)) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro g ⟨i, rfl⟩
    change φ (HolGerm.mk (G i) (hG i)) ∈
      Ideal.span (Set.range fun i => HolGerm.mk (G i ∘ η) (hGc i))
    exact Ideal.subset_span ⟨i, rfl⟩
  have hcoordinates : Ideal.map φ (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
      (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ≤
      Ideal.span (Set.range fun j : Fin m => HolGerm.mk
        (fun z : ComplexModel m => z j) (eventually_differentiableAt_coordinate j)) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro g ⟨j, rfl⟩
    change φ (HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j)) ∈
      Ideal.span (Set.range fun j : Fin m => HolGerm.mk
        (fun z : ComplexModel m => z j) (eventually_differentiableAt_coordinate j))
    rw [compHom_mk]
    exact mem_coordinate_span_of_zero _ (by simp only [Function.comp_apply, hη0, PiLp.zero_apply])
  have hm := Ideal.mem_map_of_mem φ hmem
  rw [Ideal.map_sup, Ideal.map_pow] at hm
  exact (sup_le_sup hfamily (pow_le_pow_left' hcoordinates N)) hm

end
end SGPT.Foundations.Analysis.Pending.HolomorphicPointTruncationPullback
