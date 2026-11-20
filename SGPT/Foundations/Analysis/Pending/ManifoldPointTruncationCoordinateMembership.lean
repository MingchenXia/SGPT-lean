import SGPT.Foundations.Analysis.Pending.CoherentStalkPointTruncationClosure
import SGPT.Foundations.Analysis.Pending.CoordinatePlaneDivision
import SGPT.Foundations.Analysis.Pending.HolomorphicGermReducednessBridge

set_option autoImplicit false

/-! # Original point powers and complete stalks in actual centered coordinate germs -/

open Set Filter
open scoped Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldPointTruncationCoordinateMembership

open FirstPass FirstPass.HolomorphicIdealSheaves GermIdealOrder
  IdealWeightPowers RestrictedIdealExtension HolomorphicGermReducednessBridge

noncomputable section

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem holomorphic_adapted (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {F : X → ℂ} (hF : HolomorphicAt n F x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z := by
  have hs := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => F) F).mp
      (InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hF)
  exact hs.1.mono fun _ hz => hz.differentiableAt

private theorem span_mem_ring (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    (J : Ideal (HolGerm (ComplexModel n))) (S : (X → ℂ) → Prop)
    (hS : ∀ s, S s → HolomorphicAt n s x)
    (hmem : ∀ s (hs : S s),
      HolGerm.mk (fun z => s ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (holomorphic_adapted x Φ h0 (hS s hs)) ∈ J)
    {F : X → ℂ} (hF : HolomorphicAt n F x)
    (hspan : IsInSpanAt (n := n) S x F) :
    HolGerm.mk (fun z => F ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (holomorphic_adapted x Φ h0 hF) ∈ J := by
  obtain ⟨_, k, s, a, hs, ha, heq⟩ := hspan
  have hsource : IsInSpanAt (n := n) (· ∈ range s) x F :=
    ⟨hF, k, s, a, fun i => ⟨i, rfl⟩, ha, heq⟩
  have hadapt := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 s F).mp hsource
  have hring := (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
    (fun i z => s i ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
    (fun i => holomorphic_adapted x Φ h0 (hS (s i) (hs i)))
    (holomorphic_adapted x Φ h0 hF)).mp hadapt
  apply (Ideal.span_le.mpr ?_) hring
  rintro g ⟨i, rfl⟩
  exact hmem (s i) (hs i)

private theorem coordinate_mem_of_zero {F : ComplexModel n → ℂ}
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

private theorem point_mem_ring (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {g : X → ℂ} (hg : (pointIdeal n x).mem x g) :
    HolGerm.mk (fun z => g ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (holomorphic_adapted x Φ h0 hg.1) ∈
        Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j)) := by
  apply coordinate_mem_of_zero
  have hΦ0 : Φ.invFun 0 = (chartAt (ComplexModel n) x) x := by
    rw [← h0, Φ.left_inv _ Φ.center_mem_source]
  rw [hΦ0, (chartAt (ComplexModel n) x).left_inv (mem_chart_source (ComplexModel n) x)]
  exact apply_eq_zero_of_mem_pointIdeal hg

private theorem point_power_mem_ring (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0) (N : ℕ)
    {g : X → ℂ} (hg : (idealPow (pointIdeal n x) N).mem x g) :
    HolGerm.mk (fun z => g ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (holomorphic_adapted x Φ h0 (holomorphicAt_of_mem_idealPow hg)) ∈
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N := by
  induction N generalizing g with
  | zero => simp
  | succ N ih =>
    apply span_mem_ring x Φ h0 _
      (fun s => ∃ a b, (idealPow (pointIdeal n x) N).mem x a ∧
        (pointIdeal n x).mem x b ∧ s = a * b)
      (fun s hs => by
        obtain ⟨a, b, ha, hb, rfl⟩ := hs
        exact (holomorphicAt_of_mem_idealPow ha).mul hb.1)
      ?_ (holomorphicAt_of_mem_idealPow hg) (mem_idealPow_succ_iff.mp hg)
    rintro s ⟨a, b, ha, hb, rfl⟩
    have heq : HolGerm.mk
        (fun z => (a * b) ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (holomorphic_adapted x Φ h0 ((holomorphicAt_of_mem_idealPow ha).mul hb.1)) =
      HolGerm.mk (fun z => a ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (holomorphic_adapted x Φ h0 (holomorphicAt_of_mem_idealPow ha)) *
      HolGerm.mk (fun z => b ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (holomorphic_adapted x Φ h0 hb.1) := by
      rw [← HolGerm.mk_mul]
      rfl
    rw [heq, pow_succ]
    exact Ideal.mul_mem_mul (ih ha) (point_mem_ring x Φ h0 hb)

/-- A literal member of the original ideal sum gives the actual full-family
coordinate ring membership, with all representatives produced internally. -/
theorem mem_coordinate_truncation_of_original_membership {s : ℕ} (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    (I : GermIdeal n X) (G : Fin s → X → ℂ)
    (hG : ∀ i, HolomorphicAt n (G i) x)
    (hfull : ∀ g : X → ℂ, I.mem x g ↔ IsInSpanAt (n := n) (· ∈ range G) x g)
    (N : ℕ) {F : X → ℂ}
    (hmem : (sumIdeal I (idealPow (pointIdeal n x) N)).mem x F) :
    ∃ (hFT : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
        (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z)
      (hGT : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
        (fun w => G i ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z),
      HolGerm.mk (fun z => F ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) hFT ∈
        Ideal.span (Set.range fun i => HolGerm.mk
          (fun z => G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) (hGT i)) ⊔
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N := by
  let hGT := fun i => holomorphic_adapted x Φ h0 (hG i)
  let J : Ideal (HolGerm (ComplexModel n)) := Ideal.span (Set.range fun i =>
    HolGerm.mk (fun z => G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) (hGT i))
  let P : Ideal (HolGerm (ComplexModel n)) := Ideal.span (Set.range fun j : Fin n =>
    HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))
  refine ⟨holomorphic_adapted x Φ h0 hmem.1, hGT, ?_⟩
  apply span_mem_ring x Φ h0 (J ⊔ P ^ N)
    (fun g => I.mem x g ∨ (idealPow (pointIdeal n x) N).mem x g)
    (fun g hg => hg.elim (fun hi => ((hfull g).mp hi).1)
      (fun hp => holomorphicAt_of_mem_idealPow hp)) ?_ hmem.1 hmem
  intro g hg
  rcases hg with hi | hp
  · have hgi : HolomorphicAt n g x := ((hfull g).mp hi).1
    have hadapt := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
      x Φ h0 G g).mp ((hfull g).mp hi)
    have hring := (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
      (fun i z => G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) hGT
      (holomorphic_adapted x Φ h0 hgi)).mp hadapt
    exact (show J ≤ J ⊔ P ^ N from le_sup_left) hring
  · exact (show P ^ N ≤ J ⊔ P ^ N from le_sup_right) (point_power_mem_ring x Φ h0 N hp)

end
end SGPT.Foundations.Analysis.Pending.ManifoldPointTruncationCoordinateMembership
