import SGPT.Foundations.Analysis.Pending.HolomorphicGermPointTruncationClosure
import SGPT.Foundations.Analysis.Pending.EuclideanHolomorphicGermSpan
import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport
import SGPT.Foundations.Analysis.Pending.RestrictedIdealExtension
import SGPT.Foundations.Analysis.Pending.GermIdealOrder

set_option autoImplicit false

/-! # Point truncations detect the literal original coherent stalk

Actual finite generators, a translated preferred chart, and the genuine
holomorphic germ ring identify all point truncation memberships with
membership in the original coherent ideal. No compactness is assumed.
-/

open Set Filter
open scoped Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.CoherentStalkPointTruncationClosure

open FirstPass FirstPass.HolomorphicIdealSheaves GermIdealOrder
  IdealWeightPowers RestrictedIdealExtension

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
    (I : Ideal (HolGerm (ComplexModel n))) (S : (X → ℂ) → Prop)
    (hS : ∀ s, S s → HolomorphicAt n s x)
    (hmem : ∀ s (hs : S s),
      HolGerm.mk (fun z => s ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (holomorphic_adapted x Φ h0 (hS s hs)) ∈ I)
    {F : X → ℂ} (hF : HolomorphicAt n F x)
    (hspan : IsInSpanAt (n := n) S x F) :
    HolGerm.mk (fun z => F ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (holomorphic_adapted x Φ h0 hF) ∈ I := by
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

private theorem point_mem_ring (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {g : X → ℂ} (hg : (pointIdeal n x).mem x g) :
    HolGerm.mk (fun z => g ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (holomorphic_adapted x Φ h0 hg.1) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk]
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
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ N := by
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

/-- Membership in the original coherent stalk is detected by all actual point powers. -/
theorem mem_iff_mem_all_point_truncations (x : X) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) (F : X → ℂ) :
    𝔞.mem x F ↔ ∀ N : ℕ, (sumIdeal 𝔞 (idealPow (pointIdeal n x) N)).mem x F := by
  constructor
  · intro hF N
    exact le_sumIdeal_left h𝔞 x F hF
  · intro hf
    classical
    have hF : HolomorphicAt n F x := (hf 0).1
    let p := (chartAt (ComplexModel n) x) x
    let Φ : LocalHolomorphicEquivAt (n := n) p := {
      source := univ
      target := univ
      isOpen_source := isOpen_univ
      isOpen_target := isOpen_univ
      center_mem_source := mem_univ p
      toFun := fun z => z - p
      invFun := fun z => z + p
      toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
      invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
      mapsTo_toFun := fun _ _ => mem_univ _
      mapsTo_invFun := fun _ _ => mem_univ _
      left_inv := fun z _ => sub_add_cancel z p
      right_inv := fun z _ => add_sub_cancel_right z p }
    have h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0 := sub_self p
    obtain ⟨U, hU, hxU, s, G, hGdiff, hGiff⟩ := h𝔞 x
    have hG (i : Fin s) : HolomorphicAt n (G i) x :=
      Filter.eventually_of_mem (hU.mem_nhds hxU)
        (fun y hy => (hGdiff i y hy).mdifferentiableAt (hU.mem_nhds hy))
    let I : Ideal (HolGerm (ComplexModel n)) := Ideal.span (range fun i =>
      HolGerm.mk (fun z => G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (holomorphic_adapted x Φ h0 (hG i)))
    have hbridge {g : X → ℂ} (hg : HolomorphicAt n g x) :
        𝔞.mem x g ↔ HolGerm.mk
          (fun z => g ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
          (holomorphic_adapted x Φ h0 hg) ∈ I :=
      (hGiff x hxU g).trans
        ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G g).trans
          (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
            (fun i z => G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
            (fun i => holomorphic_adapted x Φ h0 (hG i))
            (holomorphic_adapted x Φ h0 hg)))
    apply (hbridge hF).mpr
    apply (HolomorphicGermPointTruncationClosure.mem_iff_mem_all_point_truncations n I _).mpr
    intro N
    apply span_mem_ring x Φ h0 _
      (fun g => 𝔞.mem x g ∨ (idealPow (pointIdeal n x) N).mem x g)
      (fun g hg => hg.elim (fun ha => ((hGiff x hxU g).mp ha).1)
        (fun hp => holomorphicAt_of_mem_idealPow hp))
      ?_ hF (hf N)
    intro g hg
    rcases hg with ha | hp
    · exact (show I ≤ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ N
        from le_sup_left) ((hbridge ((hGiff x hxU g).mp ha).1).mp ha)
    · exact (show IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ N ≤
        I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ N from le_sup_right)
        (point_power_mem_ring x Φ h0 N hp)

end
end SGPT.Foundations.Analysis.Pending.CoherentStalkPointTruncationClosure
