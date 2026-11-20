import SGPT.Foundations.Analysis.Pending.LastVariableTaylorDivision
import SGPT.Foundations.Analysis.Pending.HolomorphicGermRing

set_option autoImplicit false

/-! # Actual Cauchy division along a holomorphic graph

Natural holomorphic functions supply the quotient and the actual germ
factorization.  No residual-ideal, current nullity or whole analytic
Lebesgue-decomposition theorem is asserted here.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace SGPT.Foundations.Analysis.Pending.ActualHolomorphicGraphDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem exists_coordinate_quotient {H : E × ℂ → ℂ}
    (hH : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ H x)
    (hzero : ∀ᶠ z in 𝓝 (0 : E), H (z, 0) = 0) :
    ∃ Q : E × ℂ → ℂ,
      (∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ Q x) ∧
      ∀ᶠ x in 𝓝 (0 : E × ℂ), H x = Q x * x.2 := by
  have hz : ∀ᶠ x in 𝓝 (0 : E × ℂ), H (x.1, 0) = 0 :=
    (continuous_fst.tendsto (0 : E × ℂ)).eventually hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hH.and hz)
  rw [← ball_prod_same] at hball
  let B : Set (E × ℂ) := ball (0 : E) ε ×ˢ ball (0 : ℂ) ε
  have hBo : IsOpen B := isOpen_ball.prod isOpen_ball
  have hB0 : (0 : E × ℂ) ∈ B :=
    ⟨mem_ball_self hε, mem_ball_self hε⟩
  have hHB : DifferentiableOn ℂ H B := fun x hx =>
    ((hball hx).1).differentiableWithinAt
  have hρ : 0 < ε / 2 := half_pos hε
  have hρε : ε / 2 < ε := half_lt_self hε
  let Q := lastQuot H (ε / 2) 1
  have hQB : DifferentiableOn ℂ Q B := differentiableOn_lastQuot hρ hρε hHB 1
  refine ⟨Q, ?_, ?_⟩
  · filter_upwards [hBo.mem_nhds hB0] with x hx
    exact hQB.differentiableAt (hBo.mem_nhds hx)
  · filter_upwards [hBo.mem_nhds hB0] with x hx
    have hc : lastCoeff H (ε / 2) 0 x.1 = 0 := by
      have h := eq_lastQuot_mul_add hρ hρε hHB 1
        (x.1, 0) ⟨hx.1, mem_ball_self hε⟩
      simpa [(hball hx).2] using h.symm
    simpa [Q, hc] using eq_lastQuot_mul_add hρ hρε hHB 1 x hx

/-- The actual holomorphic quotient is produced from vanishing on a graph. -/
theorem exists_quotient_of_vanishing_on_graph {f : E × ℂ → ℂ} {k : E → ℂ}
    (hf : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ f x)
    (hk : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ k z) (hk0 : k 0 = 0)
    (hzero : ∀ᶠ z in 𝓝 (0 : E), f (z, k z) = 0) :
    ∃ q : E × ℂ → ℂ,
      (∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ q x) ∧
      ∀ᶠ x in 𝓝 (0 : E × ℂ), f x = q x * (x.2 - k x.1) := by
  let A : E × ℂ → E × ℂ := fun x => (x.1, x.2 + k x.1)
  let B : E × ℂ → E × ℂ := fun x => (x.1, x.2 - k x.1)
  have hkf : ∀ᶠ x in 𝓝 (0 : E × ℂ),
      DifferentiableAt ℂ (fun x : E × ℂ => k x.1) x := by
    filter_upwards [(continuous_fst.tendsto (0 : E × ℂ)).eventually hk] with x hx
    exact hx.comp x differentiableAt_fst
  have hA : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ A x :=
    hkf.mono fun _ hx => differentiableAt_fst.prodMk (differentiableAt_snd.add hx)
  have hB : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ B x :=
    hkf.mono fun _ hx => differentiableAt_fst.prodMk (differentiableAt_snd.sub hx)
  have hAt : Tendsto A (𝓝 (0 : E × ℂ)) (𝓝 (0 : E × ℂ)) := by
    simpa [A, hk0, Prod.mk_zero_zero] using hA.self_of_nhds.continuousAt.tendsto
  have hBt : Tendsto B (𝓝 (0 : E × ℂ)) (𝓝 (0 : E × ℂ)) := by
    simpa [B, hk0, Prod.mk_zero_zero] using hB.self_of_nhds.continuousAt.tendsto
  have hH : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ (f ∘ A) x := by
    filter_upwards [hAt.eventually hf, hA] with x hx ha
    exact hx.comp x ha
  have hz : ∀ᶠ z in 𝓝 (0 : E), (f ∘ A) (z, 0) = 0 := by
    simpa [A] using hzero
  obtain ⟨Q, hQ, hEq⟩ := exists_coordinate_quotient hH hz
  refine ⟨Q ∘ B, ?_, ?_⟩
  · filter_upwards [hBt.eventually hQ, hB] with x hx hb
    exact hx.comp x hb
  · filter_upwards [hBt.eventually hEq] with x hx
    simpa [A, B] using hx

/-- Actual graph and defining-function germ data are produced internally;
vanishing of the restriction is exactly divisibility by the nonunit graph germ. -/
theorem exists_graph_germ_divisibility_iff {f : E × ℂ → ℂ} {k : E → ℂ}
    (hf : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ f x)
    (hk : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ k z) (hk0 : k 0 = 0) :
    ∃ (hd : ∀ᶠ x in 𝓝 (0 : E × ℂ),
        DifferentiableAt ℂ (fun x : E × ℂ => x.2 - k x.1) x)
      (hr : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun z => f (z, k z)) z),
      (HolGerm.mk (fun x : E × ℂ => x.2 - k x.1) hd ∣ HolGerm.mk f hf ↔
        HolGerm.mk (fun z => f (z, k z)) hr = 0) ∧
      ¬ IsUnit (HolGerm.mk (fun x : E × ℂ => x.2 - k x.1) hd) := by
  let G : E → E × ℂ := fun z => (z, k z)
  have hG : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ G z :=
    hk.mono fun _ hx => differentiableAt_id.prodMk hx
  have hGt : Tendsto G (𝓝 (0 : E)) (𝓝 (0 : E × ℂ)) := by
    simpa [G, hk0, Prod.mk_zero_zero] using hG.self_of_nhds.continuousAt.tendsto
  have hd : ∀ᶠ x in 𝓝 (0 : E × ℂ),
      DifferentiableAt ℂ (fun x : E × ℂ => x.2 - k x.1) x := by
    filter_upwards [(continuous_fst.tendsto (0 : E × ℂ)).eventually hk] with x hx
    exact differentiableAt_snd.sub (hx.comp x differentiableAt_fst)
  have hr : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun z => f (z, k z)) z := by
    filter_upwards [hGt.eventually hf, hG] with z hfz hgz
    exact hfz.comp z hgz
  refine ⟨hd, hr, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨q, hq⟩
    obtain ⟨Q, hQ, rfl⟩ := HolGerm.exists_eq_mk q
    have he : f =ᶠ[𝓝 (0 : E × ℂ)] fun x => (x.2 - k x.1) * Q x :=
      HolGerm.mk_eq_mk_iff.mp (hq.trans (HolGerm.mk_mul _ _ hd hQ).symm)
    rw [← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hGt.eventually he] with z hz
    simpa [G] using hz
  · intro hz
    have he : ∀ᶠ z in 𝓝 (0 : E), f (z, k z) = 0 := by
      rw [← HolGerm.mk_zero] at hz
      exact HolGerm.mk_eq_mk_iff.mp hz
    obtain ⟨q, hq, hEq⟩ := exists_quotient_of_vanishing_on_graph hf hk hk0 he
    refine ⟨HolGerm.mk q hq, ?_⟩
    rw [← HolGerm.mk_mul]
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hEq] with x hx
    exact hx.trans (mul_comm _ _)
  · rw [HolGerm.isUnit_iff_eval_ne_zero]
    simp [HolGerm.eval_mk, hk0]

end SGPT.Foundations.Analysis.Pending.ActualHolomorphicGraphDivision
