import SGPT.Foundations.Analysis.Pending.ActualPrimeGermGenericAvoidance
import SGPT.Foundations.Analysis.Pending.CartanIrreducible
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false

noncomputable section
open Set Filter Topology Metric MeasureTheory

namespace SGPT.PSH

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open HolGerm OkaRelationSheaf OkaIdealOperations AnalyticGermDecomposition

/-- The SAME original prime function generates the actual reduced ideal
at EVERY point of one produced neighborhood, including singular points. -/
theorem exists_original_prime_equation_neighbourhood {n : ℕ}
    (q : ComplexModel n → ℂ) (hq : HolAt q 0)
    (hQ : Prime (HolGerm.mk q hq)) :
    ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ q (ball 0 ε) ∧
      (∀ W : Set (ComplexModel n), IsOpen W → W ⊆ ball 0 ε → W.Nonempty →
        ∃ y ∈ W, q y ≠ 0) ∧
      ∀ y ∈ ball 0 ε, ∀ a : ComplexModel n → ℂ,
        vanishingIdealF {x | q x = 0} y a ↔ InSpanAt (fun _ : Fin 1 => q) y a := by
  classical
  have hideal :=
    (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1
  obtain ⟨Ω, hΩ, h0Ω, hqΩ⟩ := hq.exists_isOpen
  have hlocal := CartanIrreducibleReduction.localCartan_of_irreducibleLocalCartan
    (CartanIrreducible.irreducibleLocalCartan n)
  have hcoh : IdealFGAt (vanishingIdealF {x | q x = 0}) 0 := by
    simpa only [Fin.forall_fin_one] using
      hlocal Ω hΩ 1 (fun _ => q) (fun _ => hqΩ) 0 h0Ω
  obtain ⟨V, hV, h0V, μ, inst, s, hsV, hsgen⟩ := hcoh
  let : Fintype μ := inst
  have hquot : ∀ i : μ, ∃ (b : ComplexModel n → ℂ) (hb : HolAt b 0),
      s i =ᶠ[𝓝 0] fun x => b x * q x := by
    intro i
    have hsi : vanishingIdealF {x | q x = 0} 0 (s i) :=
      (hsgen 0 h0V _).mpr (inSpanAt_self
        (fun j => holAt_of_differentiableOn hV (hsV j) h0V) i)
    have hdiv : HolGerm.mk q hq ∣ HolGerm.mk (s i) hsi.1 :=
      Ideal.mem_span_singleton.mp (hideal ▸ mem_vanishingIdeal_mk.mpr hsi.2)
    obtain ⟨B, hB⟩ := hdiv
    obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
    have heq : HolGerm.mk (s i) hsi.1 =
        HolGerm.mk (fun x => b x * q x) (eventually_differentiableAt_mul hb hq) := by
      rw [HolGerm.mk_mul b q hb hq, mul_comm, ← hrep]
      exact hB
    exact ⟨b, hb, HolGerm.mk_eq_mk_iff.mp heq⟩
  choose b hb hbeq using hquot
  have hev : ∀ᶠ y in 𝓝 (0 : ComplexModel n), y ∈ V ∧ HolAt q y ∧
      (∀ i, HolAt (b i) y) ∧ ∀ i, s i y = b i y * q y := by
    filter_upwards [hV.mem_nhds h0V, OkaRelationSheaf.HolAt.eventually hq,
      eventually_all.mpr (fun i => OkaRelationSheaf.HolAt.eventually (hb i)),
      eventually_all.mpr hbeq] with y hy hqy hby hsy
    exact ⟨hy, hqy, hby, hsy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hqB : DifferentiableOn ℂ q (ball 0 ε) :=
    fun y hy => (hball y hy).2.1.differentiableAt.differentiableWithinAt
  have hnonzero : ∃ x ∈ ball (0 : ComplexModel n) ε, q x ≠ 0 := by
    by_contra hx
    push Not at hx
    apply hQ.ne_zero
    rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    exact eventually_of_mem (ball_mem_nhds 0 hε) hx
  obtain ⟨x₁, hx₁, hqx₁⟩ := hnonzero
  have hnull : volume (ball (0 : ComplexModel n) ε ∩ q ⁻¹' {0}) = 0 :=
    HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero volume hqB hx₁ hqx₁
  refine ⟨ε, hε, hqB, ?_, ?_⟩
  · intro W hW hWB hWne
    by_contra hn
    push Not at hn
    have hsub : W ⊆ ball (0 : ComplexModel n) ε ∩ q ⁻¹' {0} :=
      fun y hy => ⟨hWB hy, hn y hy⟩
    have hWnull : volume W = 0 := measure_mono_null hsub hnull
    exact (hW.measure_pos volume hWne).ne' hWnull
  · intro y hy a
    rcases hball y hy with ⟨hyV, _, hby, _⟩
    constructor
    · intro ha
      obtain ⟨hahol, c, hc, hsum⟩ := (hsgen y hyV a).mp ha
      refine ⟨hahol, fun _ x => ∑ i, c i x * b i x,
        fun _ => OkaRelationSheaf.HolAt.fintype_sum (fun i => (hc i).mul (hby i)), ?_⟩
      filter_upwards [hsum, isOpen_ball.mem_nhds hy] with x hsum hx
      simp only [Fin.sum_univ_one]
      rw [hsum]
      calc
        ∑ i, c i x * s i x = ∑ i, (c i x * b i x) * q x := by
          apply Finset.sum_congr rfl
          intro i _
          rw [(hball x hx).2.2.2 i, mul_assoc]
        _ = (∑ i, c i x * b i x) * q x := (Finset.sum_mul _ _ _).symm
    · rintro ⟨hahol, c, _, heq⟩
      refine ⟨hahol, ?_⟩
      filter_upwards [heq] with x heq hqx
      simpa only [Fin.sum_univ_one, hqx, mul_zero] using heq

#print axioms exists_original_prime_equation_neighbourhood

end SGPT.PSH
