import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false

/-!
# Actual positive nef representatives preserving Xiao's numerical gap

Source: Xiao, proof of Theorem 1.2, the initial nef approximations and the
polynomials `c_epsilon`, `m_epsilon`. Both representative forms and their
class-invariant mixed integrals are constructed from nefness and a strict
numerical inequality. No bigness or Monge--Ampère estimate is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.XiaoNefPerturbation

open FirstPass FirstPass.PositiveClasses NefMixedMass ProductTestForms ManifoldTubePositivity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Half the nef error gives semipositivity; adding the other half gives a Kähler form. -/
theorem exists_isKahler_of_nef (w : KahlerBackground n M)
    {A : ClosedRealOneOneForm n M} (hA : NefWithRespectTo w A) {t : ℝ} (ht : 0 < t) :
    ∃ (f : M → ℝ) (hf : ChartSmooth (n := n) f),
      (A + t • w.form + ddcClosedForm f hf).val.IsKahler := by
  obtain ⟨f, hf, hsemi⟩ := exists_isSemipositive_of_nef hA (half_pos ht)
  have hK := NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive w hsemi (half_pos ht)
  have heq : (A + (t / 2) • w.form + ddcClosedForm f hf) + (t / 2) • w.form =
      A + t • w.form + ddcClosedForm f hf := by module
  rw [heq] at hK
  exact ⟨f, hf, hK⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Multilinearity gives an actual positive perturbation preserving a strict intersection gap. -/
theorem exists_positive_perturbation_gap (w : KahlerBackground n M)
    (A B : ClosedRealOneOneForm n M) (k : Fin n)
    (hgap : 0 < slotIntegral w (fun _ => A) -
      4 * (n : ℝ) * slotIntegral w (Function.update (fun _ => A) k B)) :
    ∃ t : ℝ, 0 < t ∧
      0 < slotIntegral w (fun _ => A + t • w.form) -
        4 * (n : ℝ) * slotIntegral w
          (Function.update (fun _ => A + t • w.form) k (B + t • w.form)) := by
  classical
  let c : ℝ → ℝ := fun t => slotIntegral w (fun _ => A + t • w.form)
  let m : ℝ → ℝ := fun t => slotIntegral w
    (fun i => (Function.update (fun _ => A) k B) i + t • w.form)
  have hc : Continuous c := continuous_slotIntegral_add_smul w (fun _ => A) (fun _ => w.form)
  have hm : Continuous m := continuous_slotIntegral_add_smul w
    (Function.update (fun _ => A) k B) (fun _ => w.form)
  have hzero : 0 < c 0 - 4 * (n : ℝ) * m 0 := by
    simpa only [c, m, zero_smul, add_zero] using hgap
  have hnhds : {t : ℝ | 0 < c t - 4 * (n : ℝ) * m t} ∈ 𝓝 (0 : ℝ) :=
    (hc.sub (continuous_const.mul hm)).continuousAt.eventually (lt_mem_nhds hzero)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have ht : 0 < r / 2 := half_pos hr
  have htball : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hr
  refine ⟨r / 2, ht, ?_⟩
  have hgood : 0 < c (r / 2) - 4 * (n : ℝ) * m (r / 2) := hball htball
  have hfam : (fun i => (Function.update (fun _ => A) k B) i + (r / 2) • w.form) =
      Function.update (fun _ => A + (r / 2) • w.form) k (B + (r / 2) • w.form) := by
    funext i
    by_cases hi : i = k <;> simp [hi]
  simpa only [c, m, hfam] using hgood

/-- Nefness produces both actual Kähler representatives and the preserved strict numerical gap. -/
theorem exists_kahler_representatives_preserving_gap (w : KahlerBackground n M)
    (A B : ClosedRealOneOneForm n M) (k : Fin n)
    (hA : NefWithRespectTo w A) (hB : NefWithRespectTo w B)
    (hgap : 0 < slotIntegral w (fun _ => A) -
      4 * (n : ℝ) * slotIntegral w (Function.update (fun _ => A) k B)) :
    ∃ (t : ℝ), 0 < t ∧ ∃ (f : M → ℝ) (hf : ChartSmooth (n := n) f)
      (g : M → ℝ) (hg : ChartSmooth (n := n) g),
      (A + t • w.form + ddcClosedForm f hf).val.IsKahler ∧
      (B + t • w.form + ddcClosedForm g hg).val.IsKahler ∧
      0 < slotIntegral w (fun _ => A + t • w.form + ddcClosedForm f hf) -
        4 * (n : ℝ) * slotIntegral w
          (Function.update (fun _ => A + t • w.form + ddcClosedForm f hf) k
            (B + t • w.form + ddcClosedForm g hg)) := by
  classical
  obtain ⟨t, ht, hgap'⟩ := exists_positive_perturbation_gap w A B k hgap
  obtain ⟨f, hf, hAf⟩ := exists_isKahler_of_nef w hA ht
  obtain ⟨g, hg, hBg⟩ := exists_isKahler_of_nef w hB ht
  refine ⟨t, ht, f, hf, g, hg, hAf, hBg, ?_⟩
  have hc := slotIntegral_add_ddc w (fun _ => A + t • w.form) (fun _ => f) (fun _ => hf)
  let pots : Fin n → M → ℝ := Function.update (fun _ => f) k g
  have hpots : ∀ i, ChartSmooth (n := n) (pots i) := by
    intro i
    by_cases hi : i = k
    · simpa [pots, hi] using hg
    · simpa [pots, hi] using hf
  have hm := slotIntegral_add_ddc w
    (Function.update (fun _ => A + t • w.form) k (B + t • w.form)) pots hpots
  have hfam : (fun i => (Function.update (fun _ => A + t • w.form) k (B + t • w.form)) i +
      ddcClosedForm (pots i) (hpots i)) =
      Function.update (fun _ => A + t • w.form + ddcClosedForm f hf) k
        (B + t • w.form + ddcClosedForm g hg) := by
    funext i
    by_cases hi : i = k <;> simp [pots, hi]
  rw [hfam] at hm
  rw [hc, hm]
  exact hgap'

end SGPT.Foundations.Analysis.Pending.XiaoNefPerturbation
