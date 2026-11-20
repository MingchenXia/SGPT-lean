import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes

set_option autoImplicit false

/-! # Actual genuine rooftop envelopes from noncollapse

Independent normalized-Harnack proof of the finite-upper-bound reduction
used by Xia, PDF 0079--0080, Step 1.1. Neither obstacle regularity nor
boundedness, a big class, genuine envelope or competitor bound is supplied.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualNoncollapsedObstacleEnvelope

open FirstPass FirstPass.PositiveClasses IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual envelope's two noncollapse hypotheses internally produce
genuineness, without obstacle regularity or a competitor-bound certificate. -/
theorem isThetaPshPotential_of_ne_infinities (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → EReal}
    (hnb : rooftopEnvelope θ.val f ≠ (fun _ => ⊥))
    (hnt : rooftopEnvelope θ.val f ≠ (fun _ => ⊤)) :
    IsThetaPshPotential θ.val (rooftopEnvelope θ.val f) := by
  classical
  have hne : (rooftopCompetitors θ.val f).Nonempty := by
    rcases eq_empty_or_nonempty (rooftopCompetitors θ.val f) with h | h
    · exact False.elim (hnb (rooftopEnvelope_of_empty h))
    · exact h
  have hex : ∃ x, rooftopEnvelope θ.val f x ≠ ⊤ := by
    by_contra! h
    exact hnt (funext h)
  obtain ⟨x0, hx0⟩ := hex
  obtain ⟨D, hD, _⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hx0)
  let O : Set M := {x | rooftopEnvelope θ.val f x < (D : EReal)}
  have hO : IsOpen O := (upperSemicontinuous_rooftopEnvelope θ.val f).isOpen_preimage _
  let μ := kahlerVolume omega
  let m : ℝ := μ.real O
  have hm : 0 < m := ENNReal.toReal_pos
    (KahlerLaplacianStokes.kahlerVolume_pos_of_isOpen omega hO ⟨x0, hD⟩).ne'
    (measure_ne_top μ O)
  obtain ⟨B, hB, hbound⟩ :=
    SingularModelUniformModelL1.exists_uniform_lintegral_neg_le_kahlerVolume θ omega 1
  let t : ℝ := (B.toReal + 1) / m
  have ht : 0 < t := div_pos (by positivity) hm
  have htm : t * m = B.toReal + 1 := by
    dsimp [t]
    field_simp
  refine isThetaPshPotential_rooftop_of_nonempty hne ⟨D + t, fun u hu x => ?_⟩
  let S : ℝ := (⨆ y, u y).toReal
  have hfin := ModelRaySupremum.iSup_ne_top_ne_bot hu.1
  have hS : (S : EReal) = ⨆ y, u y := EReal.coe_toReal hfin.1 hfin.2
  have hnonpos : ∀ y, u y - (S : EReal) ≤ 0 := by
    intro y
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot S))
      (Or.inl (EReal.coe_ne_top S))).mpr
    simpa only [zero_add] using (hS.symm ▸ le_iSup u y)
  have hpoint : ∃ y, ((-(1 : ℝ) : ℝ) : EReal) ≤ u y - (S : EReal) := by
    by_contra hn
    have hlow : ∀ y, u y ≤ ((S - 1 : ℝ) : EReal) := by
      intro y
      have hy : u y - (S : EReal) < ((-(1 : ℝ) : ℝ) : EReal) :=
        lt_of_not_ge (fun hh => hn ⟨y, hh⟩)
      have hyle := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot S))
        (Or.inl (EReal.coe_ne_top S))).mp hy.le
      simpa only [← EReal.coe_add, show -(1 : ℝ) + S = S - 1 by ring] using hyle
    have hc : S ≤ S - 1 := EReal.coe_le_coe_iff.mp (hS.symm ▸ iSup_le hlow)
    linarith
  have hnorm : ∫⁻ y, (-(u y - (S : EReal))).toENNReal ∂μ ≤ B :=
    hbound _ (hu.1.sub_const S).1 hnonpos hpoint
  have hSu : S ≤ D + t := by
    by_contra hn
    have hlt : D + t < S := lt_of_not_ge hn
    have hlower : ENNReal.ofReal t * μ O ≤
        ∫⁻ y, (-(u y - (S : EReal))).toENNReal ∂μ := by
      rw [← lintegral_indicator_const hO.measurableSet (ENNReal.ofReal t)]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ O
      · rw [indicator_of_mem hy]
        have hyD : u y ≤ (D : EReal) :=
          (le_rooftopEnvelope hu.1 hu.2 y).trans (le_of_lt hy)
        have hsub := EReal.sub_le_sub hyD (le_refl (S : EReal))
        have hneg : ((S - D : ℝ) : EReal) ≤ -(u y - (S : EReal)) := by
          have hc : -((D : EReal) - (S : EReal)) = ((S - D : ℝ) : EReal) := by
            rw [← EReal.coe_sub, ← EReal.coe_neg]
            congr 1
            ring
          simpa only [hc] using EReal.neg_le_neg_iff.mpr hsub
        have hty : (t : EReal) ≤ -(u y - (S : EReal)) :=
          (EReal.coe_le_coe_iff.mpr (by linarith)).trans hneg
        simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hty
      · rw [indicator_of_notMem hy]
        exact bot_le
    have hreal := ENNReal.toReal_mono hB.ne (hlower.trans hnorm)
    have hcontr : t * m ≤ B.toReal := by
      simpa only [m, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, Measure.real] using hreal
    rw [htm] at hcontr
    linarith
  exact (hS.symm ▸ le_iSup u x).trans (EReal.coe_le_coe_iff.mpr hSu)

end
end SGPT.Foundations.Analysis.Pending.ActualNoncollapsedObstacleEnvelope
