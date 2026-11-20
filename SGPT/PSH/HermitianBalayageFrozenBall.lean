import SGPT.PSH.HermitianBalayageZeroMassEstimate

/-!
# Canonical ordinary replacement for the frozen-ball comparison

The PSH replacement, its measurability, its actual top-degree measure and
its zero mass are produced from the canonical Perron envelope. The only
comparison input is the upper gap furnished by the extremal pasting step.
The output traces depend only on the original potential.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.PSH.SourceDomainBalayageDraft
open scoped Topology Distributions

/-- Pure old-potential traces do not depend on the unused replacement. -/
theorem nearbyMixedMeasure_old_independent {N : ℕ} {Ω : Opens (ComplexModel N)}
    {u v w : ComplexModel N → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (hw : IsLocallyBoundedPshOn Ω w) (l : ℕ) :
    nearbyMixedMeasure Ω u v hu hv l 0 = nearbyMixedMeasure Ω u w hu hw l 0 := by
  have ht : (mixedTuple u v HermitianProducts.flatQuadratic l 0 :
      Fin N → ComplexModel N → ℝ) = mixedTuple u w HermitianProducts.flatQuadratic l 0 := by
    funext i
    simp only [mixedTuple, Nat.add_zero]
    split_ifs <;> rfl
  change canonicalMixedBedfordTaylorMeasure Ω _ _ = canonicalMixedBedfordTaylorMeasure Ω _ _
  congr 1

/-- The actual canonical Perron replacement has a globally measurable
real reader, through the upper semicontinuity of its regularization. -/
theorem measurable_domainPerronEnvelope_toReal {N : ℕ}
    (Ω D : Opens (ComplexModel N)) (u : ComplexModel N → ℝ) :
    Measurable (fun z => (domainPerronEnvelope Ω D u z).toReal) :=
  (upperSemicontinuous_uscRegularization _).measurable.ereal_toReal

/-- The frozen-ball mass estimate for the actual canonical replacement.
No incoming PSH, boundary, measure, or zero-mass certificate for the
replacement is needed: these are produced by ordinary ball balayage. -/
theorem exists_canonical_ball_replacement_mass_estimate (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel (n + 1))) (a : ComplexModel (n + 1)) (r κ : ℝ),
        0 < r → 0 ≤ κ → κ ≤ 1 → closedBall a r ⊆ Ω →
        ∀ (u : ComplexModel (n + 1) → ℝ), Measurable u →
          ∀ (hu : IsLocallyBoundedPshOn Ω u),
            (∀ x ∈ closedBall a ((3 / 4 : ℝ) * r),
              (domainPerronEnvelope Ω ⟨ball a r, isOpen_ball⟩ u x).toReal - u x ≤ κ * r ^ 2) →
              (SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu
                (closedBall a (r / 4))).toReal ≤
                C * κ * ∑ l ∈ Finset.range (n + 1),
                  (nearbyMixedMeasure Ω u u hu hu l 0
                    (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_nearby_homogeneous_mass_estimate n
  refine ⟨C, hC0, ?_⟩
  intro Ω a r κ hr hκ hκ1 hball u hum hu hgap
  let D : Opens (ComplexModel (n + 1)) := ⟨ball a r, isOpen_ball⟩
  let v := fun z => (domainPerronEnvelope Ω D u z).toReal
  have hDc : IsCompact (closure (D : Set (ComplexModel (n + 1)))) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hDΩ : closure (D : Set (ComplexModel (n + 1))) ⊆ Ω :=
    closure_ball_subset_closedBall.trans hball
  have hreader := domainPerronEnvelope_reader (Nat.succ_pos n) hu hDc hDΩ
  have hv : IsLocallyBoundedPshOn Ω v := hreader.1
  have hvm : Measurable v := measurable_domainPerronEnvelope_toReal Ω D u
  have houter : closedBall a ((3 / 4 : ℝ) * r) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : (3 / 4 : ℝ) * r ≤ r)).trans hball
  have hclose : ∀ x ∈ closedBall a ((3 / 4 : ℝ) * r), |v x - u x| ≤ κ * r ^ 2 := by
    intro x hx
    have hlower : u x ≤ v x := by
      apply EReal.coe_le_coe_iff.mp
      rw [hreader.2 x (houter hx)]
      exact le_domainPerronEnvelope hu x
    rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
    exact hgap x hx
  obtain ⟨τ, hτ, hτzero⟩ := exists_domainPerronEnvelope_ball_measure_zero
    (Nat.succ_pos n) hu a hr hball
  have h := hC Ω a r κ hr hκ hκ1 houter u v hum hvm hu hv hclose τ hτ hτzero
  simpa only [nearbyMixedMeasure_old_independent hu hv hu] using h

end SGPT.PSH.HermitianBalayage
