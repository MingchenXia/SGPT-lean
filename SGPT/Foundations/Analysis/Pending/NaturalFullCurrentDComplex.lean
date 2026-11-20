import SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose

/-! # The genuine original full native current differential complex

The three complete mathematical statements and ENTIRE proofs precede this
source. Nilpotence is proved on actual full original currents, using their
calibrated whole pairings and the genuine geometric square-zero theorem.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalFullCurrentDComplex

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  NaturalFullCurrentTranspose NaturalFullNativeSmoothDuality
  ActualCompactGlobalPairingCalibration ActualCompactGlobalPairingGeometricEquality

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The original whole native pairing respects actual geometric equality in its exact degree. -/
theorem pairingInDegree_congr {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q) (T : GlobalCurrent n M k)
    {γ η : SmoothRealForm n M q} (h : γ.GeometricallyEq η) :
    pairingInDegree hk T γ = pairingInDegree hk T η := by
  subst q
  exact pairing_eq_of_geometricallyEq T h

/-- The original zero smooth form has zero original pairing. -/
theorem pairingInDegree_zero {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q) (T : GlobalCurrent n M k) :
    pairingInDegree hk T (SmoothRealForm.zero : SmoothRealForm n M q) = 0 := by
  subst q
  exact (pairingLM T).map_zero

/-- Whole zero pairings give the original zero full native current on every chart test. -/
theorem eq_zero_of_pairingInDegree_eq_zero {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q) (T : GlobalCurrent n M k)
    (h : ∀ γ : SmoothRealForm n M q, pairingInDegree hk T γ = 0) : T = 0 := by
  subst q
  apply GlobalCurrent.ext
  intro e η
  rw [← pairing_testExtension T e η]
  exact h _

/-- Two actual calibrated exterior current transposes have genuinely zero composition. -/
theorem transpose_d_squared_eq_zero (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (δ0 : GlobalCurrent n M (complementDegree n (q + 1) (by omega)) →ₗ[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)))
    (δ1 : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq) →ₗ[ℝ]
      GlobalCurrent n M (complementDegree n (q + 1) (by omega)))
    (h0 : ∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (δ0 T) γ =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) (by omega)).val + 1) *
        pairingInDegree (complementDegree_complement n (q + 1) (by omega)) T γ.exteriorDerivative)
    (h1 : ∀ T γ, pairingInDegree (complementDegree_complement n (q + 1) (by omega)) (δ1 T) γ =
      (-1 : ℝ) ^ ((complementDegree n (q + 1 + 1) hq).val + 1) *
        pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T γ.exteriorDerivative) :
    δ0.comp δ1 = 0 := by
  apply LinearMap.ext
  intro T
  change δ0 (δ1 T) = 0
  apply eq_zero_of_pairingInDegree_eq_zero (complementDegree_complement n q (by omega))
  intro γ
  rw [h0, h1]
  have hz : pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T
      γ.exteriorDerivative.exteriorDerivative = 0 := by
    rw [pairingInDegree_congr _ T γ.exteriorDerivative_sq_geometricallyEq_zero]
    exact pairingInDegree_zero _ T
  rw [hz, mul_zero, mul_zero]

/-- Compactness alone constructs a genuine full native signed current differential complex. -/
theorem exists_full_native_current_d_complex (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    ∃ (δ0 : GlobalCurrent n M (complementDegree n (q + 1) (by omega)) →ₗ[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)))
      (δ1 : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq) →ₗ[ℝ]
        GlobalCurrent n M (complementDegree n (q + 1) (by omega))),
      (∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (δ0 T) γ =
        (-1 : ℝ) ^ ((complementDegree n (q + 1) (by omega)).val + 1) *
          pairingInDegree (complementDegree_complement n (q + 1) (by omega)) T γ.exteriorDerivative) ∧
      (∀ T γ, pairingInDegree (complementDegree_complement n (q + 1) (by omega)) (δ1 T) γ =
        (-1 : ℝ) ^ ((complementDegree n (q + 1 + 1) hq).val + 1) *
          pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T γ.exteriorDerivative) ∧
      δ0.comp δ1 = 0 := by
  obtain ⟨g0, v0, u0, g1, v1, u1, hc0, ht0, hf0, ha0, hv0, hl0,
    hc1, ht1, hf1, ha1, hv1, hl1, Φ0, Φ1, hp0, hp1, D0, C0, Td0, Tc0, δ0, δc0,
    hD0, hC0, hTd0, hTc0, hi0, hic0, h0, hdc0, hu0, huc0⟩ :=
    exists_complete_current_d_dc_transposes (n := n) (M := M) q (by omega)
  obtain ⟨g1', v1', u1', g2, v2, u2, hc1', ht1', hf1', ha1', hv1', hl1',
    hc2, ht2, hf2, ha2, hv2, hl2, Φ1', Φ2, hp1', hp2, D1, C1, Td1, Tc1, δ1, δc1,
    hD1, hC1, hTd1, hTc1, hi1, hic1, h1, hdc1, hu1, huc1⟩ :=
    exists_complete_current_d_dc_transposes (n := n) (M := M) (q + 1) hq
  exact ⟨δ0, δ1, h0, h1, transpose_d_squared_eq_zero q hq δ0 δ1 h0 h1⟩

end SGPT.Foundations.Analysis.Pending.NaturalFullCurrentDComplex
