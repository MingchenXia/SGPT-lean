import SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose

/-! # The positive original normalized second transpose on full native currents

The complete mathematical statement and ENTIRE proof precede this source.
This constructs the actual positive second transpose without asserting an
unproved anticommutation identity for current differential compositions.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalFullCurrentDdcTranspose

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  NaturalFullCurrentTranspose NaturalCompleteGeometricComplexOperators
  NaturalGeometricComplexDifferentials XiaoComplexDifferential

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every admissible two-step real degree has its original positive normalized second transpose. -/
theorem exists_complete_current_ddc_transpose [CompactSpace M] (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    ∃ g0 : AddCommGroup (GeometricRealForm n M q), let _ := g0
    ∃ v0 : Module ℝ (GeometricRealForm n M q), let _ := v0
    ∃ u0 : UniformSpace (GeometricRealForm n M q), let _ := u0
    ∃ g2 : AddCommGroup (GeometricRealForm n M (q + 1 + 1)), let _ := g2
    ∃ v2 : Module ℝ (GeometricRealForm n M (q + 1 + 1)), let _ := v2
    ∃ u2 : UniformSpace (GeometricRealForm n M (q + 1 + 1)), let _ := u2
      CompleteSpace (GeometricRealForm n M q) ∧ T2Space (GeometricRealForm n M q) ∧
      FirstCountableTopology (GeometricRealForm n M q) ∧
      IsTopologicalAddGroup (GeometricRealForm n M q) ∧
      ContinuousSMul ℝ (GeometricRealForm n M q) ∧ LocallyConvexSpace ℝ (GeometricRealForm n M q) ∧
      CompleteSpace (GeometricRealForm n M (q + 1 + 1)) ∧
      T2Space (GeometricRealForm n M (q + 1 + 1)) ∧
      FirstCountableTopology (GeometricRealForm n M (q + 1 + 1)) ∧
      IsTopologicalAddGroup (GeometricRealForm n M (q + 1 + 1)) ∧
      ContinuousSMul ℝ (GeometricRealForm n M (q + 1 + 1)) ∧
      LocallyConvexSpace ℝ (GeometricRealForm n M (q + 1 + 1)) ∧
      ∃ (Φ0 : GlobalCurrent n M (complementDegree n q (by omega)) ≃ₗ[ℝ]
          (GeometricRealForm n M q →L[ℝ] ℝ))
        (Φ2 : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq) ≃ₗ[ℝ]
          (GeometricRealForm n M (q + 1 + 1) →L[ℝ] ℝ)),
        (∀ T γ, Φ0 T (GeometricRealForm.ofRepresentative γ) =
          pairingInDegree (complementDegree_complement n q (by omega)) T γ) ∧
        (∀ T γ, Φ2 T (GeometricRealForm.ofRepresentative γ) =
          pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T γ) ∧
        ∃ (C : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1 + 1))
          (B : (GeometricRealForm n M (q + 1 + 1) →L[ℝ] ℝ) →L[ℝ]
            (GeometricRealForm n M q →L[ℝ] ℝ))
          (Q : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq) →ₗ[ℝ]
            GlobalCurrent n M (complementDegree n q (by omega))),
          (∀ a, C a = geometricDdc a) ∧ B = signedTransposeCLM 1 C ∧
          (∀ T, Φ0 (Q T) = B (Φ2 T)) ∧
          (∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (Q T) γ =
            pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T (ddc γ)) ∧
          (∀ T U, (∀ γ, pairingInDegree (complementDegree_complement n q (by omega)) U γ =
              pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T (ddc γ)) →
            U = Q T) := by
  classical
  obtain ⟨m, a, χ, K, hχ, -, hs, hK, h1, hmodel⟩ :=
    exists_complete_geometric_complex_operators (n := n) (M := M)
  obtain ⟨S0, S1, S2, -, -, -, g0, v0, u0, g1, v1, u1, g2, v2, u2,
    E0, E1, E2, hc0, ht0, hf0, ha0, hv0, hl0, hc1, ht1, hf1, ha1, hv1, hl1,
    hc2, ht2, hf2, ha2, hv2, hl2, hr0, hr1, hr2, D, D1, C0, C, hD, hD1, hC0, hC⟩ := hmodel q
  let _ := g0
  let _ := v0
  let _ := u0
  let _ := ha0
  let _ := hv0
  let _ := hl0
  let _ := g2
  let _ := v2
  let _ := u2
  let _ := ha2
  let _ := hv2
  let _ := hl2
  have hq0 : q ≤ Module.finrank ℝ (ComplexModel n) := by omega
  let k0 := complementDegree n q hq0
  let k2 := complementDegree n (q + 1 + 1) hq
  have hk0 : Module.finrank ℝ (ComplexModel n) - k0.val = q :=
    complementDegree_complement n q hq0
  have hk2 : Module.finrank ℝ (ComplexModel n) - k2.val = q + 1 + 1 :=
    complementDegree_complement n (q + 1 + 1) hq
  let Φ0 := nativeDualityInDegree hk0 a χ hχ hs K hK h1 S0 E0 hr0
  let Φ2 := nativeDualityInDegree hk2 a χ hχ hs K hK h1 S2 E2 hr2
  have hp0 T γ : Φ0 T (GeometricRealForm.ofRepresentative γ) = pairingInDegree hk0 T γ :=
    nativeDualityInDegree_calibration hk0 a χ hχ hs K hK h1 S0 E0 hr0 T γ
  have hp2 T γ : Φ2 T (GeometricRealForm.ofRepresentative γ) = pairingInDegree hk2 T γ :=
    nativeDualityInDegree_calibration hk2 a χ hχ hs K hK h1 S2 E2 hr2 T γ
  let Q := currentTransposeLM Φ0 Φ2 (1 : ℝ) C
  have hQ T : Φ0 (Q T) = signedTransposeCLM 1 C (Φ2 T) :=
    currentTransposeLM_intertwining Φ0 Φ2 1 C T
  have hQread T γ : pairingInDegree hk0 (Q T) γ = pairingInDegree hk2 T (ddc γ) := by
    rw [← hp0 (Q T) γ, hQ T]
    change (1 : ℝ) * Φ2 T (C (GeometricRealForm.ofRepresentative γ)) = _
    rw [one_mul, hC]
    change Φ2 T (GeometricRealForm.ofRepresentative (ddc γ)) = _
    exact hp2 T (ddc γ)
  refine ⟨g0, v0, u0, g2, v2, u2, hc0, ht0, hf0, ha0, hv0, hl0,
    hc2, ht2, hf2, ha2, hv2, hl2, Φ0, Φ2, hp0, hp2, C,
    signedTransposeCLM 1 C, Q, hC, rfl, hQ, hQread, ?_⟩
  intro T U h
  exact eq_of_pairingInDegree_eq hk0 (fun γ => (h γ).trans (hQread T γ).symm)

end SGPT.Foundations.Analysis.Pending.NaturalFullCurrentDdcTranspose
