import SGPT.Foundations.Analysis.Pending.NaturalFullNativeSmoothDuality
import SGPT.Foundations.Analysis.Pending.NaturalCompleteGeometricComplexOperators
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Full signed original current transposes on the actual smooth duals

The complete mathematical statements and ENTIRE proofs precede this source.
The original current is unchanged. Continuity asserted here belongs to its
actual bounded-convergence smooth dual, while native current maps are linear.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  ActualCompactGlobalPairingCalibration NaturalFullNativeSmoothDuality
  NaturalCompactGeometricFormFrechetModule NaturalCompleteGeometricComplexOperators
  NaturalGlobalExteriorDifferential NaturalGeometricComplexDifferentials
  XiaoComplexDifferential

variable {n q r m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original bounded real current degree with complementary test degree q. -/
def complementDegree (n q : ℕ) (hq : q ≤ Module.finrank ℝ (ComplexModel n)) :
    CurrentDegree n :=
  ⟨Module.finrank ℝ (ComplexModel n) - q, by omega⟩

/-- Exact natural complementary-degree arithmetic. -/
theorem complementDegree_complement (n q : ℕ)
    (hq : q ≤ Module.finrank ℝ (ComplexModel n)) :
    Module.finrank ℝ (ComplexModel n) - (complementDegree n q hq).val = q := by
  change Module.finrank ℝ (ComplexModel n) -
    (Module.finrank ℝ (ComplexModel n) - q) = q
  omega

/-- The original native pairing, with its exact natural tensor degree identified. -/
def pairingInDegree [CompactSpace M] {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    (T : GlobalCurrent n M k) (γ : SmoothRealForm n M q) : ℝ :=
  pairingLM T (hk.symm ▸ γ)

/-- Whole original smooth pairings determine every full native signed current. -/
theorem eq_of_pairingInDegree_eq [CompactSpace M] {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    {T U : GlobalCurrent n M k}
    (h : ∀ γ : SmoothRealForm n M q, pairingInDegree hk T γ = pairingInDegree hk U γ) :
    T = U := by
  subst q
  apply GlobalCurrent.ext
  intro e η
  rw [← pairing_testExtension T e η, ← pairing_testExtension U e η]
  exact h _

section ActualNativeModel

variable {k : CurrentDegree n}
  (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
  [AddCommGroup (GeometricRealForm n M q)] [Module ℝ (GeometricRealForm n M q)]
  [TopologicalSpace (GeometricRealForm n M q)]
  [IsTopologicalAddGroup (GeometricRealForm n M q)]
  [ContinuousSMul ℝ (GeometricRealForm n M q)]
  [LocallyConvexSpace ℝ (GeometricRealForm n M q)]
  (a : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
  (hχ : ∀ i, ChartSmooth (n := n) (χ i))
  (hs : ∀ i, tsupport (χ i) ⊆ (a i).val.source)
  (K : Fin m → Compacts (ComplexModel n))
  (hK : ∀ i, (K i : Set (ComplexModel n)) = (a i).val '' tsupport (χ i))
  (h1 : ∀ x, ∑ i, χ i x = 1)
  (S : Submodule ℝ (Π i : Fin m,
    𝓓_{K i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
  (E : GeometricRealForm n M q ≃L[ℝ] S)
  (hread : ∀ (α : SmoothRealForm n M q) i z,
    (E (GeometricRealForm.ofRepresentative α)).val i z =
      (a i).val.target.indicator (fun y => χ i ((a i).val.symm y) • α.coeff (a i) y) z)

/-- Genuine original native duality on the same model, with its complement identified. -/
def nativeDualityInDegree [CompactSpace M] :
    GlobalCurrent n M k ≃ₗ[ℝ] (GeometricRealForm n M q →L[ℝ] ℝ) := by
  subst q
  exact nativeDuality a χ hχ hs K hK h1 S E hread

/-- The exact original whole native pairing calibration in the identified degree. -/
theorem nativeDualityInDegree_calibration [CompactSpace M]
    (T : GlobalCurrent n M k) (γ : SmoothRealForm n M q) :
    nativeDualityInDegree hk a χ hχ hs K hK h1 S E hread T
      (GeometricRealForm.ofRepresentative γ) = pairingInDegree hk T γ := by
  subst q
  exact nativeFunctionalCLM_calibration a χ hχ hs K hK h1 S E hread T γ

end ActualNativeModel

section Transpose

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The literal signed transpose, continuous for bounded-convergence dual topology. -/
def signedTransposeCLM (c : ℝ) (A : E →L[ℝ] F) :
    (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  c • A.precomp ℝ

/-- Conjugate a genuine continuous transpose back to the actual full native currents. -/
def currentTransposeLM {k0 k1 : CurrentDegree n}
    (Φ0 : GlobalCurrent n M k0 ≃ₗ[ℝ] (E →L[ℝ] ℝ))
    (Φ1 : GlobalCurrent n M k1 ≃ₗ[ℝ] (F →L[ℝ] ℝ))
    (c : ℝ) (A : E →L[ℝ] F) : GlobalCurrent n M k1 →ₗ[ℝ] GlobalCurrent n M k0 :=
  Φ0.symm.toLinearMap.comp ((signedTransposeCLM c A).toLinearMap.comp Φ1.toLinearMap)

/-- Exact native-duality intertwining, using the actual proved inverse. -/
theorem currentTransposeLM_intertwining {k0 k1 : CurrentDegree n}
    (Φ0 : GlobalCurrent n M k0 ≃ₗ[ℝ] (E →L[ℝ] ℝ))
    (Φ1 : GlobalCurrent n M k1 ≃ₗ[ℝ] (F →L[ℝ] ℝ))
    (c : ℝ) (A : E →L[ℝ] F) (T : GlobalCurrent n M k1) :
    Φ0 (currentTransposeLM Φ0 Φ1 c A T) = signedTransposeCLM c A (Φ1 T) := by
  exact Φ0.apply_symm_apply _

end Transpose

/-- Every admissible one-step degree has original d and normalized dc full signed transposes. -/
theorem exists_complete_current_d_dc_transposes [CompactSpace M] (q : ℕ)
    (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    ∃ g0 : AddCommGroup (GeometricRealForm n M q), let _ := g0
    ∃ v0 : Module ℝ (GeometricRealForm n M q), let _ := v0
    ∃ u0 : UniformSpace (GeometricRealForm n M q), let _ := u0
    ∃ g1 : AddCommGroup (GeometricRealForm n M (q + 1)), let _ := g1
    ∃ v1 : Module ℝ (GeometricRealForm n M (q + 1)), let _ := v1
    ∃ u1 : UniformSpace (GeometricRealForm n M (q + 1)), let _ := u1
      CompleteSpace (GeometricRealForm n M q) ∧ T2Space (GeometricRealForm n M q) ∧
      FirstCountableTopology (GeometricRealForm n M q) ∧
      IsTopologicalAddGroup (GeometricRealForm n M q) ∧
      ContinuousSMul ℝ (GeometricRealForm n M q) ∧ LocallyConvexSpace ℝ (GeometricRealForm n M q) ∧
      CompleteSpace (GeometricRealForm n M (q + 1)) ∧ T2Space (GeometricRealForm n M (q + 1)) ∧
      FirstCountableTopology (GeometricRealForm n M (q + 1)) ∧
      IsTopologicalAddGroup (GeometricRealForm n M (q + 1)) ∧
      ContinuousSMul ℝ (GeometricRealForm n M (q + 1)) ∧
      LocallyConvexSpace ℝ (GeometricRealForm n M (q + 1)) ∧
      ∃ (Φ0 : GlobalCurrent n M (complementDegree n q (by omega)) ≃ₗ[ℝ]
          (GeometricRealForm n M q →L[ℝ] ℝ))
        (Φ1 : GlobalCurrent n M (complementDegree n (q + 1) hq) ≃ₗ[ℝ]
          (GeometricRealForm n M (q + 1) →L[ℝ] ℝ)),
        (∀ T γ, Φ0 T (GeometricRealForm.ofRepresentative γ) =
          pairingInDegree (complementDegree_complement n q (by omega)) T γ) ∧
        (∀ T γ, Φ1 T (GeometricRealForm.ofRepresentative γ) =
          pairingInDegree (complementDegree_complement n (q + 1) hq) T γ) ∧
        ∃ (D C : GeometricRealForm n M q →L[ℝ] GeometricRealForm n M (q + 1))
          (Td Tc : (GeometricRealForm n M (q + 1) →L[ℝ] ℝ) →L[ℝ]
            (GeometricRealForm n M q →L[ℝ] ℝ))
          (δ δc : GlobalCurrent n M (complementDegree n (q + 1) hq) →ₗ[ℝ]
            GlobalCurrent n M (complementDegree n q (by omega))),
          (∀ a, D a = geometricExteriorDerivative a) ∧ (∀ a, C a = geometricDc a) ∧
          Td = signedTransposeCLM ((-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1)) D ∧
          Tc = signedTransposeCLM ((-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1)) C ∧
          (∀ T, Φ0 (δ T) = Td (Φ1 T)) ∧ (∀ T, Φ0 (δc T) = Tc (Φ1 T)) ∧
          (∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (δ T) γ =
            (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
              pairingInDegree (complementDegree_complement n (q + 1) hq) T γ.exteriorDerivative) ∧
          (∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (δc T) γ =
            (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
              pairingInDegree (complementDegree_complement n (q + 1) hq) T (dc γ)) ∧
          (∀ T U, (∀ γ, pairingInDegree (complementDegree_complement n q (by omega)) U γ =
              (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
                pairingInDegree (complementDegree_complement n (q + 1) hq) T γ.exteriorDerivative) →
            U = δ T) ∧
          (∀ T U, (∀ γ, pairingInDegree (complementDegree_complement n q (by omega)) U γ =
              (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
                pairingInDegree (complementDegree_complement n (q + 1) hq) T (dc γ)) →
            U = δc T) := by
  classical
  obtain ⟨m, a, χ, K, hχ, -, hs, hK, h1, hmodel⟩ :=
    exists_complete_geometric_complex_operators (n := n) (M := M)
  obtain ⟨S0, S1, S2, -, -, -, g0, v0, u0, g1, v1, u1, g2, v2, u2,
    E0, E1, E2, hc0, ht0, hf0, ha0, hv0, hl0, hc1, ht1, hf1, ha1, hv1, hl1,
    hc2, ht2, hf2, ha2, hv2, hl2, hr0, hr1, hr2, D, D1, C, C1, hD, hD1, hC, hC1⟩ := hmodel q
  let _ := g0
  let _ := v0
  let _ := u0
  let _ := ha0
  let _ := hv0
  let _ := hl0
  let _ := g1
  let _ := v1
  let _ := u1
  let _ := ha1
  let _ := hv1
  let _ := hl1
  have hq0 : q ≤ Module.finrank ℝ (ComplexModel n) := by omega
  let k0 := complementDegree n q hq0
  let k1 := complementDegree n (q + 1) hq
  have hk0 : Module.finrank ℝ (ComplexModel n) - k0.val = q :=
    complementDegree_complement n q hq0
  have hk1 : Module.finrank ℝ (ComplexModel n) - k1.val = q + 1 :=
    complementDegree_complement n (q + 1) hq
  let Φ0 := nativeDualityInDegree hk0 a χ hχ hs K hK h1 S0 E0 hr0
  let Φ1 := nativeDualityInDegree hk1 a χ hχ hs K hK h1 S1 E1 hr1
  have hp0 T γ : Φ0 T (GeometricRealForm.ofRepresentative γ) = pairingInDegree hk0 T γ :=
    nativeDualityInDegree_calibration hk0 a χ hχ hs K hK h1 S0 E0 hr0 T γ
  have hp1 T γ : Φ1 T (GeometricRealForm.ofRepresentative γ) = pairingInDegree hk1 T γ :=
    nativeDualityInDegree_calibration hk1 a χ hχ hs K hK h1 S1 E1 hr1 T γ
  let c : ℝ := (-1 : ℝ) ^ (k1.val + 1)
  let δ := currentTransposeLM Φ0 Φ1 c D
  let δc := currentTransposeLM Φ0 Φ1 c C
  have hd T : Φ0 (δ T) = signedTransposeCLM c D (Φ1 T) :=
    currentTransposeLM_intertwining Φ0 Φ1 c D T
  have hdc T : Φ0 (δc T) = signedTransposeCLM c C (Φ1 T) :=
    currentTransposeLM_intertwining Φ0 Φ1 c C T
  have hdread T γ : pairingInDegree hk0 (δ T) γ =
      c * pairingInDegree hk1 T γ.exteriorDerivative := by
    rw [← hp0 (δ T) γ, hd T]
    change c * Φ1 T (D (GeometricRealForm.ofRepresentative γ)) = _
    rw [hD, geometricExteriorDerivative_ofRepresentative, hp1]
  have hdcread T γ : pairingInDegree hk0 (δc T) γ =
      c * pairingInDegree hk1 T (dc γ) := by
    rw [← hp0 (δc T) γ, hdc T]
    change c * Φ1 T (C (GeometricRealForm.ofRepresentative γ)) = _
    rw [hC]
    change c * Φ1 T (GeometricRealForm.ofRepresentative (dc γ)) = _
    rw [hp1]
  refine ⟨g0, v0, u0, g1, v1, u1, hc0, ht0, hf0, ha0, hv0, hl0,
    hc1, ht1, hf1, ha1, hv1, hl1, Φ0, Φ1, hp0, hp1, D, C,
    signedTransposeCLM c D, signedTransposeCLM c C, δ, δc, hD, hC,
    rfl, rfl, hd, hdc, hdread, hdcread, ?_, ?_⟩
  · intro T U h
    exact eq_of_pairingInDegree_eq hk0 (fun γ => (h γ).trans (hdread T γ).symm)
  · intro T U h
    exact eq_of_pairingInDegree_eq hk0 (fun γ => (h γ).trans (hdcread T γ).symm)

end SGPT.Foundations.Analysis.Pending.NaturalFullCurrentTranspose
