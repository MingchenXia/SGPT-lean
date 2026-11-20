import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalFormPairing
import SGPT.Foundations.Analysis.Pending.ProductTestForms

set_option autoImplicit false

/-! # The actual unique linear pairing on all compact global smooth forms

The full mathematical statement and complete proof preceded this source.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalLinearPairing

open FirstPass ChartPartition ActualWeightedGlobalFormChartTests ActualCompactGlobalFormPairing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {k : CurrentDegree n}

private def pairingValue (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) : ℝ :=
  Classical.choose (exists_unique_pairing T γ).exists

private theorem pairingValue_eq_sum (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hχc : ∀ i, IsCompact (tsupport (χ i)))
    (hχs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (hχ1 : ∀ x, ∑ i, χ i x = 1)
    (η : ∀ i, _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (hη : ∀ i z, η i z = (e i).val.target.indicator
      (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z) :
    pairingValue T γ = ∑ i, T.inChart (e i) (η i) :=
  Classical.choose_spec (exists_unique_pairing T γ).exists m e χ hχ hχc hχs hχ1 η hη

private theorem pairingValue_add (T : GlobalCurrent n M k)
    (γ δ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingValue T (γ + δ) = pairingValue T γ + pairingValue T δ := by
  classical
  obtain ⟨m, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart n M := fun i => complexChartAt (idx i)
  have htests (a : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
      (i : Fin m) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        ∀ z, η z = (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • a.coeff (e i) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e i) a (χ i) (hχ i) (hχc i) (hχs i)
    exact ⟨η, hη⟩
  choose η hη using htests γ
  choose ζ hζ using htests δ
  have hadd (i : Fin m) (z : ComplexModel n) :
      (η i + ζ i) z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • (γ + δ).coeff (e i) y) z := by
    by_cases hz : z ∈ (e i).val.target <;> simp [hη, hζ, hz, smul_add]
  rw [pairingValue_eq_sum T (γ + δ) m e χ hχ hχc hχs hχ1 (fun i => η i + ζ i) hadd,
    pairingValue_eq_sum T γ m e χ hχ hχc hχs hχ1 η hη,
    pairingValue_eq_sum T δ m e χ hχ hχc hχs hχ1 ζ hζ]
  simp only [map_add, Finset.sum_add_distrib]

private theorem pairingValue_smul (T : GlobalCurrent n M k) (c : ℝ)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingValue T (c • γ) = c • pairingValue T γ := by
  classical
  obtain ⟨m, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart n M := fun i => complexChartAt (idx i)
  have htests (i : Fin m) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        ∀ z, η z = (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e i) γ (χ i) (hχ i) (hχc i) (hχs i)
    exact ⟨η, hη⟩
  choose η hη using htests
  have hc (i : Fin m) (z : ComplexModel n) :
      (c • η i) z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • (c • γ).coeff (e i) y) z := by
    change c • η i z = _
    by_cases hz : z ∈ (e i).val.target
    · rw [hη, indicator_of_mem hz, indicator_of_mem hz]
      change c • (χ i ((e i).val.symm z) • γ.coeff (e i) z) =
        χ i ((e i).val.symm z) • (c • γ.coeff (e i) z)
      exact smul_comm _ _ _
    · simp [hη, hz]
  rw [pairingValue_eq_sum T (c • γ) m e χ hχ hχc hχs hχ1 (fun i => c • η i) hc,
    pairingValue_eq_sum T γ m e χ hχ hχc hχs hχ1 η hη]
  simp only [map_smul, Finset.smul_sum]

/-- The current internally produces its unique real linear functional on global forms. -/
theorem exists_unique_linear_pairing (T : GlobalCurrent n M k) :
    ∃! L : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →ₗ[ℝ] ℝ,
      ∀ (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
        (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ),
        (∀ i, ChartSmooth (n := n) (χ i)) →
        (∀ i, IsCompact (tsupport (χ i))) →
        (∀ i, tsupport (χ i) ⊆ (e i).val.source) →
        (∀ x, ∑ i, χ i x = 1) →
        ∀ η : ∀ i, _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
            (Module.finrank ℝ (ComplexModel n) - k.val),
          (∀ i z, η i z = (e i).val.target.indicator
            (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z) →
          L γ = ∑ i, T.inChart (e i) (η i) := by
  classical
  let L : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →ₗ[ℝ] ℝ :=
    { toFun := pairingValue T
      map_add' := pairingValue_add T
      map_smul' := pairingValue_smul T }
  refine ⟨L, ?_, ?_⟩
  · intro γ m e χ hχ hχc hχs hχ1 η hη
    exact pairingValue_eq_sum T γ m e χ hχ hχc hχs hχ1 η hη
  · intro K hK
    apply LinearMap.ext
    intro γ
    obtain ⟨a, ha, huniq⟩ := exists_unique_pairing T γ
    have hL : L γ = a := huniq (L γ) (by
      intro m e χ hχ hχc hχs hχ1 η hη
      exact pairingValue_eq_sum T γ m e χ hχ hχc hχs hχ1 η hη)
    exact (huniq (K γ) (hK γ)).trans hL.symm

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalLinearPairing
