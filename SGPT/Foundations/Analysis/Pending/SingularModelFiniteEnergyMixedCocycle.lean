import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedTruncation
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

set_option autoImplicit false

/-!
# Actual mixed energy cocycle for all singular-model E1 endpoints

Xia SGPT PDF0124--0126, Proposition 3.1.18 and equation (3.39).
The genuine finite-type cocycle passes to the limit through the produced
actual weighted mixed truncation convergence. Common finite translation
then covers the singularity-order E1 class over every singular model.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedCocycle

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass GlobalNonPluripolar
  GlobalDiagonalScaling MongeAmpereEnergyDecreasing SingularModelEnergyTruncation
  SingularModelFiniteEnergyMixedGap SingularModelFiniteEnergyMixedTruncation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

omit [BorelSpace M] in
/-- The source endpoint mixed measure is precisely the actual binary tuple. -/
theorem endpointMixedMeasure_eq_binaryMixedMeasure
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (k : Fin (n + 1)) :
    endpointMixedMeasure θ v u hv hu k = binaryMixedMeasure hu hv (fun i => decide (i.val < k.val)) := by
  classical
  apply globalMixedMeasure_congr rfl
  funext i
  by_cases hi : i.val < k.val <;> simp [endpointMixedPotential, hi]

/-- Every actual source endpoint mixed term converges along the genuine
canonical truncations, without a weighted convergence premise. -/
theorem relativeEnergyTerm_tendsto_truncations [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (k : Fin (n + 1)) :
    Tendsto (fun j => relativeEnergyTerm θ (truncation φ v j) (truncation φ u j)
      (relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
        (preceq_of_relativePSH hv.1.relativePSH).2 j).1
      (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
        (preceq_of_relativePSH hu.1.relativePSH).2 j).1 k)
      atTop (𝓝 (relativeEnergyTerm θ v u hv.1.plurisubharmonic hu.1.plurisubharmonic k)) := by
  simpa only [relativeEnergyTerm, endpointMixedMeasure_eq_binaryMixedMeasure] using
    tendsto_integral_canonicalDiff_truncations omega hu hv (fun i => decide (i.val < k.val))

/-- The actual mixed cocycle holds for normalized genuine E1 endpoints over
an arbitrary singular model, from actual finite-type cocycle and convergence. -/
theorem toReal_energy_sub_eq_relativeEnergyOfMinimalType [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ) :
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal =
      relativeEnergyOfMinimalType θ v u hv.1.plurisubharmonic hu.1.plurisubharmonic := by
  let hp := hφ.plurisubharmonic
  let htu := fun j => relativeEInfinity_truncation hp hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2 j
  let htv := fun j => relativeEInfinity_truncation hp hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2 j
  have hTu := energy_tendsto_truncation omega θ hφ hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2
  have hTv := energy_tendsto_truncation omega θ hφ hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (preceq_of_relativeFiniteEnergy hu)] at hTu
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (preceq_of_relativeFiniteEnergy hv)] at hTv
  have hL := (EReal.tendsto_coe.mp hTu).sub (EReal.tendsto_coe.mp hTv)
  have hR : Tendsto (fun j => relativeEnergyOfMinimalType θ (truncation φ v j) (truncation φ u j)
      (htv j).1 (htu j).1) atTop
      (𝓝 (relativeEnergyOfMinimalType θ v u hv.1.plurisubharmonic hu.1.plurisubharmonic)) := by
    unfold relativeEnergyOfMinimalType
    exact (tendsto_finsetSum Finset.univ fun k _ => relativeEnergyTerm_tendsto_truncations omega hu hv k).div_const _
  have hEq (j : ℕ) := SingularModelEnergyCocycle.relativeEnergyOfMinimalType_sub
    omega θ hp (htu j).1 (htv j).1 (htu j).2 (htv j).2
  have hR' := hR.congr' (Eventually.of_forall fun j => (hEq j).symm)
  exact tendsto_nhds_unique hL hR'

private theorem binaryMixedMeasure_add_const
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (c : ℝ) (σ : Fin n → Bool) :
    binaryMixedMeasure (hu.add_const c) (hv.add_const c) σ = binaryMixedMeasure hu hv σ := by
  have hslots (i : Fin n) : ThetaPlurisubharmonic θ.val (if σ i then u else v) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hv.1 | exact hu.1
  have hshift (i : Fin n) : ThetaPlurisubharmonic θ.val
      (if σ i then fun x => u x + (c : EReal) else fun x => v x + (c : EReal)) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact (hv.add_const c).1 | exact (hu.add_const c).1
  have h := GlobalMeasureInvariance.globalMixedMeasure_sub_const hslots (fun _ => -c)
  have heq : (fun i : Fin n => fun x => (if σ i then u else v) x - ((-c : ℝ) : EReal)) =
      (fun i => if σ i then fun x => u x + (c : EReal) else fun x => v x + (c : EReal)) := by
    funext i x
    cases σ i <;> simp [EReal.coe_neg, sub_eq_add_neg]
  rw [globalMixedMeasure_congr rfl heq _ hshift] at h
  exact h

private theorem canonicalDiff_add_coe (a b : EReal) (c : ℝ) :
    canonicalERealDiffToReal (a + (c : EReal)) (b + (c : EReal)) = canonicalERealDiffToReal a b := by
  cases a <;> cases b <;>
    simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal,
      ← EReal.coe_add, ← EReal.coe_sub]

private theorem relativeEnergyOfMinimalType_common_translation
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) (c : ℝ) :
    relativeEnergyOfMinimalType θ (fun x => v x + (c : EReal)) (fun x => u x + (c : EReal))
      (hv.add_const c) (hu.add_const c) = relativeEnergyOfMinimalType θ v u hv hu := by
  classical
  unfold relativeEnergyOfMinimalType
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold relativeEnergyTerm
  rw [endpointMixedMeasure_eq_binaryMixedMeasure, endpointMixedMeasure_eq_binaryMixedMeasure,
    binaryMixedMeasure_add_const hu hv c]
  simp only [canonicalDiff_add_coe]

/-- Every actual mixed source endpoint term is integrable for singularity-order
E1 endpoints; actual common-constant measure invariance produces the transfer. -/
theorem integrable_endpoint_canonicalDiff_of_preceq [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (k : Fin (n + 1)) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (endpointMixedMeasure θ v u hv.1.plurisubharmonic hu.1.plurisubharmonic k) := by
  obtain ⟨c, hcu, hcv⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  have hi := integrable_canonicalDiff_binaryMixedMeasure omega
    (hu.relativeFiniteEnergy_add omega hcu) (hv.relativeFiniteEnergy_add omega hcv)
    (fun i => decide (i.val < k.val))
  change Integrable (fun x => canonicalERealDiffToReal (u x + (c : EReal)) (v x + (c : EReal)))
    (binaryMixedMeasure (hu.1.plurisubharmonic.add_const c) (hv.1.plurisubharmonic.add_const c)
      (fun i => decide (i.val < k.val))) at hi
  rw [binaryMixedMeasure_add_const hu.1.plurisubharmonic hv.1.plurisubharmonic c] at hi
  simp only [canonicalDiff_add_coe] at hi
  rw [endpointMixedMeasure_eq_binaryMixedMeasure]
  exact hi

/-- Xia's actual E1 mixed energy cocycle over every singular model holds for
the full singularity-order E1 class, without any cocycle or convergence premise. -/
theorem toReal_energy_sub_eq_relativeEnergyOfMinimalType_of_preceq [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    (energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal =
      relativeEnergyOfMinimalType θ v u hv.1.plurisubharmonic hu.1.plurisubharmonic := by
  obtain ⟨c, hcu, hcv⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  have h := toReal_energy_sub_eq_relativeEnergyOfMinimalType omega
    (hu.relativeFiniteEnergy_add omega hcu) (hv.relativeFiniteEnergy_add omega hcv)
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu c,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega hv c] at h
  change ((energy θ φ hφ u).toReal + c * modelVolume θ φ hφ) -
      ((energy θ φ hφ v).toReal + c * modelVolume θ φ hφ) =
    relativeEnergyOfMinimalType θ (fun x => v x + (c : EReal)) (fun x => u x + (c : EReal))
      (hv.1.plurisubharmonic.add_const c) (hu.1.plurisubharmonic.add_const c) at h
  rw [relativeEnergyOfMinimalType_common_translation hu.1.plurisubharmonic hv.1.plurisubharmonic c] at h
  linarith

/-- The source sum-of-actual-integrals form (3.39), with genuine E1 endpoint
integrability produced above and no boundedness of the model reference. -/
theorem mul_toReal_energy_sub_eq_sum_endpoint_integrals [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    ((n : ℝ) + 1) * ((energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal) =
      ∑ k : Fin (n + 1), ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂endpointMixedMeasure θ v u hv.1.plurisubharmonic hu.1.plurisubharmonic k := by
  rw [toReal_energy_sub_eq_relativeEnergyOfMinimalType_of_preceq omega hu hv,
    relativeEnergyOfMinimalType]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  rfl

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedCocycle
