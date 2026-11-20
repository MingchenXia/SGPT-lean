import SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormFrechetModule
import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration

/-!
# Actual signed currents on the complete global smooth-form module

The original full LF coordinate currents internally supply a finite product CLM.
The actual supported linear equivalence then gives a genuine continuous global
functional on the original geometric quotient, with the actual native pairing
on every representative. No positivity or caller continuity certificate is used.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalGlobalCurrentSmoothDual

open FirstPass NaturalCompactGeometricFormFrechetModule ActualCompactGlobalPairingCalibration

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {k : CurrentDegree n}

/-- The actual full native current pairing on a finite product of supported stages. -/
def stagePairingCLM (T : GlobalCurrent n M k) (e : Fin m → ComplexChart n M)
    (K : Fin m → Compacts (ComplexModel n))
    (hK : ∀ i, (K i : Set (ComplexModel n)) ⊆ (e i).val.target) :
    (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n) - k.val)]→L[ℝ] ℝ))
      →L[ℝ] ℝ :=
  ∑ i, ((T.inChart (e i)).comp (TestFunction.ofSupportedInCLM ℝ (hK i))).comp
    (ContinuousLinearMap.proj i)

/-- The constructed product functional evaluates exactly the original entire native tests. -/
theorem stagePairingCLM_apply (T : GlobalCurrent n M k) (e : Fin m → ComplexChart n M)
    (K : Fin m → Compacts (ComplexModel n))
    (hK : ∀ i, (K i : Set (ComplexModel n)) ⊆ (e i).val.target)
    (A : Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n) - k.val)]→L[ℝ] ℝ)) :
    stagePairingCLM T e K hK A =
      ∑ i, T.inChart (e i) (TestFunction.ofSupportedIn (hK i) (A i)) := by
  simp [stagePairingCLM]
  rfl

/-- Before all signed currents, internally construct the same actual complete global smooth space. -/
theorem exists_complete_current_dual [CompactSpace M] (k : CurrentDegree n) :
    ∃ g : AddCommGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
      let _ := g
      ∃ v : Module ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
        let _ := v
        ∃ u : UniformSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
          let _ := u
          CompleteSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          T2Space (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          FirstCountableTopology
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          IsTopologicalAddGroup
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          ContinuousSMul ℝ
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          LocallyConvexSpace ℝ
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          ∀ T : GlobalCurrent n M k, ∃! L :
            GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ,
            ∀ γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val),
              L (GeometricRealForm.ofRepresentative γ) = pairingLM T γ := by
  classical
  obtain ⟨m, e, χ, K, hχ, -, hs, hK, h1, hmodel⟩ :=
    exists_complete_locally_convex_module (n := n) (M := M)
  obtain ⟨S, -, g, v, u, E, hcomplete, hT2, hfc, ha, hv, hl, hread⟩ :=
    hmodel (Module.finrank ℝ (ComplexModel n) - k.val)
  let _ := g
  let _ := v
  let _ := u
  have hKT (i : Fin m) : (K i : Set (ComplexModel n)) ⊆ (e i).val.target := by
    rw [hK i]
    rintro _ ⟨x, hx, rfl⟩
    exact (e i).val.map_source (hs i hx)
  have hc (i : Fin m) : IsCompact (tsupport (χ i)) := (isClosed_tsupport _).isCompact
  let sub : S →L[ℝ] (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
      (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n) - k.val)]→L[ℝ] ℝ)) :=
    { toLinearMap := S.subtype, cont := continuous_subtype_val }
  refine ⟨g, v, u, hcomplete, hT2, hfc, ha, hv, hl, fun T => ?_⟩
  let L := (stagePairingCLM T e K hKT).comp (sub.comp E.toContinuousLinearMap)
  have hcal (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
      L (GeometricRealForm.ofRepresentative γ) = pairingLM T γ := by
    let η (i : Fin m) : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
        (Module.finrank ℝ (ComplexModel n) - k.val) := TestFunction.ofSupportedIn (hKT i)
      ((E (GeometricRealForm.ofRepresentative γ)).val i)
    have hη (i : Fin m) (z : ComplexModel n) : η i z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z := hread γ i z
    have hpair := pairing_eq_sum T γ m e χ hχ hc hs h1 η hη
    change stagePairingCLM T e K hKT ((E (GeometricRealForm.ofRepresentative γ)).val) = _
    rw [stagePairingCLM_apply]
    exact hpair.symm
  refine ⟨L, hcal, ?_⟩
  intro L' hL'
  apply ContinuousLinearMap.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro γ
  exact (hL' γ).trans (hcal γ).symm

end SGPT.Foundations.Analysis.Pending.NaturalGlobalCurrentSmoothDual
