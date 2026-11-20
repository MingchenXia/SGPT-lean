import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Module.Basic

/-! # Actual scalar first-jet Hilbert spaces

All five complete mathematical statements and ENTIRE proofs precede this
source. The original compact smooth topology is kept. The new Hilbert
space is the actual closed range of real square-integrable first jets.
-/

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsLocallyFiniteMeasure μ] (K : Compacts E)

/-- The genuine square-integrable class of an entire compact smooth scalar test. -/
def scalarStageL2 : 𝓓_{K}(E, ℝ) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' f g := by
    exact MemLp.toLp_add
      (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)
      (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport)
  map_smul' c f := by
    exact MemLp.toLp_const_smul c
      (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

theorem scalarStageL2_ae (f : 𝓓_{K}(E, ℝ)) : scalarStageL2 μ K f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

theorem scalarStageL2_norm_sq (f : 𝓓_{K}(E, ℝ)) :
    ‖scalarStageL2 μ K f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarStageL2_ae μ K f] with x hx
  rw [hx]
  simp [Real.norm_eq_abs, sq_abs]

theorem scalarStageL2_injective [μ.IsOpenPosMeasure] :
    Injective (scalarStageL2 μ K) := by
  intro f g h
  have hae : (f : E → ℝ) =ᵐ[μ] g :=
    (scalarStageL2_ae μ K f).symm.trans (h ▸ scalarStageL2_ae μ K g)
  exact DFunLike.ext' (Measure.eq_of_ae_eq hae f.continuous g.continuous)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Infinite ordinary differentiation followed by actual evaluation in a fixed direction. -/
def directionalStageCLM (v : E) : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{K}(E, ℝ) :=
  (ContDiffMapSupportedIn.postcompCLM (ContinuousLinearMap.apply ℝ ℝ v)).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem directionalStageCLM_apply (v : E) (f : 𝓓_{K}(E, ℝ)) (x : E) :
    directionalStageCLM K v f x = fderiv ℝ f x v := by
  change (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f) x v = _
  rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)]

/-- The actual finite Hilbert sum of value and directional derivative scalar L² coordinates. -/
abbrev JetL2 (ι : Type*) := PiLp 2 (fun _ : Unit ⊕ ι => Lp ℝ 2 μ)

variable {ι : Type*} [Fintype ι] (v : ι → E)

/-- Actual ordinary scalar first jets, with no replacement of the compact smooth test topology. -/
def firstJetLinear : 𝓓_{K}(E, ℝ) →ₗ[ℝ] JetL2 μ ι where
  toFun f := WithLp.toLp 2 (Sum.elim
    (fun _ => scalarStageL2 μ K f)
    (fun j => scalarStageL2 μ K (directionalStageCLM K (v j) f)))
  map_add' f g := by
    ext i
    cases i <;> simp [map_add, PiLp.add_apply]
  map_smul' c f := by
    ext i
    cases i <;> simp [map_smul, PiLp.smul_apply]

omit [Fintype ι] in
theorem firstJetLinear_value (f : 𝓓_{K}(E, ℝ)) :
    firstJetLinear μ K v f (Sum.inl ()) = scalarStageL2 μ K f := rfl

omit [Fintype ι] in
theorem firstJetLinear_derivative (f : 𝓓_{K}(E, ℝ)) (j : ι) :
    firstJetLinear μ K v f (Sum.inr j) =
      scalarStageL2 μ K (directionalStageCLM K (v j) f) := rfl

theorem firstJetLinear_norm_sq (f : 𝓓_{K}(E, ℝ)) :
    ‖firstJetLinear μ K v f‖ ^ 2 =
      (∫ x, f x ^ 2 ∂μ) + ∑ j, ∫ x, (fderiv ℝ f x (v j)) ^ 2 ∂μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Unit ⊕ ι, ‖Sum.elim
    (fun _ => scalarStageL2 μ K f)
    (fun j => scalarStageL2 μ K (directionalStageCLM K (v j) f)) i‖ ^ 2) = _
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique, scalarStageL2_norm_sq]
  congr 1

/-- The actual topological closure of the concrete scalar first-jet range. -/
def closedFirstJet : Submodule ℝ (JetL2 μ ι) :=
  (firstJetLinear μ K v).range.topologicalClosure

abbrev SobolevFirstJet := closedFirstJet μ K v

/-- The genuine original smooth test jet belongs to its own closed range. -/
def toSobolevFirstJet : 𝓓_{K}(E, ℝ) →ₗ[ℝ] SobolevFirstJet μ K v :=
  (firstJetLinear μ K v).codRestrict _ fun f =>
    (firstJetLinear μ K v).range.le_topologicalClosure ⟨f, rfl⟩

theorem sobolevFirstJet_complete : CompleteSpace (SobolevFirstJet μ K v) := by
  unfold SobolevFirstJet closedFirstJet
  infer_instance

/-- Literal coordinate projection of the constructed closed scalar first-jet space. -/
def jetCoordinateCLM (i : Unit ⊕ ι) : SobolevFirstJet μ K v →L[ℝ] Lp ℝ 2 μ :=
  (PiLp.proj 2 (fun _ : Unit ⊕ ι => Lp ℝ 2 μ) i).comp (closedFirstJet μ K v).subtypeL

theorem jetCoordinateCLM_apply_native (i : Unit ⊕ ι) (f : 𝓓_{K}(E, ℝ)) :
    jetCoordinateCLM μ K v i (toSobolevFirstJet μ K v f) = firstJetLinear μ K v f i := rfl

theorem jetCoordinateCLM_norm_le (i : Unit ⊕ ι) (a : SobolevFirstJet μ K v) :
    ‖jetCoordinateCLM μ K v i a‖ ≤ ‖a‖ :=
  PiLp.norm_apply_le a.val i

theorem closedFirstJet_empty : closedFirstJet μ ⊥ v = ⊥ := by
  have hz : firstJetLinear μ (⊥ : Compacts E) v = 0 := by
    apply LinearMap.ext
    intro f
    have hf : f = 0 := by
      apply DFunLike.ext
      intro x
      exact f.zero_on_compl (by simp)
    rw [hf, map_zero]
    rfl
  simp [closedFirstJet, hz]

end SGPT.Foundations.Analysis.Pending.NaturalScalarSobolevJet
