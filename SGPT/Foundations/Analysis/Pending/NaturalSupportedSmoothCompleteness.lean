module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Sequences

/-!
# Completeness of actual compact-support smooth stages

The actual uniform space of all smooth functions supported in a compact set is complete.
The proof reconstructs every derivative from a limit of actual full jets.
-/

@[expose] public section


open Filter Set TopologicalSpace
open scoped Topology Distributions ContDiff BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending.NaturalSupportedSmoothCompleteness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Compacts E}

/-- The actual full jet embedding into the countable product of bounded continuous jets. -/
noncomputable def jetMap :
    𝓓_{K}(E, F) →L[ℝ] Π m : ℕ, E →ᵇ (E [×m]→L[ℝ] F) :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)

/-- Uniform limits of every actual derivative reconstruct an actual supported smooth map. -/
theorem exists_supported_smooth_of_jet_limits
    (f : ℕ → 𝓓_{K}(E, F)) (G : Π m : ℕ, E →ᵇ (E [×m]→L[ℝ] F))
    (hG : ∀ m, Tendsto (fun j => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ m (f j))
      atTop (𝓝 (G m))) :
    ∃ g : 𝓓_{K}(E, F), ∀ m, ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ m g = G m := by
  have hU (m : ℕ) : TendstoUniformly (fun j => iteratedFDeriv ℝ m (f j)) (G m) atTop := by
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hG m))
  have hT (j : ℕ) : HasFTaylorSeriesUpTo (⊤ : ℕ∞) (f j) (ftaylorSeries ℝ (f j)) :=
    (f j).contDiff.ftaylorSeries
  let p : E → FormalMultilinearSeries ℝ E F := fun x m => G m x
  let g : E → F := fun x => (G 0 x).curry0
  have hTaylor : HasFTaylorSeriesUpTo (⊤ : ℕ∞) g p := by
    refine ⟨fun _ => rfl, ?_, fun m _ => (G m).continuous⟩
    intro m _ x
    have hderiv : TendstoUniformly
        (fun j y => (iteratedFDeriv ℝ m.succ (f j) y).curryLeft)
        (fun y => (G m.succ y).curryLeft) atTop :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin m.succ => E) F).isometry.uniformContinuous
        |>.comp_tendstoUniformly (hU m.succ)
    exact hasFDerivAt_of_tendstoUniformly hderiv
      (fun j y => (hT j).fderiv m (by exact_mod_cast (WithTop.coe_lt_top m)) y)
      (fun y => (hU m).tendsto_at y) x
  have hsupport : EqOn g 0 (K : Set E)ᶜ := by
    intro x hx
    have hfg : Tendsto (fun j => f j x) atTop (𝓝 (g x)) := by
      have h := (continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto (G 0 x)
        |>.comp ((hU 0).tendsto_at x)
      simpa [g, Function.comp_def, iteratedFDeriv_zero_eq_comp] using h
    have hzero : Tendsto (fun j => f j x) atTop (𝓝 (0 : F)) := by
      have heq : (fun j => f j x) = fun _ : ℕ => (0 : F) :=
        funext fun j => (f j).zero_on_compl hx
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hfg hzero
  let gK : 𝓓_{K}(E, F) := ⟨g, hTaylor.contDiff, hsupport⟩
  refine ⟨gK, fun m => ?_⟩
  apply BoundedContinuousFunction.ext
  intro x
  have hgfun : (gK : E → F) = g := rfl
  simp only [ContDiffMapSupportedIn.structureMapCLM_top_apply, hgfun]
  exact (hTaylor.eq_iteratedFDeriv (m := m)
    (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)) x).symm

/-- The actual all-jet embedding has closed image; no smooth limit is assumed. -/
theorem isClosed_range_jetMap : IsClosed (range (jetMap (E := E) (F := F) (K := K))) := by
  apply IsSeqClosed.isClosed
  intro z G hz hlim
  choose f hf using hz
  have hseq : (fun j => jetMap (f j)) = z := funext hf
  rw [← hseq] at hlim
  obtain ⟨g, hg⟩ := exists_supported_smooth_of_jet_limits f G
    (fun m => tendsto_pi_nhds.mp hlim m)
  exact ⟨g, funext hg⟩

variable [CompleteSpace F] in
/-- Completeness of the existing, faithful, all-derivative uniform structure. -/
noncomputable instance completeSpace : CompleteSpace 𝓓_{K}(E, F) :=
  (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (n := ⊤) ℝ).isUniformInducing
    |>.completeSpace isClosed_range_jetMap.isComplete

/-- The existing countable derivative seminorms give a countable neighborhood base. -/
instance firstCountableTopology : FirstCountableTopology 𝓓_{K}(E, F) :=
  (ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ K).firstCountableTopology

end SGPT.Foundations.Analysis.Pending.NaturalSupportedSmoothCompleteness
