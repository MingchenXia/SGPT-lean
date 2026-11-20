import SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarCurrent
import SGPT.Foundations.Analysis.Pending.DistributionDdcChartCovariance

set_option autoImplicit false

/-! Native ddC of internally assembled signed scalar distributions is realized
in the ORIGINAL global degree-two current space. Full tensor overlap is
proved from the actual adjoint test identity and internally supplied scalar
compatibility. No global class or smooth remainder is asserted. -/

noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarDdc
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  DDCOverlap DistributionChartPullback DistributionDdcChartCovariance
  FiniteScalarDistributionGluing ThetaPshChartLimitGluing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

private theorem ddcAdjoint_mono {Ω U : Opens (ComplexModel n)} {q : ℕ}
    (hU : U ≤ Ω) (B : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm U q) :
    ddcAdjoint B (TestFunction.monoCLM ℝ η : TestForm Ω q) =
      (TestFunction.monoCLM ℝ (ddcAdjoint B η) : 𝓓(Ω, ℝ)) := by
  apply TestFunction.ext
  intro z
  rw [ddcAdjoint_monoCLM_apply hU, testFunction_inclusion_coe hU]

private def ddcCurrentFamily
    (S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ)) :
    ChartCurrentFamily n M (degreeTwo hn) :=
  fun e => toLocalCurrent b (degreeTwo hn) (ddC (S e))

private theorem ddcCurrentFamily_compatible
    (S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hS : ScalarFamilyCompatible S) : CurrentFamilyCompatible (ddcCurrentFamily b hn S) := by
  intro e f η θ hrel
  let B := currentPairingBasis b (degreeTwo hn)
  change wedgePairing B (ddC (S e)) (TestFunction.monoCLM ℝ η) =
    wedgePairing B (ddC (S f)) (TestFunction.monoCLM ℝ θ)
  have hrel' : ∀ z ∈ (chartTransition e f).source,
      ddcAdjoint B η z = transitionJac e f z *
        ddcAdjoint B θ ((chartTransition e f) z) := by
    intro z hz
    have h := congrArg (fun φ : 𝓓(overlapSource e f, ℝ) => φ z)
      (weighted_adjoint_eq B e f η θ hrel)
    change pullFun e f (ddcAdjoint B θ) z = ddcAdjoint B η z at h
    rw [pullFun_of_mem e f _ hz] at h
    exact h.symm
  have he := congrArg (S e) (ddcAdjoint_mono (overlapSource_le e f) B η)
  have hf := congrArg (S f) (ddcAdjoint_mono (overlapTarget_le e f) B θ)
  exact (wedgePairing_ddC B (S e) _).trans
    (he.trans ((hS e f (ddcAdjoint B η) (ddcAdjoint B θ) hrel').trans
      (hf.symm.trans (wedgePairing_ddC B (S f) _).symm)))

/-- Natural finite signed chart data internally produce the ORIGINAL global
native ddC current, including all full tensor overlap compatibility. -/
def finiteGlobalDdc {ι : Type*} [Fintype ι] (g : ι → ComplexChart n M)
    (χ : ι → M → ℝ) (hχ : ∀ a, ChartSmooth (n := n) (χ a))
    (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) : GlobalCurrent n M (degreeTwo hn) :=
  ⟨ddcCurrentFamily b hn (finiteScalarFamily g χ hχ hc hs R),
    ddcCurrentFamily_compatible b hn _ (finiteScalarFamily_compatible g χ hχ hc hs R)⟩

/-- Original coefficient extraction recovers the entire native ddC form;
no density, factorial or desired-class certificate occurs. -/
theorem finiteGlobalDdc_coefficients {ι : Type*} [Fintype ι]
    (g : ι → ComplexChart n M) (χ : ι → M → ℝ)
    (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) (e : ComplexChart n M) :
    (finiteGlobalDdc b hn g χ hχ hc hs R).coefficients b e =
      ddC (finiteScalarFamily g χ hχ hc hs R e) :=
  CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) _

/-- Closedness uses the actual native derivative identity in every chart. -/
theorem finiteGlobalDdc_isClosed {ι : Type*} [Fintype ι]
    (g : ι → ComplexChart n M) (χ : ι → M → ℝ)
    (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) :
    (finiteGlobalDdc b hn g χ hχ hc hs R).IsClosed b := by
  intro e
  rw [finiteGlobalDdc_coefficients]
  exact _root_.SGPT.Foundations.Analysis.Pending.LocalCurrents.ddC_isClosed _

/-- Type(1,1) is the actual coefficient predicate, for arbitrary signed inputs. -/
theorem finiteGlobalDdc_isTypeOneOne {ι : Type*} [Fintype ι]
    (g : ι → ComplexChart n M) (χ : ι → M → ℝ)
    (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) :
    (finiteGlobalDdc b hn g χ hχ hc hs R).IsTypeOneOne b hn := by
  intro e
  rw [finiteGlobalDdc_coefficients]
  exact _root_.SGPT.Foundations.Analysis.Pending.LocalCurrents.ddC_isOneOne _

end SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarDdc
