import SGPT.Foundations.Analysis.Pending.FullPositiveCurrentLocalPshPotential
import SGPT.Foundations.Analysis.Pending.ClosedCurrentSmoothBottChernRepresentative
import SGPT.Foundations.Analysis.Pending.XiaoCompatibleGlobalPotential
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-! Every original compact closed fully positive (1,1) current internally
has a genuine smooth background and global noncollapsed theta-PSH potential,
with equality in the ORIGINAL full current space. No class, reader or
compatibility certificate is supplied. ENTIRE BP proofs precede this source. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
namespace SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  LelongPoincareDivisor GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
  FiniteScalarDistributionGluing ThetaPshChartLimitGluing
  XiaoPoissonChartCompatibility XiaoCompatibleGlobalPotential
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  GlobalPositiveCurrentACRestriction FullPositiveCurrentLocalPshPotential
  ClosedCurrentSmoothBottChernRepresentative

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Original full scalar-density compatibility implies the actual coordinate
pullback identity, with genuine complete tests and their actual support. -/
theorem isCoordinateCompatible_of_scalarFamilyCompatible
    (S : (e : ComplexChart (m + 1) M) → 𝓓'(chartTarget e, ℝ))
    (hS : ScalarFamilyCompatible S) : IsCoordinateCompatible S := by
  intro e f ψ hψ
  let θ : 𝓓(overlapTarget e f, ℝ) :=
    ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψ⟩
  let η : 𝓓(overlapSource e f, ℝ) :=
    pullTest e f ψ hψ (image_tsupport_subset_source e f hψ)
  have hrel : ∀ z ∈ (chartTransition e f).source,
      η z = transitionJac e f z * θ ((chartTransition e f) z) := by
    intro z hz
    exact pullFun_of_mem e f ψ hz
  have ht : (TestFunction.monoCLM ℝ θ : 𝓓(chartTarget f, ℝ)) = ψ := by
    apply TestFunction.ext
    intro z
    rw [congrFun (testFunction_inclusion_coe (overlapTarget_le e f) θ) z]
    rfl
  have he : (TestFunction.monoCLM ℝ η : 𝓓(chartTarget e, ℝ)) =
      pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ) := by
    apply TestFunction.ext
    intro z
    rw [congrFun (testFunction_inclusion_coe (overlapSource_le e f) η) z]
    rfl
  have h := hS e f η θ hrel
  rw [he, ht] at h
  exact h.symm

private theorem ddC_add {U : Opens (ComplexModel (m + 1))}
    (R Q : 𝓓'(U, ℝ)) : ddC (R + Q) = ddC R + ddC Q := by
  exact map_add ddCLM R Q

private theorem restrictForm_add {Ω U : Opens (ComplexModel (m + 1))}
    (hU : U ≤ Ω) (A B : DistributionForm Ω 2) :
    restrictForm (A + B) hU = restrictForm A hU + restrictForm B hU := by
  ext v φ
  rfl

/-- The original full positive current supplies the local Levi inequalities
of its actual smooth-background/scalar-distribution decomposition. -/
theorem isLocallyThetaPshDistribution_of_original_full_positive
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (σ : ClosedRealOneOneForm (m + 1) M)
    (S : (e : ComplexChart (m + 1) M) → 𝓓'(chartTarget e, ℝ))
    (hread : ∀ e, T.coefficients (canonicalBasis (m + 1)) e =
      smoothFormDistribution (canonicalBasis (m + 1)) σ.val e + ddC (S e)) :
    ∀ e, IsLocallyThetaPshDistribution (canonicalBasis (m + 1)).addHaar σ.val e (S e) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hpot⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials σ e z hz
  let U : Opens (ComplexModel (m + 1)) := ⟨W, hpot.1⟩
  have hU : U ≤ chartTarget e := hpot.2.1
  have hρ : LocallyIntegrableOn ρ U (canonicalBasis (m + 1)).addHaar :=
    hpot.2.2.1.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hσ : restrictForm
      (smoothFormDistribution (canonicalBasis (m + 1)) σ.val e) hU =
      ddC (regularDistribution (canonicalBasis (m + 1)).addHaar ρ hρ) := by
    have h := restrictForm_smoothFormDistribution_eq_ddC σ.val e hU ρ hpot
    rw [coefficients_smoothGlobalCurrent] at h
    exact h
  let R := restrictDistribution (S e) hU +
    regularDistribution (canonicalBasis (m + 1)).addHaar ρ hρ
  have hR : ddC R = restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hU := by
    have h := congrArg (fun A => restrictForm A hU) (hread e)
    rw [restrictForm_add, hσ, restrictForm_ddC] at h
    dsimp only [R]
    rw [ddC_add]
    exact (add_comm _ _).trans h.symm
  obtain ⟨u, hu⟩ := exists_pshRepresentative_of_original_full_positive
    (canonicalBasis (m + 1)).addHaar T hT e hU R hR
  exact ⟨U, hU, ρ, hρ, hzW, hpot, hu.hasNonnegativeDistributionalLevi⟩

/-- Original compact closed full positivity internally creates the smooth
background, all local/coordinate data, and a genuine global theta potential
whose actual original current is exactly the input current. -/
theorem exists_theta_representation_of_original_closed_full_positive [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ (σ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
      (hu : IsThetaPshPotential σ.val u),
      T = thetaPotentialCurrent σ.val u hu ∧
      ∀ e : ComplexChart (m + 1) M,
        (∀ᵐ z ∂(canonicalBasis (m + 1)).addHaar.restrict (chartTarget e),
          chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) ∧
        ∃ hL : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
          (chartTarget e) (canonicalBasis (m + 1)).addHaar,
          T.coefficients (canonicalBasis (m + 1)) e =
            smoothFormDistribution (canonicalBasis (m + 1)) σ.val e +
            ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
              (fun z => (chartFunction u e z).toReal) hL) := by
  obtain ⟨k, g, P, hP, R, χ, hχ, hc, hs, Q, σ,
      _hnon, _hsP, _hsum, _hR, _hT, hread, _hQ⟩ :=
    exists_smooth_native_bott_chern_representative (canonicalBasis (m + 1))
      (Nat.succ_pos m) T hclosed h11
  let S := finiteScalarFamily g χ hχ hc hs R
  have hS : ScalarFamilyCompatible S := finiteScalarFamily_compatible g χ hχ hc hs R
  have hlocal := isLocallyThetaPshDistribution_of_original_full_positive T hT σ S hread
  obtain ⟨u, hu, hchart⟩ := exists_isThetaPshPotential_of_isCoordinateCompatible
    (canonicalBasis (m + 1)).addHaar S
    (isCoordinateCompatible_of_scalarFamilyCompatible S hS) hlocal
  refine ⟨σ, u, hu, ?_, ?_⟩
  · apply globalCurrent_ext (canonicalBasis (m + 1))
    intro e
    rw [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
      coefficients_smoothGlobalCurrent, globalDDC_coefficients, hread e]
    obtain ⟨_hfin, hL, heq⟩ := hchart e
    change smoothFormDistribution (canonicalBasis (m + 1)) σ.val e + ddC (S e) =
      smoothFormDistribution (canonicalBasis (m + 1)) σ.val e +
        ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
          (fun z => (chartFunction u e z).toReal) _)
    rw [heq]
  · intro e
    obtain ⟨hfin, hL, heq⟩ := hchart e
    exact ⟨hfin, hL, (hread e).trans (congrArg
      (fun F => smoothFormDistribution (canonicalBasis (m + 1)) σ.val e + ddC F) heq)⟩

end SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation
