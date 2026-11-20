import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentMollifiedACForm
import SGPT.Foundations.Analysis.Pending.DistributionConvolutionSmoothness

set_option autoImplicit false

/-! Genuine buffered local smoothness of the SAME native mollified form.
The full mathematical statements and ENTIRE proofs precede this source.
Only x in the original open domain is used to supply the common buffer,
cutoff and threshold before ALL original currents. No global regularization,
mass bound, class calibration or desired smoothness certificate is assumed. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentSmoothACApproximation
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentSemicontinuity LocalCurrentDensityMatrix LocalCurrentLebesgue
  LocalCurrentDeterminant TopDegreeDensity LocalPositiveCurrentMollifiedACForm

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- The original domain alone supplies one buffered neighborhood and threshold
on which the native mollified forms of ALL signed original currents are smooth. -/
theorem exists_buffered_smooth_mollified_forms
    {x : ComplexModel (m + 1)} (hx : x ∈ U) :
    ∃ (V : Opens (ComplexModel (m + 1))) (_ : V ≤ U), x ∈ V ∧
      ∃ N : ℕ, ∀ (T : LocalProductCurrent (m + 1) U m) (k : ℕ), N ≤ k →
        ContDiffOn ℝ (⊤ : ℕ∞) (mollifiedForm T k) V := by
  classical
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let V : Opens (ComplexModel (m + 1)) := ⟨ball x (δ/4),isOpen_ball⟩
  let ρ : ContDiffBump x := ⟨δ/2,3*δ/4,by positivity,by linarith⟩
  let K : Compacts (ComplexModel (m + 1)) :=
    ⟨closedBall x (3*δ/4),isCompact_closedBall _ _⟩
  have hKU : (K : Set (ComplexModel (m + 1))) ⊆ U :=
    (closedBall_subset_ball (by linarith : 3*δ/4 < δ)).trans hδU
  let χ : 𝓓(U,ℝ) := ⟨ρ,ρ.contDiff,ρ.hasCompactSupport,by
    change tsupport (ρ : ComplexModel (m + 1) → ℝ) ⊆ U
    rw [ρ.tsupport_eq]
    exact hKU⟩
  have hχK : tsupport χ ⊆ K := by
    change tsupport (ρ : ComplexModel (m + 1) → ℝ) ⊆ closedBall x (3*δ/4)
    rw [ρ.tsupport_eq]
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_bump_rOut_lt (n := m+1) (by positivity : 0 < δ/4))
  have hVU : V ≤ U :=
    (ball_subset_ball (by linarith : δ/4 ≤ δ)).trans hδU
  refine ⟨V,hVU,by exact mem_ball_self (by positivity),N,?_⟩
  intro T k hk
  let F : ComplexModel (m+1) → RealForm (m+1) 2 := fun z =>
    ∑ i, distributionCutoffTranslatedPairing
      (T (formBasis (m+1) m i)) χ (mol (m+1) k 0)
      (contDiff_mol k 0) K hχK hKU z • dualForm m i
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    ContDiff.sum fun i _ => (distributionCutoffTranslatedPairing_contDiff
      (T (formBasis (m+1) m i)) χ (mol (m+1) k 0)
      (contDiff_mol k 0) K hχK hKU).smul contDiff_const
  apply hF.contDiffOn.congr
  intro z hz
  have hbuffer : closedBall z (bump (m+1) k).rOut ⊆ closedBall x (δ/2) := by
    intro y hy
    have hyz := mem_closedBall.mp hy
    have hzx := mem_ball.mp hz
    exact mem_closedBall.mpr (le_of_lt ((dist_triangle y z x).trans_lt
      (by linarith [hN k hk])))
  have hzU : closedBall z (bump (m+1) k).rOut ⊆ U :=
    hbuffer.trans ((closedBall_subset_ball (by linarith : δ/2 < δ)).trans hδU)
  have htest : (if h : closedBall z (bump (m+1) k).rOut ⊆ U then
      bumpTest U k z h else 0) = TestFunction.ofSupportedIn hKU
        (cutoffTranslatedKernelSupportedIn χ (mol (m+1) k 0)
          (contDiff_mol k 0) K hχK z) := by
    rw [dif_pos hzU]
    ext y
    change mol (m+1) k z y = χ y * mol (m+1) k 0 (y-z)
    have hkernel : mol (m+1) k 0 (y-z) = mol (m+1) k z y := by
      unfold mol
      congr 1
      abel
    rw [hkernel]
    by_cases hy : mol (m+1) k z y = 0
    · simp only [hy,mul_zero]
    · have hyball := hbuffer (mem_closedBall.mpr (dist_lt_of_mol_ne_zero hy).le)
      have hχone : χ y = 1 := ρ.one_of_mem_closedBall hyball
      rw [hχone,one_mul]
  change (∑ i, T (formBasis (m+1) m i)
    (if h : closedBall z (bump (m+1) k).rOut ⊆ U then
      bumpTest U k z h else 0) • dualForm m i) = F z
  rw [htest]
  rfl

/-- Actual smooth positive local forms recover the native entire AC form,
matrix and top density on one common internally produced AE set. -/
theorem exists_local_smooth_positive_ac_approximation
    {x : ComplexModel (m + 1)} (hx : x ∈ U) :
    ∃ (V : Opens (ComplexModel (m+1))) (_ : V ≤ U), x ∈ V ∧
      ∃ N : ℕ, ∀ (T : LocalProductCurrent (m+1) U m) (hT : IsPositive T),
        (∀ k, N ≤ k → ContDiffOn ℝ (⊤ : ℕ∞) (mollifiedForm T k) V ∧
          ∀ z ∈ V, IsOneOne (mollifiedForm T k z) ∧
            (normalizedHermitianMatrix (mollifiedForm T k z)).PosSemidef) ∧
        (∀ᵐ z ∂volume, z ∈ V →
          Tendsto (fun k => mollifiedForm T k z) atTop (𝓝 (acForm hT z)) ∧
          Tendsto (fun k => normalizedHermitianMatrix (mollifiedForm T k z))
            atTop (𝓝 (acMatrix hT z)) ∧
          Tendsto (fun k => actualTopPowerDensity (mollifiedForm T k z))
            atTop (𝓝 (actualTopPowerDensity (acForm hT z)))) := by
  obtain ⟨V,hVU,hxV,N,hN⟩ := exists_buffered_smooth_mollified_forms hx
  refine ⟨V,hVU,hxV,N,?_⟩
  intro T hT
  refine ⟨fun k hk => ⟨hN T k hk,fun z _ => mollifiedForm_isPositive hT k z⟩,?_⟩
  filter_upwards [ae_tendsto_mollifiedForm_matrix_density hT] with z hz hzV
  exact hz (hVU hzV)

end SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentSmoothACApproximation
