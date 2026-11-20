import SGPT.Foundations.Analysis.Pending.Demailly1992AlgebraicApproximation
import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.SmoothC0OriginalCurrentConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

/-! ANY ORIGINAL closed full-positive T -> internal same-class analytic weak
approximation with uniform negative errors tending to zero. Full BP statement
and ENTIRE proof precede SOURCE. No supplied representation, approximation,
limit or calibration. AC a.e. convergence and resolution-smooth remainders
are separate stronger obligations, not consequences asserted here. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticWeakRegularization
open FirstPass FirstPass.PositiveClasses FirstPass.GlobalAnalyticSingularities
  FirstPass.NumericalRestrictedVolumeScaffold CurrentBottChernClass CanonicalCurrentFrame
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  GlobalCurrentPotentials GlobalPositiveCurrentACRestriction
  ThetaPotentialCurrentBottChernClass XiaoFormC0Topology LelongPoincareDivisor
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem tendsto_regular_of_antitone
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (v : ℕ → M → EReal) (hv : ∀ k, IsGlobalQuasiPshPotential (n := m + 1) (v k))
    (hanti : ∀ x, Antitone fun k => v k x) (hinf : ∀ x, ⨅ k, v k x = u x)
    (e : ComplexChart (m + 1) M) (φ : 𝓓(chartTarget e, ℝ)) :
    Tendsto (fun k => regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (v k) e z).toReal)
      (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
        (Nat.succ_pos m) (v k) (hv k) e) φ) atTop
      (𝓝 (regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction u e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
          (Nat.succ_pos m) u hu e) φ)) := by
  let μ := (canonicalBasis (m + 1)).addHaar
  let f (k : ℕ) (z : ComplexModel (m + 1)) := φ z * (chartFunction (v k) e z).toReal
  let g (z : ComplexModel (m + 1)) := φ z * (chartFunction u e z).toReal
  have hf (k : ℕ) : Integrable (f k) μ :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
        (Nat.succ_pos m) (v k) (hv k) e)
  have hg : Integrable g μ := φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
    (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
      (Nat.succ_pos m) u hu e)
  have hfin : ∀ᵐ z ∂μ, z ∈ chartTarget e →
      (chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) ∧
      (chartFunction (v 0) e z ≠ ⊤ ∧ chartFunction (v 0) e z ≠ ⊥) :=
    (ae_restrict_iff' e.val.open_target.measurableSet).mp
      ((quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
        (Nat.succ_pos m) u hu e).and
        (quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
          (Nat.succ_pos m) (v 0) (hv 0) e))
  have hlow (k : ℕ) (z : ComplexModel (m + 1)) :
      chartFunction u e z ≤ chartFunction (v k) e z := by
    change u (e.val.symm z) ≤ v k (e.val.symm z)
    rw [← hinf]
    exact iInf_le _ k
  have hhigh (k : ℕ) (z : ComplexModel (m + 1)) :
      chartFunction (v k) e z ≤ chartFunction (v 0) e z :=
    hanti (e.val.symm z) (Nat.zero_le k)
  let B (z : ComplexModel (m + 1)) := |g z| + |f 0 z|
  have hB : Integrable B μ := hg.abs.add (hf 0).abs
  have hbound (k : ℕ) : ∀ᵐ z ∂μ, ‖f k z‖ ≤ B z := by
    filter_upwards [hfin] with z hz
    by_cases hzU : z ∈ chartTarget e
    · obtain ⟨huz,hv0z⟩ := hz hzU
      have hvbot : chartFunction (v k) e z ≠ ⊥ := by
        intro h
        exact huz.2 (bot_unique (h ▸ hlow k z))
      have hl := EReal.toReal_le_toReal (hlow k z) huz.2 (by
        intro h
        exact hv0z.1 (top_unique (h ▸ hhigh k z)))
      have hh := EReal.toReal_le_toReal (hhigh k z) hvbot hv0z.1
      have ha : |(chartFunction (v k) e z).toReal| ≤
          |(chartFunction u e z).toReal| + |(chartFunction (v 0) e z).toReal| := by
        apply abs_le.mpr
        constructor
        · linarith [neg_abs_le (chartFunction u e z).toReal,
            abs_nonneg (chartFunction (v 0) e z).toReal]
        · linarith [le_abs_self (chartFunction (v 0) e z).toReal,
            abs_nonneg (chartFunction u e z).toReal]
      simpa only [f,g,B,Real.norm_eq_abs,abs_mul,mul_add] using
        mul_le_mul_of_nonneg_left ha (abs_nonneg (φ z))
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hzU (φ.tsupport_subset ht))
      simp [f,g,B,hφ]
  have ht : ∀ᵐ z ∂μ, Tendsto (fun k => f k z) atTop (𝓝 (g z)) := by
    filter_upwards [hfin] with z hz
    by_cases hzU : z ∈ chartTarget e
    · have hpoint : Tendsto (fun k => chartFunction (v k) e z) atTop
          (𝓝 (chartFunction u e z)) := by
        change Tendsto (fun k => v k (e.val.symm z)) atTop (𝓝 (u (e.val.symm z)))
        rw [← hinf]
        exact tendsto_atTop_iInf (hanti _)
      exact ((EReal.tendsto_toReal (hz hzU).1.1 (hz hzU).1.2).comp hpoint).const_mul (φ z)
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hzU (φ.tsupport_subset hs))
      simp only [f,g,hφ,zero_mul]
      exact tendsto_const_nhds
  simpa only [regularDistribution_apply,f,g] using
    tendsto_integral_of_dominated_convergence B (fun k => (hf k).aestronglyMeasurable) hB hbound ht

private theorem tendsto_globalDDC_of_antitone
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (v : ℕ → M → EReal) (hv : ∀ k, IsGlobalQuasiPshPotential (n := m + 1) (v k))
    (hanti : ∀ x, Antitone fun k => v k x) (hinf : ∀ x, ⨅ k, v k x = u x)
    (e : ComplexChart (m + 1) M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    Tendsto (fun k => (globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (v k) (hv k)).inChart e η) atTop
      (𝓝 ((globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu).inChart e η)) := by
  have hcoeff (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(chartTarget e, ℝ)) :
      Tendsto (fun k => chartDDC (canonicalBasis (m + 1)) (v k) e
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
          (Nat.succ_pos m) (v k) (hv k) e) w φ) atTop
        (𝓝 (chartDDC (canonicalBasis (m + 1)) u e
          (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
            (Nat.succ_pos m) u hu e) w φ)) := by
    have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
    have eval (R : 𝓓'(chartTarget e, ℝ)) : ddC R w φ =
        R (DDCOverlap.ddcAdjointCoeff (w 0) (w 1) φ) :=
      (congrArg (fun t => ddC R t φ) hw).trans (DDCOverlap.ddC_apply_eq R _ _ φ)
    change Tendsto (fun k => ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (v k) e z).toReal) _) w φ) atTop
      (𝓝 (ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction u e z).toReal) _) w φ))
    simp only [eval]
    exact tendsto_regular_of_antitone u hu v hv hanti hinf e _
  simp only [globalDDC_inChart,ddCCurrentFamily,toLocalCurrent,wedgePairing_apply]
  exact tendsto_finsetSum _ fun s _ => (hcoeff _ _).const_smul (Equiv.Perm.sign s.out)

variable [CompactSpace M]

/-- ANY ORIGINAL closed full-positive T internally supplies genuine analytic
same-class approximants, full-test weak convergence and uniform negative error.
No AC matrix convergence or smooth cross-pole remainder is asserted. -/
theorem exists_analytic_same_class_original_weak_regularization
    (ω : KahlerBackground (m + 1) M)
    (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) :
    ∃ (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
      (hu : IsThetaPshPotential θ.val u),
      T.val = thetaPotentialCurrent θ.val u hu ∧
      ∃ (ε : ℕ → ℝ) (v : ℕ → M → EReal)
        (hv : ∀ k, IsThetaPshPotential (θ + ε k • ω.form).val (v k)),
        (∀ k, 0 ≤ ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
        (∀ k, HasAnalyticSingularities (n := m + 1) (v k)) ∧
        (∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) (v k)) ∧
        (∀ x, Antitone fun k => v k x) ∧ (∀ x, ⨅ k, v k x = u x) ∧
        let reg := smoothClosedCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)
        let A (k : ℕ) := thetaClosedCurrent (θ + ε k • ω.form) (v k) (hv k) + (-ε k) • reg ω.form
        (∀ k, bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (A k) =
          bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T ∧
          IsFullPositive (A k + ε k • reg ω.form).val) ∧
        ∀ (e : ComplexChart (m + 1) M)
          (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
          Tendsto (fun k => (A k).val.inChart e η) atTop (𝓝 (T.val.inChart e η)) := by
  classical
  obtain ⟨θ,u,hu,heq,_⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T.val T.property.1 T.property.2 hT
  obtain ⟨v,ε,han,hsmooth,hanti,hinf,hεnon,hεlim,hv⟩ :=
    Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation ω θ u hu
  refine ⟨θ,u,hu,heq,ε,v,hv,hεnon,hεlim,han,hsmooth,hanti,hinf,?_,?_⟩
  · intro k
    constructor
    · let q := bottChernClassLinearMap (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m)
      have hTc : T = thetaClosedCurrent θ u hu := Subtype.ext heq
      rw [hTc]
      change q (thetaClosedCurrent (θ + ε k • ω.form) (v k) (hv k) +
        (-ε k) • smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω.form) =
        bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (thetaClosedCurrent θ u hu)
      rw [map_add,map_smul]
      change bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (thetaClosedCurrent (θ + ε k • ω.form) (v k) (hv k)) + (-ε k) •
        bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω.form) = _
      rw [bottChernClass_thetaClosedCurrent,bottChernClass_thetaClosedCurrent,
        bottChernClass_smoothClosedCurrent,RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_smul]
      module
    · intro e α hα
      have hp := (thetaPotentialCurrent_closed_type_positive
        (θ + ε k • ω.form).val (v k) (hv k)).2.2 e α hα
      change 0 ≤ ((thetaPotentialCurrent (θ + ε k • ω.form).val (v k) (hv k)).inChart e _) +
        (-ε k) * ((smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω.form).val.inChart e _) +
        ε k * ((smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω.form).val.inChart e _)
      linarith
  · intro e η
    have hδ : Tendsto (fun k => formC0Seminorm ω ((θ + ε k • ω.form) - θ)) atTop (𝓝 0) := by
      have he (k : ℕ) : (θ + ε k • ω.form) - θ = ε k • ω.form := by module
      simp_rw [he,map_smul_eq_mul,Real.norm_eq_abs]
      exact (hεlim.abs.mul_const _).trans (by simp)
    have hs := SmoothC0OriginalCurrentConvergence.tendsto_smoothGlobalCurrent_of_C0
      ω (canonicalBasis (m + 1)) (fun k => θ + ε k • ω.form) θ hδ e η
    have hdd := tendsto_globalDDC_of_antitone u hu.quasiPshPotential v
      (fun k => (hv k).quasiPshPotential) hanti hinf e η
    have hc := ((hεlim.neg).mul_const
      ((smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω.form).val.inChart e η))
    have ht := (hs.add hdd).add hc
    rw [neg_zero,zero_mul,add_zero] at ht
    change Tendsto (fun k => ((thetaPotentialCurrent (θ + ε k • ω.form).val (v k) (hv k)).inChart e η) +
      (-ε k) * ((smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω.form).val.inChart e η))
      atTop (𝓝 (T.val.inChart e η))
    rw [heq]
    exact ht

end SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticWeakRegularization
