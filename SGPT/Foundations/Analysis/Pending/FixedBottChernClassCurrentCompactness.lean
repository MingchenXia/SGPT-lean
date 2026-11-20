import SGPT.Foundations.Analysis.Pending.ComponentwiseThetaPshUniformL1
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCoordinateDistributions
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

set_option autoImplicit false

/-! # Original-current compactness in the SAME Bott--Chern class

Complete SOURCE mathematical statement and ENTIRE proof precede this source.
ONE actual smooth theta and componentwise-normalized potential family are
produced internally from the original common-class equality; no supplied
limit, chart compatibility, bound, calibration or class-transport certificate.
Moving classes and degenerate Calabi--Yau remain separate obligations. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal ContDiff
namespace SGPT.Foundations.Analysis.Pending.FixedBottChernClassCurrentCompactness
open FirstPass CurrentBottChernClass CanonicalCurrentFrame
  ComponentwiseNormalizedCurrentPotentials ComponentwiseThetaPshUniformL1
  GlobalCurrentPotentials ThetaPshChartLimitGluing ThetaPotentialCurrentBottChernClass
  GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  LelongPoincareDivisor StronglyPositiveForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem corrected_regular_levi
    (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartTarget e)
    (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ.val e W ρ)
    (hρ : LocallyIntegrableOn ρ W (canonicalBasis (m + 1)).addHaar) :
    HasNonnegativeDistributionalLevi
      (restrictDistribution
        (regularDistribution (canonicalBasis (m + 1)).addHaar
          (fun z => (chartFunction u e z).toReal)
          (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
            (Nat.succ_pos m) u hu.quasiPshPotential e)) hW +
        regularDistribution (canonicalBasis (m + 1)).addHaar ρ hρ) := by
  let b := canonicalBasis (m + 1)
  let hL := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e
  have hUL : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal) W b.addHaar :=
    hL.mono_set hW
  have hfin : ∀ᵐ z ∂b.addHaar.restrict W,
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hW
      (quasiPsh_chart_ae_finite b (Nat.succ_pos m) u hu.quasiPshPotential e)
  have hreal : (fun z => (chartFunction u e z).toReal + ρ z) =ᵐ[b.addHaar.restrict W]
      (fun z => (chartFunction u e z + (ρ z : EReal)).toReal) :=
    hfin.mono fun _ hz => (ereal_toReal_add_coe hz _).symm
  have hgL : LocallyIntegrableOn
      (fun z => (chartFunction u e z + (ρ z : EReal)).toReal) W b.addHaar :=
    (hUL.add hρ).congr hreal
  have hgf : ∀ᵐ z ∂b.addHaar.restrict W,
      chartFunction u e z + (ρ z : EReal) ≠ ⊤ ∧
      chartFunction u e z + (ρ z : EReal) ≠ ⊥ :=
    hfin.mono fun _ hz => ereal_add_coe_finite hz _
  have heq : regularDistribution b.addHaar
      (fun z => (chartFunction u e z + (ρ z : EReal)).toReal) hgL =
      restrictDistribution (regularDistribution b.addHaar
        (fun z => (chartFunction u e z).toReal) hL) hW +
      regularDistribution b.addHaar ρ hρ := by
    rw [restrictDistribution_regularDistribution]
    exact (regularDistribution_congr_ae_on (hUL.add hρ) hgL hreal).symm.trans
      (regularDistribution_add hUL hρ)
  rw [← heq]
  exact (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
    hu.1 e hpot).hasNonnegativeDistributionalLevi_of_locallyIntegrable hgL hgf

private theorem integral_abs_le_deficit
    (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hle : ∀ x, u x ≤ 0)
    (e : ComplexChart (m + 1) M) (K : Set (ComplexModel (m + 1)))
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∫⁻ z in K, (-u (e.val.symm z)).toENNReal
      ∂(canonicalBasis (m + 1)).addHaar ≤ B) :
    ∫ z in K, |(u (e.val.symm z)).toReal| ∂(canonicalBasis (m + 1)).addHaar ≤ B.toReal := by
  let b := canonicalBasis (m + 1)
  have hL := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e
  have hfin : ∀ᵐ z ∂b.addHaar.restrict K,
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe
      (quasiPsh_chart_ae_finite b (Nat.succ_pos m) u hu.quasiPshPotential e)
  have hid : (fun z => ENNReal.ofReal |(u (e.val.symm z)).toReal|)
      =ᵐ[b.addHaar.restrict K] fun z => (-u (e.val.symm z)).toENNReal := by
    filter_upwards [hfin] with z hz
    change ENNReal.ofReal |(chartFunction u e z).toReal| = (-chartFunction u e z).toENNReal
    rw [← EReal.coe_toReal hz.1 hz.2,← EReal.coe_neg,EReal.real_coe_toENNReal]
    rw [EReal.toReal_coe,abs_of_nonpos (EReal.toReal_nonpos (show chartFunction u e z ≤ 0 from hle _))]
  have hli : (∫⁻ z in K, ENNReal.ofReal |(u (e.val.symm z)).toReal| ∂b.addHaar) ≤ B :=
    (lintegral_congr_ae hid).trans_le hbound
  change (∫ z in K, |(chartFunction u e z).toReal| ∂b.addHaar) ≤ B.toReal
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => abs_nonneg _)
    (hL.integrableOn_compact_subset hKe hK).abs.aestronglyMeasurable]
  exact ENNReal.toReal_mono hB.ne hli

private theorem tendsto_toLocalCurrent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Opens E} {ι : Type*}
    (U : Ultrafilter ι) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (A : ι → DistributionForm Ω k.val)
    (B : DistributionForm Ω k.val)
    (hlim : ∀ v φ, Tendsto (fun i => A i v φ) (U : Filter ι) (𝓝 (B v φ)))
    (η : TestForm Ω (Module.finrank ℝ E - k.val)) :
    Tendsto (fun i => toLocalCurrent b k (A i) η) (U : Filter ι)
      (𝓝 (toLocalCurrent b k B η)) := by
  simp only [toLocalCurrent,wedgePairing_apply]
  exact tendsto_finsetSum _ fun s _ => (hlim _ _).const_smul (Equiv.Perm.sign s.out)

private theorem theta_coefficients
    (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart (m + 1) M) :
    (thetaPotentialCurrent θ.val u hu).coefficients (canonicalBasis (m + 1)) e =
      (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
        (k := degreeTwo (Nat.succ_pos m)) θ.val).coefficients (canonicalBasis (m + 1)) e +
        ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
          (fun z => (chartFunction u e z).toReal)
          (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
            (Nat.succ_pos m) u hu.quasiPshPotential e)) := by
  rw [thetaPotentialCurrent,GlobalCurrent.coefficients_add,globalDDC_coefficients]
  rfl

private theorem current_limit_of_scalar_limits {ι : Type*} (U : Ultrafilter ι)
    (θ : ClosedRealOneOneForm (m + 1) M) (u : ι → M → EReal)
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (V : M → EReal)
    (hV : IsThetaPshPotential θ.val V)
    (hlim : ∀ (e : ComplexChart (m + 1) M) (φ : 𝓓(chartTarget e, ℝ)),
      Tendsto (fun i => regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction (u i) e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
          (Nat.succ_pos m) (u i) (hu i).quasiPshPotential e) φ) (U : Filter ι)
        (𝓝 (regularDistribution (canonicalBasis (m + 1)).addHaar
          (fun z => (chartFunction V e z).toReal)
          (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1))
            (Nat.succ_pos m) V hV.quasiPshPotential e) φ)))
    (e : ComplexChart (m + 1) M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    Tendsto (fun i => (thetaPotentialCurrent θ.val (u i) (hu i)).inChart e η)
      (U : Filter ι) (𝓝 ((thetaPotentialCurrent θ.val V hV).inChart e η)) := by
  let b := canonicalBasis (m + 1)
  let A i := regularDistribution b.addHaar (fun z => (chartFunction (u i) e z).toReal)
    (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) (u i) (hu i).quasiPshPotential e)
  let B := regularDistribution b.addHaar (fun z => (chartFunction V e z).toReal)
    (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) V hV.quasiPshPotential e)
  have hddC (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(chartTarget e, ℝ)) :
      Tendsto (fun i => ddC (A i) w φ) (U : Filter ι) (𝓝 (ddC B w φ)) := by
    have eval (R : 𝓓'(chartTarget e, ℝ)) : ddC R w φ =
        R (DDCOverlap.ddcAdjointCoeff (w 0) (w 1) φ) := by
      have hw : w = ![w 0,w 1] := by ext j; fin_cases j <;> rfl
      exact (congrArg (fun t => ddC R t φ) hw).trans (DDCOverlap.ddC_apply_eq R _ _ φ)
    simp_rw [eval]
    exact hlim e _
  have hcoeff (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(chartTarget e, ℝ)) :
      Tendsto (fun i => (thetaPotentialCurrent θ.val (u i) (hu i)).coefficients b e w φ)
        (U : Filter ι) (𝓝 ((thetaPotentialCurrent θ.val V hV).coefficients b e w φ)) := by
    let C := (GlobalCurrents.smoothGlobalCurrent b
      (k := degreeTwo (Nat.succ_pos m)) θ.val).coefficients b e
    have hleft : (fun i => (thetaPotentialCurrent θ.val (u i) (hu i)).coefficients b e w φ) =
        fun i => C w φ + ddC (A i) w φ := by
      funext i
      exact congrArg (fun D => D w φ) (theta_coefficients θ (u i) (hu i) e)
    have hright : (thetaPotentialCurrent θ.val V hV).coefficients b e w φ =
        C w φ + ddC B w φ :=
      congrArg (fun D => D w φ) (theta_coefficients θ V hV e)
    rw [hleft,hright]
    exact (hddC w φ).const_add _
  have hfull := tendsto_toLocalCurrent U b (degreeTwo (Nat.succ_pos m))
    (fun i => (thetaPotentialCurrent θ.val (u i) (hu i)).coefficients b e)
    ((thetaPotentialCurrent θ.val V hV).coefficients b e) hcoeff η
  simpa only [GlobalCurrent.coefficients,CurrentPairing.toLocalCurrent_fromLocalCurrent]
    using hfull

variable [CompactSpace M]

/-- From the ORIGINAL full positive family in ONE actual class, internally
produce a SAME-class original weak limit on ALL genuine chart/fullform tests.
No potential, bound, limit or class-calibration certificate is supplied. -/
theorem exists_tendsto_same_class_originalClosedPositiveCurrent {ι : Type*}
    (U : Ultrafilter ι) (β : RealBottChern (m + 1) M)
    (T : ι → ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : ∀ i, IsFullPositive (T i).val)
    (hclass : ∀ i, bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (T i) = β) :
    ∃ S : ClosedOneOneCurrent (M := M) (canonicalBasis (m + 1)) (Nat.succ_pos m),
      IsFullPositive S.val ∧
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S = β ∧
      ∀ (e : ComplexChart (m + 1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        Tendsto (fun i => (T i).val.inChart e η) (U : Filter ι) (𝓝 (S.val.inChart e η)) := by
  classical
  obtain ⟨θ,hθ,hu⟩ := exists_normalized_representations_of_common_class β T hT hclass
  choose u hu heq hle hzero using hu
  let b := canonicalBasis (m + 1)
  let v : ι → M → ℝ := fun i x => (u i x).toReal
  have hL (i : ι) (e : ComplexChart (m + 1) M) :
      LocallyIntegrableOn (fun z => v i (e.val.symm z)) (chartTarget e) b.addHaar :=
    quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) (u i) (hu i).quasiPshPotential e
  have hbound (e : ComplexChart (m + 1) M) (K : Set (ComplexModel (m + 1)))
      (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
      ∃ B : ℝ, ∀ i, ∫ z in K, |v i (e.val.symm z)| ∂b.addHaar ≤ B := by
    obtain ⟨B,hB,hBu⟩ := exists_lintegral_compact_le_componentwise
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) e hK hKe 0
    refine ⟨B.toReal,fun i => integral_abs_le_deficit θ (u i) (hu i) (hle i) e K hK hKe B hB ?_⟩
    rw [addHaar_canonicalBasis]
    apply hBu (u i) (hu i).1 (hle i)
    intro x
    obtain ⟨y,hy,hyzero⟩ := hzero i x
    exact ⟨y,hy,by simp [hyzero]⟩
  obtain ⟨R,hR⟩ := exists_isChartLimit U v hL hbound
  have hLevi (e : ComplexChart (m + 1) M) :
      IsLocallyThetaPshDistribution b.addHaar θ.val e (R e) := by
    intro z hz
    obtain ⟨W,ρ,hzW,hpot⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
    let Ω : Opens (ComplexModel (m + 1)) := ⟨W,hpot.1⟩
    have hW : Ω ≤ chartTarget e := hpot.2.1
    have hρ : LocallyIntegrableOn ρ Ω b.addHaar :=
      hpot.2.2.1.continuousOn.locallyIntegrableOn hpot.1.measurableSet
    have hc : ∀ i, HasNonnegativeDistributionalLevi
        (restrictDistribution (regularDistribution b.addHaar
          (fun z => v i (e.val.symm z)) (hL i e)) hW +
          regularDistribution b.addHaar ρ hρ) :=
      fun i => corrected_regular_levi θ (u i) (hu i) e hW ρ hpot hρ
    refine ⟨Ω,hW,ρ,hρ,hzW,hpot,?_⟩
    apply PshUltrafilterLimit.HasNonnegativeDistributionalLevi.of_tendsto (l := (U : Filter ι))
      (hS := Eventually.of_forall hc)
    intro φ
    have ht := (hR e (TestFunction.monoCLM ℝ φ)).add
      (tendsto_const_nhds (x := regularDistribution b.addHaar ρ hρ φ))
    simpa only [add_apply,restrictDistribution_apply,regularDistribution_apply] using ht
  obtain ⟨V,hV,hreg⟩ := exists_isThetaPshPotential_of_isChartLimit v R hR hLevi
  let S := thetaClosedCurrent θ V hV
  have hRS (e : ComplexChart (m + 1) M) : R e =
      regularDistribution b.addHaar (fun z => (chartFunction V e z).toReal)
        (quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) V hV.quasiPshPotential e) := by
    obtain ⟨_,hL',heq'⟩ := hreg e
    exact heq'
  refine ⟨S,(thetaPotentialCurrent_closed_type_positive θ.val V hV).2.2,
    (bottChernClass_thetaClosedCurrent θ V hV).trans hθ,?_⟩
  intro e η
  have hs := current_limit_of_scalar_limits U θ u hu V hV (fun e φ => by
    rw [← hRS e]
    simpa only [regularDistribution_apply,v,chartFunction,b] using hR e φ) e η
  change Tendsto (fun i => (T i).val.inChart e η) (U : Filter ι)
    (𝓝 ((thetaPotentialCurrent θ.val V hV).inChart e η))
  simpa only [heq] using hs

end SGPT.Foundations.Analysis.Pending.FixedBottChernClassCurrentCompactness
