import SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryRestrictionMassContinuity
import SGPT.Foundations.Analysis.Pending.MinimalPotentialPositiveTraceDomain
import SGPT.Foundations.Analysis.Pending.ActualTraceFreeNormalizedReader

set_option autoImplicit false

/-! # Actual ordinary minimal restriction equals its normalized trace mass -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryNormalizedTraceMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DiagonalMass PositiveNormalizedTrace
  NumericalTraceMass MinimalPotentialRestrictionPositiveSeed
  MinimalPotentialOrdinaryRestrictionMassContinuity MinimalPotentialPositiveTraceDomain
  PositiveOrdinaryRestrictionVaryingModelChain IEnvelopeVaryingBackgroundModelInfimum

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Natural original generic zero internally supplies the normalized domain,
the changing model chain and both actual mass limits; no limit is an input. -/
theorem exists_ordinary_restriction_mass_eq_numericalTraceMass_minimal_add_smul
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {e : ℝ} (he : 0 < e) :
    ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)),
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) hw =
        numericalTraceMass omega omegaV hι (θ + e • omega.form)
          (thetaPshSupremum (θ + e • omega.form).val) := by
  classical
  let : Nonempty M := Nonempty.map ι inferInstance
  let σ := θ + e • omega.form
  let U := thetaPshSupremum σ.val
  let η := ClosedRealOneOneForm.pullback hι σ
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  obtain ⟨hw, hMoving, hMovinglim⟩ :=
    exists_tendsto_ordinary_restriction_minimal_positive_base_mass
      omega hι hpull θ hbig hgeneric he
  obtain ⟨_, hwpos⟩ := exists_positive_ordinary_restriction_minimal_add_smul
    omega hι hpull θ hbig hgeneric he
  let hd := hasPositiveTraceRepresentativeAlong_minimal_add_smul
    omega omegaV hι hpull θ hbig hgeneric he
  let A := normalizedTraceAlong omega omegaV hι σ U hd
  have hA : IsModelPotential η A := (normalizedTraceAlong_models omega omegaV hι σ U hd).1
  have hg : (⨅ y : V, lelongNumber (n := n) U (ι y)) = 0 :=
    (Classical.choose_spec hd).1.1
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hU : IsThetaPshPotential σ.val U :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _
      (PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV he)
  obtain ⟨a, S, happ⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega σ hU
  obtain ⟨b, hbpos, hbanti, hblim, happb, hP, hPanti, _hPI, _hposInf⟩ :=
    exists_positive_varying_iModel_chain_of_ordinary_restriction
      omega hι hpull happ (thetaPshSupremum_le_zero _) hg hw hwpos
  let β : ℕ → ClosedRealOneOneForm k V := fun j => η + b j • ρ.form
  let R : ℕ → V → EReal := fun j y => S j (ι y)
  let P : ℕ → V → EReal := fun j => singularityEnvelope (β j).val (R j)
  have hR (j : ℕ) : IsThetaPshPotential (β j).val (R j) := by
    simpa only [NefCoreKahlerCurrent.pullback_add_smul] using
      AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
        happb hι hg j
  have hform (j : ℕ) : β j =
      ClosedRealOneOneForm.pullback hι (θ + (e + b j) • omega.form) := by
    dsimp only [β, η, σ, ρ]
    rw [NefCoreKahlerCurrent.pullback_add_smul, NefCoreKahlerCurrent.pullback_add_smul]
    module
  have hW (j : ℕ) : IsThetaPshPotential (β j).val
      (fun y => thetaPshSupremum (θ + (e + b j) • omega.form).val (ι y)) := by
    rw [hform j]
    exact hMoving (b j) (hbpos j)
  have hInf := isThetaPshPotential_iInf_varying_models ρ η hbanti hblim hP hPanti
  have heqInf : (⨅ j, P j) = A := by
    have hh := ActualTraceFreeNormalizedReader.traceFreeLimit_eq_normalizedTraceAlong
      omega omegaV hι hpull σ hd happb hbpos
    have hreader : TraceFreeLimit.traceFreeLimit η ρ.form b R = (⨅ j, P j) := by
      funext y
      simp only [TraceFreeLimit.traceFreeLimit, P, β, R, iInf_apply]
    exact hreader.symm.trans hh
  have hcongr (v w : V → EReal) (hv : IsThetaPshPotential η.val v)
      (hw' : IsThetaPshPotential η.val w) (hvw : v = w) :
      diagonalPotentialMass η v hv = diagonalPotentialMass η w hw' := by
    subst w
    rfl
  have hModelLim : Tendsto (fun j => diagonalPotentialMass (β j) (P j)
      (hP j).plurisubharmonic) atTop (𝓝 (diagonalPotentialMass η A hA.plurisubharmonic)) := by
    have hh := tendsto_diagonalPotentialMass_iInf_varying_models
      ρ η hbpos hbanti hblim hP hPanti
    rw [hcongr _ _ hInf hA.plurisubharmonic heqInf] at hh
    exact hh
  have hpres (j : ℕ) : diagonalPotentialMass (β j) (P j) (hP j).plurisubharmonic =
      diagonalPotentialMass (β j) (R j) (hR j) :=
    singularityEnvelopeMassPreserving ρ (β j) (R j) (hR j) (hP j).plurisubharmonic
  have hlow (j : ℕ) : diagonalPotentialMass η (fun y => U (ι y)) hw ≤
      diagonalPotentialMass (β j) (P j) (hP j).plurisubharmonic := by
    rw [hpres j]
    apply DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul ρ (hbpos j) hw (hR j)
    intro y
    apply le_of_tendsto (happ.term_tendsto (ι y))
    filter_upwards [eventually_ge_atTop j] with l hl
    exact happ.term_antitone (ι y) hl
  have hupp (j : ℕ) : diagonalPotentialMass (β j) (P j) (hP j).plurisubharmonic ≤
      diagonalPotentialMass (β j)
        (fun y => thetaPshSupremum (θ + (e + b j) • omega.form).val (ι y)) (hW j) := by
    rw [hpres j]
    obtain ⟨C, hC⟩ := (happb.term j).exists_global_upper_bound
    have hmin := le_thetaPshSupremum ((happb.term j).sub_const C)
      (sub_const_nonpositive_of_le hC)
    have hσj : σ + b j • omega.form = θ + (e + b j) • omega.form := by dsimp only [σ]; module
    rw [hσj] at hmin
    apply diagonalPotentialMass_mono_of_kahler ρ (hR j) (hW j)
    refine ⟨C, fun y _ => ?_⟩
    calc R j y = (R j y - (C : EReal)) + (C : EReal) := EReal.sub_add_cancel.symm
      _ ≤ thetaPshSupremum (θ + (e + b j) • omega.form).val (ι y) + (C : EReal) :=
        add_le_add (hmin (ι y)) le_rfl
  have hOrdLim : Tendsto (fun j => diagonalPotentialMass (β j)
      (fun y => thetaPshSupremum (θ + (e + b j) • omega.form).val (ι y)) (hW j))
      atTop (𝓝 (diagonalPotentialMass η (fun y => U (ι y)) hw)) := by
    have hh := (hMovinglim ℕ atTop b hbpos hblim).2
    simpa only [hform] using hh
  have hLimit : Tendsto (fun j => diagonalPotentialMass (β j) (P j)
      (hP j).plurisubharmonic) atTop (𝓝 (diagonalPotentialMass η (fun y => U (ι y)) hw)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hOrdLim hlow hupp
  have heq := tendsto_nhds_unique hLimit hModelLim
  refine ⟨hw, ?_⟩
  simpa only [numericalTraceMass, dif_pos hd] using heq

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryNormalizedTraceMass
