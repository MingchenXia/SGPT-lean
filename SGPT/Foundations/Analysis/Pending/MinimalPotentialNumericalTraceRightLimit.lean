import SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceSequence

set_option autoImplicit false

/-! # Actual real right-neighborhood numerical trace limit of moving minimal potentials -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceRightLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  DiagonalMass PositiveNormalizedTrace NumericalTraceMass
  MinimalPotentialPositiveTraceDomain MinimalPotentialNumericalTraceSequence

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Actual moving minimal potentials, their produced positive reader domains,
and genuine cross-background NP mass comparison imply numerical monotonicity. -/
theorem numericalTraceMass_minimal_add_smul_le
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    numericalTraceMass omega omegaV hι (θ + a • omega.form)
        (thetaPshSupremum (θ + a • omega.form).val) ≤
      numericalTraceMass omega omegaV hι (θ + b • omega.form)
        (thetaPshSupremum (θ + b • omega.form).val) := by
  classical
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    exact le_refl _
  have hb : 0 < b := ha.trans hlt
  let : Nonempty M := Nonempty.map ι inferInstance
  let κ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hmin (r : ℝ) (hr : 0 < r) :
      IsThetaPshPotential (θ + r • omega.form).val (thetaPshSupremum (θ + r • omega.form).val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _
      (PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV hr)
  let u := thetaPshSupremum (θ + a • omega.form).val
  let w := thetaPshSupremum (θ + b • omega.form).val
  have hlarge : IsThetaPshPotential (θ + b • omega.form).val u := by
    have heq : θ + a • omega.form + (b - a) • omega.form = θ + b • omega.form := by module
    simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hmin a ha) (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_pos.mpr hlt).le)
  have hinput : u ≤ w := le_thetaPshSupremum hlarge (thetaPshSupremum_le_zero _)
  let hdA := hasPositiveTraceRepresentativeAlong_minimal_add_smul omega omegaV hι hpull θ hbig hgeneric ha
  let hdB := hasPositiveTraceRepresentativeAlong_minimal_add_smul omega omegaV hι hpull θ hbig hgeneric hb
  let A := normalizedTraceAlong omega omegaV hι (θ + a • omega.form) u hdA
  let B := normalizedTraceAlong omega omegaV hι (θ + b • omega.form) w hdB
  let α := ClosedRealOneOneForm.pullback hι (θ + a • omega.form)
  let β := ClosedRealOneOneForm.pullback hι (θ + b • omega.form)
  have hA : IsThetaPshPotential α.val A := (normalizedTraceAlong_models omega omegaV hι
    (θ + a • omega.form) u hdA).1.plurisubharmonic
  have hB : IsThetaPshPotential β.val B := (normalizedTraceAlong_models omega omegaV hι
    (θ + b • omega.form) w hdB).1.plurisubharmonic
  have hdiff : θ + b • omega.form - (θ + a • omega.form) = (b - a) • omega.form := by module
  have hsemi : (θ + b • omega.form - (θ + a • omega.form)).val.IsSemipositive := by
    rw [hdiff]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_pos.mpr hlt).le
  have hAB : A ≤ B :=
    NormalizedTraceIdealOrderComparison.normalizedTraceAlong_le_of_iOrder_of_semipositive_difference
      omega omega omegaV omegaV hι (θ + a • omega.form) (θ + b • omega.form)
      (iOrderOnManifold_of_le (hmin b hb).1.quasiPlurisubharmonic hinput) hsemi hdA hdB
  have hform : α + (b - a) • κ.form = β := by
    dsimp only [α, β, κ]
    rw [NefCoreKahlerCurrent.pullback_add_smul, NefCoreKahlerCurrent.pullback_add_smul]
    module
  have hB' : IsThetaPshPotential (α + (b - a) • κ.form).val B := by
    rw [hform]
    exact hB
  have hm := DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
    κ (sub_pos.mpr hlt) hA hB' hAB
  simp only [numericalTraceMass, dif_pos hdA, dif_pos hdB]
  simpa only [hform] using hm

/-- The actual reciprocal sequence identifies the full real right-filter
limit, retaining the original undefined-normalized-trace zero branch. -/
theorem tendsto_numericalTraceMass_minimal_add_smul_right
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0) :
    Tendsto (fun e : ℝ => numericalTraceMass omega omegaV hι (θ + e • omega.form)
        (thetaPshSupremum (θ + e • omega.form).val))
      (𝓝[>] 0) (𝓝 (numericalTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
  let f : ℝ → ENNReal := fun e => numericalTraceMass omega omegaV hι (θ + e • omega.form)
    (thetaPshSupremum (θ + e • omega.form).val)
  have hmono : MonotoneOn f (Ioi 0) := fun a ha _b _hb hab =>
    numericalTraceMass_minimal_add_smul_le omega omegaV hι hpull θ hbig hgeneric ha hab
  have hright : Tendsto f (𝓝[>] 0) (𝓝 (sInf (f '' Ioi 0))) :=
    hmono.tendsto_nhdsGT (OrderBot.bddBelow _)
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hepos (j : ℕ) : 0 < e j := by dsimp only [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepath : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨helim, Eventually.of_forall hepos⟩
  have hseq : Tendsto (fun j => f (e j)) atTop
      (𝓝 (numericalTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
    simpa only [f, e, one_div] using
      tendsto_numericalTraceMass_minimal_reciprocal omega omegaV hι hpull θ hbig hgeneric
  have heq := tendsto_nhds_unique (hright.comp hepath) hseq
  rwa [heq] at hright

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceRightLimit
