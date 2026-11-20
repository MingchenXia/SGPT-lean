import SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialPerturbation

set_option autoImplicit false

/-! # Actual fixed-potential right-neighborhood numerical mass limit -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialRightLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass PositiveNormalizedTrace NumericalTraceMass NormalizedTraceBackgroundMonotonicity
  NormalizedTraceFixedPotentialPerturbation

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]


/-- Natural fixed-potential current margins internally produce both numerical
domains and their true monotonicity under positive Kahler perturbation. -/
theorem numericalTraceMass_add_smul_le
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    numericalTraceMass omega omegaV hι (θ + a • omega.form) u ≤
      numericalTraceMass omega omegaV hι (θ + b • omega.form) u := by
  classical
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    exact le_refl _
  have hb : 0 < b := ha.trans hlt
  let κ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  have hdefined (r : ℝ) (hr : 0 < r) : HasPositiveTraceRepresentativeAlong
      omega omegaV hι (θ + r • omega.form) u := by
    apply PositiveNormalizedTraceCurrentDomain.hasPositiveTraceRepresentativeAlong_of_current_margin
      omega omegaV hι hpull hr
    · simpa only [add_sub_cancel_right] using hu
    · exact hgeneric
  let hdA := hdefined a ha
  let hdB := hdefined b hb
  let A := normalizedTraceAlong omega omegaV hι (θ + a • omega.form) u hdA
  let B := normalizedTraceAlong omega omegaV hι (θ + b • omega.form) u hdB
  let α := ClosedRealOneOneForm.pullback hι (θ + a • omega.form)
  let β := ClosedRealOneOneForm.pullback hι (θ + b • omega.form)
  have hA : IsThetaPshPotential α.val A := (normalizedTraceAlong_models omega omegaV hι
    (θ + a • omega.form) u hdA).1.plurisubharmonic
  have hB : IsThetaPshPotential β.val B := (normalizedTraceAlong_models omega omegaV hι
    (θ + b • omega.form) u hdB).1.plurisubharmonic
  have hdiff : θ + b • omega.form - (θ + a • omega.form) = (b - a) • omega.form := by module
  have hsemi : (θ + b • omega.form - (θ + a • omega.form)).val.IsSemipositive := by
    rw [hdiff]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_pos.mpr hlt).le
  have hAB : A ≤ B := normalizedTraceAlong_le_of_semipositive_difference
    omega omega omegaV omegaV hι (θ + a • omega.form) (θ + b • omega.form) u hsemi hdA hdB
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

/-- The actual reciprocal sequence identifies the order-theoretic right limit,
including the original undefined-normalized-trace zero branch. -/
theorem tendsto_numericalTraceMass_add_smul_right
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    Tendsto (fun ε : ℝ => numericalTraceMass omega omegaV hι (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 (numericalTraceMass omega omegaV hι θ u)) := by
  let f : ℝ → ENNReal := fun ε => numericalTraceMass omega omegaV hι (θ + ε • omega.form) u
  have hmono : MonotoneOn f (Ioi 0) := fun a ha _b _hb hab =>
    numericalTraceMass_add_smul_le omega omegaV hι hpull θ hu hgeneric ha hab
  have hright : Tendsto f (𝓝[>] 0) (𝓝 (sInf (f '' Ioi 0))) :=
    hmono.tendsto_nhdsGT (OrderBot.bddBelow _)
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hεanti : Antitone ε := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpath : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hεpos⟩
  have hseq : Tendsto (fun j => f (ε j)) atTop
      (𝓝 (numericalTraceMass omega omegaV hι θ u)) :=
    tendsto_numericalTraceMass_add_smul_of_antitone omega omegaV hι hpull θ hu hgeneric
      hεpos hεanti hεlim
  have heq := tendsto_nhds_unique (hright.comp hpath) hseq
  rwa [heq] at hright

end
end SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialRightLimit
