import SGPT.Foundations.Analysis.Pending.ActualMinimalRestrictedMassFormula
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
import SGPT.Foundations.Analysis.Pending.FlatComplexTorusNakamaye
import SGPT.Foundations.Analysis.Pending.CurveCollarPsh
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Okounkov.TranscendentalLiftingApprox

/-!
# Restricted volumes of nef classes on smooth submanifolds

Toward the Kleiman half of `rmk:bdiv:L749`.  Let `X` be a compact complex manifold with a Kähler
form `ω`, `θ` a nef closed real `(1,1)`-form and `V ⊆ X` a closed connected complex submanifold
of dimension `k` (an irreducible analytic subvariety).  Then the numerical restricted volume of
the transcendental Nakamaye theorem (Collins–Tosatti; `SGPT.Foundations.Analysis`) is the
intersection number of the restricted class:
`⟨{θ}^k⟩_{X|V} = ∫_V (θ|_V)^k` (`numericalRestrictedVolume_eq_ofReal_of_nef`).

Proof: the restricted volume is the right limit of the non-pluripolar masses on `V` of the
restrictions of the model potentials `V_{θ+εω}`
(`ActualMinimalRestrictedMassFormula.exists_minimal_restriction_mass_inf_and_tendsto`); for nef
`θ` the class `{θ + εω}` contains a Kähler form, so `V_{θ+εω}` is bounded and its mass is the
cohomological number `∫_V (θ|_V + εω|_V)^k`
(`DominationIntersectionNumbers.diagonalMass_toReal_eq_slotIntegral_of_isBoundedPotential`),
which tends to `∫_V (θ|_V)^k`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.BDivisor.Kleiman

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.NefMixedMass SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldMassCalculus
open SGPT.Foundations.Analysis.Pending.RestrictedVolumeModelMass
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open ManifoldTubePositivity

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Nef plus Kähler is Kähler**: if `θ` is nef, the class of `θ + εω` (`ε > 0`) contains the
Kähler form `θ + εω + ddᶜf` for some smooth `f`. -/
theorem exists_isKahler_add_ddc_of_nef (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} (hθ : NefWithRespectTo omega θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : X → ℝ) (hf : ChartSmooth (n := n) f),
      ((θ + ε • omega.form) + ddcClosedForm f hf).val.IsKahler := by
  obtain ⟨f, hf, hsemi⟩ := exists_isSemipositive_of_nef hθ (half_pos hε)
  refine ⟨f, hf, ?_⟩
  have h := NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive omega hsemi (half_pos hε)
  have heq : θ + (ε / 2) • omega.form + ddcClosedForm f hf + (ε / 2) • omega.form =
      (θ + ε • omega.form) + ddcClosedForm f hf := by
    have : ε • omega.form = (ε / 2) • omega.form + (ε / 2) • omega.form := by
      rw [← add_smul, add_halves]
    rw [this]
    abel
  rwa [heq] at h

/-- The class `{θ} + ε{ω}` of a nef form is a Kähler class. -/
theorem exists_kahler_ofRepresentative_eq_of_nef (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} (hθ : NefWithRespectTo omega θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : KahlerBackground n X, RealBottChern.ofRepresentative κ.form =
      RealBottChern.ofRepresentative θ + ε • RealBottChern.ofRepresentative omega.form := by
  obtain ⟨f, hf, hK⟩ := exists_isKahler_add_ddc_of_nef omega hθ hε
  refine ⟨⟨_, hK⟩, ?_⟩
  change RealBottChern.ofRepresentative ((θ + ε • omega.form) + ddcClosedForm f hf) = _
  rw [SGPT.Okounkov.TranscendentalLifting.ofRepresentative_add_ddc,
    RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]

/-- **The non-nef locus of a nef class is empty.** -/
theorem nonNefLocus_eq_empty_of_nef (hn : 0 < n) (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} (hθ : NefWithRespectTo omega θ) :
    nonNefLocus omega (RealBottChern.ofRepresentative θ) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨ε, hxε⟩ := Set.mem_iUnion.mp hx
  obtain ⟨κ, hκ⟩ := exists_kahler_ofRepresentative_eq_of_nef omega hθ ε.2
  rw [← hκ, FlatComplexTorusNakamaye.nonKahlerLocus_kahler_eq_empty hn κ] at hxε
  exact hxε

variable [CompactSpace X]

/-- **The model potential of `{θ + εω}` is bounded for nef `θ`**: `-C ≤ V_{θ+εω} ≤ 0`. -/
theorem exists_lower_bound_thetaPshSupremum_of_nef (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X} (hθ : NefWithRespectTo omega θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x, (C : EReal) ≤ thetaPshSupremum (θ + ε • omega.form).val x := by
  obtain ⟨f, hf, hsemi⟩ := exists_isSemipositive_of_nef hθ hε
  have hpos : ((θ + ε • omega.form) + (1 : ℝ) • ddcClosedForm f hf).val.IsSemipositive := by
    rwa [one_smul]
  have hu := CurveCollarPsh.isThetaPshPotential_scaled_smooth_of_semipositive
    (θ + ε • omega.form) f hf 1 hpos
  have hcont : Continuous f := ProductTestForms.ChartSmooth.continuous hf
  obtain ⟨B, hB⟩ := (isCompact_univ.image hcont).bddAbove
  obtain ⟨A, hA⟩ := (isCompact_univ.image hcont).bddBelow
  have hfB : ∀ x, f x ≤ B := fun x => hB ⟨x, mem_univ x, rfl⟩
  have hfA : ∀ x, A ≤ f x := fun x => hA ⟨x, mem_univ x, rfl⟩
  have hu' := hu.sub_const B
  have hle : (fun x => ((1 * f x : ℝ) : EReal) - (B : EReal)) ≤ 0 := by
    intro x
    show ((1 * f x : ℝ) : EReal) - (B : EReal) ≤ 0
    rw [← EReal.coe_sub, EReal.coe_nonpos]
    linarith [hfB x]
  refine ⟨A - B, fun x => ?_⟩
  refine le_trans ?_ (le_thetaPshSupremum hu' hle x)
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith [hfA x]

/-- **Restricted volume of a nef class on a smooth submanifold**:
`⟨{θ}^k⟩_{X|V} = ∫_V (θ|_V)^k` for `θ` nef and `V` a closed connected submanifold. -/
theorem numericalRestrictedVolume_eq_ofReal_of_nef (hn : 0 < n) (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hθ : NefWithRespectTo omega θ)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
    numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) V =
      ENNReal.ofReal (slotIntegral (SubmanifoldKahlerRestriction.kahlerBackground
        (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega)
        (fun _ => ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ)) := by
  let hk := le_of_isClosedConnectedSubmanifold hV
  let hW := hV.2.2
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  let γ := ClosedRealOneOneForm.pullback (contMDiff_val hk hW) θ
  let omegaV := SubmanifoldKahlerRestriction.kahlerBackground hk hW omega
  have hnn : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ) := by
    rw [nonNefLocus_eq_empty_of_nef hn omega hθ, subset_empty_iff]
    exact hV.2.1.nonempty.ne_empty
  obtain ⟨H, hfin, -, htend⟩ :=
    ActualMinimalRestrictedMassFormula.exists_minimal_restriction_mass_inf_and_tendsto
      omega θ V hV hnn
  have hmass : ∀ ε : PositiveError, diagonalPotentialMass (γ + (ε : ℝ) • omegaV.form)
      (restrictedModel θ omega.form ε (W := V.carrier)) (H ε) =
      ENNReal.ofReal (slotIntegral omegaV (fun _ => γ + (ε : ℝ) • omegaV.form)) := by
    intro ε
    rw [← ENNReal.ofReal_toReal (hfin ε)]
    congr 1
    obtain ⟨C, hC⟩ := exists_lower_bound_thetaPshSupremum_of_nef omega hθ ε.2
    have hbdd : IsBoundedPotential (restrictedModel θ omega.form ε (W := V.carrier)) :=
      ⟨C, 0, fun y => ⟨hC y.1, thetaPshSupremum_le_zero _ y.1⟩⟩
    exact DominationIntersectionNumbers.diagonalMass_toReal_eq_slotIntegral_of_isBoundedPotential
      omegaV (H ε).1 hbdd
  let εj : ℕ → PositiveError := fun j => ⟨1 / ((j : ℝ) + 1), by positivity⟩
  have hεj : Tendsto (fun j => ((εj j : PositiveError) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := (htend atTop εj hεj).congr (fun j => hmass (εj j))
  have h2 : Tendsto (fun j => ENNReal.ofReal
      (slotIntegral omegaV (fun _ => γ + ((εj j : PositiveError) : ℝ) • omegaV.form))) atTop
      (𝓝 (ENNReal.ofReal (slotIntegral omegaV (fun _ => γ)))) := by
    have hc := ((continuous_slotIntegral_add_smul omegaV (fun _ => γ)
      (fun _ => omegaV.form)).tendsto 0).comp hεj
    have h0 : slotIntegral omegaV (fun _ => γ + (0 : ℝ) • omegaV.form) =
        slotIntegral omegaV (fun _ => γ) := by
      simp only [zero_smul, add_zero]
    rw [h0] at hc
    exact (ENNReal.continuous_ofReal.tendsto _).comp hc
  exact tendsto_nhds_unique h1 h2

end SGPT.BDivisor.Kleiman
