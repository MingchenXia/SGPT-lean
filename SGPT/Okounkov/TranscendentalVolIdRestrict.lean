import SGPT.Okounkov.TranscendentalVolIdIntegral
import SGPT.Okounkov.TranscendentalPartialExhaustion
import SGPT.Okounkov.TranscendentalPartialStatement
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

/-!
# Restriction of currents to the first flag divisor

Package VOL (blueprint `claude-tok-volid`, node `tok-volid:restriction`), the restriction steps of
DRWNXZ Lemma 7.5 (`tok:Bn-implies-Cn`): for a flag geometry `F` of dimension `m + 1`,

* `isThetaPshPotential_restrict`, `isKahlerCurrentPotential_restrict`: if `T = θ + dd^c φ ≥ κ`
  and `φ|_{Y₁}` dominates a genuine potential of `Y₁` (`w ⪯ φ|_{Y₁}`), then `φ|_{Y₁}` is a genuine
  `θ|_{Y₁}`-psh potential and `T|_{Y₁} ≥ κ|_{Y₁}` is a Kähler current of `Y₁`;
* `restrict_mem_globalAnalyticCurrents`: the restriction of a gentle current has analytic
  singularities of a global type `(c, 𝓘 𝒪_{Y₁})` (TN `hasAnalyticSingularitiesOfType_comp`);
* `exists_residual_of_fixedFirst` (`tok:valuation-analytic` with `tok:siu-analytic`): for
  `T ∈ Ω(ξ)` with `ν(T, Y₁) = t`, the residual `T - t[Y₁]` is a Kähler current with analytic
  singularities in `ξ - t{Y₁}`, its restriction `w` to `Y₁` is a Kähler current in
  `𝒜(Y₁, (ξ - t{Y₁})|_{Y₁})`, and `ν(T) = (t, ν_{Y₁}(w))`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- The restriction to `Y₁` of a potential. -/
abbrev restrictFirst (F : OriginalFlagGeometry.{u} (m + 1)) (φ : F.carrier → EReal) :
    F.tail.carrier → EReal :=
  fun y => φ (firstFlagInclusion F y)

/-- `(θ - κ)|_{Y₁} = θ|_{Y₁} - κ|_{Y₁}`. -/
theorem firstFlagRestriction_sub_kahler (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (κ : KahlerBackground (m + 1) F.carrier) :
    firstFlagRestriction F (θ - κ.form) =
      firstFlagRestriction F θ - (restrictedKahlerForm κ).form := by
  rw [restrictedKahlerForm_form]
  exact SGPT.Okounkov.TranscendentalBody.pullback_sub' _ θ κ.form

/-- A potential dominating a genuine potential is genuine. -/
theorem locallyNondegenerate_of_singularityLE {X : Type*} [TopologicalSpace X] {w v : X → EReal}
    (hw : LocallyNondegenerate w) (hwv : SingularityLE w v) : LocallyNondegenerate v := by
  obtain ⟨C, hC⟩ := hwv
  intro x U hU hxU
  obtain ⟨y, hyU, hy⟩ := hw x U hU hxU
  refine ⟨y, hyU, fun hbot => hy ?_⟩
  have h := hC y (mem_univ _)
  rw [hbot, EReal.bot_add] at h
  exact le_bot_iff.mp h

/-- **Restriction of psh potentials**: if `φ` is `θ`-psh and `φ|_{Y₁}` dominates a genuine
potential of `Y₁`, then `φ|_{Y₁}` is a genuine `θ|_{Y₁}`-psh potential. -/
theorem isThetaPshPotential_restrict {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : ThetaPlurisubharmonic θ.val φ) {w : F.tail.carrier → EReal}
    (hw : LocallyNondegenerate w) (hwφ : SingularityLE w (restrictFirst F φ)) :
    IsThetaPshPotential (firstFlagRestriction F θ).val (restrictFirst F φ) :=
  GlobalPotentialPullback.isThetaPshPotential_comp (contMDiff_firstFlagInclusion F) hφ
    (locallyNondegenerate_of_singularityLE hw hwφ)

/-- **Restriction of Kähler currents**: if `θ + dd^c φ ≥ κ` and `φ|_{Y₁}` dominates a genuine
potential, then `θ|_{Y₁} + dd^c φ|_{Y₁} ≥ κ|_{Y₁}` is a Kähler current of `Y₁`. -/
theorem isKahlerCurrentPotential_restrict {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {κ : KahlerBackground (m + 1) F.carrier}
    (hφ : IsThetaPshPotential (θ - κ.form).val φ) {w : F.tail.carrier → EReal}
    (hw : LocallyNondegenerate w) (hwφ : SingularityLE w (restrictFirst F φ)) :
    IsKahlerCurrentPotential (firstFlagRestriction F θ) (restrictFirst F φ) := by
  refine ⟨restrictedKahlerForm κ, ?_⟩
  have h := isThetaPshPotential_restrict hφ.1 hw hwφ
  rwa [firstFlagRestriction_sub_kahler] at h

/-- The restriction of a potential with analytic singularities of a global type `(c, 𝓘)` has
global type `(c, 𝓘 𝒪_{Y₁})`. -/
theorem restrict_hasAnalyticSingularities {φ : F.carrier → EReal}
    (hφ : HasAnalyticSingularities (n := m + 1) φ) :
    HasAnalyticSingularities (n := m) (restrictFirst F φ) := by
  obtain ⟨c, 𝔞, htype⟩ := hφ
  exact ⟨c, GermIdeal.pullback (m := m) (firstFlagInclusion F) 𝔞,
    AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp
      (contMDiff_firstFlagInclusion F) htype⟩

/-- The restriction of a current in `𝒜(ξ)` has analytic singularities. -/
theorem restrict_hasManifoldAnalyticSingularityType {φ : F.carrier → EReal}
    (hφ : HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    HasManifoldAnalyticSingularityType (n := m) (restrictFirst F φ) :=
  AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
    (contMDiff_firstFlagInclusion F) hφ

/-- **The residual of a current with fixed first coordinate** (`tok:valuation-analytic`,
`tok:siu-analytic`): for a unit metric `E` and `T = θ + dd^c φ ∈ Ω(ξ)` with `ν(T, Y₁) = t`, the
residual `v` (`T - t[Y₁] = θ - tΘ_E + dd^c v`) is a Kähler current potential with analytic
singularities, its restriction `w = v|_{Y₁}` is a genuine potential in
`𝒜(Y₁, (θ - tΘ_E)|_{Y₁})` and a Kähler current potential, `v|_{Y₁} = w` and
`ν(T) = (t, ν_{Y₁}(w))`. -/
theorem exists_residual_of_fixedFirst {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {φ : F.carrier → EReal} (hφ : φ ∈ gentleKahlerCurrents θ) {t : ℝ}
    (ht : flagValuation F φ 0 = t) :
    ∃ v : F.carrier → EReal, IsKahlerCurrentPotential (θ - t • E.curvature) v ∧
      v ∈ analyticCurrents (θ - t • E.curvature) ∧
      restrictFirst F v ∈ analyticCurrents (firstFlagRestriction F (θ - t • E.curvature)) ∧
      IsKahlerCurrentPotential (firstFlagRestriction F (θ - t • E.curvature)) (restrictFirst F v) ∧
      flagValuation F φ = Fin.cons t (flagValuation F.tail (restrictFirst F v)) := by
  obtain ⟨κ, hκ⟩ := hφ.2
  have hφA : φ ∈ analyticCurrents θ := gentleCurrents_subset_analyticCurrents θ hφ.1
  have hφK : φ ∈ analyticCurrents (θ - κ.form) := ⟨hκ, hφA.2⟩
  obtain ⟨D₀, hDI, hEW, hmetric⟩ := hE
  obtain ⟨-, h0, hwK, htail⟩ := flagValuation_of_analytic F hφK D₀ hDI E hEW hmetric
  obtain ⟨-, hvtype⟩ := residual_rational_and_hasManifoldAnalyticSingularityType hφA.1 hφA.2
    F.firstDivisor D₀ hDI E hEW hmetric
  set c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toNNReal with hc
  have hct : (c : ℝ) = t := by rw [← h0, ht]
  set v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ) with hvdef
  have hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val v :=
    SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hφA.1
      F.firstDivisor D₀ hDI E hEW hmetric
  have hvK : IsThetaPshPotential ((θ - κ.form) - (c : ℝ) • E.curvature).val v :=
    SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hκ
      F.firstDivisor D₀ hDI E hEW hmetric
  rw [hct] at hv hvK hwK
  have hform : (θ - κ.form) - t • E.curvature = (θ - t • E.curvature) - κ.form := by abel
  rw [hform] at hvK hwK
  have hw : restrictFirst F v ∈ analyticCurrents (firstFlagRestriction F (θ - t • E.curvature)) := by
    refine ⟨SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hwK.1 ?_, hwK.2⟩
    rw [firstFlagRestriction_sub_kahler, sub_sub_cancel]
    exact (restrictedKahlerForm κ).isSemipositive
  refine ⟨v, ⟨κ, hvK⟩, ⟨hv, hvtype⟩, hw, ?_, ?_⟩
  · refine ⟨restrictedKahlerForm κ, ?_⟩
    rw [← firstFlagRestriction_sub_kahler]
    exact hwK.1
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero, ht]
    · rw [Fin.cons_succ]
      exact congrFun htail j

end SGPT.Okounkov.TranscendentalVolId
