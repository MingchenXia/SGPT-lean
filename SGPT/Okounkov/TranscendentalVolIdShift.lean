import SGPT.Okounkov.TranscendentalWNStatement
import SGPT.Okounkov.TranscendentalSliceDensity
import SGPT.Okounkov.TranscendentalSliceValuation
import SGPT.Okounkov.TranscendentalPartialVolume
import SGPT.Okounkov.TranscendentalVolumeConcavity
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Okounkov.TranscendentalBody2Lelong
import SGPT.Okounkov.MultiplierCancellation
import SGPT.Foundations.Analysis.Pending.DominationResidualMass
import SGPT.Foundations.Analysis.Pending.MeteredDivisorScaling

/-!
# The volume along the direction `-{Y₁}`

Package VOL of the formalization of `thm:Okounkovtranmain` (blueprint
`claude-okounkov-transcendental`, node `tok:wn-integrated`, first part, and `tok:vol-integral`;
chapter `claude-tok-volid`, nodes `tok-volid:shift-*`), Darvas--Reboulet--Witt
Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ), proofs of Theorem 2.10 and
Proposition 7.2.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag,
`ξ = {θ}` a big class, `E` a unit metric of `Y₁` (curvature `Θ_E ∈ {Y₁}`), `ξ_s = ξ - s{Y₁}`,
`ν_min = inf_{Ω(ξ)} ν(·, Y₁)`, `ν_max = sup_{Ω(ξ)} ν(·, Y₁)` (`firstValuationMin`,
`firstValuationMax`). With `f(s) = vol(ξ_s)`:

* `sourceClassVolume_sub_le` (`tok-volid:shift-mono`): `f(s) ≤ f(0)` for `s ≥ 0`: for a
  `(θ - sΘ_E)`-psh `u`, `u + s ψ_E` is `θ`-psh with the same non-pluripolar mass (the masses agree
  off the pluripolar set `Y₁`, TN `diagonalPotentialMass_sub_curvature_eq`).
* `le_sourceClassVolume_sub` (`tok-volid:shift-flat`): `f(0) ≤ f(s)` for `0 ≤ s ≤ ν_min`: for
  `T ∈ Ω(ξ)` with `c = ν(T, Y₁) ≥ s`, the residual `T - c[Y₁]` (`tok:siu-analytic`) plus
  `(c - s)[Y₁]` is a closed positive current in `ξ_s` with the mass of `T`; then
  `tok:volume-sup`. Hence `f(ν_min) = f(0)` (`sourceClassVolume_sub_firstValuationMin`).
* `sourceClassVolume_sub_firstValuationMax` (`tok-volid:shift-vanish`): `f(ν_max) = 0`: otherwise
  `ξ_s` is big for a rational `s > ν_max`, and `T + s[Y₁] ∈ 𝒜(ξ)` for `T ∈ Ω(ξ_s)` has first
  coordinate `> ν_max`, contradicting `tok:density`.
* `isBigMeetingFirstDivisor_sub` (`tok-volid:shift-meet`): for rational `t ∈ (ν_min, ν_max)`,
  `ξ_t` is big and its Kähler locus meets `Y₁`: a current `G ∈ Ω(ξ)` with `ν(G, Y₁) = t`
  (`tok:slice-density`, `tok-slice:fixed-first`) gives the Kähler current `G - t[Y₁]` in `ξ_t`,
  finite (hence of Lelong number `0`) at a point of `Y₁` (`tok:valuation-analytic`).

Rational multiples `s` are used where `s[Y₁]` must be a metered `ℚ`-divisor; the general
statements follow by the continuity of the volume (`tok:ext-volume-concave`).
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
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.PSH.VariableComplexAtlas

/-! ### Real-variable helpers -/

/-- A closed inequality between continuous functions that holds at the rational points of an
open interval holds on its closure. -/
theorem le_on_Icc_of_rat {f g : ℝ → ℝ≥0∞} (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (hab : a < b) (h : ∀ q : ℚ, a < q → (q : ℝ) < b → f q ≤ g q) :
    ∀ s ∈ Icc a b, f s ≤ g s := by
  have hcl : IsClosed {s | f s ≤ g s} := isClosed_le hf hg
  have hsub : Ioo a b ∩ range ((↑) : ℚ → ℝ) ⊆ {s | f s ≤ g s} := by
    rintro _ ⟨⟨h1, h2⟩, q, rfl⟩
    exact h q h1 h2
  have hdense : Ioo a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  intro s hs
  have hs' : s ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  have : s ∈ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) := by
    have := closure_mono hdense hs'
    rwa [closure_closure] at this
  exact closure_minimal hsub hcl this

section Shift

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- The class `ξ_s = {θ - sΘ_E}`. -/
theorem ofRepresentative_sub_smul (θ η : ClosedRealOneOneForm (m + 1) F.carrier) (s : ℝ) :
    RealBottChern.ofRepresentative (θ - s • η) =
      RealBottChern.ofRepresentative θ - s • RealBottChern.ofRepresentative η := by
  rw [sub_eq_add_neg, sub_eq_add_neg, RealBottChern.ofRepresentative_add,
    RealBottChern.ofRepresentative_neg, RealBottChern.ofRepresentative_smul]

/-- The data of a unit metric. -/
theorem unitMetric_data {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) :
    ∃ D : EffectiveDivisor (m + 1) F.carrier,
      D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) ∧
        E.support = F.flag (1 : Fin (m + 2)) ∧ DivisorMetric.IsDivisorMetric D E := hE

/-- The weight of a unit metric is nondegenerate. -/
theorem locallyNondegenerate_smul_weight (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    {s : ℚ} (hs : 0 ≤ s) :
    LocallyNondegenerate (MeteredDivisorScaling.smul hs E).weight := by
  intro x U hU hxU
  obtain ⟨y, hyU, hy⟩ := (TranscendentalLifting.isThetaPshPotential_weight E).2 x U hU hxU
  refine ⟨y, hyU, fun hbot => hy ?_⟩
  have h : ((s : ℝ) : EReal) * E.weight y = ⊥ := hbot
  rcases (EReal.mul_eq_bot _ _).mp h with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 (EReal.coe_ne_bot _)
  · exact h2
  · exact absurd h1 (EReal.coe_ne_top _)
  · exact absurd h1 (not_lt.mpr (EReal.coe_nonneg.mpr (by exact_mod_cast hs)))

/-- **`tok-volid:shift-mono`, rational form**: `vol(ξ - s{Y₁}) ≤ vol(ξ)` for rational `s ≥ 0`. -/
theorem sourceClassVolume_sub_le_rat [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    {s : ℚ} (hs : 0 ≤ s) :
    sourceClassVolume (RealBottChern.ofRepresentative (θ - (s : ℝ) • E.curvature)) ≤
      sourceClassVolume (RealBottChern.ofRepresentative θ) := by
  set θs := θ - (s : ℝ) • E.curvature with hθs
  by_cases hpsef : ∃ u : F.carrier → EReal, IsThetaPshPotential θs.val u
  · obtain ⟨u, hu⟩ := hpsef
    obtain ⟨hV, hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative F.omega θs hu
    rw [hvol]
    set D := MeteredDivisorScaling.smul hs E with hD
    set V := thetaPshSupremum θs.val
    have hDw : IsThetaPshPotential D.curvature.val D.weight :=
      TranscendentalLifting.isThetaPshPotential_weight D
    have hw : IsThetaPshPotential θ.val (fun x => V x + D.weight x) := by
      have h := isThetaPshPotential_add_from_positive_sum hV hDw
      have hform : θs + D.curvature = θ := by
        rw [hθs, hD, MeteredDivisorScaling.curvature_smul, sub_add_cancel]
      rwa [hform] at h
    have hb : IsThetaPshPotential (θ - D.curvature).val V := by
      rwa [hD, MeteredDivisorScaling.curvature_smul]
    have heq := DominationResidualMass.diagonalPotentialMass_sub_curvature_eq θ D hw hb
      (fun x _ => add_comm _ _) (locallyNondegenerate_smul_weight E hs)
    have hmass : diagonalPotentialMass θs V hV = diagonalPotentialMass (θ - D.curvature) V hb := by
      congr 1
    rw [hmass, heq]
    exact TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume F.omega θ hw
  · rw [TranscendentalVolumeConcavity.sourceClassVolume_eq_zero_of_not_pseudoeffective]
    · exact bot_le
    · rw [classPseudoeffectiveViaPotentials_ofRepresentative]
      exact hpsef

/-- `s ↦ vol(ξ - sη)` is continuous (`tok:ext-volume-concave`). -/
theorem continuous_sourceClassVolume_sub_smul [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (θ η : ClosedRealOneOneForm (m + 1) F.carrier) :
    Continuous fun s : ℝ => sourceClassVolume (RealBottChern.ofRepresentative (θ - s • η)) := by
  have h := TranscendentalVolumeConcavity.continuous_sourceClassVolume_add_smul F.omega
    (RealBottChern.ofRepresentative θ) (-RealBottChern.ofRepresentative η)
  refine h.congr fun s => ?_
  rw [ofRepresentative_sub_smul, smul_neg, ← sub_eq_add_neg]

/-- **`tok-volid:shift-mono`**: `vol(ξ - s{Y₁}) ≤ vol(ξ)` for `s ≥ 0`. -/
theorem sourceClassVolume_sub_le [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    {s : ℝ} (hs : 0 ≤ s) :
    sourceClassVolume (RealBottChern.ofRepresentative (θ - s • E.curvature)) ≤
      sourceClassVolume (RealBottChern.ofRepresentative θ) :=
  le_on_Icc_of_rat (continuous_sourceClassVolume_sub_smul θ E.curvature) continuous_const
    (by linarith : (0 : ℝ) < s + 1)
    (fun q hq _ => sourceClassVolume_sub_le_rat θ E (by exact_mod_cast hq.le)) s ⟨hs, by linarith⟩

/-- **`tok-volid:shift-flat`, rational form**: `vol(ξ) ≤ vol(ξ - s{Y₁})` for rational
`0 ≤ s ≤ ν_min`. -/
theorem le_sourceClassVolume_sub_rat [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {s : ℚ} (hs : 0 ≤ s) (hsmin : (s : ℝ) ≤ firstValuationMin F θ) :
    sourceClassVolume (RealBottChern.ofRepresentative θ) ≤
      sourceClassVolume (RealBottChern.ofRepresentative (θ - (s : ℝ) • E.curvature)) := by
  rcases hs.lt_or_eq with hs0 | rfl
  swap
  · simp
  obtain ⟨D₀, hDI, hEW, hmetric⟩ := hE
  have hΩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  rw [TranscendentalPartial.sourceClassVolume_eq_iSup_gentleKahler F.omega θ hΩ]
  refine iSup₂_le fun φ hφ => ?_
  have hφA : φ ∈ analyticCurrents θ := gentleCurrents_subset_analyticCurrents θ hφ.1
  obtain ⟨⟨c₀, hc₀, hcc₀⟩, h0, -, -⟩ := flagValuation_of_analytic F hφA D₀ hDI E hEW hmetric
  set c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toNNReal with hc
  set v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ) with hvdef
  have hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val v :=
    SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hφ.1.1
      F.firstDivisor D₀ hDI E hEW hmetric
  have hrec := SGPT.Okounkov.smooth_divisor_residual_recompose hφ.1.1 F.firstDivisor E hEW c hv
  -- `c ≥ ν_min ≥ s`
  have hcs : (s : ℝ) ≤ c := by
    have hmin : firstValuationMin F θ ≤ flagValuation F φ 0 :=
      csInf_le (bddBelow_firstValuations θ) ⟨φ, hφ, rfl⟩
    rw [h0] at hmin
    linarith
  have hcs' : (0 : ℚ) ≤ c₀ - s := by
    have : (s : ℝ) ≤ c₀ := hcc₀ ▸ hcs
    exact sub_nonneg.mpr (by exact_mod_cast this)
  set Ds := MeteredDivisorScaling.smul hs E with hDs
  set Dr := MeteredDivisorScaling.smul hcs' E with hDr
  set b : F.carrier → EReal := fun x => v x + Dr.weight x with hb
  have hbpsh : IsThetaPshPotential (θ - Ds.curvature).val b := by
    have h := isThetaPshPotential_add_from_positive_sum hv
      (TranscendentalLifting.isThetaPshPotential_weight Dr)
    have hform : (θ - (c : ℝ) • E.curvature) + Dr.curvature = θ - Ds.curvature := by
      rw [hDs, hDr, MeteredDivisorScaling.curvature_smul, MeteredDivisorScaling.curvature_smul,
        hcc₀]
      push_cast
      rw [sub_smul]
      abel
    rwa [hform] at h
  have heq : ∀ x, x ∉ Ds.support → φ x = Ds.weight x + b x := by
    intro x hx
    rw [MeteredDivisorScaling.smul_support hs hs0.ne' E] at hx
    have hne : E.weight x ≠ ⊥ := hx
    have hnt : E.weight x ≠ ⊤ := StepFourLogSingularities.weight_ne_top E x
    obtain ⟨w, hw⟩ : ∃ w : ℝ, E.weight x = w := ⟨(E.weight x).toReal, (EReal.coe_toReal hnt hne).symm⟩
    have hx' : v x + ((c : ℝ) : EReal) * E.weight x = φ x := congrFun hrec x
    rw [← hx']
    show v x + ((c : ℝ) : EReal) * E.weight x = ((s : ℝ) : EReal) * E.weight x +
      (v x + (((c₀ - s : ℚ) : ℝ) : EReal) * E.weight x)
    rw [hw, hcc₀, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, add_left_comm,
      ← EReal.coe_add]
    congr 2
    push_cast
    ring
  have hmass := DominationResidualMass.diagonalPotentialMass_sub_curvature_eq θ Ds hφ.1.1 hbpsh
    heq (locallyNondegenerate_smul_weight E hs)
  rw [← hmass]
  have hle := TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume F.omega
    (θ - Ds.curvature) hbpsh
  have hDc : θ - Ds.curvature = θ - (s : ℝ) • E.curvature := by
    rw [hDs, MeteredDivisorScaling.curvature_smul]
  exact hle.trans_eq (by rw [hDc])

/-- **`tok-volid:shift-flat`**: `vol(ξ) ≤ vol(ξ - s{Y₁})` for `0 ≤ s ≤ ν_min`. -/
theorem le_sourceClassVolume_sub [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {s : ℝ} (hs : 0 ≤ s) (hsmin : s ≤ firstValuationMin F θ) :
    sourceClassVolume (RealBottChern.ofRepresentative θ) ≤
      sourceClassVolume (RealBottChern.ofRepresentative (θ - s • E.curvature)) := by
  rcases (hs.trans hsmin).lt_or_eq with hpos | hzero
  · exact le_on_Icc_of_rat continuous_const (continuous_sourceClassVolume_sub_smul θ E.curvature)
      hpos (fun q hq hq' => le_sourceClassVolume_sub_rat hbig hE (by exact_mod_cast hq.le) hq'.le)
      s ⟨hs, hsmin⟩
  · have : s = 0 := le_antisymm (hzero ▸ hsmin) hs
    subst this
    simp

/-- **`tok-volid:shift-flat`**: `vol(ξ - ν_min{Y₁}) = vol(ξ)`. -/
theorem sourceClassVolume_sub_firstValuationMin [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    sourceClassVolume (RealBottChern.ofRepresentative (θ - firstValuationMin F θ • E.curvature)) =
      sourceClassVolume (RealBottChern.ofRepresentative θ) := by
  have h0 : 0 ≤ firstValuationMin F θ :=
    le_csInf (firstValuations_nonempty hbig) (by rintro _ ⟨φ, -, rfl⟩; exact flagValuation_nonneg φ 0)
  exact le_antisymm (sourceClassVolume_sub_le θ E h0) (le_sourceClassVolume_sub hbig hE h0 le_rfl)

/-- **`tok-volid:shift-vanish`**: `vol(ξ - ν_max{Y₁}) = 0`. -/
theorem sourceClassVolume_sub_firstValuationMax [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    sourceClassVolume (RealBottChern.ofRepresentative (θ - firstValuationMax F θ • E.curvature)) =
      0 := by
  by_contra hne
  have hpos : 0 < sourceClassVolume
      (RealBottChern.ofRepresentative (θ - firstValuationMax F θ • E.curvature)) :=
    pos_iff_ne_zero.mpr hne
  have hopen : IsOpen {s : ℝ | 0 < sourceClassVolume
      (RealBottChern.ofRepresentative (θ - s • E.curvature))} :=
    isOpen_lt continuous_const (continuous_sourceClassVolume_sub_smul θ E.curvature)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hpos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by linarith : firstValuationMax F θ <
    firstValuationMax F θ + ε)
  have hqmem : (q : ℝ) ∈ Metric.ball (firstValuationMax F θ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hqpos := hball hqmem
  have hmax0 : 0 ≤ firstValuationMax F θ := by
    obtain ⟨φ, hφ⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
    exact (flagValuation_nonneg φ 0).trans
      (le_csSup (bddAbove_firstValuations θ) ⟨φ, hφ, rfl⟩)
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (hmax0.trans hq1.le)
  have hbigq : SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (θ - (q : ℝ) • E.curvature)) :=
    (TranscendentalVolumeConcavity.volumePositiveIffBig F.omega _).mp hqpos
  obtain ⟨φ, hφ⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbigq
  have hφA : φ ∈ analyticCurrents (θ - (q : ℝ) • E.curvature) :=
    gentleCurrents_subset_analyticCurrents _ hφ.1
  have hΦ := add_smul_mem_analyticCurrents hφA (weight_mem_analyticCurrents hE)
    (a := 1) (b := q) zero_le_one hq0
  simp only [Rat.cast_one, one_smul, sub_add_cancel, EReal.coe_one, one_mul] at hΦ
  have hν := flagValuation_add_smul (F := F) hφA.1 (weight_mem_analyticCurrents hE).1
    (a := (1 : ℝ)) (b := (q : ℝ)) zero_le_one (by exact_mod_cast hq0)
  rw [flagValuation_weight hE] at hν
  simp only [EReal.coe_one, one_mul, one_smul] at hν
  have hν0 : flagValuation F (fun x => φ x + ((q : ℝ) : EReal) * E.weight x) 0 =
      flagValuation F φ 0 + q := by
    rw [hν]; simp
  have hΩθ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  have hmem := SGPT.Okounkov.TranscendentalDensity.densityStatement (m + 1) F θ hΩθ _ hΦ
  have hmem0 : flagValuation F (fun x => φ x + ((q : ℝ) : EReal) * E.weight x) 0 ∈
      closure (firstValuations F θ) := by
    have h := image_closure_subset_closure_image (continuous_apply (0 : Fin (m + 1)))
      (mem_image_of_mem _ hmem)
    rwa [image_image] at h
  have hle : flagValuation F φ 0 + q ≤ firstValuationMax F θ := by
    rw [← hν0]
    exact closure_minimal (fun a ha => le_csSup (bddAbove_firstValuations θ) ha) isClosed_Iic
      hmem0
  linarith [flagValuation_nonneg φ 0]

/-- **`tok-volid:shift-meet`**: for rational `t ∈ (ν_min, ν_max)`, `ξ - t{Y₁}` is big and its
Kähler locus meets `Y₁`. -/
theorem isBigMeetingFirstDivisor_sub
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    IsBigMeetingFirstDivisor F
      (RealBottChern.ofRepresentative θ - (t : ℝ) • RealBottChern.ofRepresentative E.curvature) := by
  obtain ⟨_, ⟨P, hP, rfl⟩, hPt⟩ := exists_lt_of_csInf_lt (firstValuations_nonempty hbig) h₁
  obtain ⟨_, ⟨T, hT, rfl⟩, hTt⟩ := exists_lt_of_lt_csSup (firstValuations_nonempty hbig) h₂
  obtain ⟨p, -, hp⟩ := flagValuation_rational_of_analytic (m + 1) F θ P
    (gentleCurrents_subset_analyticCurrents θ hP.1) 0
  obtain ⟨q, -, hq⟩ := flagValuation_rational_of_analytic (m + 1) F θ T
    (gentleCurrents_subset_analyticCurrents θ hT.1) 0
  have hpt : p < t := by
    change flagValuation F P 0 < t at hPt
    rw [hp] at hPt; exact_mod_cast hPt
  have htq : t ≤ q := by
    change (t : ℝ) < flagValuation F T 0 at hTt
    rw [hq] at hTt; exact_mod_cast hTt.le
  obtain ⟨S, hS, hSt, -⟩ := exists_mem_fixedFirst_near hT hP hq hp (Or.inl ⟨hpt, htq⟩) 0
  obtain ⟨κ, hκ⟩ := hS.2
  have hSA : S ∈ analyticCurrents (θ - κ.form) :=
    ⟨hκ, (gentleCurrents_subset_analyticCurrents θ hS.1).2⟩
  obtain ⟨D₀, hDI, hEW, hmetric⟩ := hE
  obtain ⟨-, h0, hw, -⟩ := flagValuation_of_analytic F hSA D₀ hDI E hEW hmetric
  set c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) S).toNNReal with hc
  have hct : (c : ℝ) = t := by rw [← h0, hSt]
  set v := extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c S) with hvdef
  have hv : IsThetaPshPotential ((θ - κ.form) - (c : ℝ) • E.curvature).val v :=
    SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hκ
      F.firstDivisor D₀ hDI E hEW hmetric
  -- a point of `Y₁` where the residual is finite
  obtain ⟨y₀, hy₀⟩ := F.firstDivisor.2.1.nonempty
  obtain ⟨y, -, hy⟩ := hw.1.2 (⟨y₀, hy₀⟩ : F.tail.carrier) univ isOpen_univ (mem_univ _)
  have hform : (θ - κ.form) - (c : ℝ) • E.curvature = (θ - (t : ℝ) • E.curvature) - κ.form := by
    rw [hct]; abel
  let K : KahlerCurrent (RealBottChern.ofRepresentative θ -
      (t : ℝ) • RealBottChern.ofRepresentative E.curvature) :=
    { representative := θ - (t : ℝ) • E.curvature
      represents := ofRepresentative_sub_smul θ E.curvature t
      potential := v
      lowerBound := κ
      strictlyPsh := by rw [← hform]; exact hv }
  refine ⟨(SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr ⟨K⟩, y.val, y.2, fun hnk => ?_⟩
  have hpos := hnk K
  have hzero : lelongNumber (n := m + 1) K.potential y.val = 0 :=
    SGPT.Okounkov.TranscendentalBody2.lelongNumber_eq_zero_of_ne_bot (Nat.succ_pos m) hv.1 hy
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

end Shift

end SGPT.Okounkov.TranscendentalVolId
