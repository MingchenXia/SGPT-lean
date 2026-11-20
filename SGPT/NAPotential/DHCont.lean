import SGPT.NAPotential.DHMeasure
import SGPT.NAPotential.DHContWeak
import SGPT.NAPotential.DecreasingInfimum
import SGPT.NAPotential.Supremum
import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelInfimum
import SGPT.Foundations.Analysis.Pending.IncreasingDiagonalContinuity

/-!
# Continuity of Duistermaat–Heckman measures along monotone sequences

Source: `chapter_NApotential.tex`, `prop:contDH` (blueprint chapter `claude-na-dh2`, nodes
`claude-na-dh2:tails`, `claude-na-dh2:cont-tails`, `claude-na-dh2:dec-slices`,
`claude-na-dh2:inc-slices` and `claude-naplan:contdh`).

Let `X` be a connected compact Kähler manifold, `θ` a closed smooth real `(1,1)`-form with
`{θ}` big, and `Γ^i, Γ ∈ PSH^NA(X, θ)_{>0}` (positive-mass `𝓘`-model test curves,
`SourcePositiveIModelTestCurve θ`). If either

1. `(Γ^i)` is decreasing, `Γ = inf_i Γ^i` and `vol Γ = lim_i vol Γ^i`, or
2. `(Γ^i)` is increasing and `Γ = usc-sup_i Γ^i`,

then `DH(Γ^i) ⇀ DH(Γ)` weakly (`naDuistermaatHeckman_tendsto_of_decreasingInf`,
`naDuistermaatHeckman_tendsto_of_uscSup`). The infimum and the usc supremum are those of
`PSH^NA(X, θ)` (`def:NApotential:L525`, `def:NApotential:L413`), read through the embedding
`sourcePositiveTestCurveToNA` of `prop:NAposNAemb`; the test-curve forms
(`def:testcurinf`, `def:testcurvsupsgeneral`) are also given.

ROUTE CHANGE (blueprint `claude-na-dh2:cont-tails`). The book derives the weak convergence from
`lma:DHmconv`/`lma:DHmconv2` after proving Hausdorff convergence of the partial Okounkov bodies
by `cor:decnetdS` and `thm:pobmain` (4). Here we use that `DH(Γ)([t, ∞)) = ∫_X θ_{Γ_t}^n` for
`t < Γ_max`, `DH(Γ)` vanishes on `(Γ_max, ∞)` and `DH(Γ)(ℝ) = vol Γ`
(`claude-naplan:dh-tails`, a measure with these properties is said to have the
*Duistermaat–Heckman tails* of `Γ`, `HasDHTails`). Weak convergence of finite measures on `ℝ`
follows from convergence of the total masses and of the upper tails away from one point
(`tendsto_of_tendsto_mass_of_tendsto_Ici`), and the slice masses converge by monotone
convergence of non-pluripolar masses (`prop:vol_limit_model` for decreasing sequences,
the increasing case of `thm:WN19`/`cor:incseqnppcont`). The argument is flag-free; it applies
verbatim to the general definition `eq:DHmgeneral` (`SGPT.NAPotential.DHGeneral`).

## Main results

* `HasDHTails`, `HasDHTails.unique`, `tendsto_of_hasDHTails`.
* `tendsto_naSliceMass_decreasingInf`, `tendsto_naSliceMass_generalSup_of_monotone`,
  `tendsto_sourceNAVolume_generalSup_of_monotone`.
* `eq_decreasingInf_of_toNA_eq`, `eq_generalSup_of_toNA_eq`: the `PSH^NA` operations on
  positive curves are the test-curve operations.
* `naDuistermaatHeckman_tendsto_of_decreasingInf` (`prop:contDH` (1)) and
  `naDuistermaatHeckman_tendsto_of_uscSup` (`prop:contDH` (2)), flag case.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.NAPotential.DH

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

section Tails

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The slice mass `t ↦ ∫_X θ_{Γ_t}^n` of `Γ ∈ PSH^NA(X, θ)_{>0}` for `t < Γ_max`, extended by `0`
for `t ≥ Γ_max`. -/
def naSliceMass (Γ : SourcePositiveIModelTestCurve θ) (t : ℝ) : ℝ≥0∞ :=
  if h : t < Γ.val.max then
    sourcePotentialNonPluripolarMeasure θ (Γ.val.potential ⟨t, h⟩) (Γ.val.thetaPSH _) univ
  else 0

omit [BorelSpace M] [ConnectedSpace M] in
theorem naSliceMass_of_lt (Γ : SourcePositiveIModelTestCurve θ) {t : ℝ} (ht : t < Γ.val.max) :
    naSliceMass Γ t =
      sourcePotentialNonPluripolarMeasure θ (Γ.val.potential ⟨t, ht⟩) (Γ.val.thetaPSH _) univ :=
  dif_pos ht

omit [BorelSpace M] [ConnectedSpace M] in
theorem naSliceMass_of_le (Γ : SourcePositiveIModelTestCurve θ) {t : ℝ} (ht : Γ.val.max ≤ t) :
    naSliceMass Γ t = 0 :=
  dif_neg (not_lt.mpr ht)

/-- A Borel measure `μ` on `ℝ` has the *Duistermaat–Heckman tails* of
`Γ ∈ PSH^NA(X, θ)_{>0}` if it is finite, `μ([t, ∞)) = ∫_X θ_{Γ_t}^n` for `t < Γ_max`,
`μ((Γ_max, ∞)) = 0` and `μ(ℝ) = vol Γ`. By `claude-naplan:dh-tails` the measure `DH(Γ)` of
`def:DHm` has this property for every smooth flag. -/
structure HasDHTails (μ : Measure ℝ) (Γ : SourcePositiveIModelTestCurve θ) : Prop where
  isFiniteMeasure : IsFiniteMeasure μ
  Ici_eq : ∀ t : Iio Γ.val.max, μ (Ici (t : ℝ)) =
    sourcePotentialNonPluripolarMeasure θ (Γ.val.potential t) (Γ.val.thetaPSH t) univ
  Ioi_max_eq : μ (Ioi Γ.val.max) = 0
  univ_eq : μ univ = sourceNAVolume (sourcePositiveTestCurveToNA Γ)

/-- The upper tails away from `Γ_max` are the slice masses. -/
theorem HasDHTails.Ici_eq_naSliceMass {μ : Measure ℝ} {Γ : SourcePositiveIModelTestCurve θ}
    (h : HasDHTails μ Γ) {t : ℝ} (ht : t ≠ Γ.val.max) : μ (Ici t) = naSliceMass Γ t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [naSliceMass_of_lt Γ ht]
    exact h.Ici_eq ⟨t, ht⟩
  · rw [naSliceMass_of_le Γ ht.le]
    exact measure_mono_null (Ici_subset_Ioi.mpr ht) h.Ioi_max_eq

/-- A measure with the Duistermaat–Heckman tails of `Γ` is unique. -/
theorem HasDHTails.unique {μ ν : Measure ℝ} {Γ : SourcePositiveIModelTestCurve θ}
    (hμ : HasDHTails μ Γ) (hν : HasDHTails ν Γ) : μ = ν := by
  have := hμ.isFiniteMeasure
  have := hν.isFiniteMeasure
  exact measure_eq_of_Ici_of_Ioi_eq_zero μ ν Γ.val.max hμ.Ioi_max_eq hν.Ioi_max_eq
    (fun t ht => (hμ.Ici_eq ⟨t, ht⟩).trans (hν.Ici_eq ⟨t, ht⟩).symm)

/-- **Weak convergence from the Duistermaat–Heckman tails.** Let `μᵢ` (resp. `μ`) have the
Duistermaat–Heckman tails of `Γ^i` (resp. `Γ`). If `Γ^i_max → Γ_max`, `vol Γ^i → vol Γ` and the
slice masses converge, `∫_X θ_{Γ^i_t}^n → ∫_X θ_{Γ_t}^n` for every `t < Γ_max`, then
`μᵢ ⇀ μ`. -/
theorem tendsto_of_hasDHTails {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    {Γs : ℕ → SourcePositiveIModelTestCurve θ} {Γ : SourcePositiveIModelTestCurve θ}
    (hμs : ∀ i, HasDHTails (μs i : Measure ℝ) (Γs i)) (hμ : HasDHTails (μ : Measure ℝ) Γ)
    (hmax : Tendsto (fun i => (Γs i).val.max) atTop (𝓝 Γ.val.max))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ))))
    (hslice : ∀ t < Γ.val.max,
      Tendsto (fun i => naSliceMass (Γs i) t) atTop (𝓝 (naSliceMass Γ t))) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_of_tendsto_mass_of_tendsto_Ici Γ.val.max
  · rw [← ENNReal.tendsto_coe]
    simp only [FiniteMeasure.ennreal_mass, (hμs _).univ_eq, hμ.univ_eq]
    exact hvol
  · intro t ht
    rw [← ENNReal.tendsto_coe]
    simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rw [hμ.Ici_eq_naSliceMass ht]
    have hev : (fun i => naSliceMass (Γs i) t) =ᶠ[atTop] fun i => (μs i : Measure ℝ) (Ici t) := by
      filter_upwards [hmax.eventually_ne (Ne.symm ht)] with i hi
      exact ((hμs i).Ici_eq_naSliceMass (Ne.symm hi)).symm
    refine Tendsto.congr' hev ?_
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · exact hslice t hlt
    · rw [naSliceMass_of_le Γ hgt.le]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Tendsto.eventually_lt_const hgt hmax] with i hi
      exact (naSliceMass_of_le (Γs i) hi.le).symm

/-! ### Slice masses along decreasing infima and increasing suprema -/

/-- Along the decreasing infimum `Γ = inf_i Γ^i` (`def:testcurinf`) the slice masses converge:
`∫_X θ_{Γ^i_t}^n → ∫_X θ_{Γ_t}^n` for `t < Γ_max` (`prop:vol_limit_model`: `Γ_t = inf_i Γ^i_t` is a
decreasing limit of model potentials with positive mass). -/
theorem tendsto_naSliceMass_decreasingInf (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs j).val (Γs i).val)
    (hb : BddBelow (range fun i => (Γs i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (Γs i).val) hb) {t : ℝ}
    (ht : t < (SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm).val.max) :
    Tendsto (fun i => naSliceMass (Γs i) t) atTop
      (𝓝 (naSliceMass (SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm) t)) := by
  set G := SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm with hG
  have hti : ∀ i, t < (Γs i).val.max := fun i =>
    ht.trans_le (sourceTestCurveInfCutoff_le (fun i => (Γs i).val) hb i)
  let u : ℕ → M → EReal := fun i => (Γs i).val.potential ⟨t, hti i⟩
  have hu : ∀ i, IsModelPotential (atlasClosedFormToNative θ) (u i) :=
    fun i => ((Γs i).val.slice_model omega ⟨t, hti i⟩).toNative
  have hanti : Antitone u := fun i j hij x =>
    sourceTestCurveInfSlice_antitone omega (fun i => (Γs i).val) ha hb ⟨t, ht⟩ x hij
  have hGpot : G.val.potential ⟨t, ht⟩ = ⨅ i, u i := by
    funext x
    rw [iInf_apply]
    rfl
  have hinf := ActualDecreasingModelInfimum.isThetaPshPotential_iInf_of_antitone_model hu hanti
  have hinf' : (ofFixedModel n M).IsThetaPSH θ (⨅ i, u i) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hinf
  have hpos : 0 < DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ) (⨅ i, u i)
      hinf := by
    have h := G.val.mass_positive omega ⟨t, ht⟩
    rw [sourcePotentialMass_congr hGpot _ hinf'] at h
    exact h
  have hlim := ActualDecreasingModelInfimum.tendsto_diagonalPotentialMass_iInf_of_antitone_model
    omega hu hanti hpos
  rw [naSliceMass_of_lt G ht, sourcePotentialMass_congr hGpot _ hinf']
  refine hlim.congr (fun i => ?_)
  rw [naSliceMass_of_lt (Γs i) (hti i)]
  rfl

omit [ConnectedSpace M] in
/-- For an increasing sequence of `θ`-psh functions the masses of the members converge to the
mass of the usc-regularized supremum (`thm:WN19` with the lower semicontinuity of
`cor:incseqnppcont`; `IncreasingDiagonalContinuity.diagonalPotentialMass_eq_iSup`). -/
theorem tendsto_sourceMass_of_monotone (omega : KahlerBackground n M) {v : ℕ → M → EReal}
    (hv : ∀ k, (ofFixedModel n M).IsThetaPSH θ (v k)) (hmono : Monotone v)
    {w : M → EReal} (hw : (ofFixedModel n M).IsThetaPSH θ w)
    (hvw : w = uscRegularization (⨆ k, v k)) :
    Tendsto (fun k => sourcePotentialNonPluripolarMeasure θ (v k) (hv k) univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ w hw univ)) := by
  have hvn : ∀ k, IsThetaPshPotential (atlasClosedFormToNative θ).val (v k) :=
    fun k => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hv k)
  have hwn : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (uscRegularization (⨆ k, v k)) := by
    rw [← hvw]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mp hw
  have heq := IncreasingDiagonalContinuity.diagonalPotentialMass_eq_iSup omega hvn hmono
    hwn
  have hmon := IncreasingDiagonalContinuity.diagonalPotentialMass_monotone omega hvn hmono
  have hlim := tendsto_atTop_iSup hmon
  rw [← heq] at hlim
  have hw' : (ofFixedModel n M).IsThetaPSH θ (uscRegularization (⨆ k, v k)) := by
    rw [← hvw]
    exact hw
  rw [sourcePotentialMass_congr hvw hw hw']
  exact hlim

/-- The supremum of a monotone sequence is the supremum of its tail. -/
theorem iSup_add_eq_of_monotone {α : Type*} [CompleteLattice α] {f : ℕ → α} (hf : Monotone f)
    (i₀ : ℕ) : (⨆ k, f (k + i₀)) = ⨆ i, f i :=
  le_antisymm (iSup_le fun k => le_iSup f (k + i₀))
    (iSup_le fun i => (hf (Nat.le_add_right i i₀)).trans (le_iSup (fun k => f (k + i₀)) i))

/-- Along the usc supremum `Γ = usc-sup_i Γ^i` of an increasing sequence
(`def:testcurvsupsgeneral`) the slice masses converge: for `t < Γ_max`,
`Γ_t = usc-sup_{i ≥ i₀} Γ^i_t` and `∫_X θ_{Γ^i_t}^n → ∫_X θ_{Γ_t}^n`. -/
theorem tendsto_naSliceMass_generalSup_of_monotone (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs i).val (Γs j).val)
    (hb : BddAbove (range fun i => (Γs i).val.max)) {t : ℝ}
    (ht : t < (SourcePositiveIModelTestCurve.generalSup omega Γs hb).val.max) :
    Tendsto (fun i => naSliceMass (Γs i) t) atTop
      (𝓝 (naSliceMass (SourcePositiveIModelTestCurve.generalSup omega Γs hb) t)) := by
  set G := SourcePositiveIModelTestCurve.generalSup omega Γs hb with hG
  have hGv : G.val = SourceTestCurve.increasingSup omega (fun i => (Γs i).val) hmono hb :=
    SourceTestCurve.generalSup_eq_increasing_of_monotone omega _ hmono hb
  have htG : t < sourceTestCurveSupCutoff (fun i => (Γs i).val) := by
    have h : G.val.max = sourceTestCurveSupCutoff (fun i => (Γs i).val) := by
      rw [hGv]
      rfl
    rw [← h]
    exact ht
  obtain ⟨i₀, hi₀⟩ := sourceTestCurveSupCutoff_exists (fun i => (Γs i).val) htG
  have hti : ∀ k, t < (Γs (k + i₀)).val.max := fun k =>
    hi₀.trans_le (hmono i₀ (k + i₀) (Nat.le_add_left i₀ k)).cutoff_le
  let v : ℕ → M → EReal := fun k => (Γs (k + i₀)).val.potential ⟨t, hti k⟩
  have hv : ∀ k, (ofFixedModel n M).IsThetaPSH θ (v k) := fun k => (Γs (k + i₀)).val.thetaPSH _
  have hext := sourceTestCurveSup_extension_monotone omega (fun i => (Γs i).val) hmono t
  have hvAt : ∀ k, v k = sourceTestCurveAt (Γs (k + i₀)).val.toSourceTestCurvePredata t :=
    fun k => (sourceTestCurveAt_of_lt _ (hti k)).symm
  have hvmono : Monotone v := by
    intro k l hkl
    rw [hvAt k, hvAt l]
    exact hext (Nat.add_le_add_right hkl i₀)
  have hpot : G.val.potential ⟨t, ht⟩ = uscRegularization (⨆ k, v k) := by
    have h1 : G.val.potential ⟨t, ht⟩ =
        (SourceTestCurve.increasingSup omega (fun i => (Γs i).val) hmono hb).potential
          ⟨t, htG⟩ :=
      sourceTestCurve_potential_congr hGv t ht htG
    rw [h1, SourceTestCurve.increasingSup_potential]
    change uscRegularization (⨆ i, sourceTestCurveAt (Γs i).val.toSourceTestCurvePredata t) = _
    congr 1
    rw [← iSup_add_eq_of_monotone hext i₀]
    exact iSup_congr fun k => (hvAt k).symm
  have hlim := tendsto_sourceMass_of_monotone omega hv hvmono (G.val.thetaPSH ⟨t, ht⟩) hpot
  rw [naSliceMass_of_lt G ht]
  apply (Filter.tendsto_add_atTop_iff_nat i₀).mp
  refine hlim.congr (fun k => ?_)
  rw [naSliceMass_of_lt (Γs (k + i₀)) (hti k)]

/-- Along the usc supremum of an increasing sequence the volumes converge:
`vol Γ^i → vol Γ` (`Γ_{-∞} = usc-sup_i Γ^i_{-∞}` and `prop:PSHNApvolGamma`). -/
theorem tendsto_sourceNAVolume_generalSup_of_monotone (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs i).val (Γs j).val)
    (hb : BddAbove (range fun i => (Γs i).val.max)) :
    Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA
        (SourcePositiveIModelTestCurve.generalSup omega Γs hb)))) := by
  set G := SourcePositiveIModelTestCurve.generalSup omega Γs hb with hG
  have hGv : G.val = SourceTestCurve.increasingSup omega (fun i => (Γs i).val) hmono hb :=
    SourceTestCurve.generalSup_eq_increasing_of_monotone omega _ hmono hb
  let v : ℕ → M → EReal := fun i => sourceTestCurveLimit (Γs i).val.toSourceTestCurvePredata
  have hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i) := fun i => (Γs i).val.limit_thetaPSH
  have hvmono : Monotone v := fun i j hij =>
    sourceTestCurveLimit_mono_of_extension (Γs i).val (Γs j).val
      ((sourceTestCurvePOrder_iff_extension omega _ _).mp (hmono i j hij))
  have hlimG : sourceTestCurveLimit G.val.toSourceTestCurvePredata =
      uscRegularization (⨆ i, v i) := by
    rw [hGv]
    exact SourceTestCurve.increasingSup_limit omega (fun i => (Γs i).val) hmono hb
  have hlim := tendsto_sourceMass_of_monotone omega hv hvmono G.val.limit_thetaPSH hlimG
  rw [sourceNAVolume_positiveTestCurve omega G]
  refine hlim.congr (fun i => ?_)
  rw [sourceNAVolume_positiveTestCurve omega (Γs i)]

/-! ### The `PSH^NA` operations on positive curves -/

/-- If `Γ = inf_i Γ^i` in `PSH^NA(X, θ)` (`def:NApotential:L525`) for a decreasing sequence of
positive curves `Γ^i` and a positive curve `Γ`, then `Γ` is the test-curve infimum
(`def:testcurinf`); in particular its uniform positive mass condition holds. -/
theorem eq_decreasingInf_of_toNA_eq (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j)) (sourcePositiveTestCurveToNA (Γs i)))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.decreasingInf omega (fun i => sourcePositiveTestCurveToNA (Γs i)) ha hb) :
    ∃ (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs j).val (Γs i).val)
      (hb' : BddBelow (range fun i => (Γs i).val.max))
      (hm : SourceTestCurveInfMassCondition (fun i => (Γs i).val) hb'),
      Γ = SourcePositiveIModelTestCurve.decreasingInf omega Γs ha' hb' hm := by
  have ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs j).val (Γs i).val := fun i j hij =>
    (sourcePositiveTestCurveToNA_POrder_iff omega (Γs j) (Γs i)).mp (ha i j hij)
  have hb' : BddBelow (range fun i => (Γs i).val.max) := by
    simpa only [sourcePositiveTestCurveToNA_cutoff] using hb
  -- `Γ ≤ Γ^i` for every `i`
  have hle : ∀ i, SourceTestCurvePOrder Γ.val (Γs i).val := fun i =>
    (sourcePositiveTestCurveToNA_POrder_iff omega Γ (Γs i)).mp
      (hΓ ▸ SourceNAPotential.decreasingInf_le omega _ ha hb i)
  have hcut : Γ.val.max ≤ sourceTestCurveInfCutoff (fun i => (Γs i).val) :=
    le_csInf (range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact (hle i).cutoff_le)
  have hm : SourceTestCurveInfMassCondition (fun i => (Γs i).val) hb' := by
    have hr : Γ.val.max - 1 < Γ.val.max := by linarith
    refine ⟨⟨Γ.val.max - 1, hr.trans_le hcut⟩, ?_⟩
    refine (Γ.val.mass_positive omega ⟨Γ.val.max - 1, hr⟩).trans_le (le_iInf fun i => ?_)
    obtain ⟨hc, hs⟩ := (sourceTestCurvePOrder_iff omega _ _).mp (hle i)
    exact sourcePotentialNonPluripolarMass_mono omega _ _
      (MoreSingularOn.of_le fun x _ => hs _ hr x)
  refine ⟨ha', hb', hm, sourcePositiveTestCurveToNA_injective omega ?_⟩
  rw [hΓ, sourcePositiveTestCurveToNA_decreasingInf omega Γs ha' hb' hm]

/-- If `Γ = usc-sup_i Γ^i` in `PSH^NA(X, θ)` (`def:NApotential:L413`) for positive curves, then
`Γ` is the test-curve usc supremum (`def:testcurvsupsgeneral`). -/
theorem eq_generalSup_of_toNA_eq (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.uscSup omega (fun i => sourcePositiveTestCurveToNA (Γs i)) hb) :
    ∃ hb' : BddAbove (range fun i => (Γs i).val.max),
      Γ = SourcePositiveIModelTestCurve.generalSup omega Γs hb' := by
  have hb' : BddAbove (range fun i => (Γs i).val.max) := by
    simpa only [sourcePositiveTestCurveToNA_cutoff] using hb
  refine ⟨hb', sourcePositiveTestCurveToNA_injective omega ?_⟩
  rw [hΓ, sourcePositiveTestCurveToNA_generalSup omega Γs hb']

/-! ### Continuity for measures with the Duistermaat–Heckman tails -/

/-- `prop:contDH` (1) for measures with the Duistermaat–Heckman tails, test-curve form. -/
theorem tendsto_of_hasDHTails_decreasingInf (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs j).val (Γs i).val)
    (hb : BddBelow (range fun i => (Γs i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (Γs i).val) hb)
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμs : ∀ i, HasDHTails (μs i : Measure ℝ) (Γs i))
    (hμ : HasDHTails (μ : Measure ℝ) (SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA
        (SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm))))) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_hasDHTails hμs hμ ?_ hvol
    (fun t ht => tendsto_naSliceMass_decreasingInf omega Γs ha hb hm ht)
  have hanti : Antitone fun i => (Γs i).val.max := fun i j hij => (ha i j hij).cutoff_le
  exact tendsto_atTop_ciInf hanti hb

/-- `prop:contDH` (2) for measures with the Duistermaat–Heckman tails, test-curve form. -/
theorem tendsto_of_hasDHTails_generalSup (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs i).val (Γs j).val)
    (hb : BddAbove (range fun i => (Γs i).val.max))
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμs : ∀ i, HasDHTails (μs i : Measure ℝ) (Γs i))
    (hμ : HasDHTails (μ : Measure ℝ) (SourcePositiveIModelTestCurve.generalSup omega Γs hb)) :
    Tendsto μs atTop (𝓝 μ) := by
  refine tendsto_of_hasDHTails hμs hμ ?_
    (tendsto_sourceNAVolume_generalSup_of_monotone omega Γs hmono hb)
    (fun t ht => tendsto_naSliceMass_generalSup_of_monotone omega Γs hmono hb ht)
  have hmax : (SourcePositiveIModelTestCurve.generalSup omega Γs hb).val.max =
      ⨆ i, (Γs i).val.max :=
    SourceTestCurve.generalSup_max omega _ hb
  rw [hmax]
  exact tendsto_atTop_ciSup (fun i j hij => (hmono i j hij).cutoff_le) hb

/-- **`prop:contDH` (1), measures with the Duistermaat–Heckman tails.** If `(Γ^i)` decreases,
`Γ = inf_i Γ^i` in `PSH^NA(X, θ)` and `vol Γ = lim_i vol Γ^i`, then `μᵢ ⇀ μ`. -/
theorem tendsto_of_hasDHTails_of_toNA_eq_decreasingInf (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j)) (sourcePositiveTestCurveToNA (Γs i)))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.decreasingInf omega (fun i => sourcePositiveTestCurveToNA (Γs i)) ha hb)
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ))))
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμs : ∀ i, HasDHTails (μs i : Measure ℝ) (Γs i)) (hμ : HasDHTails (μ : Measure ℝ) Γ) :
    Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨ha', hb', hm, rfl⟩ := eq_decreasingInf_of_toNA_eq omega Γs Γ ha hb hΓ
  exact tendsto_of_hasDHTails_decreasingInf omega Γs ha' hb' hm hμs hμ hvol

/-- **`prop:contDH` (2), measures with the Duistermaat–Heckman tails.** If `(Γ^i)` increases
and `Γ = usc-sup_i Γ^i` in `PSH^NA(X, θ)`, then `μᵢ ⇀ μ`. -/
theorem tendsto_of_hasDHTails_of_toNA_eq_uscSup (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) (sourcePositiveTestCurveToNA (Γs j)))
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.uscSup omega (fun i => sourcePositiveTestCurveToNA (Γs i)) hb)
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμs : ∀ i, HasDHTails (μs i : Measure ℝ) (Γs i)) (hμ : HasDHTails (μ : Measure ℝ) Γ) :
    Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨hb', rfl⟩ := eq_generalSup_of_toNA_eq omega Γs Γ hb hΓ
  exact tendsto_of_hasDHTails_generalSup omega Γs
    (fun i j hij => (sourcePositiveTestCurveToNA_POrder_iff omega (Γs i) (Γs j)).mp (hmono i j hij))
    hb' hμs hμ

end Tails

/-! ### The flag case of `prop:contDH` -/

section Flag

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} [MeasurableSpace F.carrier]
  [BorelSpace F.carrier] {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}
  (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))

/-- `DH(Γ)` of `def:DHm` as a finite Borel measure on `ℝ`. -/
def naFiniteDuistermaatHeckman (Γ : SourcePositiveIModelTestCurve θ) : FiniteMeasure ℝ :=
  ⟨naDuistermaatHeckman (F := F) hbig Γ, naDuistermaatHeckman_finite hbig Γ⟩

/-- `DH(Γ)` has the Duistermaat–Heckman tails of `Γ` (`claude-naplan:dh-tails`). -/
theorem naDuistermaatHeckman_hasDHTails (Γ : SourcePositiveIModelTestCurve θ) :
    HasDHTails (naDuistermaatHeckman (F := F) hbig Γ) Γ where
  isFiniteMeasure := naDuistermaatHeckman_finite hbig Γ
  Ici_eq t := naDuistermaatHeckman_Ici hbig Γ t
  Ioi_max_eq := naDuistermaatHeckman_Ioi_max hbig Γ
  univ_eq := naDuistermaatHeckman_univ hbig Γ

/-- **Source `prop:contDH` (1), flag case.** Let `X` carry a smooth flag, `{θ}` big,
`Γ^i, Γ ∈ PSH^NA(X, θ)_{>0}`, `(Γ^i)` decreasing, `Γ = inf_i Γ^i` (in `PSH^NA(X, θ)`) and
`vol Γ = lim_i vol Γ^i`. Then `DH(Γ^i) ⇀ DH(Γ)`. -/
theorem naDuistermaatHeckman_tendsto_of_decreasingInf (omega : KahlerBackground (m + 1) F.carrier)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j)) (sourcePositiveTestCurveToNA (Γs i)))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.decreasingInf omega (fun i => sourcePositiveTestCurveToNA (Γs i)) ha hb)
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naFiniteDuistermaatHeckman (F := F) hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman (F := F) hbig Γ)) :=
  tendsto_of_hasDHTails_of_toNA_eq_decreasingInf omega Γs Γ ha hb hΓ hvol
    (fun i => naDuistermaatHeckman_hasDHTails hbig (Γs i)) (naDuistermaatHeckman_hasDHTails hbig Γ)

/-- **Source `prop:contDH` (2), flag case.** Let `X` carry a smooth flag, `{θ}` big,
`Γ^i, Γ ∈ PSH^NA(X, θ)_{>0}`, `(Γ^i)` increasing and `Γ = usc-sup_i Γ^i` (in `PSH^NA(X, θ)`).
Then `DH(Γ^i) ⇀ DH(Γ)`. -/
theorem naDuistermaatHeckman_tendsto_of_uscSup (omega : KahlerBackground (m + 1) F.carrier)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) (sourcePositiveTestCurveToNA (Γs j)))
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.uscSup omega (fun i => sourcePositiveTestCurveToNA (Γs i)) hb) :
    Tendsto (fun i => naFiniteDuistermaatHeckman (F := F) hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman (F := F) hbig Γ)) :=
  tendsto_of_hasDHTails_of_toNA_eq_uscSup omega Γs Γ hmono hb hΓ
    (fun i => naDuistermaatHeckman_hasDHTails hbig (Γs i)) (naDuistermaatHeckman_hasDHTails hbig Γ)

/-- `prop:contDH` (1), flag case, for the test-curve infimum (`def:testcurinf`). -/
theorem naDuistermaatHeckman_tendsto_of_testCurveDecreasingInf
    (omega : KahlerBackground (m + 1) F.carrier) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs j).val (Γs i).val)
    (hb : BddBelow (range fun i => (Γs i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (Γs i).val) hb)
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA
        (SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm))))) :
    Tendsto (fun i => naFiniteDuistermaatHeckman (F := F) hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman (F := F) hbig
        (SourcePositiveIModelTestCurve.decreasingInf omega Γs ha hb hm))) :=
  tendsto_of_hasDHTails_decreasingInf omega Γs ha hb hm
    (fun i => naDuistermaatHeckman_hasDHTails hbig (Γs i)) (naDuistermaatHeckman_hasDHTails hbig _)
    hvol

/-- `prop:contDH` (2), flag case, for the test-curve usc supremum (`def:testcurvsupsgeneral`). -/
theorem naDuistermaatHeckman_tendsto_of_testCurveGeneralSup
    (omega : KahlerBackground (m + 1) F.carrier) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γs i).val (Γs j).val)
    (hb : BddAbove (range fun i => (Γs i).val.max)) :
    Tendsto (fun i => naFiniteDuistermaatHeckman (F := F) hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman (F := F) hbig
        (SourcePositiveIModelTestCurve.generalSup omega Γs hb))) :=
  tendsto_of_hasDHTails_generalSup omega Γs hmono hb
    (fun i => naDuistermaatHeckman_hasDHTails hbig (Γs i)) (naDuistermaatHeckman_hasDHTails hbig _)

end Flag

end SGPT.NAPotential.DH
