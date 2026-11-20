import SGPT.Okounkov.TranscendentalWNConv6Inner
import SGPT.Okounkov.TranscendentalWNConv6Choice
import SGPT.Okounkov.TranscendentalWNVolumeGlobalMeasurable

/-!
# Measure control: WN21 Propositions 6.1–6.4 and Corollary 6.5

Blueprint `tok-wn-conv6:liminf` and `tok-wn-conv6:main` (chapter `claude-tok-wn-conv6`), i.e.
`tok-wn:measure-control` (chapter `claude-tok-wn`); source WN21 §6.

* `MCData.liminf_of_volumeDifference` (`tok-wn-conv6:liminf`): for `δ > 0`, eventually
  `vol(ξ) ≤ ∫_ℂ I_k dω_k + δ`.  Writing `MA_k = ⟨(θ̃ + ddᶜu_k)^{n+1}⟩`,
  `vol(β) = MA_k(R_ε) + MA_k(O_ε)` (`diagonalPotentialMass_envelope`),
  `MA_k(O_ε) ≤ vol(β - {X₀}) + η` eventually (`eventually_envelopeMeasure_outer_le`),
  `MA_k(R_ε) ≤ |θ̃^{n+1}|(R_ε \ X₀) + (n + 1) ∫ I_k dω_k` (`envelopeMeasure_inner_le`),
  `vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)` (`tok-wn:formula-volume`), and
  `|θ̃^{n+1}|(R_ε \ X₀) → 0` as `ε → 0` (the sets decrease to `∅`).
* `measureControl_of_volumeDifference`: `DeformationVolumeDifferenceStatement F →
  MeasureControlStatement F`; `measureControl`: `MeasureControlStatement F`, unconditionally,
  with WN-VF2's `deformationVolumeDifference`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Okounkov.TranscendentalMain

/-- The measure of a smooth top form is finite. -/
theorem topFormMeasure_univ_ne_top {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] (w : KahlerBackground N M) (Φ : SmoothRealForm N M (2 * N)) :
    topFormMeasure w Φ univ ≠ ⊤ := by
  rw [topFormMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rcases isEmpty_or_nonempty M with hM | hM
  · simp [lintegral_of_isEmpty]
  have hc := continuous_topRatio w.isKahler.1 Φ
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (topRatio w.form.val Φ x₀) *
      kahlerVolume w univ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (kahlerVolume w) univ)) ?_
  rw [← lintegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hx₀ (mem_univ x))

namespace MCData

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} {𝒳 : Type u} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
  (D : MCData F 𝒳) [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]

omit [ConnectedSpace 𝒳] in
/-- `|θ̃^{n+1}|(R_ε \ X₀) → 0`: eventually small for `ε = 1/(j+1)`. -/
theorem exists_totalVar_small (w : KahlerBackground (m + 1 + 1) 𝒳) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ D.totalVar w ((D.outer ε)ᶜ \ centralFibre F D.μ) ≤ η := by
  set S : ℕ → Set 𝒳 := fun j => (D.outer (1 / ((j : ℝ) + 1)))ᶜ \ centralFibre F D.μ with hS
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    ((D.isOpen_outer _).isClosed_compl.measurableSet).diff D.isClosed_centralFibre.measurableSet
  have hanti : Antitone S := by
    intro i j hij z hz
    refine ⟨fun hO => hz.1 ?_, hz.2⟩
    have hO' : (1 / ((i : ℝ) + 1)) ^ 2 / (1 + (1 / ((i : ℝ) + 1)) ^ 2) < D.weight0 z := hO
    show (1 / ((j : ℝ) + 1)) ^ 2 / (1 + (1 / ((j : ℝ) + 1)) ^ 2) < D.weight0 z
    refine lt_of_le_of_lt ?_ hO'
    have hij' : (1 / ((j : ℝ) + 1)) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    have h2 : (1 / ((j : ℝ) + 1)) ^ 2 ≤ (1 / ((i : ℝ) + 1)) ^ 2 := by gcongr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hempty : (⋂ j, S j) = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hz : z ∈ centralFibre F D.μ
    · exact ⟨0, fun h => h.2 hz⟩
    · have hpos := D.weight0_pos_of_notMem hz
      -- choose `j` with `(1/(j+1))² < N₀(z)`
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (Real.sqrt_pos.mpr hpos)
      refine ⟨j, fun h => h.1 ?_⟩
      show (1 / ((j : ℝ) + 1)) ^ 2 / (1 + (1 / ((j : ℝ) + 1)) ^ 2) < D.weight0 z
      have h1 : (1 / ((j : ℝ) + 1)) ^ 2 < D.weight0 z := by
        have := pow_lt_pow_left₀ hj (by positivity) (two_ne_zero)
        rwa [Real.sq_sqrt hpos.le] at this
      calc (1 / ((j : ℝ) + 1)) ^ 2 / (1 + (1 / ((j : ℝ) + 1)) ^ 2) ≤ (1 / ((j : ℝ) + 1)) ^ 2 :=
            div_le_self (by positivity) (by nlinarith [sq_nonneg (1 / ((j : ℝ) + 1))])
        _ < D.weight0 z := h1
  have hfin : D.totalVar w (S 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ _))
    rw [totalVar, Measure.add_apply]
    exact ENNReal.add_ne_top.mpr ⟨topFormMeasure_univ_ne_top w _, topFormMeasure_univ_ne_top w _⟩
  have hlim := tendsto_measure_iInter_atTop (μ := D.totalVar w)
    (fun j => (hSm j).nullMeasurableSet) hanti ⟨0, hfin⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.mpr hη))).exists
  exact ⟨1 / ((j : ℝ) + 1), by positivity, hj.le⟩

/-- **`tok-wn-conv6:liminf`** (WN21 Propositions 6.3–6.4): given
`vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)`, for `δ > 0`, eventually `vol(ξ) ≤ ∫_ℂ I_k dω_k + δ`. -/
theorem liminf_of_volumeDifference
    (hdiff : (SGPT.PSH.VariableComplexAtlas.sourceClassVolume
        (RealBottChern.ofRepresentative D.form)).toReal -
      (SGPT.PSH.VariableComplexAtlas.sourceClassVolume
        (RealBottChern.ofRepresentative D.formPrev)).toReal = ((m + 2 : ℕ) : ℝ) * D.vol)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∀ᶠ k in atTop, ENNReal.ofReal D.vol ≤ ∫⁻ τ, D.fibreMass k τ ∂cutoffLineMeasure D.χ k + δ := by
  by_cases hδt : δ = ⊤
  · exact Eventually.of_forall fun k => by rw [hδt, add_top]; exact le_top
  set w := Classical.choice D.nonempty_kahler
  set Nn : ℝ≥0∞ := ((m + 1 + 1 : ℕ) : ℝ≥0∞) with hNn
  have hN0 : Nn ≠ 0 := by simp [hNn]
  have hNt : Nn ≠ ⊤ := ENNReal.natCast_ne_top _
  set B := SGPT.PSH.VariableComplexAtlas.sourceClassVolume (RealBottChern.ofRepresentative D.form)
  set B' := SGPT.PSH.VariableComplexAtlas.sourceClassVolume
    (RealBottChern.ofRepresentative D.formPrev)
  have hBt : B ≠ ⊤ := (TranscendentalVolumeConcavity.sourceClassVolume_lt_top w _).ne
  have hB't : B' ≠ ⊤ := (TranscendentalVolumeConcavity.sourceClassVolume_lt_top w _).ne
  have hvol0 : 0 ≤ D.vol := ENNReal.toReal_nonneg
  -- `B = B' + (n + 1) vol(ξ)` in `ℝ≥0∞`
  have hBB : B = B' + Nn * ENNReal.ofReal D.vol := by
    rw [← ENNReal.ofReal_toReal hBt, ← ENNReal.ofReal_toReal hB't, hNn, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add ENNReal.toReal_nonneg
        (by positivity)]
    congr 1
    have : ((m + 1 + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := rfl
    rw [this, ← hdiff]
    ring
  -- choose `ε` and `η`
  have hNδ : Nn * δ / 2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨mul_ne_zero hN0 hδ, ENNReal.ofNat_ne_top⟩
  obtain ⟨ε, hε, hTV⟩ := D.exists_totalVar_small w hNδ
  filter_upwards [D.eventually_envelopeMeasure_outer_le hε hNδ] with k hk
  set MA := diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
  have hin := D.envelopeMeasure_inner_le w hε k
  have htot : MA univ = B := D.diagonalPotentialMass_envelope k
  have hsplit : MA (D.outer ε) + MA (D.outer ε)ᶜ = B := by
    rw [measure_add_measure_compl (D.isOpen_outer ε).measurableSet, htot]
  set J := ∫⁻ τ, D.fibreMass k τ ∂cutoffLineMeasure D.χ k
  -- `B' + N V ≤ B' + N (J + δ)`
  have hmain : B' + Nn * ENNReal.ofReal D.vol ≤ B' + Nn * (J + δ) := by
    rw [← hBB, ← hsplit]
    calc MA (D.outer ε) + MA (D.outer ε)ᶜ ≤ (B' + Nn * δ / 2) + (Nn * δ / 2 + Nn * J) :=
          add_le_add hk (hin.trans (add_le_add hTV le_rfl))
      _ = B' + Nn * (J + δ) := by
          rw [mul_add, add_assoc, ← add_assoc (Nn * δ / 2), ENNReal.add_halves, add_comm (Nn * δ)]
  have h2 := (ENNReal.add_le_add_iff_left hB't).mp hmain
  exact (ENNReal.mul_le_mul_iff_right hN0 hNt).mp h2

end MCData

/-- **`tok-wn:measure-control`, conditional form**: the volume difference
`vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)` (WN21 Corollary 4.7) implies the integrated bound. -/
theorem measureControlLiminf_of_volumeDifference {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (hdiff : DeformationVolumeDifferenceStatement F) : MeasureControlLiminfStatement F := by
  intro 𝒳 _ _ _ D δ hδ
  have := D.compactSpace
  have := D.connectedSpace
  let : MeasurableSpace 𝒳 := borel 𝒳
  have : BorelSpace 𝒳 := ⟨rfl⟩
  have h := hdiff D.E D.hE D.hE0 𝒳 D.μ D.hμ D.Eℰ D.hEℰ D.θ D.b D.c D.hc D.hcb D.hξ D.hξc
  exact D.liminf_of_volumeDifference h hδ

theorem measureControl_of_volumeDifference {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (hdiff : DeformationVolumeDifferenceStatement F) : MeasureControlStatement F :=
  measureControl_of_liminf F (measureControlLiminf_of_volumeDifference F hdiff)

/-- **`tok-wn:measure-control`** (WN21 §6, Corollary 6.5), unconditionally. -/
theorem measureControl {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) : MeasureControlStatement F :=
  measureControl_of_volumeDifference F (deformationVolumeDifference F)

end SGPT.Okounkov.TranscendentalWN
