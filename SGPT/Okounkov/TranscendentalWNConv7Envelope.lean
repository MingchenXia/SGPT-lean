import SGPT.Okounkov.TranscendentalWNConv7Statement
import SGPT.Okounkov.TranscendentalWNRegContact
import SGPT.Okounkov.TranscendentalWNEnvelopeContact
import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior
import SGPT.Foundations.Analysis.Pending.StokesRegularLocusIdentity
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.BlowupBigPullback

/-!
# Envelopes with prescribed singularities and the fibrewise contact estimate

Blueprint `claude-tok-wn-conv7`, nodes `tok-wn-conv7:prescribed-envelope` and
`tok-wn-conv7:fibre-contact`; source WN21 §7 (the envelopes `v_k` and the estimate (MAest)
before the proof of the hard inequality of Theorem 1.7).

* `le_prescribedEnvelope`, `prescribedEnvelope_le`, `isThetaPshPotential_prescribedEnvelope`,
  `sub_one_le_prescribedEnvelope`: the envelope `P_Θ[ψ](g)` dominates its competitors, lies below a
  continuous obstacle, is `Θ`-psh when it has a competitor, and `P_Θ[ψ](g) - 1 ≤ P_Θ[ψ](g')` when
  `g - 1 ≤ g'` (WN21 Proposition 7.2: `v_k + k` increases in `k`).
* `topRatio_le_of_contact`: at a contact point of a `Θ₀`-psh `u ≤ c` (`c` constant) the density of
  `Θ₀ⁿ` is at most that of `Θⁿ` for every `Θ ≥ Θ₀` (contact positivity
  `coefficientSemipositive_of_contact` and slot monotonicity of mixed densities).
* `positiveTopMeasure_contact_le` (**MAest**, WN21 §7): let `s : V → M` be holomorphic with
  `g ∘ s = c` constant (a fibre `X_τ`, on which `g_k` is constant), `u ≤ v ≤ g` with `u`
  `Θ₀`-psh and `v ∘ s` `s^*Θ`-psh, `Θ - Θ₀ ≥ 0`.  Then
  `1_{s⁻¹{u = g}} (s^*Θ₀)ⁿ ≤ ⟨(s^*Θ + dd^c (v ∘ s))ⁿ⟩` on `s⁻¹{v = g}`; with `u = u_k`, `v = v_k`:
  `∫_{X_τ ∩ D_k} θ̃ⁿ ≤ ∫_{X_τ ∩ D'_k} ⟨((θ̃ + εη' + dd^c v_k)|_{X_τ})ⁿ⟩`.  The proof uses the
  Di Nezza--Trapani lower bound for constant obstacles (`dntConstantObstacleStatement`, package
  WN-REG) on the compact connected manifold `V`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

/-! ### The envelope `P_Θ[ψ](g)` -/

section Prescribed

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] {Θ : ClosedRealOneOneForm N M} {g g' : M → ℝ} {ψ : M → EReal}

/-- Every competitor lies below the envelope. -/
theorem le_prescribedEnvelope {v : M → EReal} (hv : v ∈ prescribedCompetitors Θ g ψ) :
    v ≤ prescribedEnvelope Θ g ψ := fun z =>
  (le_iSup (fun w : prescribedCompetitors Θ g ψ => w.1 z) ⟨v, hv⟩).trans
    (le_uscRegularization (fun y => ⨆ w : prescribedCompetitors Θ g ψ, w.1 y) z)

/-- The envelope lies below a continuous obstacle. -/
theorem prescribedEnvelope_le (hg : Continuous g) (z : M) :
    prescribedEnvelope Θ g ψ z ≤ (g z : EReal) :=
  uscRegularization_le (continuous_coe_real_ereal.comp hg).upperSemicontinuous
    (fun y => iSup_le fun w => w.2.2.1 y) z

/-- The envelope is `Θ`-psh as soon as it has a competitor (the obstacle being bounded above). -/
theorem isThetaPshPotential_prescribedEnvelope (hne : (prescribedCompetitors Θ g ψ).Nonempty)
    {B : ℝ} (hB : ∀ z, g z ≤ B) : IsThetaPshPotential Θ.val (prescribedEnvelope Θ g ψ) := by
  obtain ⟨v, hv⟩ := hne
  have : Nonempty (prescribedCompetitors Θ g ψ) := ⟨⟨v, hv⟩⟩
  exact SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    (fun w : prescribedCompetitors Θ g ψ => w.2.1) (C := B)
    fun w z => (w.2.2.1 z).trans (EReal.coe_le_coe_iff.mpr (hB z))

/-- Competitors move down by one when the obstacle does. -/
theorem sub_one_mem_prescribedCompetitors (hgg : ∀ z, g z - 1 ≤ g' z) {v : M → EReal}
    (hv : v ∈ prescribedCompetitors Θ g ψ) :
    (fun z => v z + ((-1 : ℝ) : EReal)) ∈ prescribedCompetitors Θ g' ψ := by
  refine ⟨hv.1.add_const (-1), fun z => ?_, ?_⟩
  · calc v z + ((-1 : ℝ) : EReal) ≤ (g z : EReal) + ((-1 : ℝ) : EReal) :=
          add_le_add (hv.2.1 z) le_rfl
      _ = ((g z - 1 : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
      _ ≤ (g' z : EReal) := EReal.coe_le_coe_iff.mpr (hgg z)
  · obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hv.2.2
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, fun z => ?_⟩
    calc v z + ((-1 : ℝ) : EReal) ≤ v z + 0 := add_le_add le_rfl (by norm_num)
      _ = v z := add_zero _
      _ ≤ ψ z + (C : EReal) := hC z

/-- **WN21 Proposition 7.2** (the monotonicity behind `v_k + k ↗`): if `g - 1 ≤ g'`, then
`P_Θ[ψ](g) - 1 ≤ P_Θ[ψ](g')`. -/
theorem sub_one_le_prescribedEnvelope (hgg : ∀ z, g z - 1 ≤ g' z) (z : M) :
    prescribedEnvelope Θ g ψ z + ((-1 : ℝ) : EReal) ≤ prescribedEnvelope Θ g' ψ z := by
  unfold prescribedEnvelope
  rw [← congrFun (uscRegularization_add_coe_const
    (fun y => ⨆ w : prescribedCompetitors Θ g ψ, w.1 y) (-1)) z]
  refine uscRegularization_mono (fun y => ?_) z
  rw [← iSup_add_coe]
  exact iSup_le fun w =>
    le_iSup (fun w' : prescribedCompetitors Θ g' ψ => w'.1 y)
      ⟨_, sub_one_mem_prescribedCompetitors hgg w.2⟩

end Prescribed

/-! ### The fibrewise contact estimate (MAest) -/

section Contact

variable {k : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V]

/-- `dd^c` of a constant vanishes. -/
theorem ddcClosedForm_const (c : ℝ) :
    ddcClosedForm (n := k) (fun _ : V => c) (chartSmooth_const c) = 0 := by
  apply ClosedRealOneOneForm.ext
  intro e z
  exact GlobalPotentialTransforms.smoothDDC_const c z

/-- **Positivity at contact points with a constant obstacle**: if `u` is `θ`-psh, `u ≤ c` and
`u x = c`, then `θ` is semipositive at `x`, in every chart. -/
theorem coefficientSemipositive_of_contact_const (θ : ClosedRealOneOneForm k V) {u : V → EReal}
    (hu : ThetaPlurisubharmonic θ.val u) {c : ℝ} (hle : ∀ y, u y ≤ (c : EReal)) {x : V}
    (hx : u x = (c : EReal)) (e : ComplexChart k V) (hxe : x ∈ e.val.source) :
    CoefficientSemipositive (θ.val.coeff e (e.val x)) := by
  have h := coefficientSemipositive_of_contact θ hu (chartSmooth_const c)
    (Eventually.of_forall hle) hx e hxe
  rwa [ddcClosedForm_const, add_zero] at h

/-- **The densities at a contact point**: if `u` is `θ₀`-psh with `u ≤ c` and `u x = c`, and
`θ - θ₀` is semipositive, then `θ₀ⁿ/ωⁿ ≤ θⁿ/ωⁿ` at `x`. -/
theorem topRatio_le_of_contact (w : KahlerBackground k V) {θ₀ θ : ClosedRealOneOneForm k V}
    (hθ : (θ - θ₀).val.IsSemipositive) {u : V → EReal} (hu : ThetaPlurisubharmonic θ₀.val u)
    {c : ℝ} (hle : ∀ y, u y ≤ (c : EReal)) {x : V} (hx : u x = (c : EReal)) :
    topRatio w.form.val (formPow θ₀.val k) x ≤ topRatio w.form.val (formPow θ.val k) x := by
  simp only [topRatio, chartRatio]
  set e := complexChartAt (n := k) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz := e.val.map_source hxe
  have hA : IsSemipositiveOneOne (θ₀.val.coeff e (e.val x)) :=
    ⟨θ₀.2.2 e _ hz, coefficientSemipositive_of_contact_const θ₀ hu hle hx e hxe⟩
  have hsub : (θ - θ₀).val.coeff e (e.val x) =
      θ.val.coeff e (e.val x) - θ₀.val.coeff e (e.val x) :=
    BlowupBigPullback.coeff_sub θ θ₀ e (e.val x)
  have hBA : IsSemipositiveOneOne (θ.val.coeff e (e.val x) - θ₀.val.coeff e (e.val x)) := by
    rw [← hsub]
    exact ⟨(θ - θ₀).2.2 e _ hz, hθ e _ hz⟩
  have hmono := StokesRegularLocusIdentity.actualMixedTopDensity_mono
    (A := fun _ : Fin k => θ₀.val.coeff e (e.val x))
    (B := fun _ : Fin k => θ.val.coeff e (e.val x)) (fun _ => hA) (fun _ => hBA)
  rw [formPow_coeff θ₀.val e (e.val x) k, formPow_coeff θ.val e (e.val x) k,
    topDensity_formPower, topDensity_formPower,
    ← actualMixedTopDensity_const, ← actualMixedTopDensity_const]
  exact div_le_div_of_nonneg_right hmono (topDensity_formPow_pos w.isKahler.1 hz).le

variable [CompactSpace V] [ConnectedSpace V] [MeasurableSpace V] [BorelSpace V]

/-- **MAest** (WN21 §7, the estimate before the proof of the hard inequality of Theorem 1.7;
blueprint `tok-wn-conv7:fibre-contact`).  Let `s : V → M` be holomorphic from a compact connected
manifold with a Kähler form `w`, `g` an obstacle on `M` that is constant (`= c`) on `s(V)`, `u` a
`Θ₀`-psh function and `v` a function with `u ≤ v ≤ g`, `v ∘ s` an `s^*Θ`-psh potential, and
`Θ - Θ₀` semipositive.  Then the measure `(s^*Θ₀)ⁿ` of `s⁻¹{u = g}` is at most the non-pluripolar
Monge--Ampère measure `⟨(s^*Θ + dd^c (v ∘ s))ⁿ⟩` of `s⁻¹{v = g}`. -/
theorem positiveTopMeasure_contact_le (w : KahlerBackground k V) {N : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M]
    {Θ₀ Θ : ClosedRealOneOneForm N M} (hΘ : (Θ - Θ₀).val.IsSemipositive) {s : V → M}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ s) {g : M → ℝ} {c : ℝ}
    (hgs : ∀ x, g (s x) = c) {u v : M → EReal} (hu : ThetaPlurisubharmonic Θ₀.val u)
    (hug : ∀ z, u z ≤ (g z : EReal)) (huv : ∀ z, u z ≤ v z) (hvg : ∀ z, v z ≤ (g z : EReal))
    (hvs : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val (fun x => v (s x))) :
    TranscendentalWNReg.positiveTopMeasure w (ClosedRealOneOneForm.pullback hs Θ₀)
        (s ⁻¹' {z | u z = (g z : EReal)}) ≤
      DiagonalMass.diagonalPotentialMeasure (ClosedRealOneOneForm.pullback hs Θ)
        (fun x => v (s x)) hvs (s ⁻¹' {z | v z = (g z : EReal)}) := by
  set A := s ⁻¹' {z | u z = (g z : EReal)} with hAdef
  set B := {x | v (s x) = (c : EReal)} with hBdef
  have hus : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hs Θ₀).val
      (fun x => u (s x)) := GlobalPotentialPullback.thetaPlurisubharmonic_comp hs hu
  have husc : ∀ x, u (s x) ≤ (c : EReal) := fun x => (hug (s x)).trans (by rw [hgs])
  -- `A = {u ∘ s ≥ c}` is closed
  have hAeq : A = (fun x => u (s x)) ⁻¹' Ici (c : EReal) := by
    ext x
    simp only [hAdef, mem_preimage, mem_ofPred_eq, mem_Ici, hgs]
    exact ⟨fun h => h.ge, fun h => le_antisymm (husc x) h⟩
  have hAc : IsClosed A := by
    rw [hAeq]
    exact hus.quasiPlurisubharmonic.upperSemicontinuous.isClosed_preimage _
  have hAm : MeasurableSet A := hAc.measurableSet
  -- `A ⊆ B = s⁻¹{v = g}`
  have hAB : A ⊆ B := by
    intro x hx
    have hx' : u (s x) = (c : EReal) := by rw [← hgs x]; exact hx
    exact le_antisymm ((hvg (s x)).trans (by rw [hgs])) (hx' ▸ huv (s x))
  have hBeq : s ⁻¹' {z | v z = (g z : EReal)} = B := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hBdef, hgs]
  -- the densities
  have hpull : ((ClosedRealOneOneForm.pullback hs Θ) -
      ClosedRealOneOneForm.pullback hs Θ₀).val.IsSemipositive := by
    rw [← BoucksomResolutionStep.pullback_sub]
    exact ClosedRealOneOneForm.pullback_isSemipositive hs hΘ
  have hdens : TranscendentalWNReg.positiveTopMeasure w (ClosedRealOneOneForm.pullback hs Θ₀) A ≤
      TranscendentalWNReg.positiveTopMeasure w (ClosedRealOneOneForm.pullback hs Θ) A := by
    unfold TranscendentalWNReg.positiveTopMeasure
    rw [withDensity_apply _ hAm, withDensity_apply _ hAm]
    refine setLIntegral_mono' hAm fun x hx => ENNReal.ofReal_le_ofReal ?_
    have hx' : u (s x) = (c : EReal) := by rw [← hgs x]; exact hx
    exact topRatio_le_of_contact w hpull hus husc hx'
  -- the Di Nezza--Trapani lower bound on `s^*Θ`
  have hDNT := TranscendentalWNReg.dntConstantObstacleStatement k V w
    (ClosedRealOneOneForm.pullback hs Θ) (fun x => v (s x)) hvs c
    (fun x => (hvg (s x)).trans (by rw [hgs]))
  calc TranscendentalWNReg.positiveTopMeasure w (ClosedRealOneOneForm.pullback hs Θ₀) A
      ≤ TranscendentalWNReg.positiveTopMeasure w (ClosedRealOneOneForm.pullback hs Θ) A := hdens
    _ = (TranscendentalWNReg.positiveTopMeasure w (ClosedRealOneOneForm.pullback hs Θ)).restrict
          B A := by rw [Measure.restrict_apply hAm, inter_eq_left.mpr hAB]
    _ ≤ DiagonalMass.diagonalPotentialMeasure (ClosedRealOneOneForm.pullback hs Θ)
          (fun x => v (s x)) hvs A := Measure.le_iff'.mp hDNT A
    _ ≤ DiagonalMass.diagonalPotentialMeasure (ClosedRealOneOneForm.pullback hs Θ)
          (fun x => v (s x)) hvs (s ⁻¹' {z | v z = (g z : EReal)}) :=
        measure_mono (hBeq ▸ hAB)

end Contact

end SGPT.Okounkov.TranscendentalWN
