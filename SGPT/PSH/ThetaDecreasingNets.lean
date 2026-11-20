import SGPT.PSH.CompactAntitoneSupremum
import SGPT.PSH.LocalL1
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord

set_option autoImplicit false

/-! The three complete chosen proofs precede this source. The original
theta form, functions, charts and Haar measures are retained. Compact
connected nondegeneracy is manufactured from the actual lower supremum
bound. Existing directed PSH and local L1 producers are reused. -/

noncomputable section

namespace SGPT.PSH

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

variable {n : ℕ} {M I : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- The genuine native theta criterion for an arbitrary directed infimum;
no nondegeneracy or compactness is assumed for this raw assertion. -/
theorem thetaPlurisubharmonic_iInf_of_antitone
    {theta : SmoothRealForm n M 2} {u : I → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic theta (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) :
    ThetaPlurisubharmonic theta (fun x ↦ ⨅ i, u i x) := by
  classical
  intro e z hz
  obtain ⟨W, rho, hzW, hrho, _⟩ := hu (Classical.arbitrary I) e z hz
  refine ⟨W, rho, hzW, hrho, ?_⟩
  have hdisc (i : I) : DiscPshOn
      (fun y ↦ chartFunction (u i) e y + (rho y : EReal)) W :=
    (plurisubharmonicOn_corrected_of_thetaPlurisubharmonic (hu i) e hrho).discPshOn
  have hantiW : ∀ y ∈ W,
      Antitone (fun i ↦ chartFunction (u i) e y + (rho y : EReal)) := by
    intro y _ i j hij
    exact add_le_add (hanti (e.val.symm y) hij) le_rfl
  have hlim := (discPshOn_iInf_of_antitone hdisc hantiW).plurisubharmonicOn hrho.1
  have heq : (fun y ↦ ⨅ i, (chartFunction (u i) e y + (rho y : EReal))) =
      (fun y ↦ chartFunction (fun x ↦ ⨅ i, u i x) e y + (rho y : EReal)) := by
    funext y
    rw [iInf_add_coe]
    rfl
  exact heq ▸ hlim

/-- Actual compact USC manufactures a non-bottom point. The existing genuine
connected theta identity principle produces the original potential predicate. -/
theorem isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    [CompactSpace M] [ConnectedSpace M]
    {theta : SmoothRealForm n M 2} {u : I → M → EReal}
    (hu : ∀ i, IsThetaPshPotential theta (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) (a : ℝ)
    (ha : ∀ i, (a : EReal) ≤ ⨆ x, u i x) :
    IsThetaPshPotential theta (fun x ↦ ⨅ i, u i x) ∧
      Tendsto (fun i ↦ ⨆ x, u i x) atTop (𝓝 (⨆ x, ⨅ i, u i x)) := by
  have husc (i : I) : UpperSemicontinuous (u i) :=
    (hu i).1.quasiPlurisubharmonic.upperSemicontinuous
  have hv := thetaPlurisubharmonic_iInf_of_antitone (fun i ↦ (hu i).1) hanti
  have hn := exists_iInf_ne_bot_of_compact_antitone_iSup_lower_bound u husc hanti a ha
  exact ⟨SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
    hv hn, tendsto_iSup_of_compact_antitone u husc hanti⟩

/-- Genuine local L1 convergence of the unchanged original chart functions.
Common smooth correction is cancelled only on individually manufactured
almost-everywhere finite sets, never on an uncountable simultaneous set. -/
theorem tendsto_theta_chartLocalL1_iInf_of_compact_antitone_iSup_lower_bound
    [CompactSpace M] [ConnectedSpace M]
    {theta : SmoothRealForm n M 2} {u : I → M → EReal}
    (hu : ∀ i, IsThetaPshPotential theta (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) (a : ℝ)
    (ha : ∀ i, (a : EReal) ≤ ⨆ x, u i x)
    (e : ComplexChart n M) {W K : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta e W rho)
    (hconn : IsPreconnected W) (hW : W.Nonempty)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (hK : IsCompact K) (hKW : K ⊆ W) :
    Tendsto (fun i ↦ ∫ z in K,
      ‖(chartFunction (u i) e z).toReal -
        (chartFunction (fun x ↦ ⨅ j, u j x) e z).toReal‖ ∂μ) atTop (𝓝 0) := by
  let v : M → EReal := fun x ↦ ⨅ i, u i x
  let f : I → ComplexModel n → EReal :=
    fun i z ↦ chartFunction (u i) e z + (rho z : EReal)
  let g : ComplexModel n → EReal := fun z ↦ chartFunction v e z + (rho z : EReal)
  have hv : IsThetaPshPotential theta v :=
    (isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound hu hanti a ha).1
  obtain ⟨z₀, hz₀⟩ := hW
  have hfi (i : I) : PSHOn (f i) W := by
    refine ⟨(plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      (hu i).1 e hrho).discPshOn, ?_⟩
    obtain ⟨z, hz, hne⟩ := (hu i).2.exists_chart_ne_bot e hrho.1 hrho.2.1 hz₀
    exact ⟨z, hz, EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩⟩
  have hg : PSHOn g W := by
    refine ⟨(plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      hv.1 e hrho).discPshOn, ?_⟩
    obtain ⟨z, hz, hne⟩ := hv.2.exists_chart_ne_bot e hrho.1 hrho.2.1 hz₀
    exact ⟨z, hz, EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩⟩
  have heq (z : ComplexModel n) : (⨅ i, f i z) = g z := by
    dsimp only [f, g, v, chartFunction]
    exact iInf_add_coe (fun i ↦ u i (e.val.symm z)) (rho z)
  have hantiF : ∀ z ∈ W, Antitone (fun i ↦ f i z) := by
    intro z _ i j hij
    exact add_le_add (hanti (e.val.symm z) hij) le_rfl
  have hn : ∃ z ∈ W, (⨅ i, f i z) ≠ ⊥ := by
    obtain ⟨z, hz, hne⟩ := hg.nontrivial
    exact ⟨z, hz, by rwa [heq]⟩
  have hlim := tendsto_localL1_iInf hfi hrho.1 hconn hantiF hn μ hK hKW
  have hfinG := hg.ae_finite_on_compact hrho.1 hconn μ hK hKW
  have hsame (i : I) :
      (∫ z in K, ‖(f i z).toReal - (⨅ j, f j z).toReal‖ ∂μ) =
      (∫ z in K, ‖(chartFunction (u i) e z).toReal -
        (chartFunction v e z).toReal‖ ∂μ) := by
    apply integral_congr_ae
    filter_upwards [(hfi i).ae_finite_on_compact hrho.1 hconn μ hK hKW,
      hfinG] with z hzi hzg
    rw [heq]
    have hiTop : chartFunction (u i) e z ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp hzi.1
    have hiBot : chartFunction (u i) e z ≠ ⊥ := (EReal.add_ne_bot_iff.mp hzi.2).1
    have hvTop : chartFunction v e z ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mp hzg.1
    have hvBot : chartFunction v e z ≠ ⊥ := (EReal.add_ne_bot_iff.mp hzg.2).1
    dsimp only [f, g]
    rw [EReal.toReal_add hiTop hiBot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_add hvTop hvBot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    congr 1
    ring
  have hfun : (fun i ↦ ∫ z in K, ‖(f i z).toReal - (⨅ j, f j z).toReal‖ ∂μ) =
      (fun i ↦ ∫ z in K, ‖(chartFunction (u i) e z).toReal -
        (chartFunction v e z).toReal‖ ∂μ) := funext hsame
  rw [hfun] at hlim
  exact hlim

end SGPT.PSH
