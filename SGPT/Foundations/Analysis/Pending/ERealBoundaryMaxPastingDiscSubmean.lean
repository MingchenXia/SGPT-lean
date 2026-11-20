import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingHarmonic
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

set_option autoImplicit false

/-! # Actual circle majorants and actual deficit submean for boundary-pasted extended-real functions -/

open InnerProductSpace Metric Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingDiscSubmean

open ERealBoundaryMaxPastingTopology ERealBoundaryMaxPastingHarmonic FirstPass

noncomputable section

/-- Actual Fourier harmonic approximation and actual supported comparison bound the pasted center by every genuine continuous circle majorant. -/
theorem gluedMax_le_circleAverage
    {Ω D : Set ℂ} {v u : ℂ → EReal} (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hboundary : BoundaryDominatedOn Ω D v u)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hKΩ : closedBall c R ⊆ Ω)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgu : ∀ z ∈ sphere c R, gluedMax D v u z ≤ (g z : EReal)) :
    gluedMax D v u c ≤ ((Real.circleAverage g c R : ℝ) : EReal) := by
  let G : ℂ → EReal := gluedMax D v u
  have hcΩ : c ∈ Ω := hKΩ (mem_closedBall_self hR.le)
  have hctop : G c ≠ ⊤ :=
    gluedMax_ne_top (fun z hz => (hu z hz).ne_top) (fun z hz => (hv z hz).ne_top) c hcΩ
  by_cases hcbot : G c = ⊥
  · change G c ≤ _
    simp [hcbot]
  change G c ≤ _
  rw [← EReal.coe_toReal hctop hcbot, EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  obtain ⟨h, hh, happ⟩ := exists_global_harmonic_uniformApproxOn_sphere c hR hg.continuousOn hε
  have hhplus : HarmonicOnNhd (fun z => h z + ε) univ :=
    hh.add (harmonicOnNhd_const ε)
  have hsplus : ∀ z ∈ sphere c R, G z ≤ ((h z + ε : ℝ) : EReal) := by
    intro z hz
    refine (hgu z hz).trans (EReal.coe_le_coe_iff.mpr ?_)
    have := (abs_lt.mp (happ z hz)).1
    linarith
  have hcenter : G c ≤ ((h c + ε : ℝ) : EReal) :=
    gluedMax_le_harmonic_on_closedBall hD hu hv hboundary hhplus hR hKΩ hsplus c
      (mem_closedBall_self hR.le)
  have hhclosed : HarmonicOnNhd h (closedBall c |R|) := hh.mono (subset_univ _)
  have hcircle_h : CircleIntegrable h c R :=
    (hhclosed.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hcircle_g : CircleIntegrable g c R := hg.continuousOn.circleIntegrable'
  have hcircle_const : CircleIntegrable (fun _ : ℂ => ε) c R := circleIntegrable_const ε c R
  have havg : h c ≤ Real.circleAverage g c R + ε := by
    have hmono : Real.circleAverage h c R ≤
        Real.circleAverage (fun z => g z + ε) c R := by
      apply Real.circleAverage_mono hcircle_h (hcircle_g.add hcircle_const)
      intro z hz
      have := (abs_lt.mp (happ z (by simpa [abs_of_pos hR] using hz))).2
      change h z ≤ g z + ε
      linarith
    rw [hhclosed.circleAverage_eq, Real.circleAverage_fun_add hcircle_g hcircle_const,
      Real.circleAverage_const] at hmono
    exact hmono
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal hctop hcbot]
  refine hcenter.trans (EReal.coe_le_coe_iff.mpr ?_)
  dsimp [ε] at havg ⊢
  linarith

/-- Actual compact USC majorants and genuine nonnegative monotone convergence produce the full pasted circle deficit submean, retaining poles. -/
theorem gluedMax_circleSubmean
    {Ω D : Set ℂ} {v u : ℂ → EReal} (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hboundary : BoundaryDominatedOn Ω D v u)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hKΩ : closedBall c R ⊆ Ω)
    (hC : ∀ z ∈ closedBall c R, gluedMax D v u z ≤ (C : EReal)) :
    circleDeficit (gluedMax D v u) c 1 R C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - gluedMax D v u c).toENNReal := by
  let G : ℂ → EReal := gluedMax D v u
  let K : Set ℂ := sphere c R
  have hK : IsCompact K := isCompact_sphere c R
  have hKne : K.Nonempty := by
    let z : ℂ := c + (R : ℂ)
    exact ⟨z, by simp [K, z, abs_of_pos hR]⟩
  have hKΩ' : K ⊆ Ω := fun _ hz => hKΩ (sphere_subset_closedBall hz)
  have husc : UpperSemicontinuousOn G K :=
    (upperSemicontinuousOn_gluedMax hD hu.upperSemicontinuousOn hv.upperSemicontinuousOn
      hboundary).mono hKΩ'
  have htop : ∀ z ∈ K, G z ≠ ⊤ := fun z hz =>
    gluedMax_ne_top (fun z hz => (hu z hz).ne_top) (fun z hz => (hv z hz).ne_top) z (hKΩ' hz)
  have hCK : ∀ z ∈ K, G z ≤ (C : EReal) := fun z hz => hC z (sphere_subset_closedBall hz)
  let g : ℕ → ℂ → ℝ := fun j => uscSupConvolution K G C j
  have hg : ∀ j, Continuous (g j) := fun j =>
    continuous_uscSupConvolution hKne htop hCK j
  have hgu : ∀ j z, z ∈ K → G z ≤ (g j z : EReal) := fun j z hz =>
    le_coe_uscSupConvolution hKne htop hCK j hz
  have hgC : ∀ j z, g j z ≤ C := fun j z => uscSupConvolution_le hKne htop hCK j z
  have hganti : ∀ z, Antitone fun j => g j z := fun z =>
    uscSupConvolution_antitone hKne htop hCK z
  have hginf : ∀ z, z ∈ K → (⨅ j : ℕ, (g j z : EReal)) = G z := fun z hz =>
    iInf_coe_uscSupConvolution hKne husc htop hCK hz
  have hcenter : ∀ j, G c ≤ ((Real.circleAverage (g j) c R : ℝ) : EReal) := by
    intro j
    exact gluedMax_le_circleAverage hD hu hv hboundary hR hKΩ (hg j) (hgu j)
  apply circleSubmean_of_continuous_antitone_majorants c g hg
  · intro j z _
    exact hgC j z
  · intro t j k hjk
    apply EReal.coe_le_coe_iff.mpr
    exact hganti (c + circleMap 0 R t) hjk
  · intro t
    have hz : c + circleMap 0 R t ∈ K := by
      simpa [K, circleMap] using circleMap_mem_sphere c hR.le t
    exact hginf _ hz
  · exact hcenter

end

end SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingDiscSubmean
