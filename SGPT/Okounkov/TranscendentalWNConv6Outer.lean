import SGPT.Okounkov.TranscendentalWNConv6Envelope
import SGPT.Okounkov.TranscendentalWNDeformationStrict
import SGPT.Okounkov.TranscendentalWNVolumeLine
import SGPT.Okounkov.TranscendentalWNKeyGeometry
import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

/-!
# The outer region: `limsup_k ∫_{|τ| > ε} MA(u_k) ≤ vol(β - {X₀})`

Blueprint `tok-wn-conv6:outer` (chapter `claude-tok-wn-conv6`); source WN21 Propositions 6.1 and
6.2.  The route avoids the weak convergence `MA(u_k) → MA(u_∞)`:

* on the open set `O_ε = {N₀ > ε²/(1+ε²)} = {|τ| > ε} ∪ X_∞` and for `eᵏ ε² ≥ 1`,
  `g_k = log N₀ ∘ π_{ℙ¹} ∘ μ` (`obstacle_eq_log`), whence `θ̃ + ddᶜg_k = θ̃' = θ̃ - (π_{ℙ¹}μ)^*ω_FS`
  there (`form_add_ddc_coeff_eq`), so the measures `(θ̃ + ddᶜg_k)^{n+1}_+` and `θ̃'^{n+1}_+` agree on
  `O_ε` (`positiveTopMeasure_restrict_outer`);
* the sets `D_k ∩ O_ε` decrease (`contact_outer_succ`);
* `u_∞ = inf_k u_k ≥ V_{θ̃'} + log N₀` (`lowerCompetitor_le_envelopeInf`), and
  `v = u_∞ - log N₀` extends across `X₀` to a `θ̃'`-psh `v ≤ 0` vanishing on `⋂_k D_k ∩ O_ε`
  (`outerPotential`);
* Di Nezza–Trapani for the constant obstacle `0` bounds `θ̃'^{n+1}_+(⋂_k D_k ∩ O_ε)` by the mass of
  `v`, at most `vol(β - {X₀})`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain

/-! ### The weight `N₀` on `ℙ¹` -/

theorem projectiveInfinity_eq_mk :
    projectiveInfinity = Projectivization.mk ℂ ![1, 0] (by simp) :=
  ((mk_eq_projectiveInfinity_iff _ _).mpr (by simp)).symm

theorem projectiveWeight_zero_infinity : projectiveWeight 0 projectiveInfinity = 1 := by
  rw [projectiveInfinity_eq_mk, projectiveWeight_mk]; simp

theorem projectiveWeight_zero_affineLinePoint (τ : ℂ) :
    projectiveWeight 0 (affineLinePoint τ) = ‖τ‖ ^ 2 / (‖τ‖ ^ 2 + 1) := by
  rw [affineLinePoint_eq_mk, projectiveWeight_mk]; simp

theorem eq_affineLinePoint_of_ne_infinity {p : ProjectiveLine} (hp : p ≠ projectiveInfinity) :
    p = affineLinePoint (projectiveAffine p) := by
  have h1 : p.rep 1 ≠ 0 := by
    intro h1
    apply hp
    rw [← Projectivization.mk_rep p, mk_eq_projectiveInfinity_iff]; exact h1
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [affineLinePoint_eq_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 (p.rep 1) h1, ?_⟩
  ext i
  fin_cases i <;> simp [projectiveAffine, Units.smul_def]; field_simp

/-- `O_ε = {N₀ > ε²/(1+ε²)}` on `ℙ¹`, i.e. `{|τ| > ε} ∪ {∞}`. -/
def outerLine (ε : ℝ) : Set ProjectiveLine := {p | ε ^ 2 / (1 + ε ^ 2) < projectiveWeight 0 p}

theorem continuous_projectiveWeight' (i : Fin 2) : Continuous (projectiveWeight i) :=
  ProductTestForms.ChartSmooth.continuous (n := 1) fun e => contDiffOn_projectiveWeight i e

theorem isOpen_outerLine (ε : ℝ) : IsOpen (outerLine ε) :=
  isOpen_lt continuous_const (continuous_projectiveWeight' 0)

theorem lt_norm_sq_of_mem_outerLine {ε : ℝ} {τ : ℂ} (h : affineLinePoint τ ∈ outerLine ε) :
    ε ^ 2 < ‖τ‖ ^ 2 := by
  have h' : ε ^ 2 / (1 + ε ^ 2) < ‖τ‖ ^ 2 / (‖τ‖ ^ 2 + 1) := by
    have := h; simp only [outerLine, mem_ofPred_eq] at this
    rwa [projectiveWeight_zero_affineLinePoint] at this
  have h1 : 0 < 1 + ε ^ 2 := by positivity
  have h2 : 0 < ‖τ‖ ^ 2 + 1 := by positivity
  rw [div_lt_div_iff₀ h1 h2] at h'
  nlinarith

/-- **On `O_ε`, `g_k = log N₀` for `eᵏ ε² ≥ 1`.** -/
theorem cutoffObstacleLine_eq_log {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ Real.exp k * ε ^ 2) {p : ProjectiveLine} (hp : p ∈ outerLine ε) :
    cutoffObstacleLine χ k p = Real.log (projectiveWeight 0 p) := by
  by_cases hinf : p = projectiveInfinity
  · rw [hinf, cutoffObstacleLine_infinity, projectiveWeight_zero_infinity, Real.log_one]
  · rw [eq_affineLinePoint_of_ne_infinity hinf] at hp ⊢
    set τ := projectiveAffine p
    have hτ := lt_norm_sq_of_mem_outerLine hp
    have hn : 0 < ‖τ‖ ^ 2 := lt_of_le_of_lt (sq_nonneg ε) hτ
    rw [cutoffObstacleLine_affineLinePoint, projectiveWeight_zero_affineLinePoint,
      cutoffLog_of_one_le hχ (le_trans hk (by gcongr)), Real.log_mul (Real.exp_pos _).ne' hn.ne',
      Real.log_exp, Real.log_div hn.ne' (by positivity), add_comm (‖τ‖ ^ 2) 1]
    ring

/-- **`log N₀ ≤ g_k`** (`x ≤ χ(x)`). -/
theorem projectiveLogWeight_le_cutoffObstacleLine {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ)
    (p : ProjectiveLine) :
    projectiveLogWeight 0 p ≤ (cutoffObstacleLine χ k p : EReal) := by
  by_cases hinf : p = projectiveInfinity
  · rw [hinf, cutoffObstacleLine_infinity, projectiveLogWeight_eq_coe (by
      rw [projectiveWeight_zero_infinity]; exact one_pos), projectiveWeight_zero_infinity,
      Real.log_one]
  · rw [eq_affineLinePoint_of_ne_infinity hinf]
    set τ := projectiveAffine p
    by_cases hτ : τ = 0
    · rw [hτ, affineLinePoint_zero]
      have : projectiveLogWeight 0 projectiveZero = ⊥ := by
        rw [projectiveLogWeight, projectiveWeight_zero_projectiveZero]; simp
      rw [this]; exact bot_le
    · have hn : 0 < ‖τ‖ ^ 2 := by positivity
      rw [projectiveLogWeight_eq_coe (by rw [projectiveWeight_zero_affineLinePoint]; positivity),
        cutoffObstacleLine_affineLinePoint, projectiveWeight_zero_affineLinePoint,
        cutoffLog_of_pos χ (by positivity), Real.log_mul (Real.exp_pos _).ne' hn.ne',
        Real.log_exp, Real.log_div hn.ne' (by positivity), add_comm (‖τ‖ ^ 2) 1]
      refine EReal.coe_le_coe_iff.mpr ?_
      have := hχ.le_self (k + Real.log (‖τ‖ ^ 2))
      linarith

/-! ### The data on `𝒳` -/

namespace MCData

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} {𝒳 : Type u} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
  (D : MCData F 𝒳)

/-- `O_ε ⊆ 𝒳`. -/
def outer (ε : ℝ) : Set 𝒳 := (fun z => (D.μ z).2) ⁻¹' outerLine ε

theorem isOpen_outer (ε : ℝ) : IsOpen (D.outer ε) :=
  (isOpen_outerLine ε).preimage D.contMDiff_proj.continuous

/-- `N₀ ∘ π_{ℙ¹} ∘ μ`. -/
def weight0 (z : 𝒳) : ℝ := projectiveWeight 0 (D.μ z).2

theorem chartSmooth_weight0 : ChartSmooth (n := m + 1 + 1) D.weight0 :=
  chartSmooth_projectiveWeight_comp D.hμ 0

/-- `X₀ = {N₀ ∘ π_{ℙ¹} ∘ μ = 0}`. -/
theorem mem_centralFibre_iff (z : 𝒳) : z ∈ centralFibre F D.μ ↔ D.weight0 z = 0 := by
  constructor
  · intro h
    have h2 : (D.μ z).2 = projectiveZero := by
      have := h; simp only [centralFibre, centralBase, mem_preimage, mem_prod, mem_univ,
        true_and, mem_singleton_iff] at this; exact this
    rw [weight0, h2, projectiveWeight_zero_projectiveZero]
  · intro h
    have hp : (D.μ z).2 = projectiveZero := by
      by_contra hne
      exact (projectiveWeight_zero_pos hne).ne' h
    simp only [centralFibre, centralBase, mem_preimage, mem_prod, mem_univ, true_and,
      mem_singleton_iff]
    exact hp

theorem weight0_pos_of_notMem {z : 𝒳} (hz : z ∉ centralFibre F D.μ) : 0 < D.weight0 z :=
  lt_of_le_of_ne (projectiveWeight_nonneg 0 _) (fun h => hz ((D.mem_centralFibre_iff z).mpr h.symm))

theorem outer_subset_compl_centralFibre {ε : ℝ} : D.outer ε ⊆ (centralFibre F D.μ)ᶜ := by
  intro z hz hc
  have h0 := (D.mem_centralFibre_iff z).mp hc
  have : ε ^ 2 / (1 + ε ^ 2) < D.weight0 z := hz
  rw [h0] at this
  exact absurd this (not_lt.mpr (by positivity))

/-- **`g_k = log N₀` on `O_ε` for `eᵏ ε² ≥ 1`.** -/
theorem obstacle_eq_log {ε : ℝ} {k : ℕ} (hk : 1 ≤ Real.exp k * ε ^ 2) {z : 𝒳}
    (hz : z ∈ D.outer ε) : D.obstacle k z = Real.log (D.weight0 z) :=
  cutoffObstacleLine_eq_log D.hχ hk hz

/-- `P = (π_{ℙ¹} μ)^*ω_FS`. -/
def fsPullback : ClosedRealOneOneForm (m + 1 + 1) 𝒳 :=
  ClosedRealOneOneForm.pullback D.contMDiff_proj projectiveNativeFSClosedForm

/-- `θ̃ = θ̃' + (π_{ℙ¹} μ)^*ω_FS`. -/
theorem form_eq : D.form = D.formPrev + D.fsPullback := by
  unfold form formPrev fsPullback deformationForm
  rw [sub_smul, one_smul]
  abel

/-- **`θ̃ + ddᶜ log N₀ = θ̃'` where `N₀ > 0`**, coefficientwise. -/
theorem form_add_ddcLog_coeff (e : ComplexChart (m + 1 + 1) 𝒳) {u : ComplexModel (m + 1 + 1)}
    (hu : u ∈ e.val.target) (hN : 0 < D.weight0 (e.val.symm u)) :
    D.form.val.coeff e u + smoothDDC (fun w => Real.log (D.weight0 (e.val.symm w))) u =
      D.formPrev.val.coeff e u := by
  have hP := pullback_projectiveFS_coeff D.contMDiff_proj e hu hN
  -- the open set where `N₀ > 0`
  have hcont : ContinuousOn (fun w => D.weight0 (e.val.symm w)) e.val.target :=
    (D.chartSmooth_weight0 e).continuousOn
  set S : Set (ComplexModel (m + 1 + 1)) :=
    e.val.target ∩ (fun w => D.weight0 (e.val.symm w)) ⁻¹' Ioi 0 with hS
  have hSo : IsOpen S := hcont.isOpen_inter_preimage e.val.open_target isOpen_Ioi
  have huS : u ∈ S := ⟨hu, hN⟩
  have hsm : ContDiffOn ℝ ∞ (fun w => Real.log (D.weight0 (e.val.symm w))) S :=
    ((D.chartSmooth_weight0 e).mono inter_subset_left).log fun w hw => hw.2.ne'
  have hneg := smoothDDC_neg hSo hsm huS
  rw [D.form_eq, ClosedRealOneOneForm.coeff_add]
  change _ + D.fsPullback.val.coeff e u + _ = _
  rw [show D.fsPullback.val.coeff e u = smoothDDC (fun w => -Real.log (D.weight0 (e.val.symm w))) u
    from hP, hneg]
  abel

/-- **`θ̃ + ddᶜg_k = θ̃'` on `O_ε`** (for `eᵏ ε² ≥ 1`), coefficientwise. -/
theorem form_add_ddc_coeff_eq {ε : ℝ} {k : ℕ} (hk : 1 ≤ Real.exp k * ε ^ 2)
    (e : ComplexChart (m + 1 + 1) 𝒳) {u : ComplexModel (m + 1 + 1)} (hu : u ∈ e.val.target)
    (hz : e.val.symm u ∈ D.outer ε) :
    (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k)).val.coeff e u =
      D.formPrev.val.coeff e u := by
  rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' D.outer ε) :=
    e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target (D.isOpen_outer ε)
  have hev : (fun w => D.obstacle k (e.val.symm w)) =ᶠ[𝓝 u]
      fun w => Real.log (D.weight0 (e.val.symm w)) := by
    filter_upwards [hS.mem_nhds ⟨hu, hz⟩] with w hw
    exact D.obstacle_eq_log hk hw.2
  rw [smoothDDC_congr hev]
  exact D.form_add_ddcLog_coeff e hu (D.weight0_pos_of_notMem (D.outer_subset_compl_centralFibre hz))

theorem topRatio_formPow_congr {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] (w : SmoothRealForm N M 2)
    {α β : ClosedRealOneOneForm N M} {x : M}
    (h : α.val.coeff (complexChartAt x) ((complexChartAt (n := N) x).val x) =
      β.val.coeff (complexChartAt x) ((complexChartAt (n := N) x).val x)) :
    IntegrationCurrent.topRatio w (ProductTestForms.formPow α.val N) x =
      IntegrationCurrent.topRatio w (ProductTestForms.formPow β.val N) x := by
  simp only [IntegrationCurrent.topRatio, IntegrationCurrent.chartRatio, ProductTestForms.formPow_coeff, h]

theorem topRatio_outer_eq (w : SmoothRealForm (m + 1 + 1) 𝒳 2) {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ Real.exp k * ε ^ 2) {x : 𝒳} (hx : x ∈ D.outer ε) :
    IntegrationCurrent.topRatio w (ProductTestForms.formPow
        (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k)).val (m + 1 + 1)) x =
      IntegrationCurrent.topRatio w (ProductTestForms.formPow D.formPrev.val (m + 1 + 1)) x := by
  apply topRatio_formPow_congr
  have hxe := mem_complexChartAt_source (n := m + 1 + 1) x
  exact D.form_add_ddc_coeff_eq hk _ ((complexChartAt (n := m + 1 + 1) x).val.map_source hxe)
    (by rwa [(complexChartAt (n := m + 1 + 1) x).val.left_inv hxe])

/-- **On `O_ε` the two top-power measures agree.** -/
theorem positiveTopMeasure_restrict_outer [CompactSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (w : KahlerBackground (m + 1 + 1) 𝒳) {ε : ℝ} {k : ℕ} (hk : 1 ≤ Real.exp k * ε ^ 2) :
    (SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure w
        (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k))).restrict (D.outer ε) =
      (SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure w D.formPrev).restrict (D.outer ε) := by
  have hO := (D.isOpen_outer ε).measurableSet
  rw [SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure,
    SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure, restrict_withDensity hO,
    restrict_withDensity hO]
  exact withDensity_congr_ae (ae_restrict_of_forall_mem hO fun x hx => by
    simp only [D.topRatio_outer_eq w.form.val hk hx])

/-- **The contact sets decrease on `O_ε`.** -/
theorem contact_outer_succ [CompactSpace 𝒳] [ConnectedSpace 𝒳] {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ Real.exp k * ε ^ 2) {z : 𝒳} (hz : z ∈ D.outer ε) (hc : z ∈ D.contact (k + 1)) :
    z ∈ D.contact k := by
  have hk1 : 1 ≤ Real.exp ((k + 1 : ℕ) : ℝ) * ε ^ 2 :=
    le_trans hk (by gcongr; exact_mod_cast Nat.le_succ k)
  have h1 : D.envelope (k + 1) z = (Real.log (D.weight0 z) : EReal) := by
    have : D.envelope (k + 1) z = (D.obstacle (k + 1) z : EReal) := hc
    rw [this, D.obstacle_eq_log hk1 hz]
  show D.envelope k z = (D.obstacle k z : EReal)
  rw [D.obstacle_eq_log hk hz]
  refine le_antisymm ?_ ?_
  · have := D.envelope_le_obstacle k z
    rwa [D.obstacle_eq_log hk hz] at this
  · rw [← h1]; exact D.envelope_succ_le k z

/-! ### The limit potential and the bound -/

/-- `b - 1 > c`: the class `β - {X₀}` is big. -/
theorem isBig_formPrev [CompactSpace 𝒳] :
    SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative D.formPrev) :=
  (betaBig F D.E D.hE 𝒳 D.μ D.hμ D.Eℰ D.hEℰ.isDivisorMetric D.θ (D.b - 1) D.c D.hc
    (by linarith [D.hcb]) D.hξ D.hξc.1).1

theorem exists_isThetaPshPotential_formPrev [CompactSpace 𝒳] :
    ∃ φ : 𝒳 → EReal, IsThetaPshPotential D.formPrev.val φ :=
  exists_isThetaPshPotential_of_isBigClass
    ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp D.isBig_formPrev)

/-- `V_{θ̃'}` is a `θ̃'`-psh potential. -/
theorem isThetaPshPotential_supPrev [CompactSpace 𝒳] [ConnectedSpace 𝒳] :
    IsThetaPshPotential D.formPrev.val (thetaPshSupremum D.formPrev.val) := by
  let : MeasurableSpace 𝒳 := borel 𝒳
  have : BorelSpace 𝒳 := ⟨rfl⟩
  obtain ⟨φ, hφ⟩ := D.exists_isThetaPshPotential_formPrev
  exact (TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative
    (Classical.choice D.nonempty_kahler) D.formPrev hφ).1

/-- `log N₀ ∘ π_{ℙ¹} ∘ μ` as an extended real function. -/
def logWeight0 (z : 𝒳) : EReal := projectiveLogWeight 0 (D.μ z).2

theorem logWeight0_eq_coe {z : 𝒳} (hz : z ∉ centralFibre F D.μ) :
    D.logWeight0 z = (Real.log (D.weight0 z) : EReal) :=
  projectiveLogWeight_eq_coe (D.weight0_pos_of_notMem hz)

/-- The competitor `V_{θ̃'} + log N₀`, below every `g_k`. -/
def lowerCompetitor (z : 𝒳) : EReal := thetaPshSupremum D.formPrev.val z + D.logWeight0 z

theorem interior_centralFibre : interior (centralFibre F D.μ) = ∅ :=
  interior_centralFibre_eq_empty F D.hμ

theorem isComplexAnalyticSubset_centralFibre :
    IsComplexAnalyticSubset (n := m + 1 + 1) (centralFibre F D.μ) := by
  have h : centralFibre F D.μ = (fun z => (D.μ z).2) ⁻¹' {projectiveZero} := by
    ext z; simp [centralFibre, centralBase]
  rw [h]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage D.contMDiff_proj
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (n := 1) projectiveZero)

theorem isClosed_centralFibre : IsClosed (centralFibre F D.μ) :=
  D.isComplexAnalyticSubset_centralFibre.isClosed

/-- A potential is finite at some point off `X₀` in every open set. -/
theorem exists_ne_bot_off_centralFibre {φ : 𝒳 → EReal} (hφ : LocallyNondegenerate φ)
    {U : Set 𝒳} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y ∈ U, y ∉ centralFibre F D.μ ∧ φ y ≠ ⊥ := by
  have hU' : (U \ centralFibre F D.μ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    have := interior_mono h
    rw [hU.interior_eq, D.interior_centralFibre] at this
    exact hne.ne_empty (subset_empty_iff.mp this)
  obtain ⟨x, hx⟩ := hU'
  obtain ⟨y, hy, hyb⟩ := hφ x _ (hU.sdiff D.isClosed_centralFibre) hx
  exact ⟨y, hy.1, hy.2, hyb⟩

theorem isThetaPshPotential_lowerCompetitor [CompactSpace 𝒳] [ConnectedSpace 𝒳] :
    IsThetaPshPotential D.form.val D.lowerCompetitor := by
  have hV := D.isThetaPshPotential_supPrev
  have hℓ : ThetaPlurisubharmonic D.fsPullback.val D.logWeight0 :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp D.contMDiff_proj
      (thetaPlurisubharmonic_projectiveLogWeight 0)
  refine ⟨?_, ?_⟩
  · rw [D.form_eq]
    exact LocalPotentials.thetaPlurisubharmonic_add hV.1 hℓ
  · intro x U hU hxU
    obtain ⟨y, hyU, hyX, hyb⟩ := D.exists_ne_bot_off_centralFibre hV.2 hU ⟨x, hxU⟩
    refine ⟨y, hyU, ?_⟩
    rw [lowerCompetitor, D.logWeight0_eq_coe hyX]
    intro h
    exact hyb (EReal.add_eq_bot_iff.mp h |>.resolve_right (EReal.coe_ne_bot _))

theorem lowerCompetitor_le_obstacle (k : ℕ) (z : 𝒳) :
    D.lowerCompetitor z ≤ (D.obstacle k z : EReal) :=
  calc D.lowerCompetitor z ≤ 0 + D.logWeight0 z :=
        add_le_add (thetaPshSupremum_le_zero _ z) le_rfl
    _ = D.logWeight0 z := zero_add _
    _ ≤ (D.obstacle k z : EReal) := projectiveLogWeight_le_cutoffObstacleLine D.hχ k _

/-- `u_∞ = inf_k u_k`. -/
def envelopeInf (z : 𝒳) : EReal := ⨅ k, D.envelope k z

theorem lowerCompetitor_le_envelopeInf [CompactSpace 𝒳] [ConnectedSpace 𝒳] (z : 𝒳) :
    D.lowerCompetitor z ≤ D.envelopeInf z :=
  le_iInf fun k => le_rooftopEnvelope D.isThetaPshPotential_lowerCompetitor
    (quasiEverywhere_of_forall fun z => D.lowerCompetitor_le_obstacle k z) z

theorem thetaPlurisubharmonic_envelopeInf [CompactSpace 𝒳] [ConnectedSpace 𝒳] :
    ThetaPlurisubharmonic D.form.val D.envelopeInf :=
  ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
    (fun k => (D.isThetaPshPotential_envelope k).1) D.envelope_antitone

/-- Every point off `X₀` lies in some `O_ε`, and `g_k = log N₀` there for large `k`. -/
theorem exists_obstacle_eq_log {z : 𝒳} (hz : z ∉ centralFibre F D.μ) :
    ∃ K : ℕ, ∀ k, K ≤ k → D.obstacle k z = Real.log (D.weight0 z) := by
  have hN := D.weight0_pos_of_notMem hz
  -- choose `ε` with `ε²/(1+ε²) < N₀(z)`
  set ε : ℝ := Real.sqrt (D.weight0 z / 2) with hε
  have hε2 : ε ^ 2 = D.weight0 z / 2 := Real.sq_sqrt (by positivity)
  have hεpos : 0 < ε ^ 2 := by rw [hε2]; positivity
  have hzO : z ∈ D.outer ε := by
    show ε ^ 2 / (1 + ε ^ 2) < D.weight0 z
    rw [div_lt_iff₀ (by positivity), hε2]
    nlinarith
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε ^ 2)
  refine ⟨K, fun k hk => D.obstacle_eq_log ?_ hzO⟩
  have hkK : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : (K : ℝ) ≤ Real.exp k := le_trans hkK (by
    have := Real.add_one_le_exp (k : ℝ); linarith)
  have h2 : 1 / ε ^ 2 < Real.exp k := lt_of_lt_of_le hK h1
  rw [div_lt_iff₀ hεpos] at h2
  linarith

theorem envelopeInf_le_log [CompactSpace 𝒳] [ConnectedSpace 𝒳] {z : 𝒳}
    (hz : z ∉ centralFibre F D.μ) : D.envelopeInf z ≤ (Real.log (D.weight0 z) : EReal) := by
  obtain ⟨K, hK⟩ := D.exists_obstacle_eq_log hz
  calc D.envelopeInf z ≤ D.envelope K z := iInf_le _ K
    _ ≤ (D.obstacle K z : EReal) := D.envelope_le_obstacle K z
    _ = _ := by rw [hK K le_rfl]

/-- `v = u_∞ - log N₀` off `X₀`. -/
def outerPotentialOff (z : 𝒳) : EReal :=
  D.envelopeInf z + ((-Real.log (D.weight0 z) : ℝ) : EReal)

theorem outerPotentialOff_le_zero [CompactSpace 𝒳] [ConnectedSpace 𝒳] {z : 𝒳}
    (hz : z ∉ centralFibre F D.μ) : D.outerPotentialOff z ≤ 0 := by
  have h := D.envelopeInf_le_log hz
  calc D.outerPotentialOff z ≤ (Real.log (D.weight0 z) : EReal) +
        ((-Real.log (D.weight0 z) : ℝ) : EReal) := add_le_add h le_rfl
    _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]

theorem supPrev_le_outerPotentialOff [CompactSpace 𝒳] [ConnectedSpace 𝒳] {z : 𝒳}
    (hz : z ∉ centralFibre F D.μ) : thetaPshSupremum D.formPrev.val z ≤ D.outerPotentialOff z := by
  have h := D.lowerCompetitor_le_envelopeInf z
  rw [lowerCompetitor, D.logWeight0_eq_coe hz] at h
  exact ereal_le_add_neg_of_add_le h

/-- **`v` is `θ̃'`-psh off `X₀`.** -/
theorem thetaPshOff_outerPotentialOff [CompactSpace 𝒳] [ConnectedSpace 𝒳] :
    ThetaPshOff D.formPrev.val (centralFibre F D.μ) D.outerPotentialOff := by
  intro e u hu hnot
  obtain ⟨W, ρ, huW, hρ, hpsh⟩ := D.thetaPlurisubharmonic_envelopeInf e u hu
  have hcont : ContinuousOn (fun w => D.weight0 (e.val.symm w)) e.val.target :=
    (D.chartSmooth_weight0 e).continuousOn
  set S : Set (ComplexModel (m + 1 + 1)) :=
    W ∩ (e.val.target ∩ (fun w => D.weight0 (e.val.symm w)) ⁻¹' Ioi 0) with hS
  have hSo : IsOpen S := hρ.1.inter (hcont.isOpen_inter_preimage e.val.open_target isOpen_Ioi)
  have huS : u ∈ S := ⟨huW, hu, D.weight0_pos_of_notMem hnot⟩
  have hlog : ContDiffOn ℝ ∞ (fun w => Real.log (D.weight0 (e.val.symm w))) S :=
    ((D.chartSmooth_weight0 e).mono fun w hw => hw.2.1).log fun w hw => hw.2.2.ne'
  refine ⟨S, fun w => ρ w + Real.log (D.weight0 (e.val.symm w)), huS,
    ⟨hSo, fun w hw => hw.2.1, (hρ.2.2.1.mono inter_subset_left).add hlog, fun w hw => ?_⟩, ?_⟩
  · -- `θ̃' = θ̃ + ddᶜ log N₀ = ddᶜ (ρ + log N₀)`
    rw [smoothDDC_add hSo (hρ.2.2.1.mono inter_subset_left) hlog hw, hρ.2.2.2 hw.1]
    exact D.form_add_ddcLog_coeff e hw.2.1 hw.2.2
  · refine SGPT.Foundations.Analysis.plurisubharmonicOn_congr hSo (hpsh.mono inter_subset_left)
      fun w hw => ?_
    simp only [chartFunction, outerPotentialOff]
    rw [EReal.coe_add, add_comm (ρ w : EReal), ← add_assoc, add_assoc (D.envelopeInf _),
      ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

/-- **The extension `v ∈ PSH(𝒳, θ̃')`** of `u_∞ - log N₀` across `X₀`. -/
def outerPotential : 𝒳 → EReal := extensionAcross (centralFibre F D.μ) D.outerPotentialOff

theorem outerPotential_spec [CompactSpace 𝒳] [ConnectedSpace 𝒳] :
    IsThetaPshPotential D.formPrev.val D.outerPotential ∧ D.outerPotential ≤ 0 ∧
      ∀ z ∉ centralFibre F D.μ, D.outerPotential z = D.outerPotentialOff z := by
  have hbd : PshAnalyticSetExtension.LocallyBoundedAboveOff (centralFibre F D.μ)
      D.outerPotentialOff := fun x =>
    ⟨univ, univ_mem, 0, fun y _ hy => by simpa using D.outerPotentialOff_le_zero hy⟩
  obtain ⟨hext, hoff, -⟩ := TranscendentalLifting.thetaPsh_extend_across_analytic D.formPrev
    D.isComplexAnalyticSubset_centralFibre D.interior_centralFibre
    D.thetaPshOff_outerPotentialOff hbd
  have hle0 : D.outerPotential ≤ 0 := by
    classical
    unfold outerPotential extensionAcross
    refine uscRegularization_le (g := fun _ => (0 : EReal)) upperSemicontinuous_const ?_
    intro y
    by_cases hy : y ∈ centralFibre F D.μ
    · simp [hy]
    · simp only [hy, if_false]
      exact D.outerPotentialOff_le_zero hy
  have hV := D.isThetaPshPotential_supPrev
  obtain ⟨y, -, hyX, hyb⟩ := D.exists_ne_bot_off_centralFibre hV.2 isOpen_univ univ_nonempty
  have hne : ∃ x, D.outerPotential x ≠ ⊥ := ⟨y, by
    change extensionAcross (centralFibre F D.μ) D.outerPotentialOff y ≠ ⊥
    rw [hoff y hyX]
    exact ne_bot_of_le_ne_bot hyb (D.supPrev_le_outerPotentialOff hyX)⟩
  exact ⟨⟨hext, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hext hne⟩, hle0,
    hoff⟩

/-- `(θ̃')^{n+1}_+` is finite. -/
theorem positiveTopMeasure_univ_ne_top {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] (w : KahlerBackground N M) (α : ClosedRealOneOneForm N M) :
    SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure w α univ ≠ ⊤ := by
  rw [SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  rcases isEmpty_or_nonempty M with hM | hM
  · simp [lintegral_of_isEmpty]
  have hc := IntegrationCurrent.continuous_topRatio w.isKahler.1 (ProductTestForms.formPow α.val N)
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (IntegrationCurrent.topRatio w.form.val
      (ProductTestForms.formPow α.val N) x₀) * IntegrationCurrent.kahlerVolume w univ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top (IntegrationCurrent.kahlerVolume w) univ)) ?_
  rw [← lintegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hx₀ (mem_univ x))

/-- **`tok-wn-conv6:outer`** (WN21 Propositions 6.1–6.2): for `ε > 0`,
`limsup_k ∫_{O_ε} ⟨(θ̃ + ddᶜu_k)^{n+1}⟩ ≤ vol(β - {X₀})`. -/
theorem eventually_envelopeMeasure_outer_le [CompactSpace 𝒳] [ConnectedSpace 𝒳]
    [MeasurableSpace 𝒳] [BorelSpace 𝒳] {ε : ℝ} (hε : 0 < ε) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∀ᶠ k in atTop, diagonalPotentialMeasure D.form (D.envelope k)
        (D.isThetaPshPotential_envelope k) (D.outer ε) ≤
      SGPT.PSH.VariableComplexAtlas.sourceClassVolume
        (RealBottChern.ofRepresentative D.formPrev) + η := by
  set w := Classical.choice D.nonempty_kahler
  set P := SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure w D.formPrev with hP
  -- the threshold `eᴷ ε² ≥ 1`
  have hεpos : 0 < ε ^ 2 := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε ^ 2)
  have hkK : ∀ k, K ≤ k → 1 ≤ Real.exp k * ε ^ 2 := fun k hk => by
    have hkK : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : (K : ℝ) ≤ Real.exp k := le_trans hkK (by
      have := Real.add_one_le_exp (k : ℝ); linarith)
    have h2 : 1 / ε ^ 2 < Real.exp k := lt_of_lt_of_le hK h1
    rw [div_lt_iff₀ hεpos] at h2
    linarith
  -- `MA(u_k)(O_ε) ≤ P(D_k ∩ O_ε)`
  have hmeasD : ∀ k, MeasurableSet (D.contact k) := fun k =>
    (isClosed_contact (D.isThetaPshPotential_envelope k).1 (D.chartSmooth_obstacle k)
      (D.envelope_le_obstacle k)).measurableSet
  have hO := (D.isOpen_outer ε).measurableSet
  have hMA : ∀ k, K ≤ k → diagonalPotentialMeasure D.form (D.envelope k)
      (D.isThetaPshPotential_envelope k) (D.outer ε) ≤ P (D.contact k ∩ D.outer ε) := by
    intro k hk
    have h1 := diagonalPotentialMeasure_rooftopEnvelope_le_contact w D.form
      (D.chartSmooth_obstacle k) (D.isThetaPshPotential_envelope k)
    have h2 := congrArg (fun ν : Measure 𝒳 => ν (D.contact k)) (D.positiveTopMeasure_restrict_outer w
      (hkK k hk))
    simp only [Measure.restrict_apply (hmeasD k)] at h2
    calc diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
          (D.outer ε)
        ≤ (topFormMeasure w (ProductTestForms.formPow
            (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k)).val (m + 1 + 1))).restrict
            (D.contact k) (D.outer ε) := h1 _
      _ = SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure w
            (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k))
            (D.outer ε ∩ D.contact k) := by
          rw [Measure.restrict_apply hO]; rfl
      _ = P (D.contact k ∩ D.outer ε) := by rw [inter_comm, h2]
  -- the decreasing sets and their limit
  set S : ℕ → Set 𝒳 := fun j => D.contact (K + j) ∩ D.outer ε with hS
  have hSanti : Antitone S := by
    refine antitone_nat_of_succ_le fun j z hz => ⟨?_, hz.2⟩
    exact D.contact_outer_succ (hkK (K + j) (Nat.le_add_right K j)) hz.2 hz.1
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun j => ((hmeasD (K + j)).inter hO).nullMeasurableSet) hSanti
    ⟨0, ne_top_of_le_ne_top (positiveTopMeasure_univ_ne_top w D.formPrev)
      (measure_mono (subset_univ _))⟩
  -- the limit set lies in `{v = 0}`
  obtain ⟨hv, hv0, hvoff⟩ := D.outerPotential_spec
  have hsub : (⋂ j, S j) ⊆ {z | D.outerPotential z = ((0 : ℝ) : EReal)} := by
    intro z hz
    rw [mem_iInter] at hz
    have hzO : z ∈ D.outer ε := (hz 0).2
    have hzX : z ∉ centralFibre F D.μ := D.outer_subset_compl_centralFibre hzO
    have hval : ∀ j, D.envelope (K + j) z = (Real.log (D.weight0 z) : EReal) := fun j => by
      have : D.envelope (K + j) z = (D.obstacle (K + j) z : EReal) := (hz j).1
      rw [this, D.obstacle_eq_log (hkK (K + j) (Nat.le_add_right K j)) hzO]
    have hinf : D.envelopeInf z = (Real.log (D.weight0 z) : EReal) := by
      refine le_antisymm ?_ (le_iInf fun k => ?_)
      · calc D.envelopeInf z ≤ D.envelope (K + 0) z := iInf_le _ _
          _ = _ := hval 0
      · rw [← hval k]; exact D.envelope_antitone z (Nat.le_add_left k K)
    show D.outerPotential z = ((0 : ℝ) : EReal)
    rw [hvoff z hzX, outerPotentialOff, hinf, ← EReal.coe_add, add_neg_cancel]
  -- Di Nezza–Trapani for the constant obstacle `0` and the mass bound
  have hdnt := SGPT.Okounkov.TranscendentalWNReg.dntConstantObstacleStatement (m + 1 + 1) 𝒳 w
    D.formPrev D.outerPotential hv 0 (fun x => by rw [EReal.coe_zero]; exact hv0 x)
  have hmass := TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume w
    D.formPrev hv
  have hL : P (⋂ j, S j) ≤ SGPT.PSH.VariableComplexAtlas.sourceClassVolume
      (RealBottChern.ofRepresentative D.formPrev) := by
    calc P (⋂ j, S j)
        = (P.restrict {z | D.outerPotential z = ((0 : ℝ) : EReal)}) (⋂ j, S j) := by
          rw [Measure.restrict_apply (MeasurableSet.iInter fun j => (hmeasD (K + j)).inter hO),
            inter_eq_left.mpr hsub]
      _ ≤ diagonalPotentialMeasure D.formPrev D.outerPotential hv (⋂ j, S j) := hdnt _
      _ ≤ diagonalPotentialMeasure D.formPrev D.outerPotential hv univ :=
          measure_mono (subset_univ _)
      _ ≤ _ := hmass
  have hLt : P (⋂ j, S j) ≠ ⊤ :=
    ne_top_of_le_ne_top (positiveTopMeasure_univ_ne_top w D.formPrev) (measure_mono (subset_univ _))
  -- conclusion
  have hev : ∀ᶠ j in atTop, P (S j) ≤ P (⋂ j, S j) + η :=
    ((ENNReal.tendsto_nhds hLt).mp hlim η (pos_iff_ne_zero.mpr hη)).mono fun j hj => hj.2
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hev
  refine eventually_atTop.mpr ⟨K + J, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = K + j := ⟨k - K, by omega⟩
  calc diagonalPotentialMeasure D.form (D.envelope (K + j)) (D.isThetaPshPotential_envelope (K + j))
        (D.outer ε) ≤ P (S j) := hMA (K + j) (Nat.le_add_right K j)
    _ ≤ P (⋂ j, S j) + η := hJ j (by omega)
    _ ≤ _ := add_le_add hL le_rfl

end MCData

end SGPT.Okounkov.TranscendentalWN
