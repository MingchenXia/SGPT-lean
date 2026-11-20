import SGPT.Okounkov.TranscendentalWNRegContactLocal
import SGPT.Okounkov.TranscendentalWNRegStatement
import SGPT.Okounkov.TranscendentalWNRegC11bar
import SGPT.Okounkov.TranscendentalWNEnvelopeContact

/-!
# The Di Nezza–Trapani contact formula for smooth obstacles (package WN-REG)

Package WN-REG (`claude-tok-wn-reg`, nodes `tok-wn-reg:dnt-lower`, `tok-wn-reg:dnt-smooth`,
`tok-wn-reg:dnt-constant`; `tok-wn:dnt` of the WN chapter): on a compact complex manifold `M` of
dimension `n` with a Kähler background `ω`, for a closed real `(1,1)`-form `θ`, a smooth `f` and
`u ∈ PSH(M, θ)` with `u ≤ f` and contact set `E = {u = f}`,

  `𝟙_E ⟨(θ + ddᶜu)ⁿ⟩ = 𝟙_E (θ + ddᶜf)ⁿ`.

* `positiveTopMeasure_restrict_contact_le` (`tok-wn-reg:dnt-lower`): the inequality "`≥`", from the
  local bound `ContactLocal.truncationLimitMeasure_contact_ge` through potential patches of the
  global non-pluripolar measure and a finite cover of the compact contact set;
* `dntSmoothContactStatement` (`tok-wn-reg:dnt-smooth`): `DNTSmoothContactStatement`, with the
  inequality "`≤`" from package WN-ENV (`TranscendentalWN.diagonalPotentialMeasure_restrict_contact_le`,
  `tok-wn:contact-upper`);
* `dntConstantObstacleStatement` (`tok-wn-reg:dnt-constant`): `DNTConstantObstacleStatement`, the case
  `f = c`;
* `wnRegStatement`: `WNRegStatement`, the package statement consumed by WN-KEY.

The measure `(θ + ddᶜf)ⁿ` is `positiveTopMeasure ω (θ + ddᶜf)`, the measure with density
`max((θ + ddᶜf)ⁿ/ωⁿ, 0)` (it coincides with WN-ENV's `topFormMeasure`); on `E` the density is
nonnegative (`TranscendentalWN.topRatio_nonneg_of_contact`), so no truncation takes place there.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

section Measures

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [IsComplexManifold n M] in
/-- `positiveTopMeasure ω α` is WN-ENV's `topFormMeasure ω (αⁿ)`. -/
theorem positiveTopMeasure_eq_topFormMeasure [IsComplexManifold n M] (w : KahlerBackground n M)
    (α : ClosedRealOneOneForm n M) :
    positiveTopMeasure w α = TranscendentalWN.topFormMeasure w (formPow α.val n) := rfl

/-- **The contact bound "`≥`"** (`tok-wn-reg:dnt-lower`).  Let `θ` be a closed real `(1,1)`-form,
`f` smooth, `u ∈ PSH(M, θ)` with `u ≤ f`, `E = {u = f}`.  Then `𝟙_E (θ + ddᶜf)ⁿ ≤ ⟨(θ + ddᶜu)ⁿ⟩`. -/
theorem positiveTopMeasure_restrict_contact_le (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict {x | u x = (f x : EReal)} ≤
      diagonalPotentialMeasure θ u hu := by
  set E : Set M := {x | u x = (f x : EReal)} with hE
  have hEc : IsClosed E := TranscendentalWN.isClosed_contact hu.1 hf hle
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : diagonalPotentialMeasure θ u hu = kahlerVolume w :=
      AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples (Subsingleton.elim _ _)
        (Subsingleton.elim _ _) _ (fun _ =>
          ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1)
    have h2 : positiveTopMeasure w (θ + ddcClosedForm f hf) = kahlerVolume w := by
      have hd : (fun x => ENNReal.ofReal
          (topRatio w.form.val (formPow (θ + ddcClosedForm f hf).val 0) x)) = fun _ => 1 := by
        funext x
        have : formPow (θ + ddcClosedForm f hf).val 0 = formPow w.form.val 0 := rfl
        rw [this, topRatio_formPow w.isKahler.1, ENNReal.ofReal_one]
      rw [positiveTopMeasure, hd]
      exact withDensity_one
    rw [h1, h2]
    exact Measure.restrict_le_self
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA]
  refine le_trans ?_ (measure_mono (inter_subset_left : A ∩ E ⊆ A))
  refine TranscendentalWN.le_of_local_le hEc.isCompact ?_ (hA.inter hEc.measurableSet)
    inter_subset_right
  intro x hx
  set e := complexChartAt (n := n) x with he
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hu.1 e (e.val x) hz₀
  have hWo : IsOpen W := hρ.1
  have hWt : W ⊆ e.val.target := hρ.2.1
  let Ω : Opens (ComplexModel n) := ⟨W, hWo⟩
  set q : ComplexModel n → ℝ := fun y => f (e.val.symm y) + ρ y with hqdef
  have hqW : ContDiffOn ℝ ∞ q W := ((hf e).mono hWt).add hρ.2.2.1
  set U : ComplexModel n → EReal := fun y => chartFunction u e y + (ρ y : EReal) with hUdef
  have hU : PlurisubharmonicOn U Ω := hpsh
  have hUq : ∀ y ∈ Ω, U y ≤ (q y : EReal) := by
    intro y _
    simp only [hUdef, hqdef, chartFunction, EReal.coe_add]
    exact add_le_add_left (hle _) _
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo (e.val x) hz₀W
  set R := ε / 6 with hR
  have hR0 : 0 < R := by positivity
  have hball : closedBall (e.val x) (5 * R) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hεW
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val x) R,
    e.val.isOpen_inter_preimage isOpen_ball, ⟨hxe, mem_ball_self hR0⟩, ?_⟩
  intro S hS hSN
  have hSsrc : S ⊆ e.val.source := fun y hy => (hSN hy).1.1
  set T : Set (ComplexModel n) := e.val '' S with hT
  have hTeq : T = e.val.target ∩ e.val.symm ⁻¹' S :=
    e.val.image_eq_target_inter_inv_preimage hSsrc
  have hTm : MeasurableSet T := by
    rw [hTeq]
    exact SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
      e.val.open_target.measurableSet
      e.val.continuousOn_symm hS
  have hTt : T ⊆ e.val.target := by rw [hTeq]; exact inter_subset_left
  have hST : S = e.val.symm '' T := (e.val.symm_image_image_of_subset_source hSsrc).symm
  have hTball : T ⊆ ball (e.val x) R := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hSN hy).1.2
  have hTΩ : T ⊆ Ω := hTball.trans (ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hball))
  have hTC : T ⊆ {z | z ∈ Ω ∧ U z = (q z : EReal)} ∩ ball (e.val x) R := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨hTΩ ⟨y, hy, rfl⟩, ?_⟩, hTball ⟨y, hy, rfl⟩⟩
    have hyE : u y = (f y : EReal) := (hSN hy).2
    simp only [hUdef, hqdef, chartFunction, e.val.left_inv (hSsrc hy), EReal.coe_add, hyE]
  -- the patch of the global measure
  let P : Patch (fun _ : Fin n => θ) (fun _ => u) :=
    { chart := e
      domain := Ω
      domain_le_target := hWt
      potential := fun _ => ρ
      localPotential := fun _ => hρ
      plurisubharmonic := fun _ => hpsh }
  have hSP : S ⊆ (P.source : Set M) := by
    intro y hy
    exact ⟨hSsrc hy, hTΩ ⟨y, hy, rfl⟩⟩
  have hrhs : diagonalPotentialMeasure θ u hu S = truncationLimitMeasure Ω U hU T := by
    have h1 : diagonalPotentialMeasure θ u hu S =
        (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu.1)).restrict
          (P.source : Set M) S := (Measure.restrict_eq_self _ hSP).symm
    rw [h1, globalMixedMeasure_restrict_patch, patchMeasure, Patch.pushMeasure_apply_image,
      inter_eq_left.mpr hSP]
    change MixedNonPluripolar.mixedTruncationLimitMeasure Ω (fun _ => U) (fun _ => hU) T = _
    rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn hU]
  rw [hrhs, hST, positiveTopMeasure_eq_topFormMeasure,
    TranscendentalWN.topFormMeasure_image_eq w _ e hTm hTt]
  refine le_of_eq_of_le ?_ (ContactLocal.truncationLimitMeasure_contact_ge hn hU hqW hUq hR0 hball
    hTC)
  refine setLIntegral_congr_fun hTm fun z hz => ?_
  rw [TranscendentalWN.smoothDensity_eq_topDensity_formPow θ hf hρ (hTΩ hz)]

/-- **The Di Nezza–Trapani contact formula for smooth obstacles**, diagonal case
(`tok-wn-reg:dnt-smooth`): `𝟙_E ⟨(θ + ddᶜu)ⁿ⟩ = 𝟙_E (θ + ddᶜf)ⁿ`, `E = {u = f}`. -/
theorem diagonalPotentialMeasure_restrict_contact_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict {x | u x = (f x : EReal)} := by
  refine le_antisymm ?_ ?_
  · rw [positiveTopMeasure_eq_topFormMeasure]
    exact TranscendentalWN.diagonalPotentialMeasure_restrict_contact_le w θ hu hf hle
  · have h := positiveTopMeasure_restrict_contact_le w θ hu hf hle
    calc (positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict {x | u x = (f x : EReal)}
        = ((positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict
            {x | u x = (f x : EReal)}).restrict {x | u x = (f x : EReal)} :=
          (Measure.restrict_restrict_of_subset subset_rfl).symm
      _ ≤ (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} :=
          Measure.restrict_mono subset_rfl h

end Measures

/-- The constant function as an obstacle: `θ + ddᶜc = θ`. -/
theorem add_ddcClosedForm_const (θ : ClosedRealOneOneForm n M) (c : ℝ) :
    θ + ddcClosedForm (fun _ : M => c) (chartSmooth_const c) = θ := by
  ext e z
  simp [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]

/-- **`DNTSmoothContactStatement`** (`tok-wn-reg:dnt-smooth`; the book's `thm:DNTcontact` for
`θᵢ = θ`, `φᵢ = u`, `fᵢ = f` smooth). -/
theorem dntSmoothContactStatement : DNTSmoothContactStatement.{u} := by
  intro N M _ _ _ _ _ _ _ w θ u hu f hf hle
  exact diagonalPotentialMeasure_restrict_contact_eq w θ hu hf hle

/-- **`DNTConstantObstacleStatement`** (`tok-wn-reg:dnt-constant`, `tok-wn:dnt` as WN-KEY uses it):
`u ∈ PSH(M, θ)`, `u ≤ c` gives `𝟙_{u = c} θⁿ ≤ ⟨(θ + ddᶜu)ⁿ⟩`. -/
theorem dntConstantObstacleStatement : DNTConstantObstacleStatement.{u} := by
  intro N M _ _ _ _ _ _ _ w θ u hu c hle
  have h := positiveTopMeasure_restrict_contact_le w θ hu (chartSmooth_const c) hle
  rwa [add_ddcClosedForm_const] at h

/-- **`WNRegStatement`**: the package statement consumed by WN-KEY (Berman's estimate for smooth
obstacles and the contact formula for constant obstacles). -/
theorem wnRegStatement : WNRegStatement.{u} :=
  ⟨bermanSmoothEnvelopeStatement, dntConstantObstacleStatement⟩

end SGPT.Okounkov.TranscendentalWNReg
