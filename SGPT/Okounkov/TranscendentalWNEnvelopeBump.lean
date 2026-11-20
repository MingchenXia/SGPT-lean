import SGPT.MongeAmpere.LocalMongeAmpereUpperTests
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

/-!
# The quadratic comparator for contact sets (package WN-ENV, local part 1)

Blueprint chapter `claude-tok-wn-env`, node `tok-wn-env:hessian-bump`.  Elementary calculus in
`ℂⁿ` used by `SGPT.Okounkov.TranscendentalWNEnvelopeLocal`:

* `complexHessian_norm_sub_sq` — `|z - a|²` has the identity complex Hessian;
* `bump q a s c = q + s (|z - a|² - c)`, its complex Hessian `ddᶜq + s·1`
  (`complexHessian_bump`) and its smooth density `bumpDensity q s`, jointly continuous in
  `(s, z)` (`continuousOn_bumpDensity`);
* `plurisubharmonicOn_of_leviForm_nonneg_on` — a smooth function with nonnegative Levi form on
  an open set is plurisubharmonic there; `isSmoothPshOn_bump`;
* measurability of strict and contact sets of an upper semicontinuous function against a
  continuous one.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder MatrixOrder

namespace SGPT.Okounkov.TranscendentalWN.EnvelopeLocal

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere

variable {n : ℕ}

/-! ### The quadratic comparator -/

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

theorem realHessian_comp_sub (u : ComplexModel n → ℝ) (a x v w : ComplexModel n) :
    realHessian (fun y => u (y - a)) x v w = realHessian u (x - a) v w := by
  simp only [realHessian, iteratedFDeriv_comp_sub]

theorem leviForm_comp_sub (u : ComplexModel n → ℝ) (a x v : ComplexModel n) :
    leviForm (fun y => u (y - a)) x v = leviForm u (x - a) v := by
  simp only [leviForm, realHessian_comp_sub]

theorem complexHessian_comp_sub (u : ComplexModel n → ℝ) (a x : ComplexModel n) :
    complexHessian (fun y => u (y - a)) x = complexHessian u (x - a) := by
  ext j k
  simp only [complexHessian, realHessian_comp_sub]

/-- The squared distance to a point has the identity matrix as complex Hessian. -/
theorem complexHessian_norm_sub_sq (a x : ComplexModel n) :
    complexHessian (fun y : ComplexModel n => ‖y - a‖ ^ 2) x = 1 :=
  (complexHessian_comp_sub (fun y : ComplexModel n => ‖y‖ ^ 2) a x).trans
    (complexHessian_norm_sq (x - a))

theorem contDiff_norm_sub_sq (a : ComplexModel n) :
    ContDiff ℝ ∞ (fun y : ComplexModel n => ‖y - a‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

/-- The comparator `q + s (|z - a|² - c)`. -/
def bump (q : ComplexModel n → ℝ) (a : ComplexModel n) (s c : ℝ) : ComplexModel n → ℝ :=
  fun z => q z + s * (‖z - a‖ ^ 2 - c)

theorem bump_eq (q : ComplexModel n → ℝ) (a : ComplexModel n) (s c : ℝ) :
    bump q a s c = q + s • ((fun y : ComplexModel n => ‖y - a‖ ^ 2) + fun _ => -c) := by
  funext z
  simp only [bump, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem complexHessian_bump {q : ComplexModel n → ℝ} {z : ComplexModel n}
    (hq : ContDiffAt ℝ 2 q z) (a : ComplexModel n) (s c : ℝ) :
    complexHessian (bump q a s c) z = complexHessian q z + (s : ℂ) • 1 := by
  have hg : ContDiffAt ℝ 2 (fun y : ComplexModel n => ‖y - a‖ ^ 2) z :=
    ((contDiff_norm_sub_sq a).of_le two_le_infty).contDiffAt
  have hc : ContDiffAt ℝ 2 (fun _ : ComplexModel n => -c) z := contDiffAt_const
  have hgc : ContDiffAt ℝ 2 ((fun y : ComplexModel n => ‖y - a‖ ^ 2) + fun _ => -c) z :=
    hg.add hc
  have hsgc : ContDiffAt ℝ 2 (s • ((fun y : ComplexModel n => ‖y - a‖ ^ 2) + fun _ => -c)) z :=
    hgc.const_smul s
  rw [bump_eq, complexHessian_add hq hsgc, complexHessian_smul hgc, complexHessian_add hg hc,
    complexHessian_norm_sub_sq, complexHessian_const, add_zero]

/-- The explicit density `n!/πⁿ · Re det (ddᶜq + s·1)`. -/
def bumpDensity (q : ComplexModel n → ℝ) (s : ℝ) (z : ComplexModel n) : ℝ :=
  (n.factorial : ℝ) / Real.pi ^ n * (complexHessian q z + (s : ℂ) • 1).det.re

theorem smoothDensity_bump {q : ComplexModel n → ℝ} {z : ComplexModel n}
    (hq : ContDiffAt ℝ 2 q z) (a : ComplexModel n) (s c : ℝ) :
    smoothDensity (bump q a s c) z = bumpDensity q s z := by
  rw [smoothDensity, complexHessian_bump hq, bumpDensity]

theorem bumpDensity_zero (q : ComplexModel n → ℝ) (z : ComplexModel n) :
    bumpDensity q 0 z = smoothDensity q z := by
  simp [bumpDensity, smoothDensity]

/-- The complex Hessian of a smooth function is continuous on an open set. -/
theorem continuousOn_complexHessian {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) :
    ContinuousOn (fun z => complexHessian q z) Ω := by
  have h2 : ContinuousOn (iteratedFDeriv ℝ 2 q) Ω :=
    (hq.continuousOn_iteratedFDerivWithin two_le_infty hΩ.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen 2 hΩ).symm
  have hH : ∀ v w : ComplexModel n, ContinuousOn (fun z => realHessian q z v w) Ω := fun v w =>
    (continuous_eval_const (![v, w] : Fin 2 → ComplexModel n)).comp_continuousOn h2
  refine continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => ?_
  simp only [complexHessian]
  have hre := ((hH (coordinateVector j) (coordinateVector k)).add
    (hH (Complex.I • coordinateVector j) (Complex.I • coordinateVector k)))
  have him := ((hH (coordinateVector j) (Complex.I • coordinateVector k)).sub
    (hH (Complex.I • coordinateVector j) (coordinateVector k)))
  exact ((Complex.continuous_ofReal.comp_continuousOn hre).div_const 4).add
    ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn him)).div_const 4)

/-- The explicit density is jointly continuous in `(s, z)`. -/
theorem continuousOn_bumpDensity {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) :
    ContinuousOn (fun p : ℝ × ComplexModel n => bumpDensity q p.1 p.2) (univ ×ˢ Ω) := by
  have hH : ContinuousOn (fun p : ℝ × ComplexModel n => complexHessian q p.2) (univ ×ˢ Ω) :=
    (continuousOn_complexHessian hΩ hq).comp continuous_snd.continuousOn
      (fun p hp => (mem_prod.mp hp).2)
  have hs : ContinuousOn (fun p : ℝ × ComplexModel n =>
      ((p.1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) (univ ×ˢ Ω) :=
    ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const).continuousOn
  have hdet : ContinuousOn (fun p : ℝ × ComplexModel n =>
      (complexHessian q p.2 + (p.1 : ℂ) • 1).det) (univ ×ˢ Ω) :=
    (continuous_id.matrix_det).comp_continuousOn (hH.add hs)
  exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hdet)

/-- The explicit density is continuous in the parameter. -/
theorem continuous_bumpDensity_param (q : ComplexModel n → ℝ) (z : ComplexModel n) :
    Continuous fun σ : ℝ => bumpDensity q σ z := by
  have h : Continuous fun σ : ℝ =>
      (complexHessian q z + (σ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det :=
    (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).matrix_det
  exact continuous_const.mul (Complex.continuous_re.comp h)

/-- The explicit density is continuous in the point, for a fixed parameter. -/
theorem continuousOn_bumpDensity_point {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) (σ : ℝ) :
    ContinuousOn (fun z => bumpDensity q σ z) Ω := by
  have hdet : ContinuousOn (fun z =>
      (complexHessian q z + (σ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det) Ω :=
    (continuous_id.matrix_det).comp_continuousOn
      ((continuousOn_complexHessian hΩ hq).add continuousOn_const)
  exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hdet)

/-- The smooth density of a smooth function is continuous on an open set. -/
theorem continuousOn_smoothDensity {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {q : ComplexModel n → ℝ} (hq : ContDiffOn ℝ ∞ q Ω) :
    ContinuousOn (fun z => smoothDensity q z) Ω :=
  (continuousOn_bumpDensity_point hΩ hq 0).congr fun z _ => (bumpDensity_zero q z).symm

/-! ### Plurisubharmonicity from the Levi form -/

/-- A smooth function on an open set with nonnegative Levi form is plurisubharmonic there. -/
theorem plurisubharmonicOn_of_leviForm_nonneg_on {W : Set (ComplexModel n)}
    {h : ComplexModel n → ℝ} (hW : IsOpen W) (hh : ContDiffOn ℝ ∞ h W)
    (hlevi : ∀ z ∈ W, ∀ v, 0 ≤ leviForm h z v) :
    PlurisubharmonicOn (fun z => (h z : EReal)) W := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hW hh hx
  have hmem : {y | h y = g y} ∩ W ∈ 𝓝 x := inter_mem heq (hW.mem_nhds hx)
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hmem
  have heqV : EqOn h g V := fun y hy => (hVsub hy).1
  have hlevig : ∀ y ∈ V, ∀ v, 0 ≤ leviForm g y v := by
    intro y hy v
    have hloc : h =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with t ht
      exact heqV ht
    have hH : iteratedFDeriv ℝ 2 h y = iteratedFDeriv ℝ 2 g y :=
      (hloc.iteratedFDeriv ℝ 2).eq_of_nhds
    have hL : leviForm h y v = leviForm g y v := by
      simp only [leviForm, realHessian, hH]
    rw [← hL]
    exact hlevi y (hVsub hy).2 v
  have hpshg : PlurisubharmonicOn (fun y => (g y : EReal)) V :=
    plurisubharmonicOn_of_levi_nonneg (hg.of_le two_le_infty) hV hlevig
  apply (hpshg x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  rw [heqV hy]

/-- The comparator of a smooth plurisubharmonic function is smooth plurisubharmonic. -/
theorem isSmoothPshOn_bump {Ω : Opens (ComplexModel n)} {q : ComplexModel n → ℝ}
    (hq : IsSmoothPshOn Ω q) (a : ComplexModel n) {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    IsSmoothPshOn Ω (bump q a s c) := by
  have hb : ContDiff ℝ ∞ (fun z : ComplexModel n => s * (‖z - a‖ ^ 2 - c)) :=
    contDiff_const.mul ((contDiff_norm_sub_sq a).sub contDiff_const)
  refine ⟨hq.1.add hb.contDiffOn, ?_, ?_⟩
  · have hbpsh : PlurisubharmonicOn
        (fun z => ((s * (‖z - a‖ ^ 2 - c) : ℝ) : EReal)) (Ω : Set (ComplexModel n)) := by
      refine plurisubharmonicOn_of_levi_nonneg (hb.of_le two_le_infty) Ω.isOpen ?_
      intro z _ v
      have hg : ContDiffAt ℝ 2 (fun y : ComplexModel n => ‖y - a‖ ^ 2) z :=
        ((contDiff_norm_sub_sq a).of_le two_le_infty).contDiffAt
      have hc : ContDiffAt ℝ 2 (fun _ : ComplexModel n => -c) z := contDiffAt_const
      have hfun : (fun z : ComplexModel n => s * (‖z - a‖ ^ 2 - c)) =
          s • ((fun y : ComplexModel n => ‖y - a‖ ^ 2) + fun _ => -c) := by
        funext y
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hgc : ContDiffAt ℝ 2 ((fun y : ComplexModel n => ‖y - a‖ ^ 2) + fun _ => -c) z :=
        hg.add hc
      rw [hfun, leviForm_smul hgc, leviForm_add hg hc, leviForm_const, add_zero,
        leviForm_comp_sub (fun y : ComplexModel n => ‖y‖ ^ 2)]
      exact mul_nonneg hs (leviForm_norm_sq_nonneg _ _)
    have h := hq.2.1.add hbpsh
    simpa only [bump, EReal.coe_add] using h
  · intro z hz
    have hq2 : ContDiffAt ℝ 2 q z :=
      ((hq.1 z hz).contDiffAt (Ω.isOpen.mem_nhds hz)).of_le two_le_infty
    rw [complexHessian_bump hq2]
    exact (hq.2.2 z hz).add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hs))

/-! ### Measurability of contact and strict sets -/

theorem measurableSet_lt_of_upperSemicontinuousOn {Ω : Opens (ComplexModel n)}
    {g V : ComplexModel n → ℝ} (hg : ContinuousOn g Ω)
    (hV : UpperSemicontinuousOn (fun z => (V z : EReal)) Ω) :
    MeasurableSet {z | z ∈ Ω ∧ g z < V z} := by
  have humE : Measurable (fun z : Ω => (V z : EReal)) := by
    have hsc : UpperSemicontinuousOn (fun z : Ω => (V z : EReal)) univ :=
      hV.comp continuous_subtype_val.continuousOn (fun z _ => z.property)
    exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  have hum : Measurable (fun z : Ω => V z) := by
    simpa only [EReal.toReal_coe] using humE.ereal_toReal
  have hgm : Measurable (fun z : Ω => g z) :=
    (continuousOn_iff_continuous_domRestrict.mp hg).measurable
  have hs := Ω.isOpen.measurableSet.subtype_image (measurableSet_lt hgm hum)
  convert hs using 1
  ext z
  exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩, fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.property, hw⟩⟩

theorem measurableSet_eq_of_upperSemicontinuousOn {Ω : Opens (ComplexModel n)}
    {g V : ComplexModel n → ℝ} (hg : ContinuousOn g Ω)
    (hV : UpperSemicontinuousOn (fun z => (V z : EReal)) Ω) :
    MeasurableSet {z | z ∈ Ω ∧ V z = g z} := by
  have humE : Measurable (fun z : Ω => (V z : EReal)) := by
    have hsc : UpperSemicontinuousOn (fun z : Ω => (V z : EReal)) univ :=
      hV.comp continuous_subtype_val.continuousOn (fun z _ => z.property)
    exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  have hum : Measurable (fun z : Ω => V z) := by
    simpa only [EReal.toReal_coe] using humE.ereal_toReal
  have hgm : Measurable (fun z : Ω => g z) :=
    (continuousOn_iff_continuous_domRestrict.mp hg).measurable
  have hs := Ω.isOpen.measurableSet.subtype_image (measurableSet_eq_fun hum hgm)
  convert hs using 1
  ext z
  exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩, fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.property, hw⟩⟩

end SGPT.Okounkov.TranscendentalWN.EnvelopeLocal
