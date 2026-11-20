import SGPT.PSH.TorusInvariantFinite
import SGPT.PSH.Components
import SGPT.Convex.LaurentPolytope
import SGPT.Foundations.Analysis.Pending.ConvexExhaustion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

noncomputable section
namespace SGPT.Toric
open Set Filter Metric SGPT.Convex SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- The original standard complex torus, as its actual open coordinate locus. -/
def complexTorus (n : ℕ) : Set (ComplexModel n) := {z | ∀ i, z i ≠ 0}

/-- Actual original twice-logarithmic modulus coordinates; source conclusions use the torus locus. -/
def tropicalization {n : ℕ} (z : ComplexModel n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ 2 * Real.log ‖z i‖)

/-- The literal pullback of the original extended convex function. -/
def tropicalPullback {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EReal) (z : ComplexModel n) : EReal :=
  F (tropicalization z)

theorem isOpen_complexTorus (n : ℕ) : IsOpen (complexTorus n) := by
  change IsOpen {z : ComplexModel n | ∀ i, z i ≠ 0}
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦ isOpen_ne.preimage (PiLp.continuous_apply 2 _ i))

/-- This is the already-checked original Laurent logarithmic coordinate formula. -/
theorem tropicalization_eq_torusLogCoordinates {n : ℕ} (z : ComplexModel n)
    (hz : z ∈ complexTorus n) :
    (tropicalization z).ofLp = torusLogCoordinates ⟨z.ofLp, hz⟩ := rfl

/-- The original squared-modulus normalization is retained exactly. -/
theorem tropicalization_apply_eq_log_norm_sq {n : ℕ} (z : ComplexModel n) (i : Fin n) :
    tropicalization z i = Real.log (‖z i‖ ^ 2) := by
  simp [tropicalization, Real.log_pow]

/-- Actual exponentials produce every original real tropical coordinate. -/
def expCoordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ (Real.exp (x i / 2) : ℂ))

theorem expCoordinates_mem_complexTorus {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    expCoordinates x ∈ complexTorus n := by
  intro i
  change (Real.exp (x i / 2) : ℂ) ≠ 0
  exact_mod_cast Real.exp_ne_zero (x i / 2)

theorem tropicalization_expCoordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    tropicalization (expCoordinates x) = x := by
  ext i
  change 2 * Real.log ‖(Real.exp (x i / 2) : ℂ)‖ = x i
  simp only [Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp]
  ring

/-- The genuine holomorphic exponential line has the original real segment parameters. -/
def tropicalExponentialLine {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (w : ℂ) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ Complex.exp (((x i : ℂ) + w * ((y i - x i : ℝ) : ℂ)) / 2))

theorem differentiable_tropicalExponentialLine {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    Differentiable ℂ (tropicalExponentialLine x y) := by
  apply (differentiable_piLp 2).mpr
  intro i
  change Differentiable ℂ (fun w : ℂ ↦ Complex.exp (((x i : ℂ) + w * ((y i - x i : ℝ) : ℂ)) / 2))
  fun_prop

theorem tropicalExponentialLine_mem_complexTorus {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (w : ℂ) :
    tropicalExponentialLine x y w ∈ complexTorus n := by
  intro i
  exact Complex.exp_ne_zero _

theorem tropicalization_tropicalExponentialLine {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (w : ℂ) :
    tropicalization (tropicalExponentialLine x y w) = x + w.re • (y - x) := by
  ext i
  change 2 * Real.log ‖Complex.exp (((x i : ℂ) + w * ((y i - x i : ℝ) : ℂ)) / 2)‖ =
    x i + w.re * (y i - x i)
  simp only [
    Complex.norm_exp, Real.log_exp, Complex.div_ofNat_re, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- Actual twice-real coordinates in the original logarithmic normalization. -/
def twiceRealCoordinates {n : ℕ} (w : ComplexModel n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ 2 * (w i).re)

theorem continuous_twiceRealCoordinates {n : ℕ} : Continuous (@twiceRealCoordinates n) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i ↦ by fun_prop))

theorem twiceRealCoordinates_combo {n : ℕ} (x y : ComplexModel n) (a b : ℝ) :
    twiceRealCoordinates (a • x + b • y) =
      a • twiceRealCoordinates x + b • twiceRealCoordinates y := by
  ext i
  change 2 * (a • x i + b • y i).re = a * (2 * (x i).re) + b * (2 * (y i).re)
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- Main's genuine real-convex to PSH producer applies to the actual twice-real pullback. -/
theorem plurisubharmonicOn_twiceRealCoordinates {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    PlurisubharmonicOn (fun w : ComplexModel n ↦ (f (twiceRealCoordinates w) : EReal)) univ := by
  have hconv : ConvexOn ℝ univ (fun w : ComplexModel n ↦ f (twiceRealCoordinates w)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    change f (twiceRealCoordinates (a • x + b • y)) ≤
      a • f (twiceRealCoordinates x) + b • f (twiceRealCoordinates y)
    rw [twiceRealCoordinates_combo]
    exact hf.2 (mem_univ _) (mem_univ _) ha hb hab
  have hc : Continuous (fun w : ComplexModel n ↦ f (twiceRealCoordinates w)) :=
    (continuousOn_univ.mp (hf.continuousOn isOpen_univ)).comp continuous_twiceRealCoordinates
  exact Pending.plurisubharmonicOn_of_convexOn isOpen_univ hconv hc.continuousOn

/-- The genuine local logarithm domain uses actual ratios in the slit plane. -/
def toricLogDomain {n : ℕ} (z : ComplexModel n) : Set (ComplexModel n) :=
  {w | ∀ i, w i / z i ∈ Complex.slitPlane}

/-- Actual local logarithm branches retain all original coordinate moduli. -/
def localToricLog {n : ℕ} (z w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ Complex.log (w i / z i) + (Real.log ‖z i‖ : ℂ))

theorem isOpen_toricLogDomain {n : ℕ} (z : ComplexModel n) : IsOpen (toricLogDomain z) := by
  change IsOpen {w : ComplexModel n | ∀ i, w i / z i ∈ Complex.slitPlane}
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦ Complex.isOpen_slitPlane.preimage (by fun_prop))

theorem self_mem_toricLogDomain {n : ℕ} {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    z ∈ toricLogDomain z := by
  intro i
  rw [div_self (hz i)]
  exact Complex.ofReal_mem_slitPlane.mpr (by norm_num)

theorem differentiableOn_localToricLog {n : ℕ} (z : ComplexModel n) :
    DifferentiableOn ℂ (localToricLog z) (toricLogDomain z) := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  apply (differentiableAt_piLp 2).mpr
  intro i
  change DifferentiableAt ℂ (fun w : ComplexModel n ↦
    Complex.log (w i / z i) + (Real.log ‖z i‖ : ℂ)) w
  have hdiv : DifferentiableAt ℂ (fun w : ComplexModel n ↦ w i / z i) w := by fun_prop
  exact ((Complex.differentiableAt_log (hw i)).comp w hdiv).add_const _

theorem twiceRealCoordinates_localToricLog {n : ℕ} {z w : ComplexModel n}
    (hz : z ∈ complexTorus n) (hw : w ∈ toricLogDomain z) :
    twiceRealCoordinates (localToricLog z w) = tropicalization w := by
  ext i
  have hwi : w i ≠ 0 := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero (hw i))).1
  change 2 * (Complex.log (w i / z i) + (Real.log ‖z i‖ : ℂ)).re = 2 * Real.log ‖w i‖
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hwi) (norm_ne_zero_iff.mpr (hz i))]
  ring

/-- Actual local logarithms and main's convex PSH producer give the original tropical pullback. -/
theorem plurisubharmonicOn_tropicalPullback_of_convexOn {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    PlurisubharmonicOn (tropicalPullback (fun x ↦ (f x : EReal))) (complexTorus n) := by
  intro z hz
  have hraw : PlurisubharmonicOn
      (fun w ↦ (f (twiceRealCoordinates (localToricLog z w)) : EReal)) (toricLogDomain z) :=
    Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
      (isOpen_toricLogDomain z) (differentiableOn_localToricLog z)
      (fun _ _ ↦ mem_univ _) (plurisubharmonicOn_twiceRealCoordinates hf)
  apply (hraw z (self_mem_toricLogDomain hz)).congr
  filter_upwards [(isOpen_toricLogDomain z).mem_nhds (self_mem_toricLogDomain hz)] with w hw
  change (f (twiceRealCoordinates (localToricLog z w)) : EReal) = (f (tropicalization w) : EReal)
  rw [twiceRealCoordinates_localToricLog hz hw]

/-- True finite values supply the source non-bottom clause for the original tropical PSH pullback. -/
theorem pshOn_tropicalPullback_of_convexOn {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    PSHOn (tropicalPullback (fun x ↦ (f x : EReal))) (complexTorus n) :=
  ⟨(plurisubharmonicOn_tropicalPullback_of_convexOn hf).discPshOn,
    expCoordinates 0, expCoordinates_mem_complexTorus 0, EReal.coe_ne_bot _⟩

/-- True original coordinate dilations, used only with produced positive scales. -/
def toricScaling {n : ℕ} (R : Fin n → ℝ) (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ (R i : ℂ) * w i)

def toricUnscale {n : ℕ} (R : Fin n → ℝ) (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ w i / (R i : ℂ))

theorem differentiable_toricScaling {n : ℕ} (R : Fin n → ℝ) :
    Differentiable ℂ (toricScaling R) := by
  apply (differentiable_piLp 2).mpr
  intro i
  change Differentiable ℂ (fun w : ComplexModel n ↦ (R i : ℂ) * w i)
  fun_prop

theorem toricScaling_toricUnscale {n : ℕ} (R : Fin n → ℝ) (hR : ∀ i, R i ≠ 0)
    (z : ComplexModel n) : toricScaling R (toricUnscale R z) = z := by
  ext i
  change (R i : ℂ) * (z i / (R i : ℂ)) = z i
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hR i))

theorem toricUnscale_mem_puncturedPolydisc {n : ℕ} (R : Fin n → ℝ)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) (hR : ∀ i, ‖z i‖ < R i) :
    toricUnscale R z ∈ puncturedPolydisc n := by
  intro i
  have hpos : 0 < R i := (norm_nonneg _).trans_lt (hR i)
  change 0 < ‖z i / (R i : ℂ)‖ ∧ ‖z i / (R i : ℂ)‖ < 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact ⟨div_pos (norm_pos_iff.mpr (hz i)) hpos, (div_lt_one hpos).mpr (hR i)⟩

/-- Original unit rotations preserve the literal tropical pullback after genuine coordinate scaling. -/
theorem torusInvariantOnPuncturedPolydisc_toricScaling {n : ℕ}
    (R : Fin n → ℝ) (F : EuclideanSpace ℝ (Fin n) → EReal) :
    TorusInvariantOnPuncturedPolydisc (fun w ↦ tropicalPullback F (toricScaling R w)) := by
  intro w _hw θ hθ
  apply congrArg F
  ext i
  change 2 * Real.log ‖(R i : ℂ) * (θ i * w i)‖ = 2 * Real.log ‖(R i : ℂ) * w i‖
  simp only [norm_mul, hθ i, one_mul]

/-- Actual dilations reduce original global torus finiteness to the already-proved punctured-disc theorem. -/
theorem tropicalPullback_finite_of_pshOn {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EReal}
    (hu : PSHOn (tropicalPullback F) (complexTorus n)) :
    ∀ z ∈ complexTorus n, tropicalPullback F z ≠ ⊤ ∧ tropicalPullback F z ≠ ⊥ := by
  obtain ⟨p, hp, hpn⟩ := hu.nontrivial
  intro z hz
  let R : Fin n → ℝ := fun i ↦ ‖z i‖ + ‖p i‖ + 1
  have hRz (i) : ‖z i‖ < R i := by dsimp [R]; linarith [norm_nonneg (p i)]
  have hRp (i) : ‖p i‖ < R i := by dsimp [R]; linarith [norm_nonneg (z i)]
  have hRpos (i) : 0 < R i := (norm_nonneg _).trans_lt (hRz i)
  have hRne (i) : R i ≠ 0 := (hRpos i).ne'
  have hmaps : MapsTo (toricScaling R) (puncturedPolydisc n) (complexTorus n) := by
    intro w hw i
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hRne i)) (norm_pos_iff.mp (hw i).1)
  have hs : PSHOn (fun w ↦ tropicalPullback F (toricScaling R w)) (puncturedPolydisc n) := by
    refine ⟨discPshOn_comp_holomorphic (isOpen_puncturedPolydisc n) (isOpen_complexTorus n)
      (differentiable_toricScaling R).differentiableOn hmaps hu, toricUnscale R p,
      toricUnscale_mem_puncturedPolydisc R hp hRp, ?_⟩
    simpa only [toricScaling_toricUnscale R hRne] using hpn
  have hf := hs.finite_of_torusInvariant (torusInvariantOnPuncturedPolydisc_toricScaling R F)
    (toricUnscale R z) (toricUnscale_mem_puncturedPolydisc R hz hRz)
  simpa only [toricScaling_toricUnscale R hRne] using hf

/-- The true original tropical surjectivity recovers finite values at every original real point. -/
theorem finite_of_pshOn_tropicalPullback {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EReal}
    (hu : PSHOn (tropicalPullback F) (complexTorus n)) (x : EuclideanSpace ℝ (Fin n)) :
    F x ≠ ⊤ ∧ F x ≠ ⊥ := by
  simpa only [tropicalPullback, tropicalization_expCoordinates] using
    tropicalPullback_finite_of_pshOn hu (expCoordinates x) (expCoordinates_mem_complexTorus x)

/-- Actual coordinate exponentials cover the original complex torus. -/
def toricExponential {n : ℕ} (w : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ Complex.exp (w i))

theorem continuous_toricExponential {n : ℕ} : Continuous (@toricExponential n) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i ↦ by fun_prop))

/-- True exponential surjectivity produces connectedness of the actual source torus. -/
theorem isConnected_complexTorus (n : ℕ) : IsConnected (complexTorus n) := by
  have himage : toricExponential '' (univ : Set (ComplexModel n)) = complexTorus n := by
    ext z
    constructor
    · rintro ⟨w, _, rfl⟩ i
      exact Complex.exp_ne_zero _
    · intro hz
      refine ⟨WithLp.toLp 2 (fun i ↦ Complex.log (z i)), mem_univ _, ?_⟩
      ext i
      exact Complex.exp_log (hz i)
  rw [← himage]
  exact isConnected_univ.image _ continuous_toricExponential.continuousOn

/-- Genuine original holomorphic pullback supplies the complete exponential real line. -/
theorem discPshOn_tropicalExponentialLine {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EReal}
    (hu : PSHOn (tropicalPullback F) (complexTorus n)) (x y : EuclideanSpace ℝ (Fin n)) :
    DiscPshOn (fun w : ℂ ↦ F (x + w.re • (y - x))) univ := by
  let G : ComplexModel 1 → ComplexModel n := fun w ↦ tropicalExponentialLine x y (w 0)
  have hG : Differentiable ℂ G := (differentiable_tropicalExponentialLine x y).comp (by fun_prop)
  have hd := discPshOn_comp_holomorphic (U := univ) isOpen_univ (isOpen_complexTorus n)
    hG.differentiableOn (fun w _ ↦ tropicalExponentialLine_mem_complexTorus x y (w 0)) hu
  let L : ℂ →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 (fun _ : Fin 1 ↦ (1 : ℂ)))
  have hL (w : ℂ) : L w 0 = w := by simp [L]
  have hc := hd.comp_continuousLinearMap L
  change DiscPshOn (fun w : ℂ ↦ F (tropicalization (tropicalExponentialLine x y (L w 0))))
    (L ⁻¹' univ) at hc
  simpa only [preimage_univ, hL, tropicalization_tropicalExponentialLine] using hc

/-- True finite real line chords give convexity of the original source real values. -/
theorem convexOn_toReal_of_pshOn_tropicalPullback {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EReal}
    (hu : PSHOn (tropicalPullback F) (complexTorus n)) :
    ConvexOn ℝ univ (fun x ↦ (F x).toReal) := by
  have hfin (x) := finite_of_pshOn_tropicalPullback hu x
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hzero : b = 0
  · have hA : a = 1 := by linarith
    simp [hzero, hA]
  by_cases hzeroa : a = 0
  · have hB : b = 1 := by linarith
    simp [hzeroa, hB]
  have hb0 : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
  have hb1 : b < 1 := by have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm hzeroa); linarith
  let v : ℝ → EReal := fun s ↦ F (x + s • (y - x))
  have hv : PlurisubharmonicOn (fun w : ℂ ↦ v w.re) (Complex.re ⁻¹' (univ : Set ℝ)) := by
    simpa only [preimage_univ] using
      (discPshOn_tropicalExponentialLine hu x y).plurisubharmonicOn isOpen_univ
  have hchord := hv.comp_re_toReal_le_affine_chord hb0 hb1 (subset_univ (Icc 0 1))
    (by simpa [v] using (hfin x).1) (by simpa [v] using (hfin x).2)
    (hfin (x + b • (y - x))).1 (hfin (x + b • (y - x))).2
    (by simpa [v] using (hfin y).1) (by simpa [v] using (hfin y).2)
  have hpoint : x + b • (y - x) = a • x + b • y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    module
  have hreal : (F (x + b • (y - x))).toReal ≤
      (F x).toReal + b * ((F y).toReal - (F x).toReal) := by
    simpa [v] using hchord
  rw [hpoint] at hreal
  simp only [smul_eq_mul]
  calc
    (F (a • x + b • y)).toReal ≤ (F x).toReal + b * ((F y).toReal - (F x).toReal) := hreal
    _ = a * (F x).toReal + b * (F y).toReal := by
      linear_combination -(F x).toReal * hab

/-- Original tropical PSH produces an actual finite real convex representative of F. -/
theorem exists_real_convex_of_pshOn_tropicalPullback {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EReal}
    (hu : PSHOn (tropicalPullback F) (complexTorus n)) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ univ f ∧ F = fun x ↦ (f x : EReal) := by
  refine ⟨fun x ↦ (F x).toReal, convexOn_toReal_of_pshOn_tropicalPullback hu, ?_⟩
  funext x
  have hfin := finite_of_pshOn_tropicalPullback hu x
  exact (EReal.coe_toReal hfin.1 hfin.2).symm

/-- The actual original tropical pullback is PSH precisely for finite real convex functions. -/
theorem pshOn_tropicalPullback_iff {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EReal) :
    PSHOn (tropicalPullback F) (complexTorus n) ↔
      ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ univ f ∧ F = fun x ↦ (f x : EReal) := by
  constructor
  · exact exists_real_convex_of_pshOn_tropicalPullback
  · rintro ⟨f, hf, rfl⟩
    exact pshOn_tropicalPullback_of_convexOn hf

/-- Actual source manifold PSH agrees through the proved connected original torus. -/
theorem source_pshOn_tropicalPullback_iff {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EReal) :
    (VariableComplexAtlas.identityAtlas n).IsPSHOn (tropicalPullback F) (complexTorus n) ↔
      ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ univ f ∧ F = fun x ↦ (f x : EReal) := by
  rw [VariableComplexAtlas.identityAtlas_isPSHOn_iff
    (isOpen_complexTorus n) (isConnected_complexTorus n), pshOn_tropicalPullback_iff]

/-- Literal source finite-convex versus tropical PSH equivalence, including its original manifold predicate. -/
theorem finite_convex_iff_source_psh_tropicalPullback {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EReal) :
    (IsConvex F ∧ ∀ x, F x ≠ ⊤ ∧ F x ≠ ⊥) ↔
      (VariableComplexAtlas.identityAtlas n).IsPSHOn (tropicalPullback F) (complexTorus n) := by
  rw [source_pshOn_tropicalPullback_iff]
  constructor
  · rintro ⟨hc, hfin⟩
    have heq : F = fun x ↦ ((F x).toReal : EReal) :=
      funext (fun x ↦ (EReal.coe_toReal (hfin x).1 (hfin x).2).symm)
    refine ⟨fun x ↦ (F x).toReal, ?_, heq⟩
    rw [heq] at hc
    exact isConvex_coe_iff.mp hc
  · rintro ⟨f, hf, rfl⟩
    exact ⟨isConvex_coe_iff.mpr hf, fun x ↦ ⟨EReal.coe_ne_top (f x), EReal.coe_ne_bot (f x)⟩⟩

end SGPT.Toric
