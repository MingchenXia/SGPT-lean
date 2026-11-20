import SGPT.PSH.SubharmonicStrip
import SGPT.PSH.HolomorphicPullback
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.WithLp

noncomputable section
namespace SGPT.PSH
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- The literal original coordinate product of punctured unit discs. -/
def puncturedPolydisc (n : ℕ) : Set (ComplexModel n) :=
  {z | ∀ i, 0 < ‖z i‖ ∧ ‖z i‖ < 1}

/-- The actual coordinatewise action of unit complex rotations. -/
def coordinateRotation {n : ℕ} (θ : Fin n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ θ i * z i)

/-- Original torus invariance, using the genuine coordinate action. -/
def TorusInvariantOnPuncturedPolydisc {n : ℕ} (u : ComplexModel n → EReal) : Prop :=
  ∀ z ∈ puncturedPolydisc n, ∀ θ : Fin n → ℂ, (∀ i, ‖θ i‖ = 1) →
    u (coordinateRotation θ z) = u z

theorem isOpen_puncturedPolydisc (n : ℕ) : IsOpen (puncturedPolydisc n) := by
  change IsOpen {z : ComplexModel n | ∀ i, 0 < ‖z i‖ ∧ ‖z i‖ < 1}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun z : ComplexModel n ↦ ‖z i‖) := by fun_prop
  exact (isOpen_lt (continuous_const : Continuous (fun _ : ComplexModel n ↦ (0 : ℝ))) hc).inter
    (isOpen_lt hc continuous_const)

/-- Unit rotations genuinely transport every pair with equal original moduli. -/
theorem TorusInvariantOnPuncturedPolydisc.eq_of_coordinate_norm_eq {n : ℕ}
    {u : ComplexModel n → EReal} (hu : TorusInvariantOnPuncturedPolydisc u)
    {x y : ComplexModel n} (hx : x ∈ puncturedPolydisc n)
    (hxy : ∀ i, ‖y i‖ = ‖x i‖) : u y = u x := by
  let θ : Fin n → ℂ := fun i ↦ y i / x i
  have hθ (i : Fin n) : ‖θ i‖ = 1 := by
    dsimp [θ]
    rw [norm_div, hxy i, div_self (ne_of_gt (hx i).1)]
  have heq : coordinateRotation θ x = y := by
    ext i
    exact div_mul_cancel₀ (y i) (norm_pos_iff.mp (hx i).1)
  exact heq ▸ hu x hx θ hθ

/-- The actual holomorphic exponential line retains the starting point's phases. -/
def exponentialModulusLine {n : ℕ} (x y : ComplexModel n) (w : ℂ) : ComplexModel n :=
  WithLp.toLp 2 (fun i ↦ Complex.exp (Complex.log (y i) +
    w * (((Complex.log (x i)).re - (Complex.log (y i)).re : ℝ) : ℂ)))

theorem norm_exponentialModulusLine {n : ℕ} (x y : ComplexModel n) (w : ℂ) (i : Fin n) :
    ‖exponentialModulusLine x y w i‖ = Real.exp ((Complex.log (y i)).re +
      w.re * ((Complex.log (x i)).re - (Complex.log (y i)).re)) := by
  simp [exponentialModulusLine, Complex.norm_exp, Complex.mul_re]

theorem differentiable_exponentialModulusLine {n : ℕ} (x y : ComplexModel n) :
    Differentiable ℂ (exponentialModulusLine x y) := by
  apply (differentiable_piLp 2).mpr
  intro i
  change Differentiable ℂ (fun w : ℂ ↦ Complex.exp (Complex.log (y i) +
    w * (((Complex.log (x i)).re - (Complex.log (y i)).re : ℝ) : ℂ)))
  fun_prop

/-- The genuine real domain whose entire imaginary tube maps into the source. -/
def logModulusLineDomain {n : ℕ} (x y : ComplexModel n) : Set ℝ :=
  {s | ∀ i, (Complex.log (y i)).re +
    s * ((Complex.log (x i)).re - (Complex.log (y i)).re) < 0}

theorem isOpen_logModulusLineDomain {n : ℕ} (x y : ComplexModel n) :
    IsOpen (logModulusLineDomain x y) := by
  change IsOpen {s : ℝ | ∀ i : Fin n, _}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem exponentialModulusLine_mem {n : ℕ} (x y : ComplexModel n) {w : ℂ}
    (hw : w.re ∈ logModulusLineDomain x y) : exponentialModulusLine x y w ∈ puncturedPolydisc n := by
  intro i
  rw [norm_exponentialModulusLine]
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (hw i)⟩

theorem logModulusLineDomain_Icc_subset {n : ℕ} (x y : ComplexModel n) {a b : ℝ}
    (ha : a ∈ logModulusLineDomain x y) (hb : b ∈ logModulusLineDomain x y) :
    Icc a b ⊆ logModulusLineDomain x y := by
  intro s hs i
  by_cases hd : 0 ≤ (Complex.log (x i)).re - (Complex.log (y i)).re
  · have hm := mul_le_mul_of_nonneg_right hs.2 hd
    have h := hb i
    change (Complex.log (y i)).re +
      s * ((Complex.log (x i)).re - (Complex.log (y i)).re) < 0
    linarith

  · have hm := mul_le_mul_of_nonpos_right hs.1 (le_of_not_ge hd)
    have h := ha i
    change (Complex.log (y i)).re +
      s * ((Complex.log (x i)).re - (Complex.log (y i)).re) < 0
    linarith

/-- Original punctured-disc points produce an actual open real strip around
both line parameters, including in dimension zero. -/
theorem exists_strip_in_logModulusLineDomain {n : ℕ} {x y : ComplexModel n}
    (hx : x ∈ puncturedPolydisc n) (hy : y ∈ puncturedPolydisc n) :
    ∃ a b : ℝ, a < 0 ∧ 1 < b ∧ Ioo a b ⊆ logModulusLineDomain x y := by
  have h0 : (0 : ℝ) ∈ logModulusLineDomain x y := by
    intro i
    simpa [Complex.log_re] using Real.log_neg (hy i).1 (hy i).2
  have h1 : (1 : ℝ) ∈ logModulusLineDomain x y := by
    intro i
    simpa [Complex.log_re] using Real.log_neg (hx i).1 (hx i).2
  obtain ⟨c, d, hcd, hcdJ⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_logModulusLineDomain x y).mem_nhds h0)
  obtain ⟨e, f, hef, hefJ⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_logModulusLineDomain x y).mem_nhds h1)
  let a := c / 2
  let b := (1 + f) / 2
  have ha0 : a < 0 := by dsimp [a]; linarith [hcd.1]
  have h1b : 1 < b := by dsimp [b]; linarith [hef.2]
  have ha : a ∈ logModulusLineDomain x y :=
    hcdJ ⟨by dsimp [a]; linarith [hcd.1], by dsimp [a]; linarith [hcd.1, hcd.2]⟩
  have hb : b ∈ logModulusLineDomain x y :=
    hefJ ⟨by dsimp [b]; linarith [hef.1, hef.2], by dsimp [b]; linarith [hef.2]⟩
  exact ⟨a, b, ha0, h1b, Ioo_subset_Icc_self.trans (logModulusLineDomain_Icc_subset x y ha hb)⟩

/-- Actual holomorphic pullback, transported from the existing model theorem
by a genuine complex linear map, rather than reproving singular pullback. -/
theorem discPshOn_exponentialModulusLine {n : ℕ} {u : ComplexModel n → EReal}
    (hu : PSHOn u (puncturedPolydisc n)) (x y : ComplexModel n) {a b : ℝ}
    (hI : Ioo a b ⊆ logModulusLineDomain x y) :
    DiscPshOn (fun w : ℂ ↦ u (exponentialModulusLine x y w)) (Complex.re ⁻¹' Ioo a b) := by
  let F : ComplexModel 1 → ComplexModel n := fun w ↦ exponentialModulusLine x y (w 0)
  let V : Set (ComplexModel 1) := {w | (w 0).re ∈ Ioo a b}
  have hV : IsOpen V := isOpen_Ioo.preimage (by fun_prop)
  have hF : Differentiable ℂ F := (differentiable_exponentialModulusLine x y).comp (by fun_prop)
  have hFV : MapsTo F V (puncturedPolydisc n) := fun w hw ↦
    exponentialModulusLine_mem x y (hI hw)
  have hc := discPshOn_comp_holomorphic hV (isOpen_puncturedPolydisc n) hF.differentiableOn hFV hu
  let L : ℂ →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 (fun _ : Fin 1 ↦ (1 : ℂ)))
  have hL (w : ℂ) : L w 0 = w := by simp [L]
  have hd := hc.comp_continuousLinearMap L
  have hDom : L ⁻¹' V = Complex.re ⁻¹' Ioo a b := by
    ext w
    change (L w 0).re ∈ Ioo a b ↔ w.re ∈ Ioo a b
    rw [hL]
  rw [hDom] at hd
  change DiscPshOn (fun w : ℂ ↦ u (exponentialModulusLine x y (L w 0))) _ at hd
  simpa only [hL] using hd

/-- Torus invariance gives actual equality with the real-parameter line at
every original complex point, by the produced equality of all moduli. -/
theorem TorusInvariantOnPuncturedPolydisc.exponentialModulusLine_eq_re {n : ℕ}
    {u : ComplexModel n → EReal} (hu : TorusInvariantOnPuncturedPolydisc u)
    (x y : ComplexModel n) {w : ℂ} (hw : w.re ∈ logModulusLineDomain x y) :
    u (exponentialModulusLine x y w) = u (exponentialModulusLine x y (w.re : ℂ)) := by
  apply hu.eq_of_coordinate_norm_eq (exponentialModulusLine_mem x y (by simpa using hw))
  intro i
  simp only [norm_exponentialModulusLine, Complex.ofReal_re]

/-- Literal source finiteness on the entire punctured polydisc. A produced
strip through the source non-pole point and every target point supplies the
original subharmonic hypothesis; no finite slice certificate is an input. -/
theorem PSHOn.finite_of_torusInvariant {n : ℕ} {u : ComplexModel n → EReal}
    (hu : PSHOn u (puncturedPolydisc n)) (hrot : TorusInvariantOnPuncturedPolydisc u) :
    ∀ x ∈ puncturedPolydisc n, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  obtain ⟨y, hy, hyn⟩ := hu.nontrivial
  intro x hx
  refine ⟨hu.disc.ne_top x hx, ?_⟩
  obtain ⟨a, b, ha0, h1b, hI⟩ := exists_strip_in_logModulusLineDomain hx hy
  let f : ℝ → EReal := fun s ↦ u (exponentialModulusLine x y (s : ℂ))
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha0, by linarith⟩
  have h1 : (1 : ℝ) ∈ Ioo a b := ⟨by linarith, h1b⟩
  have heq : EqOn (fun w : ℂ ↦ u (exponentialModulusLine x y w))
      (fun w : ℂ ↦ f w.re) (Complex.re ⁻¹' Ioo a b) :=
    fun w hw ↦ hrot.exponentialModulusLine_eq_re x y (hI hw)
  have hdisc : DiscPshOn (fun w : ℂ ↦ f w.re) (Complex.re ⁻¹' Ioo a b) :=
    (discPshOn_exponentialModulusLine hu x y hI).congr heq
  have hstart : exponentialModulusLine x y 0 = y := by
    ext i
    simp [exponentialModulusLine, Complex.exp_log (norm_pos_iff.mp (hy i).1)]
  have hfn : f 0 ≠ ⊥ := by simpa only [f, Complex.ofReal_zero, hstart] using hyn
  have hsh : SubharmonicOn (fun w : ℂ ↦ f w.re) (Complex.re ⁻¹' Ioo a b) :=
    subharmonicOn_of_disc hdisc ⟨0, by simpa using h0, by simpa using hfn⟩
  have hf1 := hsh.comp_re_ne_bot 1 h1
  have hnorm (i : Fin n) : ‖exponentialModulusLine x y 1 i‖ = ‖x i‖ := by
    rw [norm_exponentialModulusLine]
    simpa [Complex.log_re] using Real.exp_log (hx i).1
  have hvalue : f 1 = u x := by
    exact hrot.eq_of_coordinate_norm_eq hx hnorm
  simpa only [hvalue] using hf1

end SGPT.PSH
