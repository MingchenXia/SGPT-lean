import SGPT.PSH.GlobalL2Statement
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import SGPT.Foundations.Analysis.Pending.WirtingerCalculus
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth homogeneous extensions of sections of `𝒪(k)` on a projective submanifold


Let `C ⊆ ℂ^m` be a closed cone (`c • Z ∈ C` for `Z ∈ C`, `c ∈ ℂ`) and `F` a function which is
homogeneous of degree `k` on `C` and *holomorphic on `C ∖ {0}`* in the sense that near every point
`p ∈ C ∖ {0}` it is the restriction of a holomorphic function on a neighbourhood of `p` in `ℂ^m`
(`IsLocallyHolomorphicOn`).  Geometrically `F` is a holomorphic section of `𝒪(k)` over the
projectivization `X = ℙ(C) ⊆ ℙ^{m-1}`.

`exists_smoothExtension` constructs, for `k ≥ 2`, a function `a : ℂ^m → ℂ` with
* `a` of class `C¹` on `ℂ^m` (smooth off `0`), `a = F` on `C`;
* `|∂̄a(Z)|² ≤ M |Z|^{2k-2} dist(Z, C)²` for all `Z`.

Construction: near `p ∈ C ∖ {0}`, a local holomorphic extension is made homogeneous of degree `k`
by the slice `Z ↦ (Z_i/p_i)^k h((p_i/Z_i) Z)` (`exists_localHomExt`); finitely many of them are
glued by angular cut-offs `η(Z/|Z|)` normalized to a partition of unity near `C ∖ {0}`.  The
result `G` is smooth off `0`, positively homogeneous of degree `k`, equal to `F` on `C ∖ {0}`, and
`∂̄G = 0` on `C ∖ {0}` (the cut-offs sum to one near `C`, and the local extensions agree with `F`
there).  The estimate follows from the mean value inequality for `∂̄G` on the shell
`1/2 < |Z| < 3/2` and homogeneity; `C¹` at the vertex from `|G| ≤ A|Z|^k`, `|DG| ≤ A'|Z|^{k-1}`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.PSH.GlobalL2

variable {m : ℕ}

/-! ### Generalities -/

/-- `F` is holomorphic on `C ∖ {0}` in the ambient sense: near every point of `C ∖ {0}` it is
the restriction of a holomorphic function. -/
def IsLocallyHolomorphicOn (C : Set (ComplexModel m)) (F : ComplexModel m → ℂ) : Prop :=
  ∀ p ∈ C, p ≠ 0 → ∃ U ∈ 𝓝 p, ∃ h : ComplexModel m → ℂ, DifferentiableOn ℂ h U ∧
    ∀ Z ∈ U, Z ∈ C → h Z = F Z

theorem dbarDir_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {κ : Type*}
    (s : Finset κ) {f : κ → E → ℂ} {z e : E} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbarDir e (fun y => ∑ i ∈ s, f i y) z = ∑ i ∈ s, dbarDir e (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dbarDir_const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Finset.forall_mem_insert] at hf
    rw [dbarDir_add hf.1 (DifferentiableAt.fun_sum fun i hi => hf.2 i hi), ih hf.2]

/-! ### Homogeneous local extensions -/

/-- A holomorphic extension of `F` near `p`, homogeneous of degree `k` for positive real
scalars, on an open set invariant under positive real scalars. -/
structure LocalHomExt (C : Set (ComplexModel m)) (k : ℕ) (F : ComplexModel m → ℂ)
    (p : ComplexModel m) where
  ext : ComplexModel m → ℂ
  dom : Set (ComplexModel m)
  isOpen_dom : IsOpen dom
  mem_dom : p ∈ dom
  holo : DifferentiableOn ℂ ext dom
  eq_on : ∀ Z ∈ dom, Z ∈ C → ext Z = F Z
  hom : ∀ t : ℝ, 0 < t → ∀ Z, ext ((t : ℂ) • Z) = (t : ℂ) ^ k * ext Z
  dom_smul : ∀ t : ℝ, 0 < t → ∀ Z, (t : ℂ) • Z ∈ dom ↔ Z ∈ dom

/-- The slice map `Z ↦ (p_i / Z_i) Z` onto the affine hyperplane `{Z_i = p_i}`. -/
def sliceMap (p : ComplexModel m) (i : Fin m) (Z : ComplexModel m) : ComplexModel m :=
  (p i / Z i) • Z

theorem sliceMap_smul (p : ComplexModel m) (i : Fin m) {c : ℂ} (hc : c ≠ 0)
    (Z : ComplexModel m) : sliceMap p i (c • Z) = sliceMap p i Z := by
  unfold sliceMap
  rw [smul_smul, PiLp.smul_apply, smul_eq_mul]
  by_cases hZ : Z i = 0
  · simp [hZ]
  · congr 1
    field_simp

theorem sliceMap_self {p : ComplexModel m} {i : Fin m} (hi : p i ≠ 0) : sliceMap p i p = p := by
  unfold sliceMap
  rw [div_self hi, one_smul]

theorem differentiableAt_sliceMap (p : ComplexModel m) (i : Fin m) {Z : ComplexModel m}
    (hZ : Z i ≠ 0) : DifferentiableAt ℂ (sliceMap p i) Z := by
  have hproj : DifferentiableAt ℂ (fun Y : ComplexModel m => Y i) Z :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt
  have h1 : DifferentiableAt ℂ (fun Y : ComplexModel m => (Y i)⁻¹) Z :=
    (differentiableAt_inv hZ).comp Z hproj
  have hq : DifferentiableAt ℂ (fun Y : ComplexModel m => p i / Y i) Z := by
    simpa only [div_eq_mul_inv] using h1.const_mul (p i)
  exact hq.smul differentiableAt_id

/-- The slice extension: a local holomorphic extension near `p ≠ 0` becomes homogeneous. -/
theorem exists_localHomExt {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {k : ℕ} {F : ComplexModel m → ℂ}
    (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    (hloc : IsLocallyHolomorphicOn C F) {p : ComplexModel m} (hpC : p ∈ C) (hp0 : p ≠ 0) :
    Nonempty (LocalHomExt C k F p) := by
  obtain ⟨U, hU, h, hh, hhF⟩ := hloc p hpC hp0
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  have hi : ∃ i, p i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hp0 (by ext i; simp [hcon i])
  obtain ⟨i, hi⟩ := hi
  set D : Set (ComplexModel m) := {Z | Z i ≠ 0} ∩ sliceMap p i ⁻¹' ball p δ with hD
  have hDopen : IsOpen D := by
    have hcont : Continuous fun Z : ComplexModel m => Z i := by fun_prop
    have h1 : IsOpen {Z : ComplexModel m | Z i ≠ 0} := isOpen_ne_fun hcont continuous_const
    have h2 : ContinuousOn (sliceMap p i) {Z : ComplexModel m | Z i ≠ 0} := fun Z hZ =>
      (differentiableAt_sliceMap p i hZ).continuousAt.continuousWithinAt
    exact h2.isOpen_inter_preimage h1 isOpen_ball
  refine ⟨{ ext := fun Z => (Z i / p i) ^ k * h (sliceMap p i Z)
            dom := D
            isOpen_dom := hDopen
            mem_dom := ⟨hi, by
              show sliceMap p i p ∈ ball p δ
              rw [sliceMap_self hi]; exact mem_ball_self hδ⟩
            holo := ?_
            eq_on := ?_
            hom := ?_
            dom_smul := ?_ }⟩
  · intro Z hZ
    have hZi : Z i ≠ 0 := hZ.1
    have hZb : sliceMap p i Z ∈ ball p δ := hZ.2
    have hσZ : DifferentiableAt ℂ (fun Y => h (sliceMap p i Y)) Z := by
      have hhZ : DifferentiableAt ℂ h (sliceMap p i Z) :=
        (hh.mono hδU).differentiableAt (isOpen_ball.mem_nhds hZb)
      exact hhZ.comp Z (differentiableAt_sliceMap p i hZi)
    have hproj : DifferentiableAt ℂ (fun Y : ComplexModel m => Y i) Z :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt
    have hd : DifferentiableAt ℂ (fun Y : ComplexModel m => Y i / p i) Z := by
      simpa only [div_eq_mul_inv] using hproj.mul_const (p i)⁻¹
    exact ((hd.pow k).mul hσZ).differentiableWithinAt
  · intro Z hZ hZC
    have hZi : Z i ≠ 0 := hZ.1
    have hZb : sliceMap p i Z ∈ ball p δ := hZ.2
    have hσC : sliceMap p i Z ∈ C := hC _ Z hZC
    have h1 : h (sliceMap p i Z) = F (sliceMap p i Z) := hhF _ (hδU hZb) hσC
    have h2 : F (sliceMap p i Z) = (p i / Z i) ^ k * F Z := hF _ Z hZC
    change (Z i / p i) ^ k * h (sliceMap p i Z) = F Z
    rw [h1, h2, ← mul_assoc, ← mul_pow]
    have : Z i / p i * (p i / Z i) = 1 := by field_simp
    rw [this, one_pow, one_mul]
  · intro t ht Z
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    change (((t : ℂ) • Z) i / p i) ^ k * h (sliceMap p i ((t : ℂ) • Z)) =
      (t : ℂ) ^ k * ((Z i / p i) ^ k * h (sliceMap p i Z))
    rw [sliceMap_smul p i htne Z, PiLp.smul_apply, smul_eq_mul, mul_div_assoc, mul_pow, mul_assoc]
  · intro t ht Z
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    simp only [hD, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      sliceMap_smul p i htne Z, PiLp.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, htne, false_or]

/-! ### The normalizing function -/

/-- `ψ(s) = 1/(1 + τ(s)(s - 1))` with `τ` the smooth transition: smooth, and `ψ(s) = 1/s` for
`s ≥ 1`. -/
def normalizer (s : ℝ) : ℝ := (1 + Real.smoothTransition s * (s - 1))⁻¹

theorem normalizer_denom_pos (s : ℝ) : 0 < 1 + Real.smoothTransition s * (s - 1) := by
  have h0 := Real.smoothTransition.nonneg s
  have h1 := Real.smoothTransition.le_one s
  rcases le_or_gt s 0 with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos hs]; norm_num
  rcases le_or_gt 1 s with hs1 | hs1
  · rw [Real.smoothTransition.one_of_one_le hs1]; linarith
  · nlinarith

theorem contDiff_normalizer : ContDiff ℝ ∞ normalizer := by
  have h : ContDiff ℝ ∞ fun s : ℝ => 1 + Real.smoothTransition s * (s - 1) :=
    contDiff_const.add (Real.smoothTransition.contDiff.mul (contDiff_id.sub contDiff_const))
  exact h.inv fun s => (normalizer_denom_pos s).ne'

theorem normalizer_of_one_le {s : ℝ} (hs : 1 ≤ s) : normalizer s = s⁻¹ := by
  rw [normalizer, Real.smoothTransition.one_of_one_le hs]
  ring_nf

/-! ### The unit map -/

/-- `u(Z) = Z/|Z|`. -/
def unitMap (Z : ComplexModel m) : ComplexModel m := ((‖Z‖⁻¹ : ℝ) : ℂ) • Z

theorem contDiffAt_unitMap {Z : ComplexModel m} (hZ : Z ≠ 0) : ContDiffAt ℝ ∞ unitMap Z := by
  have hn : ContDiffAt ℝ ∞ (fun Y : ComplexModel m => ‖Y‖) Z := contDiffAt_norm ℂ hZ
  have hinv : ContDiffAt ℝ ∞ (fun Y : ComplexModel m => ‖Y‖⁻¹) Z :=
    hn.inv (norm_ne_zero_iff.mpr hZ)
  have hc : ContDiffAt ℝ ∞ (fun Y : ComplexModel m => ((‖Y‖⁻¹ : ℝ) : ℂ)) Z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp Z hinv
  exact hc.smul contDiffAt_id

theorem unitMap_smul {t : ℝ} (ht : 0 < t) (Z : ComplexModel m) :
    unitMap ((t : ℂ) • Z) = unitMap Z := by
  rw [unitMap, unitMap, smul_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, ← Complex.ofReal_mul]
  congr 2
  by_cases hn : ‖Z‖ = 0
  · simp [hn]
  · field_simp

theorem norm_unitMap {Z : ComplexModel m} (hZ : Z ≠ 0) : ‖unitMap Z‖ = 1 := by
  rw [unitMap, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hZ)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hZ)]

theorem eq_norm_smul_unitMap {Z : ComplexModel m} (hZ : Z ≠ 0) :
    Z = ((‖Z‖ : ℝ) : ℂ) • unitMap Z := by
  rw [unitMap, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hZ),
    Complex.ofReal_one, one_smul]

theorem unitMap_mem_cone {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {Z : ComplexModel m} (hZ : Z ∈ C) :
    unitMap Z ∈ C := hC _ Z hZ

/-! ### The glued extension -/

/-- The data of the gluing: a finite family of centres on `C` with homogeneous local extensions
and angular bump functions. -/
structure GluingData (C : Set (ComplexModel m)) (k : ℕ) (F : ComplexModel m → ℂ) where
  T : Finset (ComplexModel m)
  T_sub : ∀ p ∈ T, p ∈ C
  E : ∀ p : ComplexModel m, p ∈ T → LocalHomExt C k F p
  η : ∀ p : ComplexModel m, ContDiffBump p
  tsupport_sub : ∀ p (hp : p ∈ T), closedBall p (η p).rOut ⊆ (E p hp).dom
  cover : ∀ Z ∈ C, ‖Z‖ = 1 → ∃ p ∈ T, Z ∈ ball p (η p).rIn

namespace GluingData

variable {C : Set (ComplexModel m)} {k : ℕ} {F : ComplexModel m → ℂ} (Gd : GluingData C k F)

/-- The sum of the angular bumps. -/
def bumpSum (Z : ComplexModel m) : ℝ := ∑ p ∈ Gd.T, (Gd.η p) (unitMap Z)

/-- The local extension attached to a centre (zero for points outside `T`). -/
def extOf (p : ComplexModel m) (Z : ComplexModel m) : ℂ :=
  if hp : p ∈ Gd.T then (Gd.E p hp).ext Z else 0

/-- The cut-off of the centre `p`. -/
def cutoff (p : ComplexModel m) (Z : ComplexModel m) : ℝ :=
  (Gd.η p) (unitMap Z) * normalizer (Gd.bumpSum Z)

/-- The glued extension `G = ∑_p χ_p F_p`. -/
def glued (Z : ComplexModel m) : ℂ := ∑ p ∈ Gd.T, ((Gd.cutoff p Z : ℝ) : ℂ) * Gd.extOf p Z

theorem contDiffAt_bumpSum {Z : ComplexModel m} (hZ : Z ≠ 0) :
    ContDiffAt ℝ ∞ Gd.bumpSum Z := by
  unfold bumpSum
  exact ContDiffAt.sum fun p _ => (Gd.η p).contDiff.contDiffAt.comp Z (contDiffAt_unitMap hZ)

theorem contDiffAt_cutoff (p : ComplexModel m) {Z : ComplexModel m} (hZ : Z ≠ 0) :
    ContDiffAt ℝ ∞ (Gd.cutoff p) Z :=
  ((Gd.η p).contDiff.contDiffAt.comp Z (contDiffAt_unitMap hZ)).mul
    (contDiff_normalizer.contDiffAt.comp Z (Gd.contDiffAt_bumpSum hZ))

theorem bumpSum_smul {t : ℝ} (ht : 0 < t) (Z : ComplexModel m) :
    Gd.bumpSum ((t : ℂ) • Z) = Gd.bumpSum Z := by
  simp only [bumpSum, unitMap_smul ht]

theorem cutoff_smul (p : ComplexModel m) {t : ℝ} (ht : 0 < t) (Z : ComplexModel m) :
    Gd.cutoff p ((t : ℂ) • Z) = Gd.cutoff p Z := by
  simp only [cutoff, unitMap_smul ht, Gd.bumpSum_smul ht]

/-- Off the support of the angular bump of `p`, the cut-off of `p` vanishes near `Z`. -/
theorem cutoff_eventually_zero (p : ComplexModel m) {Z : ComplexModel m} (hZ : Z ≠ 0)
    (hu : unitMap Z ∉ closedBall p (Gd.η p).rOut) : ∀ᶠ Y in 𝓝 Z, Gd.cutoff p Y = 0 := by
  have hev : ∀ᶠ Y in 𝓝 Z, unitMap Y ∉ closedBall p (Gd.η p).rOut :=
    (contDiffAt_unitMap hZ).continuousAt.eventually
      (isClosed_closedBall.isOpen_compl.mem_nhds hu)
  filter_upwards [hev] with Y hY
  have : (Gd.η p) (unitMap Y) = 0 := by
    by_contra hne
    exact hY ((Gd.η p).tsupport_eq ▸ subset_tsupport _ (Function.mem_support.mpr hne))
  simp [cutoff, this]

/-- If the angular bump of `p` is not zero at `Z ≠ 0`, `Z` lies in the domain of `F_p`. -/
theorem mem_dom_of_unitMap_mem {p : ComplexModel m} (hp : p ∈ Gd.T) {Z : ComplexModel m}
    (hZ : Z ≠ 0) (hu : unitMap Z ∈ closedBall p (Gd.η p).rOut) : Z ∈ (Gd.E p hp).dom := by
  have h1 := Gd.tsupport_sub p hp hu
  have hn : 0 < ‖Z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hZ)
  exact ((Gd.E p hp).dom_smul _ hn Z).mp h1

theorem extOf_eq {p : ComplexModel m} (hp : p ∈ Gd.T) : Gd.extOf p = (Gd.E p hp).ext := by
  funext Y; simp [extOf, hp]

/-- Each term `χ_p F_p` is smooth off `0`. -/
theorem contDiffAt_term (p : ComplexModel m) {Z : ComplexModel m} (hZ : Z ≠ 0) :
    ContDiffAt ℝ ∞ (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ) * Gd.extOf p Y) Z := by
  by_cases hp : p ∈ Gd.T
  · by_cases hu : unitMap Z ∈ closedBall p (Gd.η p).rOut
    · have hZdom := Gd.mem_dom_of_unitMap_mem hp hZ hu
      have hext : ContDiffAt ℝ ∞ (Gd.extOf p) Z := by
        rw [Gd.extOf_eq hp]
        exact (contDiffAt_of_differentiableOn_complex (Gd.E p hp).holo (Gd.E p hp).isOpen_dom
          hZdom).restrict_scalars ℝ
      have hcut : ContDiffAt ℝ ∞ (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ)) Z :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp Z (Gd.contDiffAt_cutoff p hZ)
      exact hcut.mul hext
    · have hzero : (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ) * Gd.extOf p Y) =ᶠ[𝓝 Z] fun _ => 0 := by
        filter_upwards [Gd.cutoff_eventually_zero p hZ hu] with Y hY
        simp [hY]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have : (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ) * Gd.extOf p Y) = fun _ => 0 := by
      funext Y; simp [extOf, hp]
    rw [this]
    exact contDiffAt_const

theorem contDiffAt_glued {Z : ComplexModel m} (hZ : Z ≠ 0) : ContDiffAt ℝ ∞ Gd.glued Z := by
  unfold glued
  exact ContDiffAt.sum fun p _ => Gd.contDiffAt_term p hZ

/-- The glued extension is positively homogeneous of degree `k`. -/
theorem glued_smul {t : ℝ} (ht : 0 < t) (Z : ComplexModel m) :
    Gd.glued ((t : ℂ) • Z) = (t : ℂ) ^ k * Gd.glued Z := by
  simp only [glued, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Gd.cutoff_smul p ht]
  by_cases hp : p ∈ Gd.T
  · simp only [extOf, dif_pos hp, (Gd.E p hp).hom t ht Z]
    ring
  · simp [extOf, hp]

variable (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C)
include hC

/-- Near a point of `C ∖ {0}` the cut-offs sum to one. -/
theorem eventually_sum_cutoff {Z : ComplexModel m} (hZC : Z ∈ C) (hZ0 : Z ≠ 0) :
    ∀ᶠ Y in 𝓝 Z, ∑ p ∈ Gd.T, Gd.cutoff p Y = 1 := by
  obtain ⟨p, hpT, hpZ⟩ := Gd.cover (unitMap Z) (hC _ Z hZC) (norm_unitMap hZ0)
  have hev : ∀ᶠ Y in 𝓝 Z, unitMap Y ∈ ball p (Gd.η p).rIn :=
    (contDiffAt_unitMap hZ0).continuousAt.eventually (isOpen_ball.mem_nhds hpZ)
  filter_upwards [hev] with Y hY
  have h1 : (Gd.η p) (unitMap Y) = 1 := (Gd.η p).one_of_mem_closedBall (ball_subset_closedBall hY)
  have hsum : 1 ≤ Gd.bumpSum Y := by
    rw [bumpSum, ← h1]
    exact Finset.single_le_sum (f := fun q => (Gd.η q) (unitMap Y))
      (fun q _ => (Gd.η q).nonneg) hpT
  have hpos : 0 < Gd.bumpSum Y := lt_of_lt_of_le one_pos hsum
  simp only [cutoff, ← Finset.sum_mul, normalizer_of_one_le hsum]
  rw [← bumpSum]
  exact mul_inv_cancel₀ hpos.ne'

/-- `G = F` on `C ∖ {0}`. -/
theorem glued_eq {Z : ComplexModel m} (hZC : Z ∈ C) (hZ0 : Z ≠ 0) : Gd.glued Z = F Z := by
  have hsum := (Gd.eventually_sum_cutoff hC hZC hZ0).self_of_nhds
  have hterm : ∀ p ∈ Gd.T, ((Gd.cutoff p Z : ℝ) : ℂ) * Gd.extOf p Z =
      ((Gd.cutoff p Z : ℝ) : ℂ) * F Z := by
    intro p hp
    by_cases hu : unitMap Z ∈ closedBall p (Gd.η p).rOut
    · rw [Gd.extOf_eq hp, (Gd.E p hp).eq_on Z (Gd.mem_dom_of_unitMap_mem hp hZ0 hu) hZC]
    · rw [(Gd.cutoff_eventually_zero p hZ0 hu).self_of_nhds]
      simp
  rw [glued, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Complex.ofReal_sum, hsum,
    Complex.ofReal_one, one_mul]

/-- `∂̄G = 0` on `C ∖ {0}`. -/
theorem dbarDir_glued_eq_zero {Z : ComplexModel m} (hZC : Z ∈ C) (hZ0 : Z ≠ 0)
    (v : ComplexModel m) : dbarDir v Gd.glued Z = 0 := by
  have hdiff : ∀ p ∈ Gd.T, DifferentiableAt ℝ
      (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ) * Gd.extOf p Y) Z := fun p _ =>
    (Gd.contDiffAt_term p hZ0).differentiableAt (by simp)
  have hcutd : ∀ p, DifferentiableAt ℝ (Gd.cutoff p) Z := fun p =>
    (Gd.contDiffAt_cutoff p hZ0).differentiableAt (by simp)
  have hterm : ∀ p ∈ Gd.T, dbarDir v (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ) * Gd.extOf p Y) Z =
      dbarDir v (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ)) Z * F Z := by
    intro p hp
    by_cases hu : unitMap Z ∈ closedBall p (Gd.η p).rOut
    · have hZdom := Gd.mem_dom_of_unitMap_mem hp hZ0 hu
      have hholo : DifferentiableAt ℂ (Gd.extOf p) Z := by
        rw [Gd.extOf_eq hp]
        exact (Gd.E p hp).holo.differentiableAt ((Gd.E p hp).isOpen_dom.mem_nhds hZdom)
      rw [dbarDir_ofReal_mul (hcutd p) (hholo.restrictScalars ℝ),
        dbarDir_eq_zero_of_differentiableAt hholo, Gd.extOf_eq hp,
        (Gd.E p hp).eq_on Z hZdom hZC, mul_zero, add_zero]
    · have hev := Gd.cutoff_eventually_zero p hZ0 hu
      have h1 : (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ) * Gd.extOf p Y) =ᶠ[𝓝 Z] fun _ => 0 := by
        filter_upwards [hev] with Y hY; simp [hY]
      have h2 : (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ)) =ᶠ[𝓝 Z] fun _ => 0 := by
        filter_upwards [hev] with Y hY; simp [hY]
      rw [dbarDir_congr h1, dbarDir_congr h2, dbarDir_const, zero_mul]
  have hsumc : (fun Y => ∑ p ∈ Gd.T, ((Gd.cutoff p Y : ℝ) : ℂ)) =ᶠ[𝓝 Z] fun _ => 1 := by
    filter_upwards [Gd.eventually_sum_cutoff hC hZC hZ0] with Y hY
    rw [← Complex.ofReal_sum, hY, Complex.ofReal_one]
  have hcd : ∀ p ∈ Gd.T, DifferentiableAt ℝ (fun Y => ((Gd.cutoff p Y : ℝ) : ℂ)) Z :=
    fun p _ => (Complex.ofRealCLM.differentiableAt).comp Z (hcutd p)
  unfold glued
  rw [dbarDir_sum _ hdiff, Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ← dbarDir_sum _ hcd, dbarDir_congr hsumc, dbarDir_const, zero_mul]

omit hC in
/-- Existence of gluing data for a closed cone with homogeneous locally holomorphic `F`. -/
theorem nonempty (hCc : IsClosed C)
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C)
    (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    (hloc : IsLocallyHolomorphicOn C F) : Nonempty (GluingData C k F) := by
  classical
  set K₀ : Set (ComplexModel m) := C ∩ sphere 0 1 with hK₀
  have hK₀c : IsCompact K₀ := (isCompact_sphere 0 1).inter_left hCc
  have hne : ∀ p ∈ K₀, p ≠ 0 := by
    intro p hp h0
    have := hp.2
    rw [h0, mem_sphere, dist_self] at this
    exact zero_ne_one this
  let Ech : ∀ p, p ∈ K₀ → LocalHomExt C k F p := fun p hp =>
    Classical.choice (exists_localHomExt hC hF hloc hp.1 (hne p hp))
  have hρ : ∀ p, ∃ ρ : ℝ, 0 < ρ ∧ ∀ hp : p ∈ K₀, closedBall p (2 * ρ) ⊆ (Ech p hp).dom := by
    intro p
    by_cases hp : p ∈ K₀
    · obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (Ech p hp).isOpen_dom p (Ech p hp).mem_dom
      refine ⟨ε / 4, by positivity, fun hp' => ?_⟩
      exact (closedBall_subset_ball (by linarith)).trans hεsub
    · exact ⟨1, one_pos, fun hp' => absurd hp' hp⟩
  choose ρ hρ0 hρsub using hρ
  let η : ∀ p : ComplexModel m, ContDiffBump p := fun p =>
    ⟨ρ p, 2 * ρ p, hρ0 p, by linarith [hρ0 p]⟩
  obtain ⟨T, hTK, hTcov⟩ := hK₀c.elim_nhds_subcover (fun p => ball p (η p).rIn)
    (fun p _ => ball_mem_nhds p (η p).rIn_pos)
  refine ⟨{ T := T
            T_sub := fun p hp => (hTK p hp).1
            E := fun p hp => Ech p (hTK p hp)
            η := η
            tsupport_sub := fun p hp => hρsub p (hTK p hp)
            cover := fun Z hZC hZ1 => ?_ }⟩
  have hZK : Z ∈ K₀ := ⟨hZC, by rw [mem_sphere_zero_iff_norm]; exact hZ1⟩
  have := hTcov hZK
  simp only [Set.mem_iUnion] at this
  obtain ⟨p, hp, hZp⟩ := this
  exact ⟨p, hp, hZp⟩

end GluingData

end SGPT.GAGA.H0
