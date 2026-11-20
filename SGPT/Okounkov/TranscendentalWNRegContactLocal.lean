import SGPT.Okounkov.TranscendentalWNRegDensityPoint
import SGPT.Okounkov.TranscendentalWNRegC11bar
import SGPT.Okounkov.TranscendentalWNEnvelopeLocal
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
import SGPT.Foundations.Analysis.PSHD.DiscRecovery

/-!
# The Monge–Ampère measure on a contact set is at least the obstacle's (local part)

Package WN-REG (`claude-tok-wn-reg`, node `tok-wn-reg:dnt-local`): the inequality "`≥`" of the
Di Nezza–Trapani contact formula in coordinates, proved without any regularity of the potential.

Let `Ω ⊆ ℂⁿ` be open, `q` smooth on `Ω` (not necessarily plurisubharmonic) and `V ≤ q`
plurisubharmonic on `Ω`, with contact set `C = {V = q}`.  Then on `C` the Monge–Ampère measure of
`V` dominates the smooth measure `det(ddᶜq)`:

* `canonicalBedfordTaylorMeasure_contact_ge` — `V` locally bounded:
  `∫_T (ddᶜq)ⁿ ≤ (ddᶜV)ⁿ(T)` for every `T ⊆ C ∩ B(x₀, R)`, `B̄(x₀, 4R) ⊆ Ω`;
* `truncationLimitMeasure_contact_ge` — `V` with poles, for the non-pluripolar measure.

## Proof

Mollify, `V_j = V * κ_j` with TN's explicit radial kernels of radius `R/(j+1)`; this is a
decreasing smooth plurisubharmonic approximation, so `(ddᶜV_j)ⁿ → (ddᶜV)ⁿ` against compactly
supported continuous tests (Bedford–Taylor).  Put `g = q - V ≥ 0`.  The sub-mean value property
of the plurisubharmonic function `V + M|· - y|² - q` gives `⨍_{B̄(y,s)} g ≤ M s²` at contact points `y`,
hence (`DensityPoint.eventually_setLIntegral_le_of_density`) `⨍_{B̄(z,r)} g = o(r²)` at density points
`z` of `C`.  Since `∂²(V * κ_j) = (∂²q) * κ_j - g * ∂²κ_j` and `|∂²κ_j| ≤ M₀ (j+1)^{2n+2}`, the real
Hessians of `V_j` converge at such `z` to that of `q`, so `det(ddᶜV_j)(z) → det(ddᶜq)(z)` for almost
every `z ∈ C`.  Fatou's lemma against a bump function equal to `1` on a closed ball gives
`∫_{C ∩ B̄} (ddᶜq)ⁿ ≤ (ddᶜV)ⁿ(B̄)`; the Besicovitch Vitali family turns this into the statement on
all subsets of `C`.  The unbounded case follows from the bounded one applied to `max(V, -k)`
(plurifine locality of the truncation measures).

This replaces the `C^{1,1}` regularity of envelopes, the `W^{2,1}` theory and Stampacchia's
theorem in the book's proof of `lma:DNTroof` / `thm:DNTcontact`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWNReg.ContactLocal

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-! ### Calculus -/

/-- Polarization of the real Hessian of a `C²` function. -/
theorem realHessian_polarization {u : ComplexModel n → ℝ} {x : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u x) (v w : ComplexModel n) :
    realHessian u x v w =
      (realHessian u x (v + w) (v + w) - realHessian u x (v - w) (v - w)) / 4 := by
  have hs := hu.isSymmSndFDerivAt (by simp)
  simp only [realHessian_eq_fderiv, map_add, map_sub, _root_.add_apply, _root_.sub_apply]
  rw [hs w v]
  ring

/-- **Two integrations by parts**, all directions: for `g` smooth on an open `U` and a smooth `φ`
with compact support in `U`, `∫ g ∂_v∂_wφ = ∫ (∂_v∂_w g) φ`. -/
theorem integral_mul_realHessian_eq_of_contDiffOn {g φ : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ U) (v w : ComplexModel n) :
    ∫ x, g x * realHessian φ x v w = ∫ x, realHessian g x v w * φ x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hc : ∀ a, Continuous (fun x => realHessian φ x a a) := fun a =>
    continuous_realHessian hφ2 a a
  have hsub : ∀ a, Function.support (fun x => realHessian φ x a a) ⊆ tsupport φ :=
    fun a x hx => support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) fun h => hx (by
      simp [realHessian, h])
  have hcs : ∀ a, HasCompactSupport (fun x => realHessian φ x a a) := fun a => hφc.mono' (hsub a)
  have hsupp' : ∀ a, tsupport (fun x => realHessian φ x a a) ⊆ U := fun a =>
    (closure_minimal (hsub a) (isClosed_tsupport φ)).trans hsupp
  have hgc : ContinuousOn g U := hg.continuousOn
  have hA : ∀ a, Integrable (fun x => g x * realHessian φ x a a) := fun a =>
    TranscendentalWNReg.integrable_mul_of_continuousOn hU hgc (hc a) (hcs a) (hsupp' a)
  have hg2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ g)) U :=
    (hg.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen hU (by simp)
  have hgH : ∀ a b, ContinuousOn (fun x => realHessian g x a b) U := by
    intro a b
    simp only [realHessian_eq_fderiv]
    exact (hg2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hB : ∀ a, Integrable (fun x => realHessian g x a a * φ x) := fun a =>
    TranscendentalWNReg.integrable_mul_of_continuousOn hU (hgH a a) hφ.continuous hφc hsupp
  have e1 := TranscendentalWNReg.integral_mul_realHessian_eq hU hg hφ hφc hsupp (v + w)
  have e2 := TranscendentalWNReg.integral_mul_realHessian_eq hU hg hφ hφc hsupp (v - w)
  calc ∫ x, g x * realHessian φ x v w
      = ((∫ x, g x * realHessian φ x (v + w) (v + w)) -
          ∫ x, g x * realHessian φ x (v - w) (v - w)) / 4 := by
        rw [← integral_sub (hA _) (hA _), ← integral_div]
        congr 1
        funext x
        rw [realHessian_polarization (hφ2.contDiffAt) v w]
        ring
    _ = ((∫ x, realHessian g x (v + w) (v + w) * φ x) -
          ∫ x, realHessian g x (v - w) (v - w) * φ x) / 4 := by rw [e1, e2]
    _ = ∫ x, realHessian g x v w * φ x := by
        rw [← integral_sub (hB _) (hB _), ← integral_div]
        congr 1
        funext x
        by_cases hx : x ∈ U
        · have hg2x : ContDiffAt ℝ 2 g x :=
            ((hg x hx).contDiffAt (hU.mem_nhds hx)).of_le
              (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
          rw [realHessian_polarization hg2x v w]
          ring
        · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)
          simp [this]

/-- Convergence of all real Hessian entries at a point gives convergence of the Monge–Ampère
density there. -/
theorem tendsto_smoothDensity_of_tendsto_realHessian {F : ℕ → ComplexModel n → ℝ}
    {q : ComplexModel n → ℝ} {z : ComplexModel n}
    (h : ∀ a b, Tendsto (fun j => realHessian (F j) z a b) atTop (𝓝 (realHessian q z a b))) :
    Tendsto (fun j => smoothDensity (F j) z) atTop (𝓝 (smoothDensity q z)) := by
  have hc : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
  have hH : Tendsto (fun j => complexHessian (F j) z) atTop (𝓝 (complexHessian q z)) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k => ?_
    simp only [complexHessian]
    refine Tendsto.add (Tendsto.div_const ?_ _) (Tendsto.div_const (Tendsto.const_mul _ ?_) _)
    · exact (hc.tendsto _).comp ((h _ _).add (h _ _))
    · exact (hc.tendsto _).comp ((h _ _).sub (h _ _))
  have hdet := ((continuous_id.matrix_det).tendsto _).comp hH
  simp only [smoothDensity]
  exact tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp hdet)

/-- The real Hessian vanishes outside the topological support. -/
theorem realHessian_eq_zero_of_notMem_tsupport {φ : ComplexModel n → ℝ} {x : ComplexModel n}
    (hx : x ∉ tsupport φ) (v w : ComplexModel n) : realHessian φ x v w = 0 := by
  have h : iteratedFDeriv ℝ 2 φ x = 0 := by
    by_contra hne
    exact hx (support_iteratedFDeriv_subset (𝕜 := ℝ) 2 hne)
  simp [realHessian, h]

/-! ### The explicit radial kernels -/

section Kernel

variable (R : ℝ) (hR : 0 < R)

theorem explicitRadialKernel_contDiff_two (j : ℕ) :
    ContDiff ℝ 2 (explicitRadialKernel (n := n) R hR j) :=
  (explicitRadialKernel_contDiff R hR j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- **Scaling of the second derivatives**: `|∂_v∂_w κ_j| ≤ (j + 1)^{d+2} M₀`. -/
theorem exists_abs_realHessian_explicitRadialKernel_le (v w : ComplexModel n) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (j : ℕ) (y : ComplexModel n),
      |realHessian (explicitRadialKernel (n := n) R hR j) y v w| ≤
        ((j : ℝ) + 1) ^ (Module.finrank ℝ (ComplexModel n) + 2) * M₀ := by
  set κ₀ := explicitRadialKernel (n := n) R hR 0 with hκ₀
  have h2 : ContDiff ℝ 2 κ₀ := explicitRadialKernel_contDiff_two R hR 0
  have hsub : Function.support (fun y => realHessian κ₀ y v w) ⊆ tsupport κ₀ := by
    intro y hy
    by_contra hyt
    exact hy (realHessian_eq_zero_of_notMem_tsupport hyt v w)
  have hcs : HasCompactSupport (fun y => realHessian κ₀ y v w) :=
    (explicitRadialKernel_hasCompactSupport R hR 0).mono' hsub
  obtain ⟨M, hM⟩ := (continuous_realHessian h2 v w).bounded_above_of_compact_support hcs
  refine ⟨max M 0, le_max_right _ _, fun j y => ?_⟩
  set c : ℝ := (j : ℝ) + 1 with hc
  have hc0 : 0 < c := by positivity
  set d := Module.finrank ℝ (ComplexModel n)
  have hscale : explicitRadialKernel (n := n) R hR j =
      (c ^ d) • fun y => κ₀ (0 + (c • ContinuousLinearMap.id ℝ (ComplexModel n)) y) := by
    funext y
    rw [explicitRadialKernel_scale R hR 0 j y]
    simp [hc, d, κ₀]
  have hcomp : ContDiff ℝ 2
      (fun y => κ₀ (0 + (c • ContinuousLinearMap.id ℝ (ComplexModel n)) y)) :=
    h2.comp (contDiff_const.add (ContinuousLinearMap.contDiff _))
  rw [hscale, realHessian_smul hcomp.contDiffAt, realHessian_comp_affine h2]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, zero_add,
    realHessian_smul_left, realHessian_smul_right]
  have hb : |realHessian κ₀ (c • y) v w| ≤ max M 0 := by
    have := hM (c • y)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hc0 d), abs_of_pos hc0, pow_add]
  calc c ^ d * (c * (c * |realHessian κ₀ (c • y) v w|))
      ≤ c ^ d * (c * (c * max M 0)) := by gcongr
    _ = c ^ d * c ^ 2 * max M 0 := by ring

/-- The translated kernels have integral one. -/
theorem integral_explicitRadialKernel_sub (j : ℕ) (z : ComplexModel n) :
    ∫ x, explicitRadialKernel R hR j (x - z) = 1 := by
  rw [integral_sub_right_eq_self (fun x => explicitRadialKernel (n := n) R hR j x) z]
  exact explicitRadialKernel_integral_one R hR j

theorem explicitRadialKernel_sub_eq_zero (j : ℕ) {z x : ComplexModel n}
    (hx : R / ((j : ℝ) + 1) < dist x z) : explicitRadialKernel R hR j (x - z) = 0 := by
  have hnot : x - z ∉ tsupport (explicitRadialKernel (n := n) R hR j) := by
    rw [explicitRadialKernel_tsupport R hR j, mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact not_le.mpr hx
  exact image_eq_zero_of_notMem_tsupport hnot

theorem realHessian_explicitRadialKernel_sub_eq_zero (j : ℕ) {z x : ComplexModel n}
    (hx : R / ((j : ℝ) + 1) < dist x z) (v w : ComplexModel n) :
    realHessian (explicitRadialKernel (n := n) R hR j) (x - z) v w = 0 := by
  have hnot : x - z ∉ tsupport (explicitRadialKernel (n := n) R hR j) := by
    rw [explicitRadialKernel_tsupport R hR j, mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact not_le.mpr hx
  exact realHessian_eq_zero_of_notMem_tsupport hnot v w

include hR in
theorem tendsto_kernel_radius :
    Tendsto (fun j : ℕ => R / ((j : ℝ) + 1)) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat.congr fun j => by
        simp) : Tendsto (fun j : ℕ => R * ((j : ℝ) + 1)⁻¹) atTop (𝓝 (R * 0)))
  · exact mem_Ioi.mpr (by positivity)

/-- **Approximate identity at a point of continuity.** -/
theorem tendsto_integral_mul_explicitRadialKernel {h : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hh : ContinuousOn h U) {z : ComplexModel n}
    (hz : z ∈ U) :
    Tendsto (fun j => ∫ x, h x * explicitRadialKernel R hR j (x - z)) atTop (𝓝 (h z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨δ₂, hδ₂, hδ₂h⟩ := Metric.continuousOn_iff.mp hh z hz (ε / 2) (by positivity)
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨J, hJ⟩ := ((tendsto_kernel_radius R hR).mono_right nhdsWithin_le_nhds).eventually
    (gt_mem_nhds hδ0) |>.exists_forall_of_atTop
  refine ⟨J, fun j hj => ?_⟩
  have hrj : R / ((j : ℝ) + 1) < δ := hJ j hj
  set κ : ComplexModel n → ℝ := fun x => explicitRadialKernel R hR j (x - z) with hκ
  have hκc : Continuous κ :=
    (explicitRadialKernel_contDiff R hR j).continuous.comp (continuous_id.sub continuous_const)
  have hκs : HasCompactSupport κ :=
    (explicitRadialKernel_hasCompactSupport R hR j).comp_homeomorph (Homeomorph.subRight z)
  have hκU : tsupport κ ⊆ U := by
    refine (tsupport_explicitRadialKernel_translate_subset R hR j z).trans ?_
    refine (closedBall_subset_ball ?_).trans hδ₁U
    exact (show (shrinkingBump (E := ComplexModel n) R hR j).rOut = R / ((j : ℝ) + 1) from rfl) ▸
      hrj.trans_le (min_le_left _ _)
  have hint : Integrable (fun x => h x * κ x) :=
    TranscendentalWNReg.integrable_mul_of_continuousOn hU hh hκc hκs hκU
  have hκint : Integrable κ := hκc.integrable_of_hasCompactSupport hκs
  have hone : ∫ x, κ x = 1 := integral_explicitRadialKernel_sub R hR j z
  have heq : (∫ x, h x * κ x) - h z = ∫ x, (h x - h z) * κ x := by
    rw [show (fun x => (h x - h z) * κ x) = fun x => h x * κ x - h z * κ x by
      funext x; ring, integral_sub hint (hκint.const_mul _), integral_const_mul, hone, mul_one]
  rw [Real.dist_eq, heq]
  have hbound : ∀ x, ‖(h x - h z) * κ x‖ ≤ ε / 2 * κ x := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (explicitRadialKernel_nonneg R hR j _)]
    by_cases hxz : dist x z ≤ R / ((j : ℝ) + 1)
    · have hxU : x ∈ U := hδ₁U (lt_of_le_of_lt hxz (hrj.trans_le (min_le_left _ _)))
      have hle : |h x - h z| ≤ ε / 2 := by
        rw [← Real.dist_eq]
        exact (hδ₂h x hxU (lt_of_le_of_lt hxz (hrj.trans_le (min_le_right _ _)))).le
      exact mul_le_mul_of_nonneg_right hle (explicitRadialKernel_nonneg R hR j _)
    · rw [explicitRadialKernel_sub_eq_zero R hR j (not_le.mp hxz)]
      simp only [mul_zero]
      exact mul_nonneg (by positivity) (explicitRadialKernel_nonneg R hR j _)
  calc |∫ x, (h x - h z) * κ x| = ‖∫ x, (h x - h z) * κ x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ε / 2 * κ x :=
        norm_integral_le_of_norm_le (hκint.const_mul _) (Eventually.of_forall hbound)
    _ = ε / 2 := by rw [integral_const_mul, hone, mul_one]
    _ < ε := by linarith

end Kernel

/-! ### The mollified potentials -/

section Mollifier

variable {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ} {x₀ : ComplexModel n} {R : ℝ}

/-- The mollified potentials `V_j = (𝟙_{B̄(x₀, 3R)} V) * κ_j`. -/
def mollified (V : ComplexModel n → ℝ) (x₀ : ComplexModel n) (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ComplexModel n → ℝ :=
  translationPairing volume ((closedBall x₀ (3 * R)).indicator V) (explicitRadialKernel R hR j)

/-- The ball `B(x₀, 2R)` on which the mollified potentials are used. -/
def innerBall (x₀ : ComplexModel n) (R : ℝ) : Opens (ComplexModel n) :=
  ⟨ball x₀ (2 * R), isOpen_ball⟩

theorem closedBall_subset_of_mem_innerBall {z : ComplexModel n} (hz : z ∈ ball x₀ (2 * R)) :
    closedBall z R ⊆ closedBall x₀ (3 * R) :=
  closedBall_subset_closedBall' (by rw [mem_ball] at hz; linarith)

theorem locallyIntegrable_indicator (hV : IsLocallyBoundedPshOn Ω V)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) (hR : 0 < R) :
    LocallyIntegrable ((closedBall x₀ (3 * R)).indicator V) volume :=
  (integrable_indicator_of_locallyIntegrableOn_isCompact
    (locallyIntegrableOn_of_plurisubharmonicOn_real hV.1) (isCompact_closedBall _ _)
    ((closedBall_subset_closedBall (by linarith)).trans hball)).locallyIntegrable

theorem contDiff_mollified (hV : IsLocallyBoundedPshOn Ω V)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ ∞ (mollified V x₀ R hR j) :=
  contDiff_translationPairing (locallyIntegrable_indicator hV hball hR)
    (explicitRadialKernel_hasCompactSupport R hR j) (explicitRadialKernel_contDiff R hR j)

/-- The mollified potentials form a decreasing smooth plurisubharmonic approximation of `V` on
`B(x₀, 2R)` (TN's radial regularization). -/
theorem isDecreasingApproximation_mollified (hV : IsLocallyBoundedPshOn Ω V) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    IsDecreasingApproximation (innerBall x₀ R) V (mollified V x₀ R hR) := by
  set N : Set (ComplexModel n) := ball x₀ (2 * R) with hN
  set K : Set (ComplexModel n) := closedBall x₀ (3 * R) with hK
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hNK : N ⊆ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hNΩ : N ⊆ Ω := hNK.trans hKΩ
  have hballK : ∀ x ∈ N, closedBall x R ⊆ K := fun x hx => closedBall_subset_of_mem_innerBall hx
  have hpL := locallyIntegrableOn_of_plurisubharmonicOn_real hV.1
  have hpLevi := hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hV.1
  have hg := locallyIntegrable_indicator hV hball hR
  have htsupp : ∀ (j : ℕ), ∀ z ∈ N,
      tsupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) ⊆ K := fun j z hz =>
    (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
      ((closedBall_subset_closedBall (shrinkingBump_rOut_le (E := ComplexModel n) R hR j)).trans
        (hballK z hz))
  have hfPsh : ∀ j, PlurisubharmonicOn (fun x => (mollified V x₀ R hR j x : EReal))
      (innerBall x₀ R : Set (ComplexModel n)) := fun j =>
    (discPshOn_translationPairing_indicator hpL hpLevi
      (explicitRadialKernel_hasCompactSupport R hR j) (explicitRadialKernel_contDiff R hR j)
      (explicitRadialKernel_nonneg R hR j) (isCompact_closedBall _ _) hKΩ
      (htsupp j)).plurisubharmonicOn isOpen_ball
  have hfSmooth : ∀ j, IsSmoothPshOn (innerBall x₀ R) (mollified V x₀ R hR j) := fun j =>
    Pending.MongeAmpere.isSmoothPshOn_of_psh (contDiff_mollified hV hball hR j).contDiffOn (hfPsh j)
  have hanti : ∀ x ∈ innerBall x₀ R, Antitone fun j => mollified V x₀ R hR j x :=
    antitone_translationPairing_explicitRadialKernel_of_locallyBoundedPsh hV hR isOpen_ball hNΩ
      (isCompact_closedBall _ _) hKΩ hballK
  have hae : ∀ᵐ x ∂volume.restrict (innerBall x₀ R : Set (ComplexModel n)),
      Tendsto (fun j => mollified V x₀ R hR j x) atTop (𝓝 (V x)) := by
    filter_upwards [ae_restrict_of_ae (ae_tendsto_translationPairing_explicitRadialKernel hg R hR),
      ae_restrict_mem (isOpen_ball (x := x₀) (ε := 2 * R)).measurableSet] with x hxlim hxN
    rw [indicator_of_mem (hNK hxN)] at hxlim
    exact hxlim
  exact ⟨hfSmooth, hanti, tendsto_everywhere_of_ae_of_antitone_psh (hV.1.mono hNΩ) hfPsh hanti hae⟩

/-- **The real Hessians of the mollified potentials at a flat contact point.**  If
`∫_{B̄(z,r)} (q - V) = o(r² |B̄(z, r)|)`, then `∂_v∂_w V_j(z) → ∂_v∂_w q(z)`. -/
theorem tendsto_realHessian_mollified (hV : IsLocallyBoundedPshOn Ω V)
    (hq : ContDiffOn ℝ ∞ q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {z : ComplexModel n} (hz : z ∈ ball x₀ (2 * R))
    (hflat : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ x in closedBall z r, ENNReal.ofReal (q x - V x) ≤
        ENNReal.ofReal (ε * r ^ 2) * volume (closedBall z r))
    (v w : ComplexModel n) :
    Tendsto (fun j => realHessian (mollified V x₀ R hR j) z v w) atTop
      (𝓝 (realHessian q z v w)) := by
  set K : Set (ComplexModel n) := closedBall x₀ (3 * R) with hK
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hzK : closedBall z R ⊆ K := closedBall_subset_of_mem_innerBall hz
  have hzΩ : z ∈ Ω := hKΩ (hzK (mem_closedBall_self hR.le))
  have hg := locallyIntegrable_indicator hV hball hR
  set H : ℕ → ComplexModel n → ℝ := fun j y =>
    realHessian (explicitRadialKernel (n := n) R hR j) y v w with hH
  have hrad : ∀ j : ℕ, R / ((j : ℝ) + 1) ≤ R := fun j =>
    shrinkingBump_rOut_le (E := ComplexModel n) R hR j
  have hφ : ∀ j : ℕ, ContDiff ℝ ∞ (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
    fun j => (explicitRadialKernel_contDiff R hR j).comp (contDiff_id.sub contDiff_const)
  have hφc : ∀ j : ℕ, HasCompactSupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
    fun j => (explicitRadialKernel_hasCompactSupport R hR j).comp_homeomorph
      (Homeomorph.subRight z)
  have hφK : ∀ j : ℕ, tsupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) ⊆ K :=
    fun j => (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
      ((closedBall_subset_closedBall (hrad j)).trans hzK)
  -- the Hessian of the translated kernel
  have hHc : ∀ j : ℕ, Continuous (fun x => H j (x - z)) := fun j =>
    (continuous_realHessian (explicitRadialKernel_contDiff_two R hR j) v w).comp
      (continuous_id.sub continuous_const)
  have hHs : ∀ j : ℕ, HasCompactSupport (fun x => H j (x - z)) := by
    intro j
    refine (hφc j).mono' fun x hx => ?_
    by_contra hxt
    have h0 := realHessian_eq_zero_of_notMem_tsupport hxt v w
    rw [realHessian_comp_sub] at h0
    exact hx h0
  have hHK : ∀ j : ℕ, tsupport (fun x => H j (x - z)) ⊆ K := by
    intro j
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra hxK
    have hxt : x ∉ tsupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
      fun h => hxK (hφK j h)
    have h0 := realHessian_eq_zero_of_notMem_tsupport hxt v w
    rw [realHessian_comp_sub] at h0
    exact hx h0
  -- the decomposition `∂²V_j(z) = A_j - B_j`
  set A : ℕ → ℝ := fun j => ∫ x, q x * H j (x - z) with hA
  set B : ℕ → ℝ := fun j => ∫ x, (q x - K.indicator V x) * H j (x - z) with hB
  have hdecomp : ∀ j, realHessian (mollified V x₀ R hR j) z v w = A j - B j := by
    intro j
    have hint1 : Integrable (fun x => q x * H j (x - z)) :=
      TranscendentalWNReg.integrable_mul_of_continuousOn Ω.isOpen hq.continuousOn (hHc j) (hHs j)
        ((hHK j).trans hKΩ)
    have hint2 : Integrable (fun x => K.indicator V x * H j (x - z)) :=
      integrable_translationPairing_realHessian hg
        (explicitRadialKernel_hasCompactSupport R hR j)
        (explicitRadialKernel_contDiff_two R hR j) z v w
    have hint3 : Integrable (fun x => (q x - K.indicator V x) * H j (x - z)) :=
      (hint1.sub hint2).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    rw [mollified, realHessian_translationPairing hg (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff_two R hR j)]
    change ∫ x, K.indicator V x * H j (x - z) =
      (∫ x, q x * H j (x - z)) - ∫ x, (q x - K.indicator V x) * H j (x - z)
    rw [← integral_sub hint1 hint3]
    congr 1
    funext x
    ring
  -- `A_j → ∂²q(z)`
  have hAlim : Tendsto A atTop (𝓝 (realHessian q z v w)) := by
    have hIBP : ∀ j, A j = ∫ x, realHessian q x v w * explicitRadialKernel R hR j (x - z) := by
      intro j
      have h := integral_mul_realHessian_eq_of_contDiffOn Ω.isOpen hq (hφ j) (hφc j)
        ((hφK j).trans hKΩ) v w
      simp only [realHessian_comp_sub] at h
      exact h
    have hcont : ContinuousOn (fun x => realHessian q x v w) Ω := by
      have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ q)) Ω :=
        (hq.fderiv_of_isOpen (m := ∞) Ω.isOpen (by simp)).fderiv_of_isOpen Ω.isOpen (by simp)
      simp only [realHessian_eq_fderiv]
      exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
    rw [show A = fun j => ∫ x, realHessian q x v w * explicitRadialKernel R hR j (x - z) from
      funext hIBP]
    exact tendsto_integral_mul_explicitRadialKernel R hR Ω.isOpen hcont hzΩ
  -- `B_j → 0`
  obtain ⟨M₀, hM₀, hM₀b⟩ := exists_abs_realHessian_explicitRadialKernel_le (n := n) R hR v w
  set d := Module.finrank ℝ (ComplexModel n) with hd
  set c₁ := volume (ball (0 : ComplexModel n) 1) with hc₁
  have hc₁top : c₁ ≠ ⊤ := measure_ball_lt_top.ne
  have hBlim : Tendsto B atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε' hε'
    set Λ : ℝ := M₀ * R ^ (d + 2) * c₁.toReal with hΛ
    have hΛ0 : 0 ≤ Λ := by positivity
    set ε : ℝ := ε' / (2 * (Λ + 1)) with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨J, hJ⟩ := ((tendsto_kernel_radius R hR).eventually (hflat ε hε0)).exists_forall_of_atTop
    refine ⟨J, fun j hj => ?_⟩
    have hJj := hJ j hj
    set r : ℝ := R / ((j : ℝ) + 1) with hr
    set cj : ℝ := (j : ℝ) + 1 with hcj
    have hcj0 : 0 < cj := by positivity
    have hr0 : 0 < r := by positivity
    have hrR : r ≤ R := hrad j
    have hpt : ∀ x, ‖(q x - K.indicator V x) * H j (x - z)‖ₑ ≤
        (closedBall z r).indicator
          (fun x => ENNReal.ofReal (cj ^ (d + 2) * M₀) * ENNReal.ofReal (q x - V x)) x := by
      intro x
      by_cases hx : x ∈ closedBall z r
      · have hxK : x ∈ K := hzK (closedBall_subset_closedBall hrR hx)
        have hxΩ : x ∈ Ω := hKΩ hxK
        rw [indicator_of_mem hx, indicator_of_mem hxK, Real.enorm_eq_ofReal_abs, abs_mul,
          abs_of_nonneg (sub_nonneg.mpr (hVq x hxΩ)), ← ENNReal.ofReal_mul (by positivity),
          mul_comm]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hM₀b j (x - z))
          (sub_nonneg.mpr (hVq x hxΩ)))
      · have hxr : r < dist x z := not_le.mp hx
        rw [indicator_of_notMem hx]
        simp [H, realHessian_explicitRadialKernel_sub_eq_zero R hR j hxr v w]
    have hvol : volume (closedBall z r) = ENNReal.ofReal (r ^ d) * c₁ :=
      Measure.addHaar_closedBall volume z hr0.le
    have hbound : ‖B j‖ₑ ≤ ENNReal.ofReal (M₀ * ε * R ^ (d + 2)) * c₁ := by
      calc ‖B j‖ₑ ≤ ∫⁻ x, ‖(q x - K.indicator V x) * H j (x - z)‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ x, (closedBall z r).indicator
              (fun x => ENNReal.ofReal (cj ^ (d + 2) * M₀) * ENNReal.ofReal (q x - V x)) x :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (cj ^ (d + 2) * M₀) *
              ∫⁻ x in closedBall z r, ENNReal.ofReal (q x - V x) := by
            rw [lintegral_indicator measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (cj ^ (d + 2) * M₀) *
              (ENNReal.ofReal (ε * r ^ 2) * (ENNReal.ofReal (r ^ d) * c₁)) := by
            rw [← hvol]
            gcongr
        _ = ENNReal.ofReal (cj ^ (d + 2) * M₀ * (ε * r ^ 2) * r ^ d) * c₁ := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cj ^ (d + 2) * M₀ * (ε * r ^ 2)),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cj ^ (d + 2) * M₀)]
            ring
        _ = ENNReal.ofReal (M₀ * ε * R ^ (d + 2)) * c₁ := by
            congr 2
            have hcr : cj * r = R := by rw [hr, hcj]; field_simp
            calc cj ^ (d + 2) * M₀ * (ε * r ^ 2) * r ^ d
                = M₀ * ε * (cj * r) ^ (d + 2) := by rw [mul_pow, pow_add, pow_add]; ring
              _ = M₀ * ε * R ^ (d + 2) := by rw [hcr]
    have hreal : |B j| ≤ M₀ * ε * R ^ (d + 2) * c₁.toReal := by
      have h1 : ENNReal.ofReal |B j| ≤ ENNReal.ofReal (M₀ * ε * R ^ (d + 2)) * c₁ := by
        rw [← Real.enorm_eq_ofReal_abs]
        exact hbound
      rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc₁top),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
      exact h1
    rw [Real.dist_eq, sub_zero]
    calc |B j| ≤ M₀ * ε * R ^ (d + 2) * c₁.toReal := hreal
      _ = Λ * ε := by rw [hΛ]; ring
      _ = Λ * ε' / (2 * (Λ + 1)) := by rw [hε]; ring
      _ < ε' := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
  have hlim := hAlim.sub hBlim
  rw [sub_zero] at hlim
  exact hlim.congr fun j => (hdecomp j).symm

end Mollifier

/-! ### Quadratic ball averages at contact points -/

section Submean

variable {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ} {x₀ : ComplexModel n} {R : ℝ}

theorem leviForm_quad_sub (M : ℝ) (y : ComplexModel n) {q : ComplexModel n → ℝ}
    {x : ComplexModel n} (hq : ContDiffAt ℝ 2 q x) (v : ComplexModel n) :
    leviForm (fun z => M * ‖z - y‖ ^ 2 - q z) x v = M * ‖v‖ ^ 2 - leviForm q x v := by
  have hA : ContDiffAt ℝ 2 (fun z : ComplexModel n => ‖z - y‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hfun : (fun z => M * ‖z - y‖ ^ 2 - q z) =
      M • (fun z : ComplexModel n => ‖z - y‖ ^ 2) + (-q) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rw [hfun, leviForm_add (show ContDiffAt ℝ 2 (M • fun z : ComplexModel n => ‖z - y‖ ^ 2) x from
      hA.const_smul M) (show ContDiffAt ℝ 2 (-q) x from hq.neg), leviForm_smul hA, leviForm_neg,
    TranscendentalWN.EnvelopeLocal.leviForm_comp_sub (fun z : ComplexModel n => ‖z‖ ^ 2),
    leviForm_norm_sq]
  ring

theorem abs_realHessian_le (u : ComplexModel n → ℝ) (x a : ComplexModel n) :
    |realHessian u x a a| ≤ ‖iteratedFDeriv ℝ 2 u x‖ * ‖a‖ ^ 2 := by
  have h := (iteratedFDeriv ℝ 2 u x).le_opNorm ![a, a]
  rw [Fin.prod_univ_two] at h
  simpa [realHessian, sq, Real.norm_eq_abs] using h

/-- **Quadratic ball averages at contact points.**  There is `M ≥ 0` such that for every contact
point `y ∈ Ω` (`V y = q y`) and every closed ball `B̄(y, s) ⊆ B(x₀, 4R)`,
`∫_{B̄(y,s)} (q - V) ≤ M s² |B̄(y, s)|` (sub-mean value property of `V + M|· - y|² - q`). -/
theorem exists_setLIntegral_sub_le_of_contact (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : ContDiffOn ℝ ∞ q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ComplexModel n, y ∈ Ω → V y = q y → ∀ s : ℝ, 0 < s →
      closedBall y s ⊆ ball x₀ (4 * R) →
        ∫⁻ x in closedBall y s, ENNReal.ofReal (q x - V x) ≤
          ENNReal.ofReal (M * s ^ 2) * volume (closedBall y s) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set W : Set (ComplexModel n) := ball x₀ (4 * R) with hW
  have hWΩ : W ⊆ Ω := ball_subset_closedBall.trans hball
  -- a bound for the second derivatives of `q`
  have hcont : ContinuousOn (fun x => iteratedFDeriv ℝ 2 q x) Ω :=
    (hq.continuousOn_iteratedFDerivWithin (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      Ω.isOpen.uniqueDiffOn).congr fun x hx =>
      (iteratedFDerivWithin_of_isOpen 2 Ω.isOpen hx).symm
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall x₀ (4 * R)).exists_bound_of_continuousOn
    (hcont.mono hball)
  set M : ℝ := max M₂ 0 with hM
  refine ⟨M, le_max_right _ _, fun y hyΩ hyq s hs hsW => ?_⟩
  have hq2 : ∀ x ∈ W, ContDiffAt ℝ 2 q x := fun x hx =>
    ((hq x (hWΩ hx)).contDiffAt (Ω.isOpen.mem_nhds (hWΩ hx))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlevi_q : ∀ x ∈ W, ∀ v, leviForm q x v ≤ M * ‖v‖ ^ 2 := by
    intro x hx v
    have hD : ‖iteratedFDeriv ℝ 2 q x‖ ≤ M :=
      (hM₂ x (ball_subset_closedBall hx)).trans (le_max_left _ _)
    have h1 := abs_realHessian_le q x v
    have h2 := abs_realHessian_le q x (Complex.I • v)
    rw [norm_smul, Complex.norm_I, one_mul] at h2
    have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
    have e1 := (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right hD hv2))
    have e2 := (le_abs_self _).trans (h2.trans (mul_le_mul_of_nonneg_right hD hv2))
    have hM0 : 0 ≤ M * ‖v‖ ^ 2 := mul_nonneg (le_max_right _ _) hv2
    simp only [leviForm]
    linarith
  -- the plurisubharmonic comparison function
  set h : ComplexModel n → ℝ := fun x => M * ‖x - y‖ ^ 2 - q x with hh
  have hhs : ContDiffOn ℝ ∞ h W :=
    ((contDiffOn_const.mul ((contDiff_norm_sq ℝ).comp
      (contDiff_id.sub contDiff_const)).contDiffOn)).sub (hq.mono hWΩ)
  have hhpsh : PlurisubharmonicOn (fun x => (h x : EReal)) W :=
    TranscendentalWN.EnvelopeLocal.plurisubharmonicOn_of_leviForm_nonneg_on isOpen_ball hhs
      fun x hx v => by
        rw [hh, leviForm_quad_sub M y (hq2 x hx) v]
        linarith [hlevi_q x hx v]
  have hsum : PlurisubharmonicOn (fun x => ((V x + h x : ℝ) : EReal)) W := by
    have h1 := (hV.1.mono hWΩ).add hhpsh
    simpa only [EReal.coe_add] using h1
  have hsubmean := PSHD.real_ball_submean
    (FirstPass.PlurisubharmonicOn.discPshOn hsum) volume y hs hsW
  have hy0 : V y + h y = 0 := by simp [hh, hyq]
  rw [hy0, mul_zero] at hsubmean
  -- integrability on the ball
  have hBΩ : closedBall y s ⊆ Ω := hsW.trans hWΩ
  have hVint : IntegrableOn V (closedBall y s) :=
    (locallyIntegrableOn_of_plurisubharmonicOn_real hV.1).integrableOn_compact_subset hBΩ
      (isCompact_closedBall y s)
  have hqint : IntegrableOn q (closedBall y s) :=
    (hq.continuousOn.mono hBΩ).integrableOn_compact (isCompact_closedBall y s)
  have hnint : IntegrableOn (fun x : ComplexModel n => M * ‖x - y‖ ^ 2) (closedBall y s) :=
    (by fun_prop : Continuous fun x : ComplexModel n => M * ‖x - y‖ ^ 2).continuousOn
      |>.integrableOn_compact (isCompact_closedBall y s)
  have hVb := hVint.mono_set ball_subset_closedBall
  have hqb := hqint.mono_set ball_subset_closedBall
  have hnb := hnint.mono_set ball_subset_closedBall
  have hdiff : ∫ x in ball y s, (q x - V x) ≤ M * s ^ 2 * (volume (ball y s)).toReal := by
    have e : ∫ x in ball y s, (q x - V x) =
        (∫ x in ball y s, M * ‖x - y‖ ^ 2) - ∫ x in ball y s, (V x + h x) := by
      have hsumint : IntegrableOn (fun x => V x + h x) (ball y s) := hVb.add (hnb.sub hqb)
      rw [← integral_sub hnb hsumint]
      congr 1
      funext x
      simp only [hh]
      ring
    have hn2 : ∫ x in ball y s, M * ‖x - y‖ ^ 2 ≤ ∫ x in ball y s, M * s ^ 2 := by
      refine setIntegral_mono_on hnb (integrableOn_const measure_ball_lt_top.ne)
        measurableSet_ball fun x hx => ?_
      have hx' : ‖x - y‖ ≤ s := (mem_ball_iff_norm.mp hx).le
      gcongr
    rw [setIntegral_const, smul_eq_mul, mul_comm] at hn2
    rw [e]
    simp only [Measure.real] at hn2
    linarith
  have hball_eq : volume (closedBall y s) = volume (ball y s) :=
    Measure.addHaar_closedBall_eq_addHaar_ball volume y s
  have hae : (ball y s : Set (ComplexModel n)) =ᵐ[volume] closedBall y s :=
    ae_eq_of_subset_of_measure_ge ball_subset_closedBall hball_eq.le
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  calc ∫⁻ x in closedBall y s, ENNReal.ofReal (q x - V x)
      = ∫⁻ x in ball y s, ENNReal.ofReal (q x - V x) := setLIntegral_congr hae.symm
    _ = ENNReal.ofReal (∫ x in ball y s, (q x - V x)) := by
        have hsubint : IntegrableOn (fun x => q x - V x) (ball y s) := hqb.sub hVb
        rw [ofReal_integral_eq_lintegral_ofReal hsubint]
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact sub_nonneg.mpr (hVq x (hWΩ (hsW (ball_subset_closedBall hx))))
    _ ≤ ENNReal.ofReal (M * s ^ 2 * (volume (ball y s)).toReal) := ENNReal.ofReal_le_ofReal hdiff
    _ = ENNReal.ofReal (M * s ^ 2) * volume (closedBall y s) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) (sq_nonneg s)),
          ENNReal.ofReal_toReal measure_ball_lt_top.ne, hball_eq]

end Submean

/-! ### Convergence of the densities on the contact set -/

section Bounded

variable {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ} {x₀ : ComplexModel n} {R : ℝ}

/-- The contact set inside `B(x₀, 2R)`. -/
def contactBall (Ω : Opens (ComplexModel n)) (V q : ComplexModel n → ℝ) (x₀ : ComplexModel n)
    (R : ℝ) : Set (ComplexModel n) :=
  {z | z ∈ Ω ∧ V z = q z} ∩ ball x₀ (2 * R)

theorem measurableSet_contactBall (hV : IsLocallyBoundedPshOn Ω V) (hq : ContDiffOn ℝ ∞ q Ω) :
    MeasurableSet (contactBall Ω V q x₀ R) :=
  (TranscendentalWN.EnvelopeLocal.measurableSet_eq_of_upperSemicontinuousOn hq.continuousOn
    hV.1.upperSemicontinuousOn).inter measurableSet_ball

/-- **Almost every contact point is flat**, so the Monge–Ampère densities of the mollified
potentials converge there to that of the obstacle. -/
theorem ae_tendsto_smoothDensity_mollified (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : ContDiffOn ℝ ∞ q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∀ᵐ z ∂volume.restrict (contactBall Ω V q x₀ R),
      Tendsto (fun j => smoothDensity (mollified V x₀ R hR j) z) atTop (𝓝 (smoothDensity q z)) := by
  set S := contactBall Ω V q x₀ R with hS
  have hSm : MeasurableSet S := measurableSet_contactBall hV hq
  set G : ComplexModel n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((Ω : Set (ComplexModel n)).indicator q x -
      (Ω : Set (ComplexModel n)).indicator V x) with hG
  have hGm : Measurable G := by
    have hqm : Measurable ((Ω : Set (ComplexModel n)).indicator q) := by
      classical
      have h := hq.continuousOn.measurable_piecewise (continuousOn_const (c := (0 : ℝ)))
        Ω.isOpen.measurableSet
      convert h using 1
      ext x
      by_cases hx : x ∈ (Ω : Set (ComplexModel n)) <;> simp [Set.piecewise, hx]
    exact ENNReal.measurable_ofReal.comp
      (hqm.sub (LocalBedfordTaylorProducts.measurable_indicator_of_isLocallyBoundedPshOn hV))
  have hGeq : ∀ x ∈ (Ω : Set (ComplexModel n)), G x = ENNReal.ofReal (q x - V x) := by
    intro x hx
    simp only [hG, indicator_of_mem hx]
  obtain ⟨M, hM0, hM⟩ := exists_setLIntegral_sub_le_of_contact hn hV hq hVq hball
  filter_upwards [DensityPoint.ae_eventually_measure_closedBall_diff_le volume hSm,
    ae_restrict_mem hSm] with z hdens hzS
  have hz2 : z ∈ ball x₀ (2 * R) := hzS.2
  have hzR : ball z R ⊆ ball x₀ (4 * R) :=
    ball_subset_ball' (by rw [mem_ball] at hz2; linarith)
  have hsub : ∀ y ∈ S, ∀ s : ℝ, 0 < s → dist y z + s < R →
      ∫⁻ x in closedBall y s, G x ∂volume ≤ ENNReal.ofReal (M * s ^ 2) * volume (closedBall y s) := by
    intro y hy s hs hys
    have hsub1 : closedBall y s ⊆ ball x₀ (4 * R) :=
      (closedBall_subset_ball' (by linarith)).trans hzR
    have hsubΩ : closedBall y s ⊆ Ω := hsub1.trans (ball_subset_closedBall.trans hball)
    rw [setLIntegral_congr_fun measurableSet_closedBall fun x hx => hGeq x (hsubΩ hx)]
    exact hM y hy.1.1 hy.1.2 s hs hsub1
  have hflatG := DensityPoint.eventually_setLIntegral_le_of_density volume hGm hSm hzS hM0 hR
    hsub hdens
  have hflat : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ x in closedBall z r, ENNReal.ofReal (q x - V x) ≤
        ENNReal.ofReal (ε * r ^ 2) * volume (closedBall z r) := by
    intro ε hε
    filter_upwards [hflatG ε hε, Ioo_mem_nhdsGT hR] with r hr hrR
    have hsubΩ : closedBall z r ⊆ Ω :=
      ((closedBall_subset_ball hrR.2).trans hzR).trans (ball_subset_closedBall.trans hball)
    rwa [setLIntegral_congr_fun measurableSet_closedBall fun x hx => hGeq x (hsubΩ hx)] at hr
  exact tendsto_smoothDensity_of_tendsto_realHessian fun a b =>
    tendsto_realHessian_mollified hV hq hVq hR hball hz2 hflat a b

/-- The bounded test-function inequality behind the closed-ball bound: for a bump `φ` supported
in `B(x₀, 2R)`, `∫_C φ (ddᶜq)ⁿ ≤ ∫ φ d(ddᶜV)ⁿ` (Fatou along the mollified potentials). -/
theorem setLIntegral_contactBall_mul_le (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : ContDiffOn ℝ ∞ q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {φ : ComplexModel n → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ ball x₀ (2 * R)) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ z in contactBall Ω V q x₀ R, ENNReal.ofReal (φ z * smoothDensity q z) ≤
      ENNReal.ofReal (∫ z, φ z ∂canonicalBedfordTaylorMeasure Ω V hV) := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set U := innerBall x₀ R with hUdef
  set f := mollified V x₀ R hR with hf
  have hU : RelativelyCompactIn U Ω := by
    have hcl : closure (U : Set (ComplexModel n)) ⊆ closedBall x₀ (2 * R) :=
      closure_ball_subset_closedBall
    exact ⟨(isCompact_closedBall x₀ (2 * R)).of_isClosed_subset isClosed_closure hcl,
      hcl.trans ((closedBall_subset_closedBall (by linarith)).trans hball)⟩
  have hdec := isDecreasingApproximation_mollified hV hR hball
  have hweak := ((canonicalBedfordTaylorMeasure_spec Ω V hV).2.2.2 U hU).2 f hdec φ hφ hφc hφU
  -- the real test integrals as lintegrals
  have hlint : ∀ j, ENNReal.ofReal (∫ z, φ z ∂smoothMeasure U (f j) (hdec.1 j)) =
      ∫⁻ z in (U : Set (ComplexModel n)), ENNReal.ofReal (φ z * smoothDensity (f j) z) := by
    intro j
    obtain ⟨-, hint, heq⟩ :=
      FirstPass.MongeAmpere.smoothMeasure_test_integral (hdec.1 j) φ hφ hφc hφU
    rw [heq, ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with z hz
    exact mul_nonneg (hφ0 z) (smoothDensity_nonneg ((hdec.1 j).2.2 z hz))
  have hlim : Tendsto (fun j => ∫⁻ z in (U : Set (ComplexModel n)),
      ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, φ z ∂μ))) := by
    simp_rw [← hlint]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hweak
  have hmeas : ∀ j, AEMeasurable (fun z => ENNReal.ofReal (φ z * smoothDensity (f j) z))
      (volume.restrict (contactBall Ω V q x₀ R)) := by
    intro j
    have hc : Continuous (smoothDensity (f j)) :=
      continuousOn_univ.mp (TranscendentalWN.EnvelopeLocal.continuousOn_smoothDensity isOpen_univ
        (contDiff_mollified hV hball hR j).contDiffOn)
    exact (ENNReal.continuous_ofReal.comp (hφ.mul hc)).measurable.aemeasurable
  have hSU : contactBall Ω V q x₀ R ⊆ U := inter_subset_right
  calc ∫⁻ z in contactBall Ω V q x₀ R, ENNReal.ofReal (φ z * smoothDensity q z)
      = ∫⁻ z in contactBall Ω V q x₀ R,
          liminf (fun j => ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_tendsto_smoothDensity_mollified hn hV hq hVq hR hball] with z hz
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hz.const_mul (φ z))).liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ z in contactBall Ω V q x₀ R,
          ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop := lintegral_liminf_le' hmeas
    _ ≤ liminf (fun j => ∫⁻ z in (U : Set (ComplexModel n)),
          ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun j => lintegral_mono_set hSU) ?_ ?_
        · isBoundedDefault
        · isBoundedDefault
    _ = ENNReal.ofReal (∫ z, φ z ∂μ) := hlim.liminf_eq

/-- **The contact bound on closed balls.**  For `B̄(y, 2r) ⊆ B(x₀, 2R)`,
`∫_{C ∩ B̄(y, r)} (ddᶜq)ⁿ ≤ (ddᶜV)ⁿ(B̄(y, r))`. -/
theorem setLIntegral_contactBall_closedBall_le (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : ContDiffOn ℝ ∞ q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {y : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hyr : closedBall y (2 * r) ⊆ ball x₀ (2 * R)) :
    ∫⁻ z in contactBall Ω V q x₀ R ∩ closedBall y r, ENNReal.ofReal (smoothDensity q z) ≤
      canonicalBedfordTaylorMeasure Ω V hV (closedBall y r) := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set S := contactBall Ω V q x₀ R with hS
  have hSm : MeasurableSet S := measurableSet_contactBall hV hq
  have hBΩ : closedBall y (2 * r) ⊆ Ω :=
    hyr.trans (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans
      hball))
  have hδ : ∀ δ : ℝ, 0 < δ → δ ≤ r →
      ∫⁻ z in S ∩ closedBall y r, ENNReal.ofReal (smoothDensity q z) ≤ μ (closedBall y (δ + r)) := by
    intro δ hδ0 hδr
    let b : ContDiffBump y := ⟨r, δ + r, hr, by linarith⟩
    have hbc : Continuous (b : ComplexModel n → ℝ) := b.continuous
    have hbs : HasCompactSupport (b : ComplexModel n → ℝ) := b.hasCompactSupport
    have hbt : tsupport (b : ComplexModel n → ℝ) = closedBall y (δ + r) := b.tsupport_eq
    have hbU : tsupport (b : ComplexModel n → ℝ) ⊆ ball x₀ (2 * R) := by
      rw [hbt]
      exact (closedBall_subset_closedBall (by linarith)).trans hyr
    have hkey := setLIntegral_contactBall_mul_le hn hV hq hVq hR hball hbc hbs hbU fun _ => b.nonneg
    have hint_le : ENNReal.ofReal (∫ z, b z ∂μ) ≤ μ (closedBall y (δ + r)) := by
      by_cases hi : Integrable (b : ComplexModel n → ℝ) μ
      · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => b.nonneg),
          ← lintegral_indicator_one measurableSet_closedBall]
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall y (δ + r)
        · rw [indicator_of_mem hz, Pi.one_apply, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal b.le_one
        · have hz' : z ∉ tsupport (b : ComplexModel n → ℝ) := by rwa [hbt]
          rw [image_eq_zero_of_notMem_tsupport hz', ENNReal.ofReal_zero]
          simp
      · rw [integral_undef hi, ENNReal.ofReal_zero]
        simp
    calc ∫⁻ z in S ∩ closedBall y r, ENNReal.ofReal (smoothDensity q z)
        = ∫⁻ z in S ∩ closedBall y r, ENNReal.ofReal (b z * smoothDensity q z) := by
          refine setLIntegral_congr_fun (hSm.inter measurableSet_closedBall) fun z hz => ?_
          rw [b.one_of_mem_closedBall hz.2, one_mul]
      _ ≤ ∫⁻ z in S, ENNReal.ofReal (b z * smoothDensity q z) :=
          lintegral_mono_set inter_subset_left
      _ ≤ ENNReal.ofReal (∫ z, b z ∂μ) := hkey
      _ ≤ μ (closedBall y (δ + r)) := hint_le
  -- `δ → 0`
  have hfin : μ (Metric.cthickening r (closedBall y r)) ≠ ⊤ := by
    rw [cthickening_closedBall hr.le hr.le]
    exact (canonicalBedfordTaylorMeasure_finiteOnCompacts hV (isCompact_closedBall _ _)
      (by rw [show r + r = 2 * r by ring]; exact hBΩ)).ne
  have htend := (tendsto_measure_cthickening_of_isClosed ⟨r, hr, hfin⟩ isClosed_closedBall).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioc_mem_nhdsGT hr] with δ hδm
  rw [cthickening_closedBall hδm.1.le hr.le]
  exact hδ δ hδm.1 hδm.2

/-- **The contact bound for bounded potentials.**  Let `V ≤ q` on `Ω`, `V` locally bounded
plurisubharmonic, `q` smooth, and `B̄(x₀, 4R) ⊆ Ω`.  For every `T ⊆ {V = q} ∩ B(x₀, R)`,
`∫_T (ddᶜq)ⁿ ≤ (ddᶜV)ⁿ(T)`. -/
theorem canonicalBedfordTaylorMeasure_contact_ge (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : ContDiffOn ℝ ∞ q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {T : Set (ComplexModel n)}
    (hT : T ⊆ {z | z ∈ Ω ∧ V z = q z} ∩ ball x₀ R) :
    ∫⁻ z in T, ENNReal.ofReal (smoothDensity q z) ≤ canonicalBedfordTaylorMeasure Ω V hV T := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set S := contactBall Ω V q x₀ R with hS
  have hSm : MeasurableSet S := measurableSet_contactBall hV hq
  have hTS : T ⊆ S := fun z hz =>
    ⟨(hT hz).1, ball_subset_ball (by linarith) (hT hz).2⟩
  set ρ := (volume.restrict S).withDensity fun z => ENNReal.ofReal (smoothDensity q z) with hρ
  have hρac : ρ ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have h2R : closedBall x₀ (2 * R) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  set ν := μ.restrict (closedBall x₀ (2 * R)) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (canonicalBedfordTaylorMeasure_finiteOnCompacts hV (isCompact_closedBall _ _) h2R).ne
  have key := (Besicovitch.vitaliFamily (volume : Measure (ComplexModel n))).measure_le_of_frequently_le
    ν hρac T ?_
  · calc ∫⁻ z in T, ENNReal.ofReal (smoothDensity q z) = ρ T := by
          rw [hρ, withDensity_apply', Measure.restrict_restrict' hSm, inter_eq_left.mpr hTS]
      _ ≤ ν T := key
      _ ≤ μ T := Measure.restrict_apply_le _ _
  · intro y hy
    rw [VitaliFamily.frequently_filterAt_iff]
    intro ε hε
    have hyR : dist y x₀ < R := (hT hy).2
    set r := min ε (R / 2) with hr
    have hr0 : 0 < r := lt_min hε (by positivity)
    have hrε : r ≤ ε := min_le_left _ _
    have hrR : r ≤ R / 2 := min_le_right _ _
    have hyr : closedBall y (2 * r) ⊆ ball x₀ (2 * R) :=
      closedBall_subset_ball' (by linarith)
    refine ⟨closedBall y r, ⟨r, hr0, rfl⟩, closedBall_subset_closedBall hrε, ?_⟩
    have hsub : closedBall y r ⊆ closedBall x₀ (2 * R) :=
      (closedBall_subset_closedBall (by linarith)).trans (hyr.trans ball_subset_closedBall)
    rw [hρ, withDensity_apply _ measurableSet_closedBall, Measure.restrict_restrict
      measurableSet_closedBall, inter_comm, hν, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr hsub]
    exact setLIntegral_contactBall_closedBall_le hn hV hq hVq hR hball hr0 hyr

end Bounded

/-! ### Potentials with poles -/

/-- **The local contact bound "`≥`".**  Let `U ≤ q` on `Ω`, with `U` plurisubharmonic (possibly
with poles) and `q` smooth on `Ω` (not necessarily plurisubharmonic), `n > 0`, and
`B̄(x₀, 5R) ⊆ Ω`.  For every `T ⊆ {U = q} ∩ B(x₀, R)`, the non-pluripolar Monge–Ampère measure of
`U` satisfies `∫_T (ddᶜq)ⁿ ≤ ⟨(ddᶜU)ⁿ⟩(T)`. -/
theorem truncationLimitMeasure_contact_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {U : ComplexModel n → EReal} (hU : PlurisubharmonicOn U Ω) {q : ComplexModel n → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω) (hUq : ∀ z ∈ Ω, U z ≤ q z) {x₀ : ComplexModel n} {R : ℝ}
    (hR : 0 < R) (hball : closedBall x₀ (5 * R) ⊆ Ω) {T : Set (ComplexModel n)}
    (hT : T ⊆ {z | z ∈ Ω ∧ U z = q z} ∩ ball x₀ R) :
    ∫⁻ z in T, ENNReal.ofReal (smoothDensity q z) ≤ truncationLimitMeasure Ω U hU T := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall x₀ (5 * R)).exists_bound_of_continuousOn
    (hq.continuousOn.mono hball)
  set k : ℕ := ⌈B⌉₊ + 1 with hk
  have hkB : B < k := by
    rw [hk]; push_cast
    linarith [Nat.le_ceil B]
  have hqk : ∀ z ∈ closedBall x₀ (5 * R), -(k : ℝ) < q z := by
    intro z hz
    have := hB z hz
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (q z)]
  let Ω' : Opens (ComplexModel n) := ⟨ball x₀ (5 * R), isOpen_ball⟩
  have hΩ' : Ω' ≤ Ω := ball_subset_closedBall.trans hball
  have hVk : IsLocallyBoundedPshOn Ω (truncationReal U k) := truncationReal_isLocallyBoundedPshOn hU k
  have hVk' : IsLocallyBoundedPshOn Ω' (truncationReal U k) := BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hVk hΩ'
  have htr : ∀ z ∈ Ω, (truncationReal U k z : EReal) = max (U z) ((-(k : ℝ) : ℝ) : EReal) :=
    fun z hz => coe_truncationReal hU k hz
  have hVq : ∀ z ∈ Ω', truncationReal U k z ≤ q z := by
    intro z hz
    have h := htr z (hΩ' hz)
    have hle : max (U z) ((-(k : ℝ) : ℝ) : EReal) ≤ (q z : EReal) :=
      max_le (hUq z (hΩ' hz)) (EReal.coe_le_coe_iff.mpr (hqk z (ball_subset_closedBall hz)).le)
    rw [← h] at hle
    exact EReal.coe_le_coe_iff.mp hle
  have hlocus : T ⊆ strictTruncationLocus Ω U k := by
    intro z hz
    obtain ⟨⟨hzΩ, hzU⟩, hzB⟩ := hT hz
    refine ⟨hzΩ, ?_⟩
    rw [hzU]
    exact EReal.coe_lt_coe_iff.mpr (hqk z (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hzB))
  have hT' : T ⊆ {z | z ∈ Ω' ∧ truncationReal U k z = q z} ∩ ball x₀ R := by
    intro z hz
    obtain ⟨⟨hzΩ, hzU⟩, hzB⟩ := hT hz
    have hzΩ' : z ∈ Ω' := ball_subset_ball (by linarith) hzB
    refine ⟨⟨hzΩ', ?_⟩, hzB⟩
    have h := htr z hzΩ
    rw [hzU, max_eq_left (EReal.coe_le_coe_iff.mpr
      (hqk z (ball_subset_closedBall hzΩ')).le)] at h
    exact EReal.coe_eq_coe_iff.mp h
  have hball' : closedBall x₀ (4 * R) ⊆ Ω' := closedBall_subset_ball (by linarith)
  calc ∫⁻ z in T, ENNReal.ofReal (smoothDensity q z)
      ≤ canonicalBedfordTaylorMeasure Ω' (truncationReal U k) hVk' T :=
        canonicalBedfordTaylorMeasure_contact_ge hn hVk' (hq.mono hΩ') hVq hR hball' hT'
    _ = (canonicalBedfordTaylorMeasure Ω (truncationReal U k) hVk).restrict
          (Ω' : Set (ComplexModel n)) T := by
        rw [canonicalBedfordTaylorMeasure_restrict hΩ' hVk hVk']
    _ ≤ canonicalBedfordTaylorMeasure Ω (truncationReal U k) hVk T :=
        Measure.restrict_apply_le _ _
    _ = truncationMeasure Ω U hU k T := by
        rw [truncationMeasure, Measure.restrict_eq_self _ hlocus]
    _ = (truncationLimitMeasure Ω U hU).restrict (strictTruncationLocus Ω U k) T := by
        rw [truncationLimitMeasure_restrict_strictLocus]
    _ ≤ truncationLimitMeasure Ω U hU T := Measure.restrict_apply_le _ _

end SGPT.Okounkov.TranscendentalWNReg.ContactLocal
