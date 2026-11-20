import SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiSubspace
import SGPT.Foundations.Analysis.Pending.OTSliceVanishing
import SGPT.Foundations.Analysis.Pending.RiemannExtension
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.RestrictionOhsawaTakegoshi
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.LogPole
import SGPT.Foundations.Analysis.LocalPshDiscControl
import Mathlib.RingTheory.Complex
import Mathlib.Algebra.Order.Chebyshev

/-!
# Local `L²` extension with a subcritical gain, by a ramified cover

Blueprint `claude-ot3.tex`, nodes `claude-ot3:change-of-variables`, `claude-ot3:ramified-step`,
`claude-ot3:local-gain`.

TN's local Ohsawa--Takegoshi theorem (`ohsawaTakegoshiHyperplane_of_regular`, Chen's proof from
Hörmander's estimate) extends a holomorphic function `g` from the hyperplane `{w = 0}` of a convex
domain with an `L²(e^{-φ})` bound.  Applied to the pulled-back weight `φ(z, v^N)` on the ramified
domain, averaged over `v ↦ ζ v` (`ζ^N = 1`) and descended along `v ↦ v^N`, it gives an extension
`H` of `g` with the **subcritical gain**

  `∫ |H|² e^{-φ} |w|^{-2(1 - 1/N)} < ∞`

(`exists_extension_ramified`).  The change of variables `w = v^N` is
`lintegral_ball_mul_rpow_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-! ### The change of variables `w = v^N` in one variable -/

section ChangeOfVariables

/-- Lebesgue-almost every point of `ℂ` lies in the slit plane. -/
theorem slitPlane_ae_eq_univ : (Complex.slitPlane : Set ℂ) =ᵐ[volume] (univ : Set ℂ) := by
  have hsub : (Complex.slitPlane : Set ℂ)ᶜ ⊆ (LinearMap.ker (Complex.imLm) : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, Complex.mem_slitPlane_iff, not_or, not_lt] at hz
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Complex.imLm_coe]
    exact not_not.mp hz.2
  have hker : (LinearMap.ker (Complex.imLm) : Submodule ℝ ℂ) ≠ ⊤ := by
    intro h
    have : Complex.I ∈ LinearMap.ker (Complex.imLm) := by rw [h]; trivial
    simp at this
  have h0 : volume ((Complex.slitPlane : Set ℂ)ᶜ) = 0 :=
    measure_mono_null hsub (Measure.addHaar_submodule volume _ hker)
  simp only [ae_eq_univ]
  exact h0

/-- The real Jacobian determinant of `z ↦ z a` is `|a|²`. -/
theorem det_restrictScalars_smulRight (a : ℂ) :
    (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ :
      ℂ →L[ℝ] ℂ)).det = ‖a‖ ^ 2 := by
  have h1 : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) =
      a • LinearMap.id := by
    ext; simp [mul_comm]
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, h1, LinearMap.det_smul, LinearMap.det_id,
    Module.finrank_self, pow_one, mul_one, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

/-- **The change of variables `w = v^N`.**  For a nonnegative function `h` on `ℂ`,
`∫_{|w| < ρ} h(w) |w|^{2/N - 2} ≤ N² ∫_{|v| < ρ^{1/N}} h(v^N)`. -/
theorem lintegral_ball_mul_rpow_le {N : ℕ} (hN : N ≠ 0) (ρ : ℝ) (h : ℂ → ℝ≥0∞) :
    ∫⁻ w in ball (0 : ℂ) ρ, h w * ENNReal.ofReal (‖w‖ ^ ((2 : ℝ) / N - 2)) ≤
      ENNReal.ofReal ((N : ℝ) ^ 2) * ∫⁻ v in ball (0 : ℂ) (ρ ^ ((1 : ℝ) / N)), h (v ^ N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set c : ℂ := ((N : ℂ))⁻¹ with hc
  set D : Set ℂ := ball (0 : ℂ) ρ ∩ Complex.slitPlane with hD
  have hDm : MeasurableSet D := measurableSet_ball.inter Complex.isOpen_slitPlane.measurableSet
  set g : ℂ → ℂ := fun u => u ^ c with hg
  set g' : ℂ → ℂ →L[ℝ] ℂ := fun u =>
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (c * u ^ (c - 1))).restrictScalars ℝ) with hg'
  have hderiv : ∀ u ∈ D, HasFDerivWithinAt g (g' u) D u := fun u hu =>
    ((Complex.hasStrictDerivAt_cpow_const (c := c) hu.2).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  have hpow : ∀ u : ℂ, g u ^ N = u := fun u => Complex.cpow_nat_inv_pow u hN
  have hinj : InjOn g D := fun u _ u' _ huu => by
    rw [← hpow u, ← hpow u', huu]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hderiv hinj
    (fun v => h (v ^ N))
  -- the Jacobian
  have hnorm_c : ‖c‖ = (N : ℝ)⁻¹ := by rw [hc, norm_inv, Complex.norm_natCast]
  have hjac : ∀ u ∈ D, |(g' u).det| = (N : ℝ)⁻¹ ^ 2 * ‖u‖ ^ ((2 : ℝ) / N - 2) := by
    intro u hu
    have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hu.2
    rw [hg', det_restrictScalars_smulRight, abs_of_nonneg (by positivity), norm_mul, mul_pow,
      hnorm_c, Complex.norm_cpow_of_ne_zero hu0]
    have hre : (c - 1).re = (N : ℝ)⁻¹ - 1 := by simp [hc]
    have him : (c - 1).im = 0 := by simp [hc]
    rw [hre, him, mul_zero, Real.exp_zero, div_one]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg u)]
    congr 1
    push_cast
    field_simp
  -- the image lies in the small ball
  have himage : g '' D ⊆ ball (0 : ℂ) (ρ ^ ((1 : ℝ) / N)) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hu.2
    rw [mem_ball_zero_iff, hg]
    simp only
    rw [Complex.norm_cpow_of_ne_zero hu0]
    have hre : c.re = (N : ℝ)⁻¹ := by simp [hc]
    have him : c.im = 0 := by simp [hc]
    rw [hre, him, mul_zero, Real.exp_zero, div_one, one_div]
    exact Real.rpow_lt_rpow (norm_nonneg u) (mem_ball_zero_iff.mp hu.1) (inv_pos.mpr hNR)
  calc ∫⁻ w in ball (0 : ℂ) ρ, h w * ENNReal.ofReal (‖w‖ ^ ((2 : ℝ) / N - 2))
      = ∫⁻ w in D, h w * ENNReal.ofReal (‖w‖ ^ ((2 : ℝ) / N - 2)) := by
        refine setLIntegral_congr ?_
        have := (ae_eq_refl (ball (0 : ℂ) ρ)).inter slitPlane_ae_eq_univ.symm
        rw [inter_univ] at this
        exact this
    _ = ∫⁻ w in D, ENNReal.ofReal ((N : ℝ) ^ 2) *
          (ENNReal.ofReal |(g' w).det| * h (g w ^ N)) := by
        refine setLIntegral_congr_fun hDm fun w hw => ?_
        rw [hjac w hw, hpow w, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm (h w)]
        congr 2
        field_simp
    _ = ENNReal.ofReal ((N : ℝ) ^ 2) * ∫⁻ v in g '' D, h (v ^ N) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcv]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2) * ∫⁻ v in ball (0 : ℂ) (ρ ^ ((1 : ℝ) / N)), h (v ^ N) :=
        mul_le_mul' le_rfl (lintegral_mono_set himage)

end ChangeOfVariables

/-! ### Slabs, rotations and the ramified cover in the last variable -/

section Slab

open Pending Pending.OTChen

variable {k : ℕ}

/-- The slab `Ω₀ × D(0, ρ) ⊆ ℂ^{k+1}`. -/
def slab (Ω₀ : Set (ComplexModel k)) (ρ : ℝ) : Set (ComplexModel (k + 1)) :=
  {z | initCoords z ∈ Ω₀ ∧ ‖z (Fin.last k)‖ < ρ}

theorem slab_eq_preimage (Ω₀ : Set (ComplexModel k)) (ρ : ℝ) :
    slab Ω₀ ρ = splitCLE k ⁻¹' (Ω₀ ×ˢ ball (0 : ℂ) ρ) := by
  ext z; simp [slab]

theorem isOpen_slab {Ω₀ : Set (ComplexModel k)} (hΩ₀ : IsOpen Ω₀) (ρ : ℝ) :
    IsOpen (slab Ω₀ ρ) := by
  rw [slab_eq_preimage]
  exact (hΩ₀.prod isOpen_ball).preimage (splitCLE k).continuous

theorem convex_slab {Ω₀ : Set (ComplexModel k)} (hΩ₀ : Convex ℝ Ω₀) (ρ : ℝ) :
    Convex ℝ (slab Ω₀ ρ) := by
  rw [slab_eq_preimage]
  exact (hΩ₀.prod (convex_ball 0 ρ)).linear_preimage
    (((splitCLE k : ComplexModel (k + 1) →L[ℂ] ComplexModel k × ℂ)).toLinearMap.restrictScalars ℝ)

theorem sliceMap_mem_slab {Ω₀ : Set (ComplexModel k)} {ρ : ℝ} {u : ℂ} {w : ComplexModel k} :
    sliceMap k u w ∈ slab Ω₀ ρ ↔ w ∈ Ω₀ ∧ ‖u‖ < ρ := by
  simp [slab, initCoords_sliceMap]

theorem hyperplaneEmbedding_eq_sliceMap (w : ComplexModel k) :
    hyperplaneEmbedding k w = sliceMap k 0 w := by
  simp [sliceMap]

theorem hyperplaneEmbedding_mem_slab {Ω₀ : Set (ComplexModel k)} {ρ : ℝ} (hρ : 0 < ρ)
    {w : ComplexModel k} : hyperplaneEmbedding k w ∈ slab Ω₀ ρ ↔ w ∈ Ω₀ := by
  rw [hyperplaneEmbedding_eq_sliceMap, sliceMap_mem_slab]; simp [hρ]

theorem differentiable_sliceMap_comp {F : ComplexModel (k + 1) → ℂ}
    {Ω : Set (ComplexModel (k + 1))} (hF : DifferentiableOn ℂ F Ω) :
    DifferentiableOn ℂ (fun z => sliceMap k (F z) (initCoords z)) Ω := by
  have h1 : (fun z => sliceMap k (F z) (initCoords z)) =
      fun z => (splitCLE k).symm (initCoords z, F z) := by
    funext z; rfl
  rw [h1]
  have hi : Differentiable ℂ (fun z : ComplexModel (k + 1) => initCoords z) := by
    have : (fun z : ComplexModel (k + 1) => initCoords z) =
        fun z => ((ContinuousLinearMap.fst ℂ (ComplexModel k) ℂ).comp
          (splitCLE k : ComplexModel (k + 1) →L[ℂ] ComplexModel k × ℂ)) z := by
      funext z; rfl
    rw [this]; exact ContinuousLinearMap.differentiable _
  exact (splitCLE k).symm.differentiable.comp_differentiableOn
    (hi.differentiableOn.prodMk hF)

theorem differentiable_last : Differentiable ℂ (fun z : ComplexModel (k + 1) => z (Fin.last k)) :=
  (EuclideanSpace.proj (Fin.last k) : ComplexModel (k + 1) →L[ℂ] ℂ).differentiable

theorem continuous_last : Continuous (fun z : ComplexModel (k + 1) => z (Fin.last k)) :=
  differentiable_last.continuous

/-- Multiplication of the last coordinate by `u`. -/
def rotLast (u : ℂ) (z : ComplexModel (k + 1)) : ComplexModel (k + 1) :=
  sliceMap k (u * z (Fin.last k)) (initCoords z)

/-- The ramified cover `(w, v) ↦ (w, v^N)`. -/
def ramify (N : ℕ) (z : ComplexModel (k + 1)) : ComplexModel (k + 1) :=
  sliceMap k (z (Fin.last k) ^ N) (initCoords z)

theorem rotLast_sliceMap (u v : ℂ) (w : ComplexModel k) :
    rotLast u (sliceMap k v w) = sliceMap k (u * v) w := by
  simp [rotLast, initCoords_sliceMap]

theorem ramify_sliceMap (N : ℕ) (v : ℂ) (w : ComplexModel k) :
    ramify N (sliceMap k v w) = sliceMap k (v ^ N) w := by
  simp [ramify, initCoords_sliceMap]

theorem rotLast_rotLast (u u' : ℂ) (z : ComplexModel (k + 1)) :
    rotLast u (rotLast u' z) = rotLast (u * u') z := by
  rw [← sliceMap_initCoords z, rotLast_sliceMap, rotLast_sliceMap, rotLast_sliceMap, mul_assoc]

theorem ramify_rotLast {N : ℕ} {u : ℂ} (hu : u ^ N = 1) (z : ComplexModel (k + 1)) :
    ramify N (rotLast u z) = ramify N z := by
  rw [← sliceMap_initCoords z, rotLast_sliceMap, ramify_sliceMap, ramify_sliceMap, mul_pow, hu,
    one_mul]

theorem differentiable_rotLast (u : ℂ) : Differentiable ℂ (rotLast (k := k) u) := by
  intro z
  exact (differentiable_sliceMap_comp (Ω := univ)
    ((differentiable_last.const_mul u).differentiableOn)).differentiableAt univ_mem

theorem differentiable_ramify (N : ℕ) : Differentiable ℂ (ramify (k := k) N) := by
  intro z
  exact (differentiable_sliceMap_comp (Ω := univ)
    ((differentiable_last.pow N).differentiableOn)).differentiableAt univ_mem

theorem rotLast_mem_slab {Ω₀ : Set (ComplexModel k)} {ρ : ℝ} {u : ℂ} (hu : ‖u‖ = 1)
    {z : ComplexModel (k + 1)} : rotLast u z ∈ slab Ω₀ ρ ↔ z ∈ slab Ω₀ ρ := by
  rw [rotLast, sliceMap_mem_slab, norm_mul, hu, one_mul]; rfl

theorem ramify_mem_slab {Ω₀ : Set (ComplexModel k)} {ρ : ℝ} (hρ0 : 0 ≤ ρ) {N : ℕ} (hN : N ≠ 0)
    {z : ComplexModel (k + 1)} (hz : z ∈ slab Ω₀ (ρ ^ ((1 : ℝ) / N))) : ramify N z ∈ slab Ω₀ ρ := by
  rw [ramify, sliceMap_mem_slab]
  refine ⟨hz.1, ?_⟩
  rw [norm_pow]
  calc ‖z (Fin.last k)‖ ^ N < (ρ ^ ((1 : ℝ) / N)) ^ N :=
        pow_lt_pow_left₀ hz.2 (norm_nonneg _) hN
    _ = ρ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0, one_div, inv_mul_cancel₀ (by exact_mod_cast hN),
          Real.rpow_one]

end Slab

/-! ### Rotations of the last coordinate preserve Lebesgue measure -/

section Rotation

open Pending Pending.OTChen

variable {k : ℕ}

theorem norm_sq_rotLast {u : ℂ} (hu : ‖u‖ = 1) (z : ComplexModel (k + 1)) :
    ‖rotLast u z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_sq_eq_initCoords, norm_sq_eq_initCoords z, rotLast, initCoords_sliceMap,
    sliceMap_last, norm_mul, hu, one_mul]

theorem rotLast_add (u : ℂ) (z z' : ComplexModel (k + 1)) :
    rotLast u (z + z') = rotLast u z + rotLast u z' := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [rotLast, mul_add]
  · simp [rotLast]

theorem rotLast_smul (u c : ℂ) (z : ComplexModel (k + 1)) :
    rotLast u (c • z) = c • rotLast u z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [rotLast]; ring
  · simp [rotLast]

theorem rotLast_one (z : ComplexModel (k + 1)) : rotLast 1 z = z := by
  rw [rotLast, one_mul, sliceMap_initCoords]

/-- The rotation of the last coordinate by a unit complex number, as a real linear isometry. -/
def rotLastLIE (u : ℂ) (hu : ‖u‖ = 1) : ComplexModel (k + 1) ≃ₗᵢ[ℝ] ComplexModel (k + 1) where
  toFun := rotLast u
  invFun := rotLast u⁻¹
  map_add' := rotLast_add u
  map_smul' c z := by
    rw [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ) c z,
      RCLike.real_smul_eq_coe_smul (K := ℂ) c (rotLast u z), rotLast_smul]
  left_inv z := by
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
    rw [rotLast_rotLast, inv_mul_cancel₀ hu0, rotLast_one]
  right_inv z := by
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
    rw [rotLast_rotLast, mul_inv_cancel₀ hu0, rotLast_one]
  norm_map' z := by
    have h := norm_sq_rotLast hu z
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem measurePreserving_rotLast {u : ℂ} (hu : ‖u‖ = 1) :
    MeasurePreserving (rotLast (k := k) u) volume volume :=
  (rotLastLIE u hu).measurePreserving

theorem measurableEmbedding_rotLast {u : ℂ} (hu : ‖u‖ = 1) :
    MeasurableEmbedding (rotLast (k := k) u) :=
  (rotLastLIE u hu).toHomeomorph.measurableEmbedding

/-- Rotation invariance of a set integral over a rotation-invariant set. -/
theorem setLIntegral_comp_rotLast {u : ℂ} (hu : ‖u‖ = 1) {S : Set (ComplexModel (k + 1))}
    (hS : rotLast u ⁻¹' S = S) (f : ComplexModel (k + 1) → ℝ≥0∞) :
    ∫⁻ z in S, f (rotLast u z) = ∫⁻ z in S, f z := by
  conv_lhs => rw [← hS]
  exact (measurePreserving_rotLast hu).setLIntegral_comp_preimage_emb
    (measurableEmbedding_rotLast hu) f S

end Rotation

/-! ### Averaging over the `N`-th roots of unity -/

section Average

open Pending Pending.OTChen

variable {k : ℕ}

/-- The primitive `N`-th root of unity `e^{2πi/N}`. -/
def rootOfUnity (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

theorem isPrimitiveRoot_rootOfUnity {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (rootOfUnity N) N :=
  Complex.isPrimitiveRoot_exp N hN

theorem norm_eq_one_of_pow_eq_one {N : ℕ} (hN : N ≠ 0) {u : ℂ} (hu : u ^ N = 1) : ‖u‖ = 1 := by
  have h : ‖u‖ ^ N = 1 := by rw [← norm_pow, hu, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) hN).mp h

/-- The average `Ĝ(z) = N⁻¹ ∑_{j < N} G(ζ^j · z)` over the rotations of the last coordinate. -/
def rootAverage (N : ℕ) (G : ComplexModel (k + 1) → ℂ) (z : ComplexModel (k + 1)) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, G (rotLast (rootOfUnity N ^ j) z)

theorem rootAverage_rotLast_root {N : ℕ} (hN : N ≠ 0) (G : ComplexModel (k + 1) → ℂ)
    (z : ComplexModel (k + 1)) :
    rootAverage N G (rotLast (rootOfUnity N) z) = rootAverage N G z := by
  unfold rootAverage
  congr 1
  set f : ℕ → ℂ := fun j => G (rotLast (rootOfUnity N ^ j) z) with hf
  have hrot : ∀ j, G (rotLast (rootOfUnity N ^ j) (rotLast (rootOfUnity N) z)) = f (j + 1) := by
    intro j; rw [hf, rotLast_rotLast, ← pow_succ]
  simp_rw [hrot]
  have hN' : f N = f 0 := by
    rw [hf]; simp only [(isPrimitiveRoot_rootOfUnity hN).pow_eq_one, pow_zero]
  have h1 := Finset.sum_range_succ' f N
  have h2 := Finset.sum_range_succ f N
  rw [hN'] at h2
  have : ∑ j ∈ Finset.range N, f (j + 1) + f 0 = ∑ j ∈ Finset.range N, f j + f 0 := by
    rw [← h1, h2]
  exact add_right_cancel this

theorem rootAverage_rotLast {N : ℕ} (hN : N ≠ 0) (G : ComplexModel (k + 1) → ℂ) {u : ℂ}
    (hu : u ^ N = 1) (z : ComplexModel (k + 1)) :
    rootAverage N G (rotLast u z) = rootAverage N G z := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨i, -, rfl⟩ := (isPrimitiveRoot_rootOfUnity hN).eq_pow_of_pow_eq_one hu
  clear hu
  induction i generalizing z with
  | zero => rw [pow_zero, rotLast_one]
  | succ i ih =>
    rw [pow_succ, ← rotLast_rotLast, ih, rootAverage_rotLast_root hN]

theorem rotLast_of_last_eq_zero (u : ℂ) {z : ComplexModel (k + 1)} (hz : z (Fin.last k) = 0) :
    rotLast u z = z := by
  rw [rotLast, hz, mul_zero, ← hz, sliceMap_initCoords]

theorem rootAverage_of_last_eq_zero {N : ℕ} (hN : N ≠ 0) (G : ComplexModel (k + 1) → ℂ)
    {z : ComplexModel (k + 1)} (hz : z (Fin.last k) = 0) : rootAverage N G z = G z := by
  unfold rootAverage
  simp only [rotLast_of_last_eq_zero _ hz, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem differentiableOn_rootAverage {N : ℕ} {G : ComplexModel (k + 1) → ℂ}
    {S : Set (ComplexModel (k + 1))} (hG : DifferentiableOn ℂ G S)
    (hS : ∀ j, ∀ z ∈ S, rotLast (rootOfUnity N ^ j) z ∈ S) :
    DifferentiableOn ℂ (rootAverage N G) S := by
  intro z hz
  refine (DifferentiableWithinAt.const_mul ?_ _)
  refine DifferentiableWithinAt.fun_sum fun j _ => ?_
  exact (hG _ (hS j z hz)).comp z (differentiable_rotLast _).differentiableAt.differentiableWithinAt
    (fun y hy => hS j y hy)

theorem norm_rootAverage_sq_le (N : ℕ) (G : ComplexModel (k + 1) → ℂ) (z : ComplexModel (k + 1)) :
    ‖rootAverage N G z‖ ^ 2 ≤
      ∑ j ∈ Finset.range N, ‖G (rotLast (rootOfUnity N ^ j) z)‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [rootAverage]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℕ → ℝ := fun j => ‖G (rotLast (rootOfUnity N ^ j) z)‖
  have h1 : ‖rootAverage N G z‖ ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a j := by
    unfold rootAverage
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := a)
  rw [Finset.card_range] at h2
  have hS : 0 ≤ ∑ j ∈ Finset.range N, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc ‖rootAverage N G z‖ ^ 2 ≤ ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a j) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (N : ℝ)⁻¹ ^ 2 * (∑ j ∈ Finset.range N, a j) ^ 2 := by ring
    _ ≤ (N : ℝ)⁻¹ ^ 2 * (N * ∑ j ∈ Finset.range N, a j ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, a j ^ 2 := by field_simp
    _ ≤ ∑ j ∈ Finset.range N, a j ^ 2 := by
        have : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
        nlinarith

end Average

/-! ### Descent along `v ↦ v^N` -/

section Descent

open Pending Pending.OTChen

variable {k : ℕ}

/-- The principal `N`-th root. -/
def nthRoot (N : ℕ) (w : ℂ) : ℂ := w ^ ((N : ℂ)⁻¹)

theorem nthRoot_pow {N : ℕ} (hN : N ≠ 0) (w : ℂ) : nthRoot N w ^ N = w :=
  Complex.cpow_nat_inv_pow w hN

theorem norm_cpow_inv_natCast (N : ℕ) (w : ℂ) : ‖w ^ ((N : ℂ)⁻¹)‖ = ‖w‖ ^ ((1 : ℝ) / N) := by
  have : ((N : ℂ))⁻¹ = (((1 : ℝ) / N : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_cpow_real]

theorem norm_nthRoot (N : ℕ) (w : ℂ) : ‖nthRoot N w‖ = ‖w‖ ^ ((1 : ℝ) / N) :=
  norm_cpow_inv_natCast N w

theorem nthRoot_zero {N : ℕ} (hN : N ≠ 0) : nthRoot N 0 = 0 :=
  Complex.zero_cpow (inv_ne_zero (by exact_mod_cast hN))

/-- Two `N`-th roots of the same nonzero number differ by an `N`-th root of unity. -/
theorem exists_root_of_pow_eq {N : ℕ} {u v : ℂ} (hv : v ≠ 0) (h : u ^ N = v ^ N) :
    ∃ ξ : ℂ, ξ ^ N = 1 ∧ u = ξ * v :=
  ⟨u / v, by rw [div_pow, h, div_self (pow_ne_zero _ hv)], by field_simp⟩

/-- The descended function `H(w, v) = Ĝ(w, v^{1/N})`. -/
def descend (N : ℕ) (Ĝ : ComplexModel (k + 1) → ℂ) (z : ComplexModel (k + 1)) : ℂ :=
  Ĝ (sliceMap k (nthRoot N (z (Fin.last k))) (initCoords z))

/-- An invariant function takes the same value at all `N`-th roots. -/
theorem eq_of_pow_eq_of_invariant {N : ℕ} {Ĝ : ComplexModel (k + 1) → ℂ}
    (hinv : ∀ u : ℂ, u ^ N = 1 → ∀ z, Ĝ (rotLast u z) = Ĝ z) {u v : ℂ} (h : u ^ N = v ^ N)
    (w : ComplexModel k) : Ĝ (sliceMap k u w) = Ĝ (sliceMap k v w) := by
  by_cases hv : v = 0
  · have hN : N ≠ 0 ∨ True := Or.inr trivial
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · -- `N = 0`: every `u` is a "root"; use the invariance under `u / v` only when possible
      have := hinv (u) (by simp) (sliceMap k 1 w)
      have h2 := hinv (v) (by simp) (sliceMap k 1 w)
      rw [rotLast_sliceMap, mul_one] at this h2
      rw [this, h2]
    · subst hv
      rw [zero_pow hNpos.ne'] at h
      rw [pow_eq_zero_iff hNpos.ne'] at h
      rw [h]
  · obtain ⟨ξ, hξ, rfl⟩ := exists_root_of_pow_eq hv h
    rw [← rotLast_sliceMap, hinv ξ hξ]

theorem descend_ramify {N : ℕ} (hN : N ≠ 0) {Ĝ : ComplexModel (k + 1) → ℂ}
    (hinv : ∀ u : ℂ, u ^ N = 1 → ∀ z, Ĝ (rotLast u z) = Ĝ z) (z : ComplexModel (k + 1)) :
    descend N Ĝ (ramify N z) = Ĝ z := by
  rw [descend, ramify, sliceMap_last, initCoords_sliceMap]
  conv_rhs => rw [← sliceMap_initCoords z]
  exact eq_of_pow_eq_of_invariant hinv (by rw [nthRoot_pow hN]) _

theorem descend_hyperplane {N : ℕ} (hN : N ≠ 0) (Ĝ : ComplexModel (k + 1) → ℂ)
    (w : ComplexModel k) : descend N Ĝ (hyperplaneEmbedding k w) = Ĝ (hyperplaneEmbedding k w) := by
  rw [descend, hyperplaneEmbedding_eq_sliceMap, sliceMap_last, nthRoot_zero hN,
    initCoords_sliceMap]

variable {Ω₀ : Set (ComplexModel k)} {ρ : ℝ} {N : ℕ} {Ĝ : ComplexModel (k + 1) → ℂ}

theorem descend_mem (hN : N ≠ 0) {z : ComplexModel (k + 1)} (hz : z ∈ slab Ω₀ ρ) :
    sliceMap k (nthRoot N (z (Fin.last k))) (initCoords z) ∈ slab Ω₀ (ρ ^ ((1 : ℝ) / N)) := by
  rw [sliceMap_mem_slab, norm_nthRoot]
  refine ⟨hz.1, ?_⟩
  have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  exact Real.rpow_lt_rpow (norm_nonneg _) hz.2 (by positivity)

/-- Off the hyperplane, the descended function is holomorphic: near `w₀ ≠ 0`, it is
`Ĝ(w, ℓ(v))` for a holomorphic branch `ℓ` of the `N`-th root. -/
theorem differentiableAt_descend_of_ne (hN : N ≠ 0) (_hρ : 0 ≤ ρ) (hΩ₀ : IsOpen Ω₀)
    (hĜ : DifferentiableOn ℂ Ĝ (slab Ω₀ (ρ ^ ((1 : ℝ) / N))))
    (hinv : ∀ u : ℂ, u ^ N = 1 → ∀ z, Ĝ (rotLast u z) = Ĝ z) {z : ComplexModel (k + 1)}
    (hz : z ∈ slab Ω₀ ρ) (hz0 : z (Fin.last k) ≠ 0) : DifferentiableAt ℂ (descend N Ĝ) z := by
  set w₀ := z (Fin.last k) with hw₀
  set u₀ := nthRoot N w₀ with hu₀
  set ℓ : ℂ → ℂ := fun w => u₀ * (w / w₀) ^ ((N : ℂ)⁻¹) with hℓ
  have hℓpow : ∀ w, ℓ w ^ N = w := by
    intro w
    rw [hℓ, mul_pow, Complex.cpow_nat_inv_pow _ hN, hu₀, nthRoot_pow hN]
    field_simp
  have hℓnorm : ∀ w, ‖ℓ w‖ = ‖w‖ ^ ((1 : ℝ) / N) := by
    intro w
    rw [hℓ, norm_mul, hu₀, norm_nthRoot, norm_cpow_inv_natCast, norm_div,
      Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
    field_simp
  set O : Set (ComplexModel (k + 1)) :=
    {y | y (Fin.last k) / w₀ ∈ Complex.slitPlane} ∩ slab Ω₀ ρ with hO
  have hOopen : IsOpen O := by
    refine IsOpen.inter ?_ (isOpen_slab hΩ₀ ρ)
    exact Complex.isOpen_slitPlane.preimage (continuous_last.div_const w₀)
  have hzO : z ∈ O := ⟨by simp [← hw₀, div_self hz0], hz⟩
  have hℓd : DifferentiableOn ℂ (fun y : ComplexModel (k + 1) => ℓ (y (Fin.last k))) O := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.const_mul ?_ u₀
    have h1 : DifferentiableAt ℂ (fun y : ComplexModel (k + 1) => y (Fin.last k) / w₀) y := by
      simp only [div_eq_mul_inv]
      exact ((differentiable_last (k := k)) y).mul_const _
    exact ((Complex.hasStrictDerivAt_cpow_const (c := (N : ℂ)⁻¹) hy.1).hasDerivAt.differentiableAt).comp
      y h1
  have hmap : DifferentiableOn ℂ
      (fun y => sliceMap k (ℓ (y (Fin.last k))) (initCoords y)) O :=
    differentiable_sliceMap_comp hℓd
  have hmem : sliceMap k (ℓ w₀) (initCoords z) ∈ slab Ω₀ (ρ ^ ((1 : ℝ) / N)) := by
    rw [sliceMap_mem_slab, hℓnorm]
    exact ⟨hz.1, Real.rpow_lt_rpow (norm_nonneg _) hz.2 (by positivity)⟩
  have hcomp : DifferentiableAt ℂ (fun y => Ĝ (sliceMap k (ℓ (y (Fin.last k))) (initCoords y))) z :=
    (hĜ.differentiableAt ((isOpen_slab hΩ₀ _).mem_nhds hmem)).comp z
      (hmap.differentiableAt (hOopen.mem_nhds hzO))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hOopen.mem_nhds hzO] with y hy
  rw [descend]
  exact eq_of_pow_eq_of_invariant hinv (by rw [nthRoot_pow hN, hℓpow]) _

/-- On the hyperplane, the descended function is continuous. -/
theorem continuousAt_descend_of_eq_zero (hN : N ≠ 0) (hΩ₀ : IsOpen Ω₀)
    (hĜ : DifferentiableOn ℂ Ĝ (slab Ω₀ (ρ ^ ((1 : ℝ) / N)))) {z : ComplexModel (k + 1)}
    (hz : z ∈ slab Ω₀ ρ) (hz0 : z (Fin.last k) = 0) : ContinuousAt (descend N Ĝ) z := by
  have hmem := descend_mem (Ω₀ := Ω₀) (ρ := ρ) hN hz
  have hĜc : ContinuousAt Ĝ (sliceMap k (nthRoot N (z (Fin.last k))) (initCoords z)) :=
    (hĜ.differentiableAt ((isOpen_slab hΩ₀ _).mem_nhds hmem)).continuousAt
  suffices hmapc : ContinuousAt
      (fun y : ComplexModel (k + 1) => sliceMap k (nthRoot N (y (Fin.last k))) (initCoords y)) z from
    ContinuousAt.comp (g := Ĝ) hĜc hmapc
  have hroot : ContinuousAt (fun y : ComplexModel (k + 1) => nthRoot N (y (Fin.last k))) z := by
    have h1 : ContinuousAt (fun w : ℂ => w ^ ((N : ℂ)⁻¹)) 0 := by
      have := Complex.continuousAt_cpow_zero_of_re_pos (z := (N : ℂ)⁻¹) (by
        simp only [Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
        have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
        positivity)
      exact ContinuousAt.comp (f := fun w : ℂ => (w, (N : ℂ)⁻¹)) this
        (continuous_id.prodMk continuous_const).continuousAt
    rw [← hz0] at h1
    exact ContinuousAt.comp (f := fun y : ComplexModel (k + 1) => y (Fin.last k)) (x := z) h1
      continuous_last.continuousAt
  have hinit : Continuous (fun y : ComplexModel (k + 1) => initCoords y) := by
    have : (fun y : ComplexModel (k + 1) => initCoords y) =
        fun y => ((ContinuousLinearMap.fst ℂ (ComplexModel k) ℂ).comp
          (splitCLE k : ComplexModel (k + 1) →L[ℂ] ComplexModel k × ℂ)) y := by
      funext y; rfl
    rw [this]; exact ContinuousLinearMap.continuous _
  have hs : Continuous (fun q : ℂ × ComplexModel k => sliceMap k q.1 q.2) := by
    have : (fun q : ℂ × ComplexModel k => sliceMap k q.1 q.2) =
        fun q => (splitCLE k).symm (q.2, q.1) := by funext q; rfl
    rw [this]; exact (splitCLE k).symm.continuous.comp (continuous_snd.prodMk continuous_fst)
  exact hs.continuousAt.comp (hroot.prodMk hinit.continuousAt)

/-- **The descended function is holomorphic** (Riemann extension across the hyperplane). -/
theorem differentiableOn_descend (hN : N ≠ 0) (hρ : 0 ≤ ρ) (hΩ₀ : IsOpen Ω₀)
    (hĜ : DifferentiableOn ℂ Ĝ (slab Ω₀ (ρ ^ ((1 : ℝ) / N))))
    (hinv : ∀ u : ℂ, u ^ N = 1 → ∀ z, Ĝ (rotLast u z) = Ĝ z) :
    DifferentiableOn ℂ (descend N Ĝ) (slab Ω₀ ρ) := by
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hz0 : z₀ (Fin.last k) ≠ 0
  · exact differentiableAt_descend_of_ne hN hρ hΩ₀ hĜ hinv hz₀ hz0
  push Not at hz0
  have hΩo := isOpen_slab hΩ₀ ρ
  set f : ComplexModel (k + 1) → ℂ := fun y => descend N Ĝ (y + z₀) with hf
  set h : ComplexModel (k + 1) → ℂ := fun y => y (Fin.last k) with hh
  have hnear : ∀ᶠ y in 𝓝 (0 : ComplexModel (k + 1)), y + z₀ ∈ slab Ω₀ ρ := by
    have : Tendsto (fun y : ComplexModel (k + 1) => y + z₀) (𝓝 0) (𝓝 z₀) :=
      (continuous_add_const z₀).tendsto' 0 z₀ (by simp)
    exact this.eventually (hΩo.mem_nhds hz₀)
  have hlast : ∀ y : ComplexModel (k + 1), (y + z₀) (Fin.last k) = y (Fin.last k) := by
    intro y; simp [hz0]
  have hfc : ∀ y, y + z₀ ∈ slab Ω₀ ρ → y (Fin.last k) = 0 → ContinuousAt f y := by
    intro y hy hy0
    have := continuousAt_descend_of_eq_zero hN hΩ₀ hĜ hy (by rw [hlast, hy0])
    exact ContinuousAt.comp (g := descend N Ĝ) (f := fun y => y + z₀) this
      (continuous_add_const z₀).continuousAt
  have hfd : ∀ y, y + z₀ ∈ slab Ω₀ ρ → y (Fin.last k) ≠ 0 → DifferentiableAt ℂ f y := by
    intro y hy hy0
    have := differentiableAt_descend_of_ne hN hρ hΩ₀ hĜ hinv hy (by rw [hlast]; exact hy0)
    have hT : DifferentiableAt ℂ (fun y : ComplexModel (k + 1) => y + z₀) y := by fun_prop
    exact DifferentiableAt.comp (g := descend N Ĝ) (f := fun y => y + z₀) y this hT
  have hcont0 : ContinuousAt f 0 := hfc 0 (by simpa using hz₀) (by simp)
  obtain ⟨F, hFd, hFeq⟩ := RiemannExtension.exists_extension_euclidean (d := k + 1) (h := h)
    (f := f) (Eventually.of_forall fun y => (differentiable_last y))
    (by
      intro hev
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
      have hy : (EuclideanSpace.single (Fin.last k) ((ε / 2 : ℝ) : ℂ) : ComplexModel (k + 1)) ∈
          ball (0 : ComplexModel (k + 1)) ε := by
        rw [mem_ball_zero_iff, PiLp.norm_single, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      have := hball _ hy
      simp only [hh, PiLp.single_apply, if_true] at this
      exact (by positivity : (0 : ℝ) < ε / 2).ne' (by exact_mod_cast this))
    (by
      filter_upwards [hnear] with y hy hy0
      exact hfd y hy hy0)
    (by
      refine ⟨‖f 0‖ + 1, ?_⟩
      have := hcont0.norm.eventually (gt_mem_nhds (lt_add_one ‖f 0‖))
      filter_upwards [this] with y hy _
      exact hy.le)
  -- `F = f` near `0`, including on the hyperplane
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((hFd.and hFeq).and hnear)
  have heq : ∀ y ∈ ball (0 : ComplexModel (k + 1)) ε, F y = f y := by
    intro y hy
    by_cases hy0 : y (Fin.last k) ≠ 0
    · exact (hball y hy).1.2 hy0
    push Not at hy0
    set e : ComplexModel (k + 1) := EuclideanSpace.single (Fin.last k) 1 with he
    set g : ℂ → ComplexModel (k + 1) := fun t => y + t • e with hg
    have hgt : Tendsto g (𝓝[≠] 0) (𝓝 y) := by
      have : Tendsto g (𝓝 0) (𝓝 y) := by
        simpa [hg] using (continuous_const.add (continuous_id.smul continuous_const)).tendsto
          (0 : ℂ) (f := fun t : ℂ => y + t • e)
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), F (g t) = f (g t) := by
      have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g t ∈ ball (0 : ComplexModel (k + 1)) ε :=
        hgt.eventually (isOpen_ball.mem_nhds hy)
      filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
      refine (hball _ ht).1.2 ?_
      simpa [hh, hg, he, hy0] using ht0
    have hF' : Tendsto (fun t => F (g t)) (𝓝[≠] 0) (𝓝 (F y)) :=
      ((hball y hy).1.1.continuousAt).tendsto.comp hgt
    have hf' : Tendsto (fun t => f (g t)) (𝓝[≠] 0) (𝓝 (f y)) :=
      (hfc y (hball y hy).2 hy0).tendsto.comp hgt
    exact tendsto_nhds_unique hF' (hf'.congr' (hev.mono fun t ht => ht.symm))
  have hfd0 : DifferentiableAt ℂ f 0 :=
    (hball 0 (mem_ball_self hε)).1.1.congr_of_eventuallyEq
      (eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) fun y hy => (heq y hy).symm)
  have : descend N Ĝ = fun y => f (y - z₀) := by
    funext y; simp [hf]
  rw [this]
  have hfd0' : DifferentiableAt ℂ f (z₀ - z₀) := by rw [sub_self]; exact hfd0
  have hT : DifferentiableAt ℂ (fun y : ComplexModel (k + 1) => y - z₀) z₀ := by fun_prop
  exact DifferentiableAt.comp (g := f) (f := fun y => y - z₀) z₀ hfd0' hT

end Descent

/-! ### The ramified extension step -/

section Ramified

open Pending Pending.OTChen

variable {k : ℕ}

/-- TN's hyperplane Ohsawa--Takegoshi theorem, for any Borel structures. -/
theorem hyperplaneOT [ik : MeasurableSpace (ComplexModel k)] [hik : BorelSpace (ComplexModel k)]
    [i : MeasurableSpace (ComplexModel (k + 1))] [hi : BorelSpace (ComplexModel (k + 1))]
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel (k + 1)), IsOpen Ω → Convex ℝ Ω →
        (∀ z ∈ Ω, ‖z (Fin.last k)‖ < R) →
        ∀ φ : ComplexModel (k + 1) → EReal, PlurisubharmonicOn φ Ω →
          ∀ c : ℝ, 0 < c →
          ∀ f : ComplexModel k → ℂ,
            DifferentiableOn ℂ f (hyperplaneEmbedding k ⁻¹' Ω) →
            ∃ F : ComplexModel (k + 1) → ℂ, DifferentiableOn ℂ F Ω ∧
              (∀ w ∈ hyperplaneEmbedding k ⁻¹' Ω,
                F (hyperplaneEmbedding k w) = f w) ∧
              (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
                ENNReal.ofReal C *
                  ∫⁻ w in hyperplaneEmbedding k ⁻¹' Ω,
                    multiplierDensity (fun w => φ (hyperplaneEmbedding k w)) c f w := by
  obtain rfl : i = borel _ := hi.measurable_eq
  obtain rfl : ik = borel _ := hik.measurable_eq
  exact ohsawaTakegoshiHyperplane_of_regular ohsawaTakegoshiHyperplaneRegular k R hR

/-- **The ramified extension step.**  Let `Ω₀ ⊆ ℂ^k` be open and convex, `ρ > 0`, `φ` psh on the
slab `Ω₀ × D(0, ρ)` and `g` holomorphic on `Ω₀` with `∫_{Ω₀} |g|² e^{-φ(·, 0)} < ∞`.  For every
`N ≥ 1` there is a holomorphic `H` on the slab with `H(·, 0) = g` and
`∫ |H|² e^{-φ} |w|^{2/N - 2} < ∞` (`w` the last coordinate). -/
theorem exists_extension_ramified {Ω₀ : Set (ComplexModel k)} (hΩ₀ : IsOpen Ω₀)
    (hconv : Convex ℝ Ω₀) {ρ : ℝ} (hρ : 0 < ρ) {φ : ComplexModel (k + 1) → EReal}
    (hφ : PlurisubharmonicOn φ (slab Ω₀ ρ)) {N : ℕ} (hN : N ≠ 0) {g : ComplexModel k → ℂ}
    (hg : DifferentiableOn ℂ g Ω₀)
    (hgi : ∫⁻ w in Ω₀, multiplierDensity (fun w => φ (hyperplaneEmbedding k w)) 1 g w ≠ ⊤) :
    ∃ H : ComplexModel (k + 1) → ℂ, DifferentiableOn ℂ H (slab Ω₀ ρ) ∧
      (∀ w ∈ Ω₀, H (hyperplaneEmbedding k w) = g w) ∧
      ∫⁻ z in slab Ω₀ ρ, multiplierDensity φ 1 H z *
        ENNReal.ofReal (‖z (Fin.last k)‖ ^ ((2 : ℝ) / N - 2)) ≠ ⊤ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set ρ' : ℝ := ρ ^ ((1 : ℝ) / N) with hρ'
  have hρ'0 : 0 < ρ' := Real.rpow_pos_of_pos hρ _
  set Ω : Set (ComplexModel (k + 1)) := slab Ω₀ ρ with hΩ
  set Ω' : Set (ComplexModel (k + 1)) := slab Ω₀ ρ' with hΩ'
  have hΩo : IsOpen Ω := isOpen_slab hΩ₀ ρ
  have hΩ'o : IsOpen Ω' := isOpen_slab hΩ₀ ρ'
  set φ' : ComplexModel (k + 1) → EReal := fun z => φ (ramify N z) with hφ'
  have hφ'psh : PlurisubharmonicOn φ' Ω' :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hΩ'o
      (differentiable_ramify N).differentiableOn (fun z hz => ramify_mem_slab hρ.le hN hz) hφ
  have hslice' : hyperplaneEmbedding k ⁻¹' Ω' = Ω₀ := by
    ext w; exact hyperplaneEmbedding_mem_slab hρ'0
  have hramhyp : ∀ w, ramify N (hyperplaneEmbedding k w) = hyperplaneEmbedding k w := by
    intro w
    rw [hyperplaneEmbedding_eq_sliceMap, ramify_sliceMap, zero_pow hN]
  -- Step 1: Ohsawa--Takegoshi on the ramified slab
  obtain ⟨C, hC, hOT⟩ := hyperplaneOT (k := k) hρ'0
  obtain ⟨G, hGd, hGext, hGint⟩ := hOT Ω' hΩ'o (convex_slab hconv ρ')
    (fun z hz => hz.2) φ' hφ'psh 1 one_pos g (by rw [hslice']; exact hg)
  have hGfin : ∫⁻ z in Ω', multiplierDensity φ' 1 G z ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hGint
    rw [hslice']
    simpa [hφ', hramhyp] using hgi
  -- Step 2: average over the roots of unity
  set Ĝ := rootAverage N G with hĜ
  have hrootnorm : ∀ j, ‖rootOfUnity N ^ j‖ = 1 := fun j =>
    norm_eq_one_of_pow_eq_one hN (by
      rw [← pow_mul, mul_comm, pow_mul, (isPrimitiveRoot_rootOfUnity hN).pow_eq_one, one_pow])
  have hrotΩ' : ∀ j, ∀ z ∈ Ω', rotLast (rootOfUnity N ^ j) z ∈ Ω' := fun j z hz =>
    (rotLast_mem_slab (hrootnorm j)).mpr hz
  have hĜd : DifferentiableOn ℂ Ĝ Ω' := differentiableOn_rootAverage hGd hrotΩ'
  have hinv : ∀ u : ℂ, u ^ N = 1 → ∀ z, Ĝ (rotLast u z) = Ĝ z := fun u hu z =>
    rootAverage_rotLast hN G hu z
  have hφ'rot : ∀ j z, φ' (rotLast (rootOfUnity N ^ j) z) = φ' z := by
    intro j z
    simp only [hφ']
    rw [ramify_rotLast (by
      rw [← pow_mul, mul_comm, pow_mul, (isPrimitiveRoot_rootOfUnity hN).pow_eq_one, one_pow])]
  have hĜint : ∫⁻ z in Ω', multiplierDensity φ' 1 Ĝ z ≠ ⊤ := by
    have hle : ∀ z, multiplierDensity φ' 1 Ĝ z ≤
        ∑ j ∈ Finset.range N, multiplierDensity φ' 1 G (rotLast (rootOfUnity N ^ j) z) := by
      intro z
      simp only [multiplierDensity, hφ'rot, ← Finset.sum_mul]
      refine mul_le_mul' ?_ le_rfl
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_rootAverage_sq_le N G z)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_finsetSum']
    · refine ENNReal.sum_ne_top.mpr fun j _ => ?_
      rw [setLIntegral_comp_rotLast (hrootnorm j) (S := Ω') (by
        ext z; exact rotLast_mem_slab (hrootnorm j))]
      exact hGfin
    · intro j _
      have hc : ContinuousOn (fun z => G (rotLast (rootOfUnity N ^ j) z)) Ω' :=
        hGd.continuousOn.comp (differentiable_rotLast _).continuous.continuousOn (hrotΩ' j)
      have := RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
        (μ := volume) hΩ'o hφ'psh.upperSemicontinuousOn hc one_ne_zero
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [multiplierDensity, hφ'rot]
  -- Step 3: descend along `v ↦ v^N`
  set H := descend N Ĝ with hH
  have hHd : DifferentiableOn ℂ H Ω := differentiableOn_descend hN hρ.le hΩ₀ hĜd hinv
  have hHext : ∀ w ∈ Ω₀, H (hyperplaneEmbedding k w) = g w := by
    intro w hw
    rw [hH, descend_hyperplane hN, hĜ, rootAverage_of_last_eq_zero hN G
      (hyperplaneEmbedding_last k w), hGext w (by rw [hslice']; exact hw)]
  refine ⟨H, hHd, hHext, ?_⟩
  -- Step 4: the weighted integral, by the change of variables `w = v^N` in the last variable
  set D : ComplexModel (k + 1) → ℝ≥0∞ := fun z => multiplierDensity φ 1 H z *
    ENNReal.ofReal (‖z (Fin.last k)‖ ^ ((2 : ℝ) / N - 2)) with hD
  set E : ComplexModel (k + 1) → ℝ≥0∞ := Ω'.indicator (multiplierDensity φ' 1 Ĝ) with hE
  have hEm : AEMeasurable E volume :=
    (aemeasurable_indicator_iff hΩ'o.measurableSet).mpr
      (RestrictionOhsawaTakegoshi.aemeasurable_multiplierDensity_of_upperSemicontinuousOn
        hΩ'o hφ'psh.upperSemicontinuousOn hĜd.continuousOn one_ne_zero)
  have hEm' : AEMeasurable (fun q : ComplexModel k × ℂ => E (sliceMap k q.2 q.1))
      ((volume : Measure (ComplexModel k)).prod (volume : Measure ℂ)) := by
    have h1 : AEMeasurable (E ∘ (splitEquiv k).symm)
        ((volume : Measure (ComplexModel (k + 1))).map (splitEquiv k)) := by
      refine ((splitEquiv k).measurableEmbedding.aemeasurable_map_iff).mpr ?_
      have hfun : (E ∘ (splitEquiv k).symm) ∘ (splitEquiv k) = E := by
        funext z; simp [sliceMap_initCoords]
      rw [hfun]
      exact hEm
    rw [map_splitEquiv_volume] at h1
    exact (aemeasurable_smul_measure_iff (by exact_mod_cast (splitFactor_pos k).ne')).mp h1
  have hinner : ∀ w : ComplexModel k,
      ∫⁻ v, Ω.indicator D (sliceMap k v w) ≤
        ENNReal.ofReal ((N : ℝ) ^ 2) * ∫⁻ v, E (sliceMap k v w) := by
    intro w
    by_cases hw : w ∈ Ω₀
    · have h1 : (fun v => Ω.indicator D (sliceMap k v w)) =
          (ball (0 : ℂ) ρ).indicator (fun v => multiplierDensity φ 1 H (sliceMap k v w) *
            ENNReal.ofReal (‖v‖ ^ ((2 : ℝ) / N - 2))) := by
        funext v
        by_cases hv : v ∈ ball (0 : ℂ) ρ
        · rw [indicator_of_mem hv, indicator_of_mem (sliceMap_mem_slab.mpr
            ⟨hw, mem_ball_zero_iff.mp hv⟩), hD]
          simp only [sliceMap_last]
        · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv (mem_ball_zero_iff.mpr
            (sliceMap_mem_slab.mp h).2))]
      have h2 : (fun v => E (sliceMap k v w)) =
          (ball (0 : ℂ) ρ').indicator (fun v => multiplierDensity φ' 1 Ĝ (sliceMap k v w)) := by
        funext v
        by_cases hv : v ∈ ball (0 : ℂ) ρ'
        · rw [indicator_of_mem hv, hE, indicator_of_mem (sliceMap_mem_slab.mpr
            ⟨hw, mem_ball_zero_iff.mp hv⟩)]
        · rw [indicator_of_notMem hv, hE, indicator_of_notMem (fun h => hv (mem_ball_zero_iff.mpr
            (sliceMap_mem_slab.mp h).2))]
      rw [h1, h2, lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball]
      refine (lintegral_ball_mul_rpow_le hN ρ
        (fun v => multiplierDensity φ 1 H (sliceMap k v w))).trans (le_of_eq ?_)
      congr 1
      refine lintegral_congr fun v => ?_
      simp only [multiplierDensity]
      rw [← ramify_sliceMap, hH, descend_ramify hN hinv]
    · have h0 : (fun v => Ω.indicator D (sliceMap k v w)) = fun _ => 0 := by
        funext v
        exact indicator_of_notMem (fun h => hw (sliceMap_mem_slab.mp h).1) _
      rw [h0, lintegral_zero]
      exact zero_le
  have hmain : ∫⁻ z in Ω, D z ≤ ENNReal.ofReal ((N : ℝ) ^ 2) * ∫⁻ z in Ω', multiplierDensity φ' 1 Ĝ z := by
    rw [← lintegral_indicator hΩo.measurableSet, lintegral_eq_splitFactor_mul,
      ← lintegral_indicator hΩ'o.measurableSet]
    calc (splitFactor k : ℝ≥0∞) * ∫⁻ q, Ω.indicator D (sliceMap k q.2 q.1)
          ∂((volume : Measure (ComplexModel k)).prod volume)
        ≤ (splitFactor k : ℝ≥0∞) * ∫⁻ w, ∫⁻ v, Ω.indicator D (sliceMap k v w) :=
          mul_le_mul' le_rfl (lintegral_prod_le _)
      _ ≤ (splitFactor k : ℝ≥0∞) * ∫⁻ w, ENNReal.ofReal ((N : ℝ) ^ 2) *
            ∫⁻ v, E (sliceMap k v w) := mul_le_mul' le_rfl (lintegral_mono hinner)
      _ = ENNReal.ofReal ((N : ℝ) ^ 2) * ((splitFactor k : ℝ≥0∞) *
            ∫⁻ q, E (sliceMap k q.2 q.1) ∂((volume : Measure (ComplexModel k)).prod volume)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod _ hEm']
          ring
      _ = ENNReal.ofReal ((N : ℝ) ^ 2) * ∫⁻ z, E z := by rw [lintegral_eq_splitFactor_mul]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hĜint) hmain

end Ramified

/-! ### Iteration over the normal variables: the radial gain -/

section Gain

open Pending Pending.OTChen OhsawaTakegoshiSubspace

variable {k : ℕ}

/-- `e^{-(x + t)} = e^{-x} e^{-t}` for `x < ⊤` (exponent `1`). -/
theorem multiplierWeight_one_add_coe {x : EReal} (hx : x ≠ ⊤) (t : ℝ) :
    multiplierWeight 1 (x + (t : EReal)) =
      multiplierWeight 1 x * ENNReal.ofReal (Real.exp (-t)) := by
  induction x using EReal.rec with
  | bot =>
      rw [EReal.bot_add, multiplierWeight_bot one_pos, ENNReal.top_mul]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | coe s =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
  | top => exact absurd rfl hx

/-- The weight `e^{-(x + a log t)} = e^{-x} t^{-a}` for `t > 0`. -/
theorem multiplierWeight_add_log {x : EReal} (hx : x ≠ ⊤) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    multiplierWeight 1 (x + (a : EReal) * ENNReal.log (ENNReal.ofReal t)) =
      multiplierWeight 1 x * ENNReal.ofReal (t ^ (-a)) := by
  rw [ENNReal.log_ofReal_of_pos ht, ← EReal.coe_mul, multiplierWeight_one_add_coe hx,
    Real.rpow_def_of_pos ht]
  congr 3; ring

/-- The domains `Ω₀ × D(0, ρ)^d ⊆ ℂ^{k+d}`. -/
def gainDom (Ω₀ : Set (ComplexModel k)) (ρ : ℝ) : (d : ℕ) → Set (ComplexModel (k + d))
  | 0 => Ω₀
  | d + 1 => slab (gainDom Ω₀ ρ d) ρ

/-- The squared norm `∑_{i ≥ k} |z_i|²` of the normal coordinates of `z ∈ ℂ^{k+d}`. -/
def normalSq (k : ℕ) : (d : ℕ) → ComplexModel (k + d) → ℝ
  | 0 => fun _ => 0
  | d + 1 => fun z => normalSq k d (initCoords z) + ‖z (Fin.last (k + d))‖ ^ 2

/-- The projection onto the normal coordinates. -/
def normalCLM (k : ℕ) : (d : ℕ) → ComplexModel (k + d) →L[ℂ] ComplexModel (k + d)
  | 0 => 0
  | d + 1 => ((splitCLE (k + d)).symm : ComplexModel (k + d) × ℂ →L[ℂ] ComplexModel (k + d + 1)).comp
      (((normalCLM k d).prodMap (ContinuousLinearMap.id ℂ ℂ)).comp
        (splitCLE (k + d) : ComplexModel (k + d + 1) →L[ℂ] ComplexModel (k + d) × ℂ))

theorem norm_normalCLM_sq (k : ℕ) : ∀ (d : ℕ) (z : ComplexModel (k + d)),
    ‖normalCLM k d z‖ ^ 2 = normalSq k d z
  | 0, z => by simp [normalCLM, normalSq]
  | d + 1, z => by
    have h : normalCLM k (d + 1) z = sliceMap (k + d) (z (Fin.last (k + d)))
        (normalCLM k d (initCoords z)) := rfl
    rw [h, norm_sq_eq_initCoords, initCoords_sliceMap, sliceMap_last, norm_normalCLM_sq k d,
      normalSq]

theorem normalSq_nonneg (k : ℕ) (d : ℕ) (z : ComplexModel (k + d)) : 0 ≤ normalSq k d z := by
  rw [← norm_normalCLM_sq]; positivity

theorem normalSq_hyperplane (k d : ℕ) (y : ComplexModel (k + d)) :
    normalSq k (d + 1) (hyperplaneEmbedding (k + d) y) = normalSq k d y := by
  simp [normalSq, hyperplaneEmbedding_eq_sliceMap, initCoords_sliceMap]

theorem sq_last_le_normalSq (k d : ℕ) (z : ComplexModel (k + d + 1)) :
    ‖z (Fin.last (k + d))‖ ^ 2 ≤ normalSq k (d + 1) z := by
  rw [normalSq]; linarith [normalSq_nonneg k d (initCoords z)]

/-- The hyperplane `{z_last = 0}` is Lebesgue-null. -/
theorem volume_last_eq_zero (m : ℕ) :
    volume {z : ComplexModel (m + 1) | z (Fin.last m) = 0} = 0 := by
  set ℓ : ComplexModel (m + 1) →ₗ[ℝ] ℂ :=
    ((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ) :
      ComplexModel (m + 1) →ₗ[ℂ] ℂ).restrictScalars ℝ with hℓ
  have hsub : {z : ComplexModel (m + 1) | z (Fin.last m) = 0} = (LinearMap.ker ℓ : Set _) := by
    ext z; simp [hℓ]
  have hker : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single (Fin.last m) (1 : ℂ) : ComplexModel (m + 1)) ∈ LinearMap.ker ℓ := by
      rw [h]; trivial
    simp [hℓ] at this
  rw [hsub]
  exact Measure.addHaar_submodule volume _ hker

theorem ae_normalSq_pos (k d : ℕ) :
    ∀ᵐ z : ComplexModel (k + (d + 1)), 0 < normalSq k (d + 1) z := by
  have h0 := volume_last_eq_zero (k + d)
  rw [← compl_mem_ae_iff] at h0
  filter_upwards [h0] with z hz
  have hz' : z (Fin.last (k + d)) ≠ 0 := hz
  have h1 := sq_last_le_normalSq k d z
  have h2 : 0 < ‖z (Fin.last (k + d))‖ ^ 2 := by positivity
  linarith

theorem isOpen_gainDom {Ω₀ : Set (ComplexModel k)} (hΩ₀ : IsOpen Ω₀) (ρ : ℝ) :
    ∀ d, IsOpen (gainDom Ω₀ ρ d)
  | 0 => hΩ₀
  | d + 1 => isOpen_slab (isOpen_gainDom hΩ₀ ρ d) ρ

theorem convex_gainDom {Ω₀ : Set (ComplexModel k)} (hΩ₀ : Convex ℝ Ω₀) (ρ : ℝ) :
    ∀ d, Convex ℝ (gainDom Ω₀ ρ d)
  | 0 => hΩ₀
  | d + 1 => convex_slab (convex_gainDom hΩ₀ ρ d) ρ

theorem subspaceCLM_mem_gainDom {Ω₀ : Set (ComplexModel k)} {ρ : ℝ} (hρ : 0 < ρ)
    {w : ComplexModel k} (hw : w ∈ Ω₀) : ∀ d, OhsawaTakegoshiSubspace.subspaceCLM k d w ∈ gainDom Ω₀ ρ d
  | 0 => hw
  | d + 1 => by
    rw [OhsawaTakegoshiSubspace.subspaceCLM_succ]
    exact (hyperplaneEmbedding_mem_slab hρ).mpr (subspaceCLM_mem_gainDom hρ hw d)

/-- The gain exponent `d (1 - 1/N)`. -/
def gainExp (N d : ℕ) : ℝ := d * (1 - 1 / (N : ℝ))

/-- **Local extension with a radial subcritical gain.**  On `Ω₀ × D(0, ρ)^d ⊆ ℂ^{k+d}` with `Ω₀`
open convex, for `φ` psh and `f` holomorphic on `Ω₀` with `∫_{Ω₀} |f|² e^{-φ(·,0)} < ∞`, and every
`N ≥ 1`, there is a holomorphic extension `F` of `f` with
`∫ |F|² e^{-φ} |w|^{-2 d (1 - 1/N)} < ∞` (`|w|² = normalSq`). -/
theorem exists_extension_gain {Ω₀ : Set (ComplexModel k)} (hΩ₀ : IsOpen Ω₀)
    (hconv : Convex ℝ Ω₀) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : N ≠ 0) :
    ∀ (d : ℕ) (φ : ComplexModel (k + d) → EReal), PlurisubharmonicOn φ (gainDom Ω₀ ρ d) →
    ∀ f : ComplexModel k → ℂ, DifferentiableOn ℂ f Ω₀ →
      ∫⁻ w in Ω₀, multiplierDensity (fun w => φ (subspaceCLM k d w)) 1 f w ≠ ⊤ →
      ∃ F : ComplexModel (k + d) → ℂ, DifferentiableOn ℂ F (gainDom Ω₀ ρ d) ∧
        (∀ w ∈ Ω₀, F (subspaceCLM k d w) = f w) ∧
        ∫⁻ z in gainDom Ω₀ ρ d, multiplierDensity φ 1 F z *
          ENNReal.ofReal (normalSq k d z ^ (-gainExp N d)) ≠ ⊤
  | 0 => by
    intro φ _ f hf hfi
    refine ⟨f, hf, fun w _ => rfl, ?_⟩
    simpa [normalSq, gainExp, gainDom] using hfi
  | d + 1 => by
    intro φ hφ f hf hfi
    have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    set a : ℝ := gainExp N d with ha
    have ha0 : 0 ≤ a := by
      rw [ha, gainExp]
      have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNR]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    set Ωd := gainDom Ω₀ ρ d with hΩd
    have hΩdo : IsOpen Ωd := isOpen_gainDom hΩ₀ ρ d
    have hslice : hyperplaneEmbedding (k + d) ⁻¹' gainDom Ω₀ ρ (d + 1) = Ωd := by
      ext y; exact hyperplaneEmbedding_mem_slab hρ
    -- the induction hypothesis on the hyperplane
    have hφ' : PlurisubharmonicOn (fun y => φ (hyperplaneEmbedding (k + d) y)) Ωd := by
      have := hφ.comp_continuousLinearMap (hyperplaneCLM (k + d))
      rwa [show (hyperplaneCLM (k + d) : ComplexModel (k + d) → ComplexModel (k + d + 1)) ⁻¹'
        gainDom Ω₀ ρ (d + 1) = Ωd from hslice] at this
    obtain ⟨G, hGd, hGext, hGint⟩ := exists_extension_gain hΩ₀ hconv hρ hN d
      (fun y => φ (hyperplaneEmbedding (k + d) y)) hφ' f hf (by simpa [subspaceCLM_succ] using hfi)
    -- the weight `Q = φ + a log |w|²`
    set Q : ComplexModel (k + d + 1) → EReal := fun z =>
      φ z + (a : EReal) * logNormSq (normalCLM k (d + 1) z) with hQ
    have hQpsh : PlurisubharmonicOn Q (gainDom Ω₀ ρ (d + 1)) := by
      intro z hz
      rcases ha0.lt_or_eq with hapos | hazero
      · exact (hφ z hz).add (((plurisubharmonicAt_logNormSq _).comp_continuousLinearMap
          (normalCLM k (d + 1))).const_mul hapos)
      · have : Q = φ := by funext z; simp [hQ, ← hazero]
        rw [this]; exact hφ z hz
    have hlogQ : ∀ z, logNormSq (normalCLM k (d + 1) z) =
        ENNReal.log (ENNReal.ofReal (normalSq k (d + 1) z)) := by
      intro z; rw [logNormSq, norm_normalCLM_sq]
    -- the slice integral of `Q`
    have hslQ : ∫⁻ y in Ωd, multiplierDensity (fun y => Q (hyperplaneEmbedding (k + d) y)) 1 G y ≠ ⊤ := by
      refine ne_top_of_le_ne_top hGint (le_of_eq (setLIntegral_congr_fun_ae hΩdo.measurableSet ?_))
      have hae : ∀ᵐ y : ComplexModel (k + d), a = 0 ∨ 0 < normalSq k d y := by
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · exact Eventually.of_forall fun _ => Or.inl (by simp [ha, gainExp])
        · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
          exact (ae_normalSq_pos k d').mono fun y hy => Or.inr hy
      filter_upwards [hae] with y hy hyΩ
      have hne : φ (hyperplaneEmbedding (k + d) y) ≠ ⊤ :=
        (hφ _ ((hyperplaneEmbedding_mem_slab hρ).mpr hyΩ)).ne_top
      simp only [multiplierDensity, hQ, hlogQ, normalSq_hyperplane]
      rw [mul_assoc]
      congr 1
      rcases hy with hy0 | hypos
      · simp [hy0, ← ha]
      · rw [multiplierWeight_add_log hne a hypos]
    -- the ramified step
    obtain ⟨H, hHd, hHext, hHint⟩ := exists_extension_ramified (isOpen_gainDom hΩ₀ ρ d)
      (convex_gainDom hconv ρ d) hρ hQpsh hN hGd hslQ
    refine ⟨H, hHd, fun w hw => ?_, ?_⟩
    · rw [subspaceCLM_succ, hHext _ (subspaceCLM_mem_gainDom hρ hw d), hGext w hw]
    refine ne_top_of_le_ne_top hHint (setLIntegral_mono_ae'
      (isOpen_gainDom hΩ₀ ρ (d + 1)).measurableSet ?_)
    have h0 := volume_last_eq_zero (k + d)
    rw [← compl_mem_ae_iff] at h0
    filter_upwards [h0] with z hz hzΩ
    have hz' : z (Fin.last (k + d)) ≠ 0 := hz
    set t := normalSq k (d + 1) z with ht
    set ℓ := ‖z (Fin.last (k + d))‖ ^ 2 with hℓ
    have hℓpos : 0 < ℓ := by positivity
    have hℓt : ℓ ≤ t := sq_last_le_normalSq k d z
    have htpos : 0 < t := hℓpos.trans_le hℓt
    have hne : φ z ≠ ⊤ := (hφ z hzΩ).ne_top
    simp only [multiplierDensity, hQ, hlogQ]
    rw [← ht, multiplierWeight_add_log hne a htpos]
    have hb : 0 ≤ 1 - 1 / (N : ℝ) := by
      have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNR]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      linarith
    have hexp : gainExp N (d + 1) = a + (1 - 1 / (N : ℝ)) := by
      rw [ha, gainExp, gainExp]; push_cast; ring
    have key : ENNReal.ofReal (t ^ (-gainExp N (d + 1))) ≤ ENNReal.ofReal (t ^ (-a)) *
        ENNReal.ofReal (‖z (Fin.last (k + d))‖ ^ ((2 : ℝ) / N - 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hexp, neg_add, Real.rpow_add htpos]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc t ^ (-(1 - 1 / (N : ℝ))) ≤ ℓ ^ (-(1 - 1 / (N : ℝ))) :=
            Real.rpow_le_rpow_of_nonpos hℓpos hℓt (by linarith)
        _ = ‖z (Fin.last (k + d))‖ ^ ((2 : ℝ) / N - 2) := by
            rw [hℓ, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
            congr 1; push_cast; ring
    refine le_trans (mul_le_mul' le_rfl key) (le_of_eq ?_)
    ring

end Gain

/-! ### The gain extension in the flattening coordinates `ℂ^m × ℂ^{n-m}` -/

section Flat

open Pending Pending.OTChen OhsawaTakegoshiSubspace RegularLocusDense

/-- The domain `Ω₀ × D(0, ρ)^{n-m} ⊆ ℂ^n` (first `m` coordinates in `Ω₀`). -/
def flatDom (n m : ℕ) (Ω₀ : Set (ComplexModel m)) (ρ : ℝ) : Set (ComplexModel n) :=
  {z | coordinateProjection n m z ∈ Ω₀ ∧ ∀ i : Fin n, m ≤ i.1 → ‖z i‖ < ρ}

/-- The squared norm `∑_{i ≥ m} |z_i|²` of the normal coordinates. -/
def normalWeight (n m : ℕ) (z : ComplexModel n) : ℝ :=
  ∑ i : Fin n, if m ≤ i.1 then ‖z i‖ ^ 2 else 0

theorem normalWeight_nonneg (n m : ℕ) (z : ComplexModel n) : 0 ≤ normalWeight n m z :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

theorem coordinateProjection_initCoords {m d : ℕ} (z : ComplexModel (m + (d + 1))) :
    coordinateProjection (m + (d + 1)) m z = coordinateProjection (m + d) m (initCoords z) := by
  ext a
  simp only [coordinateProjection_apply, initCoords_apply]
  have h1 : a.1 < m + (d + 1) := by omega
  have h2 : a.1 < m + d := by omega
  rw [dif_pos h1, dif_pos h2]
  rfl

theorem gainDom_eq_flatDom (m : ℕ) (Ω₀ : Set (ComplexModel m)) (ρ : ℝ) :
    ∀ d, gainDom Ω₀ ρ d = flatDom (m + d) m Ω₀ ρ
  | 0 => by
    ext z
    simp only [gainDom, flatDom, mem_ofPred_eq]
    have : coordinateProjection (m + 0) m z = z := by
      ext a; simp [coordinateProjection_apply]
    rw [this]
    constructor
    · intro h; exact ⟨h, fun i hi => absurd i.2 (by omega)⟩
    · exact fun h => h.1
  | d + 1 => by
    ext z
    change z ∈ slab (gainDom Ω₀ ρ d) ρ ↔ z ∈ flatDom (m + (d + 1)) m Ω₀ ρ
    rw [gainDom_eq_flatDom m Ω₀ ρ d]
    simp only [slab, flatDom, mem_ofPred_eq]
    rw [coordinateProjection_initCoords]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun i hi => ?_⟩
      refine Fin.lastCases ?_ (fun j hj => ?_) i hi
      · exact fun _ => h3
      · exact h2 j hj
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun j hj => by simpa using h2 j.castSucc hj⟩, h2 (Fin.last _) (by simp)⟩

theorem normalSq_eq_normalWeight (m : ℕ) : ∀ d (z : ComplexModel (m + d)),
    normalSq m d z = normalWeight (m + d) m z
  | 0, z => by
    simp only [normalSq, normalWeight]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [if_neg (by omega)]
  | d + 1, z => by
    show normalSq m d (initCoords z) + ‖z (Fin.last (m + d))‖ ^ 2 = normalWeight (m + (d + 1)) m z
    rw [normalSq_eq_normalWeight m d, normalWeight, normalWeight]
    refine Eq.trans ?_ (Fin.sum_univ_castSucc (n := m + d)
      (fun i : Fin (m + d + 1) => if m ≤ i.1 then ‖z i‖ ^ 2 else 0)).symm
    simp only [initCoords_apply, Fin.val_castSucc, Fin.val_last]
    rw [if_pos (by omega)]

theorem coordinateInclusion_mem_flatDom {n m : ℕ} (hmn : m ≤ n) {Ω₀ : Set (ComplexModel m)}
    {ρ : ℝ} (hρ : 0 < ρ) {w : ComplexModel m} :
    coordinateInclusion n m w ∈ flatDom n m Ω₀ ρ ↔ w ∈ Ω₀ := by
  simp only [flatDom, mem_ofPred_eq, coordinateProjection_coordinateInclusion hmn]
  refine ⟨fun h => h.1, fun h => ⟨h, fun i hi => ?_⟩⟩
  rw [coordinateInclusion_apply, dif_neg (by omega), norm_zero]
  exact hρ

/-- **Local extension with a subcritical radial gain, in flattening coordinates.**  Let `m ≤ n`,
`Ω₀ ⊆ ℂ^m` open and convex, `ρ > 0`, `φ` psh on `Ω₀ × D(0, ρ)^{n-m}` and `f` holomorphic on `Ω₀`
with `∫_{Ω₀} |f|² e^{-φ(·, 0)} < ∞`.  For every `N ≥ 1` there is a holomorphic `F` with
`F(·, 0) = f` and `∫ |F|² e^{-φ} |w|^{-2(n-m)(1-1/N)} < ∞`, `|w|² = ∑_{i ≥ m} |z_i|²`. -/
theorem exists_extension_flat {n m : ℕ} (hmn : m ≤ n) {Ω₀ : Set (ComplexModel m)}
    (hΩ₀ : IsOpen Ω₀) (hconv : Convex ℝ Ω₀) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : N ≠ 0)
    {φ : ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ (flatDom n m Ω₀ ρ))
    {f : ComplexModel m → ℂ} (hf : DifferentiableOn ℂ f Ω₀)
    (hfi : ∫⁻ w in Ω₀, multiplierDensity (fun w => φ (coordinateInclusion n m w)) 1 f w ≠ ⊤) :
    ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F (flatDom n m Ω₀ ρ) ∧
      (∀ w ∈ Ω₀, F (coordinateInclusion n m w) = f w) ∧
      ∫⁻ z in flatDom n m Ω₀ ρ, multiplierDensity φ 1 F z *
        ENNReal.ofReal (normalWeight n m z ^ (-(((n - m : ℕ) : ℝ) * (1 - 1 / (N : ℝ))))) ≠ ⊤ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hincl : (⇑(coordinateInclusion (m + d) m) : ComplexModel m → ComplexModel (m + d)) =
      ⇑(subspaceCLM m d) := funext (RestrictionOhsawaTakegoshi.coordinateInclusion_add_eq_subspaceCLM m d)
  rw [← gainDom_eq_flatDom] at hφ ⊢
  rw [hincl] at hfi ⊢
  obtain ⟨F, hFd, hFext, hFint⟩ := exists_extension_gain hΩ₀ hconv hρ hN d φ hφ f hf hfi
  refine ⟨F, hFd, hFext, ?_⟩
  have hd : m + d - m = d := by omega
  simp only [hd]
  refine ne_top_of_le_ne_top hFint (le_of_eq (setLIntegral_congr_fun
    (isOpen_gainDom hΩ₀ ρ d).measurableSet fun z _ => ?_))
  rw [normalSq_eq_normalWeight, gainExp]

end Flat

end SGPT.Trace.OTMargin
