import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Compact.Basic

set_option autoImplicit false

/-!
# Bounded Hölder continuous maps: the Banach space `C^{0,r}_b(X, F)`

For an exponent `r : ℝ≥0`, a metric space `X` and a real normed space `F`, the space
`BoundedHolderMap r X F` consists of the bounded continuous maps `f : X → F` that are
`r`-Hölder continuous.  It is normed by

`‖f‖ = ‖f‖_∞ + [f]_r`,  where `[f]_r = nnHolderNorm r f`

is the least `r`-Hölder constant of `f` (mathlib's `nnHolderNorm`,
`Topology.MetricSpace.HolderNorm`).
This is the space `C^{0,r}(X̄)` of Gilbarg--Trudinger, §4.1 and (4.6), for `X` the closure of a
bounded domain, and the coefficient space of the Schauder theory.

## Main definitions

* `BoundedHolderMap r X F`: the bounded `r`-Hölder continuous maps `X → F`.
* `BoundedHolderMap.ofLE`: for `X` bounded and `s ≤ r`, the inclusion
  `C^{0,r}_b(X, F) →L[𝕜] C^{0,s}_b(X, F)`.

## Main results

* `BoundedHolderMap.instCompleteSpace`: `C^{0,r}_b(X, F)` is a Banach space when `F` is complete.
* `BoundedHolderMap.instNormedRing`, `instNormedAlgebra`: for a normed `ℝ`-algebra `R`,
  `C^{0,r}_b(X, R)` is a normed algebra; the product estimate is
  `holderWith_mul : [f g]_r ≤ ‖f‖_∞ [g]_r + [f]_r ‖g‖_∞` (`norm_mul_le` follows).
* `BoundedHolderMap.holderWith_interpolate`: the interpolation inequality
  `[f]_{r t} ≤ [f]_r ^ t (2 ‖f‖_∞) ^ (1 - t)` for `0 ≤ t ≤ 1`.
* `BoundedHolderMap.isCompactOperator_ofLE`: for `X` compact, `F` finite dimensional (proper)
  and `s < r`, the inclusion `C^{0,r}(X, F) → C^{0,s}(X, F)` is a compact operator
  (Arzelà--Ascoli + interpolation; Gilbarg--Trudinger, Lemma 6.33 for `k = 0`).

## Implementation notes

The space is a structure extending `X →ᵇ F` with the Hölder condition as a `Prop` field, so the
sup-norm part and all algebraic operations are inherited from `BoundedContinuousFunction`.  The
norm is the sum (not the maximum) of the two seminorms, which makes the product estimate read
`‖f g‖ ≤ ‖f‖ ‖g‖` on the nose.  The exponent `r` is an arbitrary `ℝ≥0`; `r = 0` gives the bounded
continuous maps with the norm `‖f‖_∞ + osc f`, and `r > 1` is allowed (on `ℝᵐ` it only contains
locally constant maps, which is harmless).

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction

namespace HolderWith

variable {X Y : Type*} [PseudoEMetricSpace X] {C r : ℝ≥0}

/-- A pointwise limit of `(C, r)`-Hölder maps is `(C, r)`-Hölder. -/
theorem of_tendsto [PseudoEMetricSpace Y] {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → X → Y}
    {g : X → Y} (hf : ∀ᶠ i in l, HolderWith C r (f i))
    (hg : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) : HolderWith C r g := fun x y =>
  le_of_tendsto ((hg x).edist (hg y)) (hf.mono fun _ hi => hi x y)

/-- Negation preserves Hölder continuity. -/
theorem neg [SeminormedAddCommGroup Y] {f : X → Y} (hf : HolderWith C r f) :
    HolderWith C r (-f) := fun x y => by
  simpa only [Pi.neg_apply, edist_neg_neg] using hf x y

/-- A map with values at mutual distance `≤ C` is `(C, 0)`-Hölder. -/
theorem of_dist_le_zero [PseudoMetricSpace Y] {f : X → Y} {C : ℝ≥0}
    (hf : ∀ x y, dist (f x) (f y) ≤ C) : HolderWith C 0 f := fun x y => by
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist]
  exact (ENNReal.ofReal_le_ofReal (hf x y)).trans_eq (ENNReal.ofReal_coe_nnreal)

theorem of_dist_le {X : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y}
    (hf : ∀ x y, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ)) : HolderWith C r f := fun x y => by
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (hf x y)

end HolderWith

namespace SGPT.Foundations.Analysis.Pending

/-- The space `C^{0,r}_b(X, F)` of bounded continuous maps `X → F` that are `r`-Hölder
continuous, normed by `‖f‖_∞ + [f]_r`. -/
structure BoundedHolderMap (r : ℝ≥0) (X F : Type*) [MetricSpace X] [NormedAddCommGroup F]
    extends X →ᵇ F where
  /-- The map is `r`-Hölder continuous. Use `BoundedHolderMap.memHolder` instead. -/
  protected memHolder' : MemHolder r toFun

namespace BoundedHolderMap

section Basic

variable {r s : ℝ≥0} {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

instance instFunLike : FunLike (BoundedHolderMap r X F) X F where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance instBoundedContinuousMapClass :
    BoundedContinuousMapClass (BoundedHolderMap r X F) X F where
  map_continuous f := f.continuous_toFun
  map_bounded f := f.map_bounded'

@[ext]
theorem ext {f g : BoundedHolderMap r X F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toBoundedContinuousFunction (f : BoundedHolderMap r X F) :
    ⇑f.toBoundedContinuousFunction = f :=
  rfl

@[simp]
theorem coe_mk (f : X →ᵇ F) (hf : MemHolder r f) : ⇑(⟨f, hf⟩ : BoundedHolderMap r X F) = f :=
  rfl

theorem toBoundedContinuousFunction_injective :
    Function.Injective (toBoundedContinuousFunction : BoundedHolderMap r X F → X →ᵇ F) :=
  fun _ _ h => ext fun x => DFunLike.congr_fun h x

theorem memHolder (f : BoundedHolderMap r X F) : MemHolder r f :=
  f.memHolder'

/-- The Hölder seminorm `[f]_r` is a Hölder constant of `f`. -/
theorem holderWith (f : BoundedHolderMap r X F) : HolderWith (nnHolderNorm r f) r f :=
  f.memHolder.holderWith

theorem continuous (f : BoundedHolderMap r X F) : Continuous f :=
  f.continuous_toFun

end Basic

/-! ### Algebraic structure -/

section Algebra

variable {r : ℝ≥0} {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

instance instZero : Zero (BoundedHolderMap r X F) :=
  ⟨⟨0, memHolder_zero⟩⟩

instance instAdd : Add (BoundedHolderMap r X F) :=
  ⟨fun f g => ⟨f.toBoundedContinuousFunction + g.toBoundedContinuousFunction,
    f.memHolder.add g.memHolder⟩⟩

instance instNeg : Neg (BoundedHolderMap r X F) :=
  ⟨fun f => ⟨-f.toBoundedContinuousFunction, f.holderWith.neg.memHolder⟩⟩

instance instSub : Sub (BoundedHolderMap r X F) :=
  ⟨fun f g => ⟨f.toBoundedContinuousFunction - g.toBoundedContinuousFunction, by
    change MemHolder r (⇑f - ⇑g)
    rw [sub_eq_add_neg]
    exact f.memHolder.add g.holderWith.neg.memHolder⟩⟩

@[simp] theorem coe_zero : ⇑(0 : BoundedHolderMap r X F) = 0 := rfl

@[simp] theorem coe_add (f g : BoundedHolderMap r X F) : ⇑(f + g) = f + g := rfl

@[simp] theorem coe_neg (f : BoundedHolderMap r X F) : ⇑(-f) = -f := rfl

@[simp] theorem coe_sub (f g : BoundedHolderMap r X F) : ⇑(f - g) = f - g := rfl

instance instSMul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] :
    SMul 𝕜 (BoundedHolderMap r X F) :=
  ⟨fun c f => ⟨c • f.toBoundedContinuousFunction, f.memHolder.smul⟩⟩

@[simp] theorem coe_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] (c : 𝕜)
    (f : BoundedHolderMap r X F) : ⇑(c • f) = c • ⇑f := rfl

variable [NormedSpace ℝ F]

instance instSMulNat : SMul ℕ (BoundedHolderMap r X F) :=
  ⟨fun n f => ⟨n • f.toBoundedContinuousFunction, f.memHolder.nsmul n⟩⟩

instance instSMulInt : SMul ℤ (BoundedHolderMap r X F) :=
  ⟨fun n f => ⟨n • f.toBoundedContinuousFunction, by
    change MemHolder r (n • ⇑f)
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact f.memHolder.smul⟩⟩

instance instAddCommGroup : AddCommGroup (BoundedHolderMap r X F) :=
  toBoundedContinuousFunction_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `toBoundedContinuousFunction` as an additive group homomorphism. -/
@[simps]
def toBoundedContinuousFunctionAddHom : BoundedHolderMap r X F →+ (X →ᵇ F) where
  toFun := toBoundedContinuousFunction
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] :
    Module 𝕜 (BoundedHolderMap r X F) :=
  toBoundedContinuousFunction_injective.module 𝕜 toBoundedContinuousFunctionAddHom
    fun _ _ => rfl

end Algebra

/-! ### The Hölder norm -/

section Norm

variable {r : ℝ≥0} {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

section NoSMul

/-- The norm `‖f‖ = ‖f‖_∞ + [f]_r` of `C^{0,r}_b(X, F)`. -/
instance instNorm : Norm (BoundedHolderMap r X F) :=
  ⟨fun f => ‖f.toBoundedContinuousFunction‖ + nnHolderNorm r f⟩

theorem norm_def (f : BoundedHolderMap r X F) :
    ‖f‖ = ‖f.toBoundedContinuousFunction‖ + nnHolderNorm r f :=
  rfl

theorem nnHolderNorm_neg (f : BoundedHolderMap r X F) :
    nnHolderNorm r (-⇑f) = nnHolderNorm r f := by
  refine le_antisymm f.holderWith.neg.nnholderNorm_le ?_
  have h := f.holderWith.neg.memHolder.holderWith.neg
  rw [neg_neg] at h
  exact h.nnholderNorm_le

theorem norm_toBoundedContinuousFunction_le (f : BoundedHolderMap r X F) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖f‖ :=
  le_add_of_nonneg_right (NNReal.coe_nonneg _)

theorem nnHolderNorm_le_norm (f : BoundedHolderMap r X F) : (nnHolderNorm r f : ℝ) ≤ ‖f‖ :=
  le_add_of_nonneg_left (norm_nonneg _)

/-- `‖f‖` is at most `‖f‖_∞ + C` for any `r`-Hölder constant `C` of `f`. -/
theorem norm_le_of_holderWith (f : BoundedHolderMap r X F) {C : ℝ≥0}
    (hf : HolderWith C r f) : ‖f‖ ≤ ‖f.toBoundedContinuousFunction‖ + C := by
  rw [norm_def]
  gcongr
  exact hf.nnholderNorm_le

theorem norm_apply_le (f : BoundedHolderMap r X F) (x : X) : ‖f x‖ ≤ ‖f‖ :=
  (f.toBoundedContinuousFunction.norm_coe_le_norm x).trans f.norm_toBoundedContinuousFunction_le

end NoSMul

variable [NormedSpace ℝ F]

private theorem normedSpaceCore {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] :
    NormedSpace.Core 𝕜 (BoundedHolderMap r X F) where
  norm_nonneg f := by rw [norm_def]; positivity
  norm_smul c f := by
    rw [norm_def, norm_def, coe_smul, f.memHolder.nnHolderNorm_smul c]
    change ‖c • f.toBoundedContinuousFunction‖ + _ = _
    rw [norm_smul, NNReal.coe_mul, coe_nnnorm, mul_add]
  norm_triangle f g := by
    rw [norm_def, norm_def, norm_def, coe_add]
    have h1 : ‖(f + g).toBoundedContinuousFunction‖ ≤
        ‖f.toBoundedContinuousFunction‖ + ‖g.toBoundedContinuousFunction‖ :=
      norm_add_le _ _
    have h2 := f.memHolder.nnHolderNorm_add_le g.memHolder
    have h2' : (nnHolderNorm r (⇑f + ⇑g) : ℝ) ≤ nnHolderNorm r f + nnHolderNorm r g := by
      exact_mod_cast h2
    linarith
  norm_eq_zero_iff f := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    swap
    · subst h
      rw [norm_def, show (0 : BoundedHolderMap r X F).toBoundedContinuousFunction = 0 from rfl,
        coe_zero, nnHolderNorm_zero, norm_zero, NNReal.coe_zero, add_zero]
    rw [norm_def] at h
    have h0 : ‖f.toBoundedContinuousFunction‖ = 0 := le_antisymm (by
      have : (0 : ℝ) ≤ nnHolderNorm r f := NNReal.coe_nonneg _
      linarith) (norm_nonneg _)
    exact toBoundedContinuousFunction_injective (norm_eq_zero.1 h0)

instance instNormedAddCommGroup : NormedAddCommGroup (BoundedHolderMap r X F) :=
  NormedAddCommGroup.ofCore (𝕜 := ℝ) normedSpaceCore

instance instNormedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] :
    NormedSpace 𝕜 (BoundedHolderMap r X F) :=
  NormedSpace.ofCore normedSpaceCore

/-- A Hölder constant of `f` is given by its norm. -/
theorem holderWith_norm (f : BoundedHolderMap r X F) : HolderWith ‖f‖₊ r f :=
  f.holderWith.mono (by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact f.nnHolderNorm_le_norm)

theorem dist_toBoundedContinuousFunction_le (f g : BoundedHolderMap r X F) :
    dist f.toBoundedContinuousFunction g.toBoundedContinuousFunction ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  exact (f - g).norm_toBoundedContinuousFunction_le

theorem lipschitzWith_toBoundedContinuousFunction :
    LipschitzWith 1 (toBoundedContinuousFunction : BoundedHolderMap r X F → X →ᵇ F) :=
  LipschitzWith.of_dist_le_mul fun f g => by
    simpa using dist_toBoundedContinuousFunction_le f g

theorem continuous_toBoundedContinuousFunction :
    Continuous (toBoundedContinuousFunction : BoundedHolderMap r X F → X →ᵇ F) :=
  lipschitzWith_toBoundedContinuousFunction.continuous

end Norm

/-! ### Completeness -/

section Complete

variable {r : ℝ≥0} {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `C^{0,r}_b(X, F)` is complete: a Cauchy sequence converges uniformly, the Hölder constants of
the differences `fₙ - fₘ` pass to the limit `m → ∞`. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (BoundedHolderMap r X F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    (lipschitzWith_toBoundedContinuousFunction.uniformContinuous.comp_cauchySeq hu)
  have hgx : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x)) := fun x =>
    ((continuous_eval_const x).tendsto g).comp hg
  -- for `ε > 0` and `n` large, `u n - g` is `(ε, r)`-Hölder
  have key : ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n ≥ N, HolderWith ε r (⇑(u n) - ⇑g) := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun n hn => HolderWith.of_tendsto (l := atTop) (f := fun m => ⇑(u n) - ⇑(u m))
      (Filter.eventually_atTop.2 ⟨N, fun m hm => ?_⟩) fun x =>
        tendsto_const_nhds.sub (hgx x)⟩
    have h := (u n - u m).holderWith
    refine h.mono ?_
    rw [← NNReal.coe_le_coe]
    exact (u n - u m).nnHolderNorm_le_norm.trans ((dist_eq_norm (u n) (u m)).symm ▸
      (hN n hn m hm).le)
  obtain ⟨N, hN⟩ := key 1 one_pos
  have hgH : MemHolder r (g : X → F) := by
    have h := ((u N).holderWith.add (hN N le_rfl).neg).memHolder
    rwa [show ⇑(u N) + -(⇑(u N) - ⇑g) = ⇑g by abel] at h
  set G : BoundedHolderMap r X F := ⟨g, hgH⟩
  refine ⟨G, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := key (ε / 2).toNNReal (Real.toNNReal_pos.2 (half_pos hε))
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hg (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have h1 := (u n - G).norm_le_of_holderWith (hN₁ n (le_of_max_le_left hn))
  have h2 : ‖(u n - G).toBoundedContinuousFunction‖ < ε / 2 := by
    have := hN₂ n (le_of_max_le_right hn)
    rwa [dist_eq_norm] at this
  rw [Real.coe_toNNReal _ (half_pos hε).le] at h1
  linarith

end Complete

/-! ### Products: `C^{0,r}_b(X, R)` is a normed algebra -/

section Ring

variable {r : ℝ≥0} {X R : Type*} [MetricSpace X] [NormedRing R]

/-- **Product estimate**: `[f g]_r ≤ ‖f‖_∞ [g]_r + [f]_r ‖g‖_∞`. -/
theorem holderWith_mul (f g : BoundedHolderMap r X R) {Cf Cg : ℝ≥0} (hf : HolderWith Cf r f)
    (hg : HolderWith Cg r g) :
    HolderWith (‖f.toBoundedContinuousFunction‖₊ * Cg + Cf * ‖g.toBoundedContinuousFunction‖₊) r
      (⇑f * ⇑g) := by
  refine HolderWith.of_dist_le fun x y => ?_
  have hfx := f.toBoundedContinuousFunction.norm_coe_le_norm x
  have hgy := g.toBoundedContinuousFunction.norm_coe_le_norm y
  have h1 := hf.dist_le x y
  have h2 := hg.dist_le x y
  have hd : 0 ≤ dist x y ^ (r : ℝ) := Real.rpow_nonneg dist_nonneg _
  simp only [Pi.mul_apply, dist_eq_norm] at h1 h2 ⊢
  calc ‖f x * g x - f y * g y‖ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
        congr 1; noncomm_ring
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖f.toBoundedContinuousFunction‖ * (Cg * dist x y ^ (r : ℝ)) +
          Cf * dist x y ^ (r : ℝ) * ‖g.toBoundedContinuousFunction‖ := by
        gcongr
        exacts [hfx, hgy]
    _ = _ := by push_cast; ring

instance instOne : One (BoundedHolderMap r X R) :=
  ⟨⟨1, memHolder_const⟩⟩

instance instMul : Mul (BoundedHolderMap r X R) :=
  ⟨fun f g => ⟨f.toBoundedContinuousFunction * g.toBoundedContinuousFunction,
    (f.holderWith_mul g f.holderWith g.holderWith).memHolder⟩⟩

instance instNatCast : NatCast (BoundedHolderMap r X R) :=
  ⟨fun n => ⟨n, memHolder_const⟩⟩

instance instIntCast : IntCast (BoundedHolderMap r X R) :=
  ⟨fun n => ⟨n, memHolder_const⟩⟩

@[simp] theorem coe_one : ⇑(1 : BoundedHolderMap r X R) = 1 := rfl

@[simp] theorem coe_mul (f g : BoundedHolderMap r X R) : ⇑(f * g) = ⇑f * ⇑g := rfl

theorem memHolder_pow (f : BoundedHolderMap r X R) (n : ℕ) :
    MemHolder r ⇑(f.toBoundedContinuousFunction ^ n) := by
  induction n with
  | zero => exact ⟨0, fun x y => by simp⟩
  | succ n ih =>
    let fn : BoundedHolderMap r X R := ⟨f.toBoundedContinuousFunction ^ n, ih⟩
    rw [pow_succ]
    exact (fn.holderWith_mul f fn.holderWith f.holderWith).memHolder

instance instPow : Pow (BoundedHolderMap r X R) ℕ :=
  ⟨fun f n => ⟨f.toBoundedContinuousFunction ^ n, f.memHolder_pow n⟩⟩

/-- `‖f g‖ ≤ ‖f‖ ‖g‖` for the norm `‖·‖_∞ + [·]_r`. -/
theorem norm_mul_le' (f g : BoundedHolderMap r X R) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  have h := (f * g).norm_le_of_holderWith (f.holderWith_mul g f.holderWith g.holderWith)
  have h1 : ‖(f * g).toBoundedContinuousFunction‖ ≤
      ‖f.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖ :=
    norm_mul_le f.toBoundedContinuousFunction g.toBoundedContinuousFunction
  rw [norm_def f, norm_def g]
  push_cast at h
  have := norm_nonneg f.toBoundedContinuousFunction
  have := norm_nonneg g.toBoundedContinuousFunction
  have := (nnHolderNorm r f).coe_nonneg
  have := (nnHolderNorm r g).coe_nonneg
  nlinarith

variable [NormedAlgebra ℝ R]

instance instRing : Ring (BoundedHolderMap r X R) :=
  toBoundedContinuousFunction_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

instance instNormedRing : NormedRing (BoundedHolderMap r X R) where
  dist_eq f g := by rw [dist_eq_norm, ← norm_neg, neg_sub, sub_eq_neg_add]
  norm_mul_le := norm_mul_le'

instance instNormedCommRing {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] :
    NormedCommRing (BoundedHolderMap r X R) where
  mul_comm f g := ext fun x => mul_comm (f x) (g x)

instance instAlgebra {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] :
    Algebra 𝕜 (BoundedHolderMap r X R) :=
  Algebra.ofModule (fun c f g => ext fun x => smul_mul_assoc c (f x) (g x))
    (fun c f g => ext fun x => mul_smul_comm c (f x) (g x))

instance instNormedAlgebra {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] :
    NormedAlgebra 𝕜 (BoundedHolderMap r X R) where
  norm_smul_le c f := (norm_smul c f).le

end Ring

/-! ### Lower exponents, interpolation and the compact embedding -/

section Interpolation

variable {r s : ℝ≥0} {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

/-- A bounded map is `(2 ‖f‖_∞, 0)`-Hölder. -/
theorem holderWith_zero (f : BoundedHolderMap r X F) :
    HolderWith (2 * ‖f.toBoundedContinuousFunction‖₊) 0 f :=
  HolderWith.of_dist_le_zero fun x y => by
    simpa using f.toBoundedContinuousFunction.dist_le_two_norm x y

/-- **Interpolation inequality**: for `0 ≤ t ≤ 1`,
`[f]_{r t} ≤ [f]_r ^ t (2 ‖f‖_∞) ^ (1 - t)` (Gilbarg--Trudinger (6.89) for `k = 0`). -/
theorem holderWith_interpolate (f : BoundedHolderMap r X F) {t : ℝ≥0} (ht : t ≤ 1) :
    HolderWith (nnHolderNorm r f ^ (t : ℝ) *
      (2 * ‖f.toBoundedContinuousFunction‖₊) ^ ((1 - t : ℝ≥0) : ℝ)) (r * t) f := by
  have h := f.holderWith.interpolate f.holderWith_zero (add_tsub_cancel_of_le ht)
  simpa using h

/-- On a bounded space, the inclusion `C^{0,r}_b(X, F) → C^{0,s}_b(X, F)` for `s ≤ r`. -/
def ofLE [BoundedSpace X] (hsr : s ≤ r) (f : BoundedHolderMap r X F) : BoundedHolderMap s X F :=
  ⟨f.toBoundedContinuousFunction, f.memHolder.of_le hsr⟩

@[simp]
theorem coe_ofLE [BoundedSpace X] (hsr : s ≤ r) (f : BoundedHolderMap r X F) :
    ⇑(ofLE hsr f) = f :=
  rfl

variable [NormedSpace ℝ F]

/-- On a bounded space, the inclusion `C^{0,r}_b(X, F) →L[𝕜] C^{0,s}_b(X, F)` for `s ≤ r`. -/
def ofLECLM (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [BoundedSpace X] (hsr : s ≤ r) :
    BoundedHolderMap r X F →L[𝕜] BoundedHolderMap s X F :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := ofLE hsr
      map_add' _ _ := ext fun _ => rfl
      map_smul' _ _ := ext fun _ => rfl } (by
    obtain ⟨D, hD⟩ := Metric.boundedSpace_iff_edist.1 ‹BoundedSpace X›
    refine ⟨1 + D ^ (r - s : ℝ), fun f => ?_⟩
    have h := f.holderWith.of_le hD hsr
    have h1 := (ofLE hsr f).norm_le_of_holderWith h
    have h2 : ‖(ofLE hsr f).toBoundedContinuousFunction‖ = ‖f.toBoundedContinuousFunction‖ := rfl
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [h2, NNReal.coe_mul, NNReal.coe_rpow] at h1
    rw [norm_def f]
    have := norm_nonneg f.toBoundedContinuousFunction
    have := (nnHolderNorm r f).coe_nonneg
    have : (0 : ℝ) ≤ (D : ℝ) ^ (r - s : ℝ) := Real.rpow_nonneg D.coe_nonneg _
    nlinarith)

@[simp]
theorem ofLECLM_apply (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [BoundedSpace X]
    (hsr : s ≤ r) (f : BoundedHolderMap r X F) : ofLECLM 𝕜 hsr f = ofLE hsr f :=
  rfl

/-- **Compact embedding** `C^{0,r}(X, F) ⊂⊂ C^{0,s}(X, F)` for `s < r` on a compact space `X`
with values in a proper space `F` (e.g. finite dimensional): Arzelà--Ascoli gives uniform
convergence along a subsequence, and the interpolation inequality upgrades it to convergence in
`C^{0,s}` (Gilbarg--Trudinger, Lemma 6.36 for `k = 0`). -/
theorem isCompactOperator_ofLE [CompactSpace X] [ProperSpace F] (hsr : s < r) :
    IsCompactOperator (ofLE (X := X) (F := F) hsr.le) := by
  have hr : 0 < r := lt_of_le_of_lt zero_le hsr
  -- the set `A` of `1`-Hölder maps of sup norm `≤ 1`
  set A : Set (X →ᵇ F) := {g | ‖g‖ ≤ 1 ∧ HolderWith 1 r g} with hA
  have hH : IsClosed {g : X →ᵇ F | HolderWith 1 r g} := by
    have : {g : X →ᵇ F | HolderWith 1 r g} =
        ⋂ x, ⋂ y, {g : X →ᵇ F | edist (g x) (g y) ≤ 1 * edist x y ^ (r : ℝ)} := by
      ext g; simp [HolderWith, ENNReal.coe_one]
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((continuous_eval_const x).edist (continuous_eval_const y)) continuous_const
  have hAc : IsClosed A := (isClosed_le continuous_norm continuous_const).inter hH
  have hequi : Equicontinuous fun g : A => ⇑(g : X →ᵇ F) := by
    intro x₀
    refine Metric.equicontinuousAt_iff_right.2 fun ε hε => ?_
    have hcont : Continuous fun x : X => dist x₀ x ^ (r : ℝ) :=
      (continuous_const.dist continuous_id).rpow_const fun _ => Or.inr r.coe_nonneg
    have h0 : dist x₀ x₀ ^ (r : ℝ) = 0 := by
      rw [dist_self, Real.zero_rpow (NNReal.coe_pos.2 hr).ne']
    have hev := (hcont.tendsto x₀).eventually (gt_mem_nhds (a := ε) (by rw [h0]; exact hε))
    filter_upwards [hev] with x hx g
    have := g.2.2.dist_le x₀ x
    simp only [NNReal.coe_one, one_mul] at this
    exact this.trans_lt hx
  have hAcpt : IsCompact A :=
    BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall (0 : F) 1)
      (isCompact_closedBall 0 1) A hAc
      (fun g x hg => mem_closedBall_zero_iff.2 ((g.norm_coe_le_norm x).trans hg.1)) hequi
  have : CompactSpace A := isCompact_iff_compactSpace.1 hAcpt
  -- the map `A → C^{0,s}` is continuous by interpolation
  let Φ : A → BoundedHolderMap s X F := fun g => ⟨g.1, (g.2.2.memHolder).of_le hsr.le⟩
  set t₁ : ℝ≥0 := s / r with ht₁
  have ht₁1 : t₁ ≤ 1 := div_le_one_of_le₀ hsr.le zero_le
  set t₂ : ℝ≥0 := 1 - t₁ with ht₂
  have ht₂0 : (0 : ℝ) < t₂ := by
    rw [ht₂, NNReal.coe_pos, tsub_pos_iff_lt, ht₁]
    exact (div_lt_one hr).2 hsr
  have hrt : r * t₁ = s := by rw [ht₁, mul_div_cancel₀ _ hr.ne']
  have hΦ : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    -- `dist (Φ h) (Φ g) ≤ ψ (dist h g)` with `ψ d = d + 2 ^ t₁ (2 d) ^ t₂`
    set ψ : ℝ → ℝ := fun d => d + 2 ^ (t₁ : ℝ) * (2 * d) ^ (t₂ : ℝ) with hψ
    have hψc : Continuous ψ :=
      continuous_id.add (continuous_const.mul ((continuous_const.mul continuous_id).rpow_const
        fun _ => Or.inr t₂.coe_nonneg))
    have hψ0 : ψ 0 = 0 := by simp [hψ, Real.zero_rpow ht₂0.ne']
    have hd0 : Tendsto (fun h : A => dist h g) (𝓝 g) (𝓝 0) :=
      (continuous_id.dist continuous_const).tendsto' g 0 (dist_self g)
    refine squeeze_zero (fun _ => dist_nonneg) (fun h => ?_)
      ((hψc.tendsto' 0 0 hψ0).comp hd0)
    -- the difference `h - g` as an element of `C^{0,r}`
    have hd : HolderWith 2 r (⇑(h : X →ᵇ F) - ⇑(g : X →ᵇ F)) := by
      have := h.2.2.add g.2.2.neg
      rw [← sub_eq_add_neg] at this
      exact this.mono (by norm_num)
    let D : BoundedHolderMap r X F := ⟨(h : X →ᵇ F) - (g : X →ᵇ F), hd.memHolder⟩
    have hDs : HolderWith (2 ^ (t₁ : ℝ) * (2 * ‖D.toBoundedContinuousFunction‖₊) ^ (t₂ : ℝ))
        s D := by
      have h' := hd.interpolate D.holderWith_zero
        (show t₁ + t₂ = 1 from add_tsub_cancel_of_le ht₁1)
      rw [show r * t₁ + 0 * t₂ = s by rw [zero_mul, add_zero, hrt]] at h'
      exact h'
    have hDΦ : Φ h - Φ g = ⟨D.toBoundedContinuousFunction, hDs.memHolder⟩ := rfl
    rw [dist_eq_norm, hDΦ]
    refine (BoundedHolderMap.norm_le_of_holderWith _ hDs).trans_eq ?_
    simp only [hψ, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat, coe_nnnorm,
      Function.comp_apply, Subtype.dist_eq, dist_eq_norm]
    rfl
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, range Φ, isCompact_range hΦ,
      ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  rw [mem_closedBall_zero_iff] at hf
  refine ⟨⟨f.toBoundedContinuousFunction, f.norm_toBoundedContinuousFunction_le.trans hf,
    f.holderWith.mono ?_⟩, rfl⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_one]
  exact f.nnHolderNorm_le_norm.trans hf

end Interpolation

end BoundedHolderMap

end SGPT.Foundations.Analysis.Pending
