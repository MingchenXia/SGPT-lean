import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

/-!
# Uniform limits of `C^k` maps with uniformly convergent derivatives

If `C^k` maps `fₙ : E → F` converge pointwise to `f` and, for every `i ≤ k`, their `i`-th
derivatives `Dⁱ fₙ` converge uniformly to maps `gᵢ`, then `f` is `C^k` and `Dⁱ f = gᵢ`
(`iteratedFDeriv_eq_of_tendstoUniformly`, `contDiff_of_tendstoUniformly_iteratedFDeriv`).

This is the iterated form of mathlib's `hasFDerivAt_of_tendstoUniformly` (first derivatives,
`Mathlib.Analysis.Calculus.UniformLimitsDeriv`), obtained by induction on `i` through
`iteratedFDeriv_succ_eq_comp_left`.  It is the analytic input of the completeness of the
spaces `C^k_b` and `C^{k,r}_b` (`BoundedContDiffHolderMap`).

Part of the linear track `L1` of the plan for Yau's theorem.
-/

open Filter Topology

namespace SGPT.Foundations.Analysis.Pending

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ι : Type*} {l : Filter ι} {k : ℕ} {f : ι → E → F} {f₀ : E → F}
  {g : (i : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F}

/-- **Derivative of a uniform limit of iterated derivatives**: if `Dⁱ (f n) → g i` and
`Dⁱ⁺¹ (f n) → g (i + 1)` uniformly, with `i < k` and `f n` of class `C^k`, then `g i` has
derivative `curryLeft (g (i + 1) x)` at every `x`. -/
theorem hasFDerivAt_of_tendstoUniformly_iteratedFDeriv [l.NeBot] (hf : ∀ n, ContDiff ℝ k (f n))
    {i : ℕ} (hik : i < k)
    (hgi : TendstoUniformly (fun n => iteratedFDeriv ℝ i (f n)) (g i) l)
    (hgi' : TendstoUniformly (fun n => iteratedFDeriv ℝ (i + 1) (f n)) (g (i + 1)) l) (x : E) :
    HasFDerivAt (g i)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F (g (i + 1) x)) x := by
  set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F
  have hL : ∀ n y, fderiv ℝ (iteratedFDeriv ℝ i (f n)) y =
      L (iteratedFDeriv ℝ (i + 1) (f n) y) := by
    intro n y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have hconv : TendstoUniformly (fun n y => L (iteratedFDeriv ℝ (i + 1) (f n) y))
      (fun y => L (g (i + 1) y)) l :=
    L.isometry.uniformContinuous.comp_tendstoUniformly hgi'
  exact hasFDerivAt_of_tendstoUniformly hconv (fun n y => by
      rw [← hL]
      exact ((hf n).differentiable_iteratedFDeriv (by exact_mod_cast hik) y).hasFDerivAt)
    (fun y => hgi.tendsto_at y) x

/-- **Iterated derivatives of uniform limits**: if `C^k` maps `f n` converge pointwise to `f₀`
and `Dⁱ (f n) → g i` uniformly for every `i ≤ k`, then `Dⁱ f₀ = g i` for `i ≤ k`. -/
theorem iteratedFDeriv_eq_of_tendstoUniformly [l.NeBot] (hf : ∀ n, ContDiff ℝ k (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) l (𝓝 (f₀ x)))
    (hg : ∀ i ≤ k, TendstoUniformly (fun n => iteratedFDeriv ℝ i (f n)) (g i) l) :
    ∀ i ≤ k, iteratedFDeriv ℝ i f₀ = g i := by
  intro i hi
  induction i with
  | zero =>
    funext x
    have h1 := (hg 0 (Nat.zero_le _)).tendsto_at x
    have h2 : Tendsto (fun n => iteratedFDeriv ℝ 0 (f n) x) l
        (𝓝 ((continuousMultilinearCurryFin0 ℝ E F).symm (f₀ x))) := by
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto _).comp (hlim x)
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact tendsto_nhds_unique h2 h1
  | succ i ih =>
    have hik : i < k := hi
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hik.le,
      (hasFDerivAt_of_tendstoUniformly_iteratedFDeriv hf hik (hg i hik.le) (hg (i + 1) hi)
        x).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

/-- **Uniform limits of `C^k` maps**: if `C^k` maps `f n` converge pointwise to `f₀` and their
`i`-th derivatives converge uniformly for every `i ≤ k`, then `f₀` is `C^k`. -/
theorem contDiff_of_tendstoUniformly_iteratedFDeriv [l.NeBot] (hf : ∀ n, ContDiff ℝ k (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) l (𝓝 (f₀ x)))
    (hg : ∀ i ≤ k, TendstoUniformly (fun n => iteratedFDeriv ℝ i (f n)) (g i) l) :
    ContDiff ℝ k f₀ := by
  have heq := iteratedFDeriv_eq_of_tendstoUniformly hf hlim hg
  suffices h : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) f₀ from h
  rw [contDiff_iff_continuous_differentiable]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hm' : m ≤ k := by exact_mod_cast hm
    rw [heq m hm']
    exact (hg m hm').continuous (Frequently.of_forall fun n =>
      (hf n).continuous_iteratedFDeriv (by exact_mod_cast hm'))
  · have hm' : m < k := by exact_mod_cast hm
    rw [heq m hm'.le]
    exact fun x => (hasFDerivAt_of_tendstoUniformly_iteratedFDeriv hf hm' (hg m hm'.le)
      (hg (m + 1) hm') x).differentiableAt

end SGPT.Foundations.Analysis.Pending
