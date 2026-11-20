import SGPT.Envelopes.DNTC11LocalContact

/-!
# Locally integrable complex Hessian densities

Lane CZ-LP (`claude-cz-lp`, nodes `czlp:density`, `czlp:flat-zero`, `czlp:limit`).  The book uses
the class `C^{1,1̄}(X)` of continuous functions with bounded `ω`-Laplacian; for `n ≥ 2` their
complex Hessians are in general unbounded, and the book's Monge–Ampère measure `θ_fⁿ` is the
absolutely continuous measure whose density is the determinant of the *function* representing the
distributional complex Hessian.  This file develops the local theory of such representing
functions when they are only locally integrable.

In a coordinate domain `U ⊆ ℂⁿ`, a continuous function `g` has the *Hessian density*
`h : ℂⁿ → Mat_n(ℂ)` (`IsHessianDensityOn g h U`) if `h` is measurable, pointwise Hermitian and
locally integrable on `U`, and `∫ g ∂_v∂̄_v φ = ∫ ⟨h v, v⟩ φ` for every smooth `φ` with compact
support in `U` and every `v`.  It generalizes `DNTC11.IsBoundedHessianDensityOn` (`L^∞_loc`).

## Main results

* `isHessianDensityOn_of_bounded`, `isHessianDensityOn_of_contDiffOn`: bounded and classical
  densities; `IsHessianDensityOn.add`, `sub`, `smul`, `mono`.
* `IsHessianDensityOn.ae_tendsto_complexHessian_mollified`: the complex Hessians of the radial
  mollifications converge almost everywhere to the density (Lebesgue differentiation).
* `IsHessianDensityOn.ae_eq`: densities are unique almost everywhere.
* `IsHessianDensityOn.ae_eq_zero_of_isLittleO`: **second-order vanishing kills the density** —
  if `g ≥ 0` on `U`, then at almost every zero `z` of `g` at which `g(z + y) = o(‖y‖²)`, the density
  vanishes (the Lebesgue-point form of Stampacchia's lemma used in the book's proof of
  `lma:DNTroof`).
* `IsHessianDensityOn.ae_hermQuad_nonneg_of_psh`: the density of a plurisubharmonic function is
  semipositive almost everywhere.
* `IsHessianDensityOn.of_tendsto`: if smooth `G_k → g` locally uniformly and their complex Hessians
  converge in `L¹_loc` to `h`, then `h` is the density of `g`.
* `exists_isHessianDensityOn_of_summable`: if moreover the `L¹(K)` norms of the increments of the
  complex Hessians are summable on every compact `K ⊆ U`, a density exists and is the almost
  everywhere limit of the complex Hessians.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal ComplexOrder

namespace SGPT.Analysis.CZLp

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11

variable {n : ℕ}

/-- **Locally integrable complex Hessian density.**  On the open set `U ⊆ ℂⁿ`, the continuous
function `g` has the measurable, pointwise Hermitian, locally integrable matrix function `h` as the
density of its distributional complex Hessian: `∫ g ∂_v∂̄_v φ = ∫ ⟨h v, v⟩ φ` for all smooth `φ`
with compact support in `U` and all `v`. -/
structure IsHessianDensityOn (g : ComplexModel n → ℝ)
    (h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (U : Set (ComplexModel n)) : Prop where
  isOpen : IsOpen U
  continuousOn : ContinuousOn g U
  isHermitian : ∀ z, (h z).IsHermitian
  measurable : ∀ i j, Measurable fun z => h z i j
  integrableOn : ∀ K, IsCompact K → K ⊆ U → ∀ i j, IntegrableOn (fun z => h z i j) K
  levi : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∀ v, ∫ z, g z * leviForm φ z v = ∫ z, hermQuad (h z) v * φ z

/-- Bounded densities are densities. -/
theorem isHessianDensityOn_of_bounded {g : ComplexModel n → ℝ}
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hg : IsBoundedHessianDensityOn g h U) : IsHessianDensityOn g h U where
  isOpen := hg.isOpen
  continuousOn := hg.continuousOn
  isHermitian := hg.isHermitian
  measurable := hg.measurable
  integrableOn K hK hKU i j := by
    obtain ⟨C, hC⟩ := hg.bounded K hK hKU
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (hg.measurable i j).aestronglyMeasurable (M := C) ?_
    filter_upwards [hC] with z hz
    exact hz i j
  levi := hg.levi

/-- **Smooth functions**: their classical complex Hessian (extended by `0`) is a density. -/
theorem isHessianDensityOn_of_contDiffOn {ρ : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ U) : IsHessianDensityOn ρ (smoothHess U ρ) U :=
  isHessianDensityOn_of_bounded (isBoundedHessianDensityOn_of_contDiffOn hU hρ)

namespace IsHessianDensityOn

variable {g g' : ComplexModel n → ℝ} {h h' : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
  {U : Set (ComplexModel n)}

theorem mono (hg : IsHessianDensityOn g h U) {V : Set (ComplexModel n)} (hV : IsOpen V)
    (hVU : V ⊆ U) : IsHessianDensityOn g h V where
  isOpen := hV
  continuousOn := hg.continuousOn.mono hVU
  isHermitian := hg.isHermitian
  measurable := hg.measurable
  integrableOn K hK hKV := hg.integrableOn K hK (hKV.trans hVU)
  levi φ hφ hφc hφV := hg.levi φ hφ hφc (hφV.trans hVU)

theorem congr_fun (hg : IsHessianDensityOn g h U) (heq : g = g') : IsHessianDensityOn g' h U :=
  heq ▸ hg

theorem integrableOn_norm_sum (hg : IsHessianDensityOn g h U) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) : IntegrableOn (fun z => ∑ p, ∑ q, ‖h z p q‖) K :=
  integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    (hg.integrableOn K hK hKU p q).norm

theorem integrableOn_hermQuad (hg : IsHessianDensityOn g h U) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) (v : ComplexModel n) :
    IntegrableOn (fun z => hermQuad (h z) v) K := by
  refine Integrable.mono' ((hg.integrableOn_norm_sum hK hKU).mul_const (‖v‖ ^ 2))
    (measurable_hermQuad hg.measurable v).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_hermQuad_le _ _

/-- Products with a compactly supported continuous function are integrable. -/
theorem integrable_hermQuad_mul (hg : IsHessianDensityOn g h U) {φ : ComplexModel n → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ComplexModel n) :
    Integrable (fun z => hermQuad (h z) v * φ z) := by
  have hK : IsCompact (tsupport φ) := hφc
  have h1 : IntegrableOn (fun z => hermQuad (h z) v * φ z) (tsupport φ) :=
    (hg.integrableOn_hermQuad hK hφU v).mul_continuousOn hφ.continuousOn hK
  have heq : (fun z => hermQuad (h z) v * φ z) =
      (tsupport φ).indicator (fun z => hermQuad (h z) v * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, mul_zero]
  rw [heq]
  exact h1.integrable_indicator (isClosed_tsupport φ).measurableSet

theorem integrable_mul_leviForm (hg : IsHessianDensityOn g h U) {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (v : ComplexModel n) : Integrable (fun z => g z * leviForm φ z v) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsub : Function.support (fun x => leviForm φ x v) ⊆ tsupport φ := by
    intro x hx
    by_contra hxt
    apply hx
    simp only [leviForm, ContactLocal.realHessian_eq_zero_of_notMem_tsupport hxt, add_zero,
      zero_div]
  have hcs : HasCompactSupport (fun x => leviForm φ x v) := hφc.mono' hsub
  have hts : tsupport (fun x => leviForm φ x v) ⊆ U :=
    (closure_minimal hsub (isClosed_tsupport φ)).trans hφU
  exact integrable_mul_of_continuousOn hg.isOpen hg.continuousOn (continuous_leviForm hφ2 v) hcs hts

theorem add (hg : IsHessianDensityOn g h U) (hg' : IsHessianDensityOn g' h' U) :
    IsHessianDensityOn (fun z => g z + g' z) (fun z => h z + h' z) U where
  isOpen := hg.isOpen
  continuousOn := hg.continuousOn.add hg'.continuousOn
  isHermitian z := (hg.isHermitian z).add (hg'.isHermitian z)
  measurable i j := by
    show Measurable fun z => h z i j + h' z i j
    exact (hg.measurable i j).add (hg'.measurable i j)
  integrableOn K hK hKU i j := by
    show IntegrableOn (fun z => h z i j + h' z i j) K
    exact (hg.integrableOn K hK hKU i j).add (hg'.integrableOn K hK hKU i j)
  levi φ hφ hφc hφU v := by
    simp only [add_mul, hermQuad_add]
    rw [integral_add (hg.integrable_mul_leviForm hφ hφc hφU v)
        (hg'.integrable_mul_leviForm hφ hφc hφU v),
      integral_add (hg.integrable_hermQuad_mul hφ.continuous hφc hφU v)
        (hg'.integrable_hermQuad_mul hφ.continuous hφc hφU v),
      hg.levi φ hφ hφc hφU v, hg'.levi φ hφ hφc hφU v]

theorem smul (hg : IsHessianDensityOn g h U) (c : ℝ) :
    IsHessianDensityOn (fun z => c * g z) (fun z => (c : ℂ) • h z) U where
  isOpen := hg.isOpen
  continuousOn := continuousOn_const.mul hg.continuousOn
  isHermitian z := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, (hg.isHermitian z).eq, Complex.star_def, Complex.conj_ofReal]
  measurable i j := by
    show Measurable fun z => (c : ℂ) * h z i j
    exact measurable_const.mul (hg.measurable i j)
  integrableOn K hK hKU i j := by
    show IntegrableOn (fun z => (c : ℂ) * h z i j) K
    exact (hg.integrableOn K hK hKU i j).const_mul _
  levi φ hφ hφc hφU v := by
    simp only [hermQuad_smul, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hg.levi φ hφ hφc hφU v]

theorem sub (hg : IsHessianDensityOn g h U) (hg' : IsHessianDensityOn g' h' U) :
    IsHessianDensityOn (fun z => g z - g' z) (fun z => h z - h' z) U := by
  have h1 := hg.add (hg'.smul (-1))
  have e1 : (fun z => g z + -1 * g' z) = fun z => g z - g' z := by funext z; ring
  have e2 : (fun z => h z + ((-1 : ℝ) : ℂ) • h' z) = fun z => h z - h' z := by
    funext z; simp [sub_eq_add_neg]
  rw [e1, e2] at h1
  exact h1

/-- Adding a smooth function adds its classical complex Hessian. -/
theorem add_contDiffOn (hg : IsHessianDensityOn g h U) {ρ : ComplexModel n → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ U) :
    IsHessianDensityOn (fun z => g z + ρ z) (fun z => h z + smoothHess U ρ z) U :=
  hg.add (isHessianDensityOn_of_contDiffOn hg.isOpen hρ)

/-! ### Radial mollifications -/

section Mollifier

variable {Ω : Opens (ComplexModel n)} {x₀ : ComplexModel n} {R : ℝ}

open ContactLocal in
/-- **The Levi forms of the mollifications are the mollified Levi densities.** -/
theorem leviForm_mollified_eq (hg : IsHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {z : ComplexModel n} (hz : z ∈ ball x₀ (2 * R)) (j : ℕ)
    (v : ComplexModel n) :
    leviForm (mollified g x₀ R hR j) z v =
      ∫ x, hermQuad (h x) v * explicitRadialKernel R hR j (x - z) := by
  set K := closedBall x₀ (3 * R) with hKdef
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hloc := locallyIntegrable_indicator_closedBall hg.continuousOn hR hball
  rw [mollified, leviForm_translationPairing hloc (explicitRadialKernel_hasCompactSupport R hR j)
    (explicitRadialKernel_contDiff_two R hR j)]
  have hzK : closedBall z R ⊆ K := closedBall_subset_of_mem_innerBall hz
  have hφ : ContDiff ℝ ∞ (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
    (explicitRadialKernel_contDiff R hR j).comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) :=
    (explicitRadialKernel_hasCompactSupport R hR j).comp_homeomorph (Homeomorph.subRight z)
  have hφK : tsupport (fun x => explicitRadialKernel (n := n) R hR j (x - z)) ⊆ K :=
    (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
      ((closedBall_subset_closedBall (shrinkingBump_rOut_le (E := ComplexModel n) R hR j)).trans hzK)
  rw [← hg.levi _ hφ hφc (hφK.trans hKΩ) v]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.leviForm_comp_sub]
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · have hxr := dist_lt_of_notMem_closedBall hz hx j
    have h0 : leviForm (explicitRadialKernel (n := n) R hR j) (x - z) v = 0 := by
      simp only [leviForm, realHessian_explicitRadialKernel_sub_eq_zero R hR j hxr, add_zero,
        zero_div]
    rw [indicator_of_notMem hx, h0, mul_zero, mul_zero]

open ContactLocal in
/-- **Almost everywhere convergence of the mollified Levi forms** (Lebesgue differentiation). -/
theorem ae_tendsto_leviForm_mollified (hg : IsHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) (v : ComplexModel n) :
    ∀ᵐ z, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => leviForm (mollified g x₀ R hR j) z v) atTop (𝓝 (hermQuad (h z) v)) := by
  set K := closedBall x₀ (3 * R) with hKdef
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hint : LocallyIntegrable (K.indicator fun x => hermQuad (h x) v) volume :=
    ((hg.integrableOn_hermQuad (isCompact_closedBall _ _) hKΩ v).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  filter_upwards [ae_tendsto_translationPairing_explicitRadialKernel hint R hR] with z hz hz2
  have hzK : z ∈ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz2
  rw [indicator_of_mem hzK] at hz
  refine hz.congr' (Eventually.of_forall fun j => ?_)
  show _ = leviForm (mollified g x₀ R hR j) z v
  rw [leviForm_mollified_eq hg hR hball hz2 j v, integral_hermQuad_mul_kernel_eq hR hz2 j]

open ContactLocal in
/-- **Almost everywhere convergence of the mollified complex Hessians.** -/
theorem ae_tendsto_complexHessian_mollified (hg : IsHessianDensityOn g h Ω) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∀ᵐ z, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => complexHessian (mollified g x₀ R hR j) z) atTop (𝓝 (h z)) := by
  have hall : ∀ᵐ z, ∀ t : Fin n × Fin n × Fin 4, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => leviForm (mollified g x₀ R hR j) z (polVec t.1 t.2.1 t.2.2)) atTop
        (𝓝 (hermQuad (h z) (polVec t.1 t.2.1 t.2.2))) :=
    ae_all_iff.mpr fun t => ae_tendsto_leviForm_mollified hg hR hball _
  filter_upwards [hall] with z hz hz2
  have hfun : (fun j => complexHessian (mollified g x₀ R hR j) z) =
      fun j => polarize (leviForm (mollified g x₀ R hR j) z) := by
    funext j
    exact complexHessian_eq_polarize
      ((contDiff_mollified_of_continuousOn hg.continuousOn hR hball j).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  rw [hfun, ← polarize_hermQuad (hg.isHermitian z)]
  exact tendsto_polarize fun a b i => hz ⟨a, b, i⟩ hz2

end Mollifier

theorem ae_restrict_of_forall_mem_nhds_local {p : ComplexModel n → Prop}
    {W : Set (ComplexModel n)}
    (h : ∀ z ∈ W, ∃ N : Set (ComplexModel n), IsOpen N ∧ z ∈ N ∧ ∀ᵐ y ∂volume.restrict N, p y) :
    ∀ᵐ y ∂volume.restrict W, p y := by
  classical
  choose N hNo hzN hN using h
  set S : W → Set (ComplexModel n) := fun z => N z.1 z.2 with hS
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S fun z => hNo z.1 z.2
  have : Countable T := hTc.to_subtype
  have hWsub : W ⊆ ⋃ i : T, S i := by
    intro z hz
    have : z ∈ ⋃ i, S i := mem_iUnion.mpr ⟨⟨z, hz⟩, hzN z hz⟩
    rw [← hTU] at this
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp this
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  exact ae_restrict_of_ae_restrict_of_subset hWsub
    ((ae_restrict_iUnion_iff _ _).mpr fun i => hN i.1.1 i.1.2)

/-- An almost everywhere property on `U` may be checked on small balls. -/
theorem ae_of_forall_ball {p : ComplexModel n → Prop} (hU : IsOpen U)
    (hloc : ∀ z₀ ∈ U, ∀ R : ℝ, 0 < R → closedBall z₀ (4 * R) ⊆ U →
      ∀ᵐ z, z ∈ ball z₀ (2 * R) → p z) :
    ∀ᵐ z, z ∈ U → p z := by
  have h : ∀ᵐ z ∂volume.restrict U, p z := by
    refine ae_restrict_of_forall_mem_nhds_local fun z₀ hz₀ => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
    set R := ε / 5 with hR
    have hR0 : 0 < R := by positivity
    have hball : closedBall z₀ (4 * R) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
    refine ⟨ball z₀ (2 * R), isOpen_ball, mem_ball_self (by positivity), ?_⟩
    filter_upwards [ae_restrict_of_ae (hloc z₀ hz₀ R hR0 hball),
      ae_restrict_mem isOpen_ball.measurableSet] with z hz hzB
    exact hz hzB
  exact (ae_restrict_iff' hU.measurableSet).mp h

/-- **Densities are unique almost everywhere.** -/
theorem ae_eq (hg : IsHessianDensityOn g h U) (hg' : IsHessianDensityOn g h' U) :
    ∀ᵐ z, z ∈ U → h z = h' z := by
  refine ae_of_forall_ball hg.isOpen fun z₀ _ R hR hball => ?_
  let Ω : Opens (ComplexModel n) := ⟨U, hg.isOpen⟩
  have h1 := ae_tendsto_complexHessian_mollified (Ω := Ω) hg hR hball
  have h2 := ae_tendsto_complexHessian_mollified (Ω := Ω) hg' hR hball
  filter_upwards [h1, h2] with z hz1 hz2 hzB
  exact tendsto_nhds_unique (hz1 hzB) (hz2 hzB)

/-- `0` is locally bounded and plurisubharmonic. -/
theorem isLocallyBoundedPshOn_zero (Ω : Opens (ComplexModel n)) :
    IsLocallyBoundedPshOn Ω (fun _ => (0 : ℝ)) := by
  refine ⟨?_, fun z hz => ⟨Ω, hz, le_rfl, 0, fun w _ => by simp⟩⟩
  exact fun x _ => plurisubharmonicAt_const ((0 : ℝ) : EReal) (EReal.coe_ne_top 0) x

open ContactLocal in
theorem mollified_zero (x₀ : ComplexModel n) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    mollified (fun _ => (0 : ℝ)) x₀ R hR j = fun _ => 0 := by
  funext z
  simp [mollified, translationPairing]

/-- **Second-order vanishing kills the density** (the Lebesgue-point form of Stampacchia's lemma).
If `g ≥ 0` on `U` has the density `h`, then `h z = 0` at almost every `z ∈ U` with `g z = 0` at
which `g` vanishes to second order: `g(z + y) = o(‖y‖²)`. -/
theorem ae_eq_zero_of_isLittleO (hg : IsHessianDensityOn g h U) (hg0 : ∀ z ∈ U, 0 ≤ g z) :
    ∀ᵐ z, z ∈ U → g z = 0 → (fun y => g (z + y)) =o[𝓝 0] (fun y => ‖y‖ ^ 2) → h z = 0 := by
  refine ae_of_forall_ball hg.isOpen fun z₀ _ R hR hball => ?_
  let Ω : Opens (ComplexModel n) := ⟨U, hg.isOpen⟩
  have hall : ∀ᵐ z, ∀ v : ComplexModel n × Fin n × Fin n × Fin 4, z ∈ ball z₀ (2 * R) →
      Tendsto (fun j => leviForm (ContactLocal.mollified g z₀ R hR j) z
        (polVec v.2.1 v.2.2.1 v.2.2.2)) atTop
        (𝓝 (hermQuad (h z) (polVec v.2.1 v.2.2.1 v.2.2.2))) := by
    have : ∀ᵐ z, ∀ t : Fin n × Fin n × Fin 4, z ∈ ball z₀ (2 * R) →
        Tendsto (fun j => leviForm (ContactLocal.mollified g z₀ R hR j) z (polVec t.1 t.2.1 t.2.2))
          atTop (𝓝 (hermQuad (h z) (polVec t.1 t.2.1 t.2.2))) :=
      ae_all_iff.mpr fun t => ae_tendsto_leviForm_mollified (Ω := Ω) hg hR hball _
    filter_upwards [this] with z hz v hzB
    exact hz ⟨v.2.1, v.2.2.1, v.2.2.2⟩ hzB
  filter_upwards [hall] with z hz hzB hgz hlo
  -- flatness of `g` at `z`
  have hflat : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ x in closedBall z r, ENNReal.ofReal (g x - (fun _ => (0 : ℝ)) x) ≤
        ENNReal.ofReal (ε * r ^ 2) * volume (closedBall z r) := by
    intro ε hε
    have hev := hlo.def hε
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp hev
    refine Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun r hr => ?_
    have hr0 : 0 < r := hr.1
    calc ∫⁻ x in closedBall z r, ENNReal.ofReal (g x - (fun _ => (0 : ℝ)) x)
        ≤ ∫⁻ _x in closedBall z r, ENNReal.ofReal (ε * r ^ 2) := by
          refine setLIntegral_mono measurable_const fun x hx => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hxz : dist (x - z) 0 < δ := by
            rw [dist_zero_right, ← dist_eq_norm]
            exact lt_of_le_of_lt (mem_closedBall.mp hx) hr.2
          have hb := hδb hxz
          simp only [add_sub_cancel, Real.norm_eq_abs, norm_pow, abs_norm] at hb
          have hxr : ‖x - z‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
          have hsq : ‖x - z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
          simp only [sub_zero]
          calc g x ≤ |g x| := le_abs_self _
            _ ≤ ε * ‖x - z‖ ^ 2 := hb
            _ ≤ ε * r ^ 2 := mul_le_mul_of_nonneg_left hsq hε.le
      _ = ENNReal.ofReal (ε * r ^ 2) * volume (closedBall z r) := setLIntegral_const _ _
  have hlim : ∀ t : Fin n × Fin n × Fin 4, hermQuad (h z) (polVec t.1 t.2.1 t.2.2) = 0 := by
    intro t
    have hA := hz (0, t.1, t.2.1, t.2.2) hzB
    have h0 := tendsto_leviForm_mollified_of_flat (Ω := Ω) (isLocallyBoundedPshOn_zero Ω)
      hg.continuousOn hg0 hR hball hzB hflat (polVec t.1 t.2.1 t.2.2) hA
    have hzero : (fun j => leviForm (ContactLocal.mollified (fun _ => (0 : ℝ)) z₀ R hR j) z
        (polVec t.1 t.2.1 t.2.2)) = fun _ => 0 := by
      funext j
      rw [mollified_zero z₀ hR j]
      simp [leviForm, realHessian]
    rw [hzero] at h0
    exact tendsto_nhds_unique h0 tendsto_const_nhds
  rw [← polarize_hermQuad (hg.isHermitian z)]
  ext j k
  simp only [polarize]
  rw [hlim (j, k, 0), hlim (j, k, 1), hlim (j, k, 2), hlim (j, k, 3)]
  simp

/-- **The density of a plurisubharmonic function is semipositive almost everywhere.** -/
theorem ae_hermQuad_nonneg_of_psh (hg : IsHessianDensityOn g h U)
    (hpsh : IsLocallyBoundedPshOn ⟨U, hg.isOpen⟩ g) :
    ∀ᵐ z, z ∈ U → ∀ v, 0 ≤ hermQuad (h z) v := by
  refine ae_of_forall_ball hg.isOpen fun z₀ _ R hR hball => ?_
  let Ω : Opens (ComplexModel n) := ⟨U, hg.isOpen⟩
  have happ := (ContactLocal.isDecreasingApproximation_mollified (Ω := Ω) hpsh hR hball).1
  filter_upwards [ae_tendsto_complexHessian_mollified (Ω := Ω) hg hR hball] with z hz hzB v
  have hcont : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => hermQuad A v := by
    simp only [hermQuad, sesqForm]
    fun_prop
  have hlim := (hcont.tendsto _).comp (hz hzB)
  refine ge_of_tendsto' hlim fun j => ?_
  have hpsd := (happ j).2.2 z hzB
  simp only [Function.comp_apply]
  have hs : sesqForm (complexHessian (ContactLocal.mollified g z₀ R hR j) z) v v =
      star (fun i => star (v i)) ⬝ᵥ
        (complexHessian (ContactLocal.mollified g z₀ R hR j) z).mulVec (fun i => star (v i)) := by
    simp only [sesqForm, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hermQuad, hs]
  exact (Complex.nonneg_iff.mp (hpsd.dotProduct_mulVec_nonneg _)).1

end IsHessianDensityOn

end SGPT.Analysis.CZLp
