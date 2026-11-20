import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local Hölder regularity: maps of class `C^{k,r}` near a point

A map `u : E → F` is **of class `C^{k,r}` near `z`** (`HolderAt k r u z`) if it agrees on a
neighbourhood of `z` with an element of the whole-space Hölder space `C^{k,r}_b(E, F)`
(`BoundedContDiffHolderMap k r E F`).  This is the local notion used by the regularity bootstrap of
the Monge–Ampère equation (TN.4 B5, the proof of Yau's theorem, P2):
one derivative is gained at a time, and smoothness means `C^{k,r}` near every point for every `k`.

## Main results (`E` finite-dimensional, `r ≤ 1`)

* `holderAt_of_contDiffAt`: a map of class `C^{k+1}` near `z` is of class `C^{k,r}` near `z`;
  hence `HolderAt.of_le` (lowering `k`) and `holderAt_const`.
* `HolderAt.bilinear`, `HolderAt.clm`, `HolderAt.add`, `HolderAt.sub`, `HolderAt.sum`: the class is
  stable under continuous bilinear and linear operations.
* `HolderAt.derivative`: the derivative of a `C^{k+1,r}` germ is a `C^{k,r}` germ;
  `HolderAt.of_fderiv` (the converse): if `u` is differentiable near `z` and `u`, `Du` are `C^{k,r}`
  near `z`, then `u` is `C^{k+1,r}` near `z`; `HolderAt.fderiv_of_apply`: `Du` is `C^{k,r}` near `z`
  as soon as its values on a basis are.
* `HolderAt.comp_contDiff` (**Nemytskii**): if `w` is `C^{k,r}` near `z` and `G` is smooth, then
  `x ↦ G (x, w x)` is `C^{k,r}` near `z` (induction on `k` with the chain rule; the case `k = 0` by a
  cut-off of `G`, which makes it globally Lipschitz).
* `contDiffAt_infty_of_holderAt`: a map that is `C^{k,r}` near `z` for every `k` is smooth at `z`.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.HolderGerm

/-! ### Cut-offs -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth compactly supported cut-off, supported in a given neighbourhood of `z` and equal to
`1` near `z`. -/
theorem exists_cutoff_nhds {z : E} {U : Set E} (hU : U ∈ 𝓝 z) :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ U ∧
      θ =ᶠ[𝓝 z] fun _ => 1 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (interior_mem_nhds.mpr hU)
  have hK : closedBall z (ε / 2) ⊆ interior U :=
    (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨θ, hθs, hθc, hθU, hθ1⟩ :=
    exists_contDiff_eq_one_of_isCompact (isCompact_closedBall z (ε / 2)) isOpen_interior hK
  refine ⟨θ, hθs, hθc, hθU.trans interior_subset, ?_⟩
  filter_upwards [closedBall_mem_nhds z (half_pos hε)] with x hx using hθ1 x hx

/-- `θ • f` is smooth if `f` is smooth near every point of `tsupport θ`. -/
theorem contDiff_smul_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : WithTop ℕ∞} {θ : E → ℝ} {f : E → F} (hθ : ContDiff ℝ m θ)
    (hf : ∀ x ∈ tsupport θ, ContDiffAt ℝ m f x) : ContDiff ℝ m (fun x => θ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport θ
  · exact hθ.contDiffAt.smul (hf x hx)
  · have h0 : θ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

/-- A continuous compactly supported map is bounded. -/
theorem exists_norm_le_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F] {θ : E → F}
    (hθ : Continuous θ) (hc : HasCompactSupport θ) : ∃ C, 0 ≤ C ∧ ∀ x, ‖θ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hθ.bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- A `C¹` map with compact support is bounded and Lipschitz. -/
theorem exists_lipschitz_of_hasCompactSupport {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ K) ∧ ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K₀, hK₀⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨K₁, hK₁⟩ :=
    (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ 0)
  refine ⟨max K₀ K₁, hK₀0.trans (le_max_left _ _), fun x => (hK₀ x).trans (le_max_left _ _),
    fun x y => ?_⟩
  exact (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable one_ne_zero) z) (fun z _ => (hK₁ z).trans (le_max_right K₀ K₁))
    (mem_univ y) (mem_univ x)

end Cutoff

/-! ### The local class -/

section Def

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `u` is **of class `C^{k,r}` near `z`**: it agrees near `z` with an element of
`C^{k,r}_b(E, F)`. -/
def HolderAt (k : ℕ) (r : ℝ≥0) (u : E → F) (z : E) : Prop :=
  ∃ w : BoundedContDiffHolderMap k r E F, ⇑w =ᶠ[𝓝 z] u

variable {k : ℕ} {r : ℝ≥0} {u v : E → F} {z : E}

theorem HolderAt.congr (h : HolderAt k r u z) (huv : u =ᶠ[𝓝 z] v) : HolderAt k r v z := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, hw.trans huv⟩

theorem holderAt_congr (huv : u =ᶠ[𝓝 z] v) : HolderAt k r u z ↔ HolderAt k r v z :=
  ⟨fun h => h.congr huv, fun h => h.congr huv.symm⟩

theorem BoundedContDiffHolderMap.holderAt (w : BoundedContDiffHolderMap k r E F) (z : E) :
    HolderAt k r (⇑w) z :=
  ⟨w, EventuallyEq.rfl⟩

theorem HolderAt.contDiffAt (h : HolderAt k r u z) : ContDiffAt ℝ k u z := by
  obtain ⟨w, hw⟩ := h
  exact w.contDiff.contDiffAt.congr_of_eventuallyEq hw.symm

/-- The class is open: `C^{k,r}` near `z` implies `C^{k,r}` near every point close to `z`. -/
theorem HolderAt.eventually (h : HolderAt k r u z) : ∀ᶠ x in 𝓝 z, HolderAt k r u x := by
  obtain ⟨w, hw⟩ := h
  filter_upwards [hw.eventually_nhds] with x hx using ⟨w, hx⟩

theorem HolderAt.eventually_differentiableAt (h : HolderAt k r u z) (hk : 1 ≤ k) :
    ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ u x := by
  filter_upwards [h.eventually] with x hx
  exact hx.contDiffAt.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk)

theorem HolderAt.add (hu : HolderAt k r u z) (hv : HolderAt k r v z) :
    HolderAt k r (fun x => u x + v x) z := by
  obtain ⟨w₁, h₁⟩ := hu
  obtain ⟨w₂, h₂⟩ := hv
  refine ⟨w₁ + w₂, ?_⟩
  filter_upwards [h₁, h₂] with x e₁ e₂
  simp [e₁, e₂]

theorem HolderAt.sub (hu : HolderAt k r u z) (hv : HolderAt k r v z) :
    HolderAt k r (fun x => u x - v x) z := by
  obtain ⟨w₁, h₁⟩ := hu
  obtain ⟨w₂, h₂⟩ := hv
  refine ⟨w₁ - w₂, ?_⟩
  filter_upwards [h₁, h₂] with x e₁ e₂
  simp [e₁, e₂]

theorem HolderAt.const_smul (c : ℝ) (hu : HolderAt k r u z) :
    HolderAt k r (fun x => c • u x) z := by
  obtain ⟨w, h⟩ := hu
  refine ⟨c • w, ?_⟩
  filter_upwards [h] with x e
  simp [e]

theorem holderAt_zero : HolderAt k r (fun _ : E => (0 : F)) z :=
  ⟨0, EventuallyEq.rfl⟩

theorem HolderAt.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (h : ∀ i ∈ s, HolderAt k r (f i) z) : HolderAt k r (fun x => ∑ i ∈ s, f i x) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (holderAt_zero (k := k) (r := r) (z := z) (E := E) (F := F))
  | insert a s has ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp [Finset.sum_insert has]

/-- The class is stable under continuous bilinear maps (`r ≤ 1`). -/
theorem HolderAt.bilinear {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] (hr : r ≤ 1) (B : F₁ →L[ℝ] F₂ →L[ℝ] F)
    {f : E → F₁} {g : E → F₂} (hf : HolderAt k r f z) (hg : HolderAt k r g z) :
    HolderAt k r (fun x => B (f x) (g x)) z := by
  obtain ⟨w₁, h₁⟩ := hf
  obtain ⟨w₂, h₂⟩ := hg
  refine ⟨BoundedContDiffHolderMap.bilinear hr B w₁ w₂, ?_⟩
  filter_upwards [h₁, h₂] with x e₁ e₂
  simp [e₁, e₂]

theorem HolderAt.mul (hr : r ≤ 1) {f g : E → ℝ} (hf : HolderAt k r f z) (hg : HolderAt k r g z) :
    HolderAt k r (fun x => f x * g x) z :=
  hf.bilinear hr (ContinuousLinearMap.mul ℝ ℝ) hg

theorem HolderAt.smul (hr : r ≤ 1) {f : E → ℝ} (hf : HolderAt k r f z) (hu : HolderAt k r u z) :
    HolderAt k r (fun x => f x • u x) z :=
  hf.bilinear hr (ContinuousLinearMap.lsmul ℝ ℝ) hu

/-- The derivative of a `C^{k+1,r}` germ is a `C^{k,r}` germ. -/
theorem HolderAt.derivative (h : HolderAt (k + 1) r u z) : HolderAt k r (fderiv ℝ u) z := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.fderivMap, by rw [BoundedContDiffHolderMap.coe_fderivMap]; exact hw.fderiv⟩

end Def

/-! ### Results needing a finite-dimensional source -/

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {r : ℝ≥0} {u : E → F} {z : E}

/-- **A `C^{k+1}` germ is a `C^{k,r}` germ** (`r ≤ 1`): cut off and use that compactly supported
`C^{k+1}` maps lie in `C^{k,r}_b`. -/
theorem holderAt_of_contDiffAt (hr : r ≤ 1) (hu : ContDiffAt ℝ (k + 1 : ℕ) u z) :
    HolderAt k r u z := by
  have hev : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ (k + 1 : ℕ) u x := hu.eventually (by simp)
  obtain ⟨θ, hθs, hθc, hθU, hθ1⟩ := exists_cutoff_nhds hev
  have hf : ContDiff ℝ (k + 1 : ℕ) (fun x => θ x • u x) :=
    contDiff_smul_of_contDiffAt (hθs.of_le (by exact_mod_cast le_top)) fun x hx => hθU hx
  have hfc : HasCompactSupport (fun x => θ x • u x) := hθc.smul_right
  refine ⟨BoundedContDiffHolderMap.ofHasCompactSupport hr _ hf hfc, ?_⟩
  filter_upwards [hθ1] with x hx
  simp [hx]

theorem holderAt_const (hr : r ≤ 1) (c : F) : HolderAt k r (fun _ : E => c) z :=
  holderAt_of_contDiffAt hr contDiffAt_const

theorem HolderAt.of_succ (hr : r ≤ 1) (h : HolderAt (k + 1) r u z) : HolderAt k r u z :=
  holderAt_of_contDiffAt hr (by exact_mod_cast h.contDiffAt)

theorem HolderAt.of_le (hr : r ≤ 1) (h : HolderAt k r u z) {j : ℕ} (hjk : j ≤ k) :
    HolderAt j r u z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d with
  | zero => exact h
  | succ d ih => exact ih ((show j + (d + 1) = (j + d) + 1 by omega) ▸ h |>.of_succ hr)

/-- The class is stable under continuous linear maps (`r ≤ 1`). -/
theorem HolderAt.clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (hr : r ≤ 1)
    (L : F →L[ℝ] G) (hu : HolderAt k r u z) : HolderAt k r (fun x => L (u x)) z := by
  have h := (holderAt_const (k := k) (z := z) hr (1 : ℝ)).bilinear hr
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip L) hu
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp

/-- **Integration of a germ**: if `u` is differentiable near `z` and `u`, `Du` are `C^{k,r}` near
`z`, then `u` is `C^{k+1,r}` near `z` (`r ≤ 1`).  With a cut-off `θ = 1` near `z`,
`D(θ u) = θ Du + Dθ ⊗ u` lies in `C^{k,r}_b`. -/
theorem HolderAt.of_fderiv (hr : r ≤ 1) (hu : HolderAt k r u z)
    (hdu : HolderAt k r (fderiv ℝ u) z) (hdiff : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ u x) :
    HolderAt (k + 1) r u z := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨G, hG⟩ := hdu
  have hev : ∀ᶠ x in 𝓝 z, (⇑w =ᶠ[𝓝 x] u) ∧ (⇑G =ᶠ[𝓝 x] fderiv ℝ u) ∧
      DifferentiableAt ℝ u x :=
    hw.eventually_nhds.and (hG.eventually_nhds.and hdiff)
  obtain ⟨θ, hθs, hθc, hθU, hθ1⟩ := exists_cutoff_nhds hev
  have hθd : Differentiable ℝ θ := hθs.differentiable (by simp)
  set f : E → F := fun x => θ x • u x with hfdef
  set D : E → E →L[ℝ] F := fun x => θ x • G x + (fderiv ℝ θ x).smulRight (w x) with hDdef
  have key : ∀ x, HasFDerivAt f (D x) x := by
    intro x
    by_cases hx : x ∈ tsupport θ
    · obtain ⟨h1, h2, h3⟩ := hθU hx
      have h := (hθd x).hasFDerivAt.smul h3.hasFDerivAt
      rw [hDdef]
      simp only
      rw [h1.eq_of_nhds, h2.eq_of_nhds]
      exact h
    · have h0 : θ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have hθx : θ x = 0 := h0.eq_of_nhds
      have hDθ : fderiv ℝ θ x = 0 := by
        rw [h0.fderiv_eq]; exact fderiv_const_apply 0
      have hf0 : f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0] with y hy
        simp [hfdef, hy]
      have hD0 : D x = 0 := by simp [hDdef, hθx, hDθ]
      rw [hD0]
      exact (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq hf0
  have hfd : fderiv ℝ f = D := funext fun x => (key x).fderiv
  -- the derivative as an element of `C^{k,r}_b`
  set θ₁ : BoundedContDiffHolderMap k r E ℝ := BoundedContDiffHolderMap.ofHasCompactSupport hr θ
    (hθs.of_le (by exact_mod_cast le_top)) hθc
  set Dθ₁ : BoundedContDiffHolderMap k r E (E →L[ℝ] ℝ) :=
    BoundedContDiffHolderMap.ofHasCompactSupport hr (fderiv ℝ θ)
      (hθs.fderiv_right (m := (k + 1 : ℕ)) (by exact_mod_cast le_top)) (hθc.fderiv (𝕜 := ℝ))
  set Dtot : BoundedContDiffHolderMap k r E (E →L[ℝ] F) :=
    BoundedContDiffHolderMap.bilinear hr (ContinuousLinearMap.lsmul ℝ ℝ) θ₁ G +
      BoundedContDiffHolderMap.bilinear hr (ContinuousLinearMap.smulRightL ℝ E F) Dθ₁ w
  have hDtot : fderiv ℝ f = ⇑Dtot := by
    rw [hfd]
    funext x
    simp [Dtot, θ₁, Dθ₁, hDdef]
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_norm_le_of_hasCompactSupport hθs.continuous hθc
  have hfw : ∀ x, f x = θ x • w x := by
    intro x
    by_cases hx : x ∈ tsupport θ
    · simp only [hfdef, (hθU hx).1.eq_of_nhds]
    · simp [hfdef, image_eq_zero_of_notMem_tsupport hx]
  have hbd : ∀ x, ‖f x‖ ≤ Cθ * ‖w‖ := by
    intro x
    rw [hfw, norm_smul]
    exact mul_le_mul (hCθ x) (w.norm_apply_le x) (norm_nonneg _) hCθ0
  refine ⟨BoundedContDiffHolderMap.ofFDeriv f (fun x => (key x).differentiableAt) Dtot hDtot hbd,
    ?_⟩
  filter_upwards [hθ1] with x hx
  simp [hfdef, hx]

/-- `Du` is a `C^{k,r}` germ as soon as its values on a basis are. -/
theorem HolderAt.fderiv_of_apply (hr : r ≤ 1) {ι : Type*} [Fintype ι] (bs : Module.Basis ι ℝ E)
    (h : ∀ i, HolderAt k r (fun x => fderiv ℝ u x (bs i)) z) : HolderAt k r (fderiv ℝ u) z := by
  set c : ι → E →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (bs.coord i) with hc
  have hsum : HolderAt k r (fun x => ∑ i, ContinuousLinearMap.smulRightL ℝ E F (c i)
      (fderiv ℝ u x (bs i))) z :=
    HolderAt.sum _ fun i _ => (h i).clm hr (ContinuousLinearMap.smulRightL ℝ E F (c i))
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  ext v
  have hL : ∀ L : E →L[ℝ] F, L v = ∑ i, bs.repr v i • L (bs i) := fun L => by
    conv_lhs => rw [← bs.sum_repr v]
    rw [map_sum]
    simp_rw [map_smul]
  simp only [_root_.sum_apply, ContinuousLinearMap.smulRightL_apply_apply, hc]
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply]

/-- A map that is `C^{k,r}` near `z` for every `k` is smooth at `z`. -/
theorem contDiffAt_infty_of_holderAt (h : ∀ k, HolderAt k r u z) : ContDiffAt ℝ ∞ u z :=
  contDiffAt_infty.mpr fun k => (h k).contDiffAt

end FiniteDim

/-! ### Composition with a smooth map (Nemytskii) -/

section Nemytskii

universe w

variable {E F₁ : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] {r : ℝ≥0} {z : E}

/-- An element of `C^{0,r}_b` from a continuous bounded `r`-Hölder map. -/
def ofHolderWith {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (g : E → X)
    (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) {C : ℝ≥0} (hC : HolderWith C r g) :
    BoundedContDiffHolderMap 0 r E X where
  toFun := g
  contDiff' := contDiff_zero.mpr hg
  bounded' i hi := by
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact ⟨B, fun x => by rw [norm_iteratedFDeriv_zero]; exact hB x⟩
  memHolder' := by
    rw [iteratedFDeriv_zero_eq_comp]
    exact ⟨C, hC.comp_isometry (LinearIsometryEquiv.isometry _)⟩

/-- **Nemytskii**: if `w` is `C^{k,r}` near `z` (`r ≤ 1`) and `G` is smooth, then
`x ↦ G (x, w x)` is `C^{k,r}` near `z`. -/
theorem HolderAt.comp_contDiff (hr : r ≤ 1) {k : ℕ} {w : E → F₁}
    (hw : HolderAt k r w z) {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {G : E × F₁ → F₂} (hG : ContDiff ℝ ∞ G) : HolderAt k r (fun x => G (x, w x)) z := by
  induction k generalizing F₂ with
  | zero =>
    obtain ⟨w₀, hw₀⟩ := hw
    set R : ℝ := ‖w₀‖ with hR
    have hS : IsCompact (closedBall z 1 ×ˢ closedBall (0 : F₁) R) :=
      (isCompact_closedBall z 1).prod (isCompact_closedBall 0 R)
    obtain ⟨θ, hθs, hθc, -, hθ1⟩ :=
      exists_contDiff_eq_one_of_isCompact hS isOpen_univ (subset_univ _)
    set Ĝ : E × F₁ → F₂ := fun p => θ p • G p with hĜdef
    have hĜs : ContDiff ℝ ∞ Ĝ := hθs.smul hG
    have hĜc : HasCompactSupport Ĝ := hθc.smul_right
    obtain ⟨K, hK0, hKb, hKl⟩ :=
      exists_lipschitz_of_hasCompactSupport (hĜs.of_le (by exact_mod_cast le_top)) hĜc
    set g : E → F₂ := fun x => Ĝ (x, w₀ x) with hgdef
    have hgc : Continuous g := hĜs.continuous.comp (continuous_id.prodMk w₀.contDiff.continuous)
    -- `w₀` is `r`-Hölder
    have hw₀h : ∀ x y, dist (w₀ x) (w₀ y) ≤ 2 * ‖w₀‖ * dist x y ^ (r : ℝ) := by
      intro x y
      have h := (w₀.holderWith_iteratedFDeriv hr (le_refl 0)).dist_le x y
      rw [iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply, LinearIsometryEquiv.dist_map] at h
      simpa using h
    have hg1 : ∀ x y, dist (g x) (g y) ≤ K * (dist x y + 2 * ‖w₀‖ * dist x y ^ (r : ℝ)) := by
      intro x y
      rw [dist_eq_norm]
      refine (hKl _ _).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      rw [← dist_eq_norm, Prod.dist_eq]
      exact max_le (le_add_of_nonneg_right (by positivity)) (by linarith [hw₀h x y, dist_nonneg (x := x) (y := y)])
    have hg2 : ∀ x y, dist (g x) (g y) ≤ 2 * K := fun x y => by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hKb (x, w₀ x), hKb (y, w₀ y)])
    set C : ℝ := K * (1 + 2 * ‖w₀‖) + 2 * K with hCdef
    have hC0 : 0 ≤ C := by positivity
    have hHol : HolderWith C.toNNReal r g := by
      refine HolderWith.of_dist_le fun x y => ?_
      rw [Real.coe_toNNReal _ hC0]
      have hd := dist_nonneg (x := x) (y := y)
      have hp0 : 0 ≤ dist x y ^ (r : ℝ) := Real.rpow_nonneg hd _
      rcases le_total (dist x y) 1 with h1 | h1
      · have hle : dist x y ≤ dist x y ^ (r : ℝ) :=
          Real.self_le_rpow_of_le_one hd h1 (by exact_mod_cast hr)
        calc dist (g x) (g y) ≤ K * (dist x y + 2 * ‖w₀‖ * dist x y ^ (r : ℝ)) := hg1 x y
          _ ≤ K * (dist x y ^ (r : ℝ) + 2 * ‖w₀‖ * dist x y ^ (r : ℝ)) := by gcongr
          _ ≤ C * dist x y ^ (r : ℝ) := by
              rw [hCdef]; nlinarith [norm_nonneg w₀]
      · have hge : 1 ≤ dist x y ^ (r : ℝ) := Real.one_le_rpow h1 r.coe_nonneg
        calc dist (g x) (g y) ≤ 2 * K := hg2 x y
          _ ≤ 2 * K * dist x y ^ (r : ℝ) := le_mul_of_one_le_right (by positivity) hge
          _ ≤ C * dist x y ^ (r : ℝ) := by
              rw [hCdef]; nlinarith [norm_nonneg w₀, mul_nonneg hK0 (norm_nonneg w₀)]
    refine ⟨ofHolderWith g hgc (fun x => hKb (x, w₀ x)) hHol, ?_⟩
    filter_upwards [hw₀, ball_mem_nhds z one_pos] with x hx hxb
    show θ (x, w₀ x) • G (x, w₀ x) = G (x, w x)
    have hmem : (x, w₀ x) ∈ closedBall z 1 ×ˢ closedBall (0 : F₁) R :=
      ⟨ball_subset_closedBall hxb, by
        rw [mem_closedBall, dist_zero_right]; exact w₀.norm_apply_le x⟩
    rw [hθ1 _ hmem, one_smul, hx]
  | succ k ih =>
    have hw' : HolderAt k r w z := hw.of_succ hr
    have h0 : HolderAt k r (fun x => G (x, w x)) z := ih hw' hG
    have hD : HolderAt k r (fun x => fderiv ℝ G (x, w x)) z :=
      ih hw' (hG.fderiv_right (m := ∞) le_rfl)
    have hDw : HolderAt k r (fderiv ℝ w) z := hw.derivative
    set L₁ : (E × F₁ →L[ℝ] F₂) →L[ℝ] (E →L[ℝ] F₂) :=
      (ContinuousLinearMap.compL ℝ E (E × F₁) F₂).flip (ContinuousLinearMap.inl ℝ E F₁) with hL₁
    set B₂ : (E × F₁ →L[ℝ] F₂) →L[ℝ] (E →L[ℝ] F₁) →L[ℝ] (E →L[ℝ] F₂) :=
      (ContinuousLinearMap.compL ℝ E (E × F₁) F₂).bilinearComp (ContinuousLinearMap.id ℝ _)
        (ContinuousLinearMap.compL ℝ E F₁ (E × F₁) (ContinuousLinearMap.inr ℝ E F₁)) with hB₂
    have hsum : HolderAt k r (fun x => L₁ (fderiv ℝ G (x, w x)) +
        B₂ (fderiv ℝ G (x, w x)) (fderiv ℝ w x)) z :=
      (hD.clm hr L₁).add (hD.bilinear hr B₂ hDw)
    have hdiff : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ w x := hw.eventually_differentiableAt (by omega)
    have hGd : Differentiable ℝ G := hG.differentiable (by simp)
    have hfd : ∀ᶠ x in 𝓝 z, L₁ (fderiv ℝ G (x, w x)) + B₂ (fderiv ℝ G (x, w x)) (fderiv ℝ w x) =
        fderiv ℝ (fun x => G (x, w x)) x := by
      filter_upwards [hdiff] with x hx
      have hc := (hGd (x, w x)).hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hx.hasFDerivAt)
      rw [show (fun x => G (x, w x)) = G ∘ fun x => (id x, w x) from rfl, hc.fderiv]
      ext v
      simp only [hL₁, hB₂, _root_.add_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply,
        ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.prod_apply]
      rw [← map_add]
      simp
    refine h0.of_fderiv hr (hsum.congr hfd) ?_
    filter_upwards [hdiff] with x hx
    exact (hGd (x, w x)).comp x (differentiableAt_id.prodMk hx)

end Nemytskii

/-! ### Charts of a Hölder atlas -/

section Manifold

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {k : ℕ} {r : ℝ≥0} {F : Type}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map of `C^{k,r}(M)` is `C^{k,r}` near every point of every chart target. -/
theorem holderAt_comp_symm (hr : r ≤ 1) (u : A.HolderMap k r F) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    HolderAt k r (fun x => u (e.val.symm x)) z := by
  obtain ⟨σ, hσs, hσc, hσt, hσ1⟩ := exists_cutoff_nhds (e.val.open_target.mem_nhds hz)
  obtain ⟨C, hC⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (F := F) hr e
    (hσs.of_le (by exact_mod_cast le_top)) hσc hσt
  obtain ⟨h, hh, -⟩ := hC u
  refine ⟨h, ?_⟩
  filter_upwards [hσ1] with x hx
  rw [hh, hx, one_smul]

end Manifold

end SGPT.Foundations.Analysis.Pending.HolderGerm
