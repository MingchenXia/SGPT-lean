import SGPT.Okounkov.TranscendentalWNLegendreSchur
import SGPT.Okounkov.TranscendentalWNLegendreInverse
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smooth strictly convex functions of `log |τ|²` and their partial Legendre transforms

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:smooth-family` (the classical computation of
partial Legendre transforms, Kiselman 1978; WN21 Remark 3.4), in the form used by the proof of
WN21 Theorem 3.3 (`tok-wn-leg:smooth`).

Let `D ⊆ ℂᴺ` be open and `F : ℂᴺ × ℝ → ℝ` smooth on `D × ℝ` with `∂²F/∂y² > 0` and, for every
`z ∈ D`, `y ↦ ∂F/∂y (z, y)` a bijection `ℝ → (α, β)` (`IsSmoothLegendreData`).  Put
`u(z, τ) = F(z, log |τ|²)`.  Then:

* `legendreArg F z λ = Y(z, λ)` is the unique solution of `∂F/∂y (z, Y) = λ`; it is `C^∞` on
  `D × (α, β)` (`contDiffAt_legendreArg`, inverse function theorem for
  `(z, y) ↦ (z, ∂F/∂y (z, y))`).
* `legendreValue F z λ = F(z, Y) - λ Y` is `C^∞` on `D × (α, β)`, and it is the partial Legendre
  transform `û_λ(z) = inf_y (F(z, y) - λ y)` (file `TranscendentalWNLegendreSmooth`).
* Its real Hessian in `z` is the **Schur form** `F_{zz} - F_{zy} F_{yz} / F_{yy}` at `(z, Y(z, λ))`
  (`realHessian_legendreValue`), hence its complex Hessian is `schurMatrix F (z, Y(z, λ))`
  (`complexHessian_legendreValue`).

All derivatives are TN's genuine Fréchet derivatives (`realHessian`, `complexHessian`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {N : ℕ}

/-! ### Partial derivatives in the real variable -/

section Derivatives

variable {F : ComplexModel N × ℝ → ℝ}

/-- `∂F/∂y` on `ℂᴺ × ℝ`. -/
def partialY (F : ComplexModel N × ℝ → ℝ) (p : ComplexModel N × ℝ) : ℝ :=
  fderiv ℝ F p (0, 1)

/-- `∂²F/∂y²` on `ℂᴺ × ℝ`. -/
def partialYY (F : ComplexModel N × ℝ → ℝ) (p : ComplexModel N × ℝ) : ℝ :=
  realHessian F p (0, 1) (0, 1)

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

theorem hasFDerivAt_fderiv {p : ComplexModel N × ℝ} (hF : ContDiffAt ℝ 2 F p) :
    HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) p :=
  ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt

theorem hasFDerivAt_partialY {p : ComplexModel N × ℝ} (hF : ContDiffAt ℝ 2 F p) :
    HasFDerivAt (partialY F) ((fderiv ℝ (fderiv ℝ F) p).flip (0, 1)) p := by
  have h : HasFDerivAt (fun y => fderiv ℝ F y (0, 1))
      ((fderiv ℝ F p).comp 0 + (fderiv ℝ (fderiv ℝ F) p).flip (0, 1)) p :=
    (hasFDerivAt_fderiv hF).clm_apply (hasFDerivAt_const ((0, 1) : ComplexModel N × ℝ) p)
  exact h.congr_fderiv (by simp)

theorem fderiv_partialY_apply {p : ComplexModel N × ℝ} (hF : ContDiffAt ℝ 2 F p)
    (w : ComplexModel N × ℝ) :
    fderiv ℝ (partialY F) p w = realHessian F p w (0, 1) := by
  rw [(hasFDerivAt_partialY hF).fderiv, realHessian_eq_fderiv]
  rfl

theorem hasDerivAt_slice {z : ComplexModel N} {y : ℝ} (hF : ContDiffAt ℝ 2 F (z, y)) :
    HasDerivAt (fun t : ℝ => F (z, t)) (partialY F (z, y)) y := by
  have hpath : HasDerivAt (fun t : ℝ => ((z, t) : ComplexModel N × ℝ)) (0, 1) y :=
    (hasDerivAt_const y z).prodMk (hasDerivAt_id y)
  exact (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt y hpath

theorem hasDerivAt_partialY_slice {z : ComplexModel N} {y : ℝ} (hF : ContDiffAt ℝ 2 F (z, y)) :
    HasDerivAt (fun t : ℝ => partialY F (z, t)) (partialYY F (z, y)) y := by
  have hpath : HasDerivAt (fun t : ℝ => ((z, t) : ComplexModel N × ℝ)) (0, 1) y :=
    (hasDerivAt_const y z).prodMk (hasDerivAt_id y)
  have h : HasDerivAt (fun t : ℝ => partialY F (z, t))
      (((fderiv ℝ (fderiv ℝ F) (z, y)).flip (0, 1)) (0, 1)) y :=
    (hasFDerivAt_partialY hF).comp_hasDerivAt y hpath
  rw [partialYY, realHessian_eq_fderiv]
  exact h

/-- The second derivative is symmetric at `C²` points. -/
theorem realHessian_symm {p : ComplexModel N × ℝ} (hF : ContDiffAt ℝ 2 F p)
    (a b : ComplexModel N × ℝ) : realHessian F p a b = realHessian F p b a := by
  simpa only [realHessian_eq_fderiv] using hF.isSymmSndFDerivAt (by simp) a b

/-- Splitting `(v, s) = (v, 0) + s (0, 1)` in the first slot of the Hessian. -/
theorem realHessian_split_left (p : ComplexModel N × ℝ) (v : ComplexModel N) (s : ℝ)
    (b : ComplexModel N × ℝ) :
    realHessian F p (v, s) b = realHessian F p (v, 0) b + s * realHessian F p (0, 1) b := by
  have hv : ((v, s) : ComplexModel N × ℝ) = (v, 0) + s • ((0 : ComplexModel N), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, realHessian_eq_fderiv, realHessian_eq_fderiv, realHessian_eq_fderiv, map_add,
    map_smul]
  simp

/-- `C²` real-Hessian of a composition with a continuous linear map. -/
theorem realHessian_comp_clm {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → ℝ} (A : G →L[ℝ] E) {x : G}
    (hf : ContDiffAt ℝ 2 f (A x)) (a b : G) :
    realHessian (fun y => f (A y)) x a b = realHessian f (A x) (A a) (A b) := by
  rw [realHessian_eq_fderiv, realHessian_eq_fderiv]
  have hev : fderiv ℝ (fun y => f (A y)) =ᶠ[𝓝 x] fun y => (fderiv ℝ f (A y)).comp A := by
    have hc : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (A y) :=
      A.continuous.continuousAt.eventually (hf.eventually (by simp))
    filter_upwards [hc] with y hy
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp y A.hasFDerivAt).fderiv
  rw [hev.fderiv_eq]
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (A x)) (A x) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasFDerivAt (fun y => fderiv ℝ f (A y)) ((fderiv ℝ (fderiv ℝ f) (A x)).comp A) x :=
    hd.comp x A.hasFDerivAt
  have h2 : HasFDerivAt (fun y => (fderiv ℝ f (A y)).comp A)
      ((ContinuousLinearMap.compL ℝ G E ℝ (fderiv ℝ f (A x))).comp 0 +
        ((ContinuousLinearMap.compL ℝ G E ℝ).flip A).comp
          ((fderiv ℝ (fderiv ℝ f) (A x)).comp A)) x :=
    h1.clm_comp (hasFDerivAt_const A x)
  rw [h2.fderiv]
  simp

end Derivatives

/-! ### The data of the smooth case -/

/-- **The smooth case of `tok-wn-leg:smooth-family`**: `F` is smooth on `D × ℝ`, strictly convex
in `y`, and `∂F/∂y (z, ·)` is a bijection `ℝ → (α, β)` for every `z ∈ D`. -/
structure IsSmoothLegendreData (D : Set (ComplexModel N)) (F : ComplexModel N × ℝ → ℝ)
    (α β : ℝ) : Prop where
  isOpen : IsOpen D
  contDiffOn : ContDiffOn ℝ ∞ F (D ×ˢ univ)
  partialYY_pos : ∀ z ∈ D, ∀ y : ℝ, 0 < partialYY F (z, y)
  partialY_mem : ∀ z ∈ D, ∀ y : ℝ, partialY F (z, y) ∈ Ioo α β
  partialY_surj : ∀ z ∈ D, ∀ lam ∈ Ioo α β, ∃ y : ℝ, partialY F (z, y) = lam

open Classical in
/-- The solution `Y(z, λ)` of `∂F/∂y (z, Y) = λ` (junk value `0` if there is none). -/
def legendreArg (F : ComplexModel N × ℝ → ℝ) (z : ComplexModel N) (lam : ℝ) : ℝ :=
  if hy : ∃ y : ℝ, partialY F (z, y) = lam then hy.choose else 0

/-- `F(z, Y(z, λ)) - λ Y(z, λ)`, the partial Legendre transform in the smooth case. -/
def legendreValue (F : ComplexModel N × ℝ → ℝ) (z : ComplexModel N) (lam : ℝ) : ℝ :=
  F (z, legendreArg F z lam) - lam * legendreArg F z lam

namespace IsSmoothLegendreData

variable {D : Set (ComplexModel N)} {F : ComplexModel N × ℝ → ℝ} {α β : ℝ}
  (h : IsSmoothLegendreData D F α β)
include h

theorem isOpen_prod : IsOpen (D ×ˢ (univ : Set ℝ)) := h.isOpen.prod isOpen_univ

theorem contDiffAt {z : ComplexModel N} (hz : z ∈ D) (y : ℝ) : ContDiffAt ℝ ∞ F (z, y) :=
  h.contDiffOn.contDiffAt (h.isOpen_prod.mem_nhds ⟨hz, mem_univ y⟩)

theorem contDiffAt_two {z : ComplexModel N} (hz : z ∈ D) (y : ℝ) : ContDiffAt ℝ 2 F (z, y) :=
  (h.contDiffAt hz y).of_le two_le_infty

theorem contDiffOn_partialY : ContDiffOn ℝ ∞ (partialY F) (D ×ˢ univ) := by
  have hd := h.contDiffOn.fderiv_of_isOpen h.isOpen_prod (m := ∞) (by simp)
  exact hd.clm_apply contDiffOn_const

theorem strictMono_partialY {z : ComplexModel N} (hz : z ∈ D) :
    StrictMono fun y => partialY F (z, y) :=
  strictMono_of_hasDerivAt_pos (fun y => hasDerivAt_partialY_slice (h.contDiffAt_two hz y))
    (h.partialYY_pos z hz)

theorem partialY_legendreArg {z : ComplexModel N} (hz : z ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) : partialY F (z, legendreArg F z lam) = lam := by
  have hy := h.partialY_surj z hz lam hlam
  rw [legendreArg, dif_pos hy]
  exact hy.choose_spec

theorem legendreArg_eq {z : ComplexModel N} (hz : z ∈ D) {y lam : ℝ}
    (hy : partialY F (z, y) = lam) : legendreArg F z lam = y := by
  have hex : ∃ y, partialY F (z, y) = lam := ⟨y, hy⟩
  rw [legendreArg, dif_pos hex]
  exact (h.strictMono_partialY hz).injective (hex.choose_spec.trans hy.symm)

theorem legendreArg_partialY {z : ComplexModel N} (hz : z ∈ D) (y : ℝ) :
    legendreArg F z (partialY F (z, y)) = y :=
  h.legendreArg_eq hz rfl

/-- **`Y` is smooth** (inverse function theorem for `(z, y) ↦ (z, ∂F/∂y (z, y))`). -/
theorem contDiffAt_legendreArg {z₀ : ComplexModel N} (hz₀ : z₀ ∈ D) {lam₀ : ℝ}
    (hlam₀ : lam₀ ∈ Ioo α β) :
    ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℝ => legendreArg F q.1 q.2) (z₀, lam₀) := by
  set y₀ := legendreArg F z₀ lam₀ with hy₀
  set p₀ : ComplexModel N × ℝ := (z₀, y₀) with hp₀_def
  have hp₀ : ContDiffAt ℝ 2 F p₀ := h.contDiffAt_two hz₀ y₀
  let Ψ : ComplexModel N × ℝ → ComplexModel N × ℝ := fun p => (p.1, partialY F p)
  have hΨs : ContDiffAt ℝ ∞ Ψ p₀ :=
    contDiffAt_fst.prodMk
      (h.contDiffOn_partialY.contDiffAt (h.isOpen_prod.mem_nhds ⟨hz₀, mem_univ _⟩))
  set L : ComplexModel N × ℝ →L[ℝ] ℝ := (fderiv ℝ (fderiv ℝ F) p₀).flip (0, 1) with hL
  set c : ℝ := L (0, 1) with hc_def
  have hc : 0 < c := by
    have := h.partialYY_pos z₀ hz₀ y₀
    rw [partialYY, realHessian_eq_fderiv] at this
    exact this
  have hsplit : ∀ v : ComplexModel N × ℝ, L v = L (v.1, 0) + v.2 * c := by
    intro v
    have hv : v = (v.1, 0) + v.2 • ((0 : ComplexModel N), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, smul_eq_mul]
  let fwd : (ComplexModel N × ℝ) →L[ℝ] (ComplexModel N × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ComplexModel N) ℝ).prod L
  let bwd : (ComplexModel N × ℝ) →L[ℝ] (ComplexModel N × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ComplexModel N) ℝ).prod
      (c⁻¹ • (ContinuousLinearMap.snd ℝ (ComplexModel N) ℝ -
        L.comp ((ContinuousLinearMap.inl ℝ (ComplexModel N) ℝ).comp
          (ContinuousLinearMap.fst ℝ (ComplexModel N) ℝ))))
  have hleft : Function.LeftInverse bwd fwd := by
    intro v
    have h1 := hsplit v
    ext
    · simp [fwd, bwd]
    · simp only [fwd, bwd, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        smul_apply, sub_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul]
      rw [h1]
      field_simp
      ring
  have hright : Function.RightInverse bwd fwd := by
    intro v
    have h1 := hsplit (bwd v)
    ext
    · simp [fwd, bwd]
    · simp only [fwd, ContinuousLinearMap.prod_apply]
      rw [h1]
      simp only [bwd, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        smul_apply, sub_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul]
      field_simp
      ring
  let Ψ' : (ComplexModel N × ℝ) ≃L[ℝ] (ComplexModel N × ℝ) :=
    ContinuousLinearEquiv.equivOfInverse fwd bwd hleft hright
  have hΨ' : HasFDerivAt Ψ (Ψ' : (ComplexModel N × ℝ) →L[ℝ] (ComplexModel N × ℝ)) p₀ :=
    (hasFDerivAt_fst).prodMk (hasFDerivAt_partialY hp₀)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hg := hΨs.to_localInverse hΨ' hn
  have hΨp₀ : Ψ p₀ = (z₀, lam₀) := by
    simp only [Ψ, hp₀_def, hy₀, h.partialY_legendreArg hz₀ hlam₀]
  set T := hΨs.toOpenPartialHomeomorph Ψ hΨ' hn with hT
  have htarget : T.target ∈ 𝓝 (z₀, lam₀) := by
    rw [← hΨp₀]
    exact T.open_target.mem_nhds (hΨs.image_mem_toOpenPartialHomeomorph_target hΨ' hn)
  have heq : (fun q : ComplexModel N × ℝ => legendreArg F q.1 q.2) =ᶠ[𝓝 (z₀, lam₀)]
      fun q => (hΨs.localInverse hΨ' hn q).2 := by
    have hDn : (D ×ˢ Ioo α β) ∈ 𝓝 (z₀, lam₀) :=
      (h.isOpen.prod isOpen_Ioo).mem_nhds ⟨hz₀, hlam₀⟩
    filter_upwards [htarget, hDn] with q hqT hqD
    have hr : Ψ (T.symm q) = q := by
      have := T.right_inv hqT
      rwa [hT, ContDiffAt.toOpenPartialHomeomorph_coe] at this
    have h1 : (T.symm q).1 = q.1 :=
      calc (T.symm q).1 = (Ψ (T.symm q)).1 := rfl
        _ = q.1 := by rw [hr]
    have h2 : partialY F (T.symm q) = q.2 :=
      calc partialY F (T.symm q) = (Ψ (T.symm q)).2 := rfl
        _ = q.2 := by rw [hr]
    have h3 : partialY F (q.1, (T.symm q).2) = q.2 := by
      rw [← h1]
      exact h2
    exact h.legendreArg_eq hqD.1 h3
  rw [← hΨp₀] at heq ⊢
  exact (contDiffAt_snd.comp _ hg).congr_of_eventuallyEq heq

theorem contDiffAt_legendreArg_slice {z₀ : ComplexModel N} (hz₀ : z₀ ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) : ContDiffAt ℝ ∞ (fun z => legendreArg F z lam) z₀ :=
  (h.contDiffAt_legendreArg hz₀ hlam).comp z₀ (contDiffAt_id.prodMk contDiffAt_const)

theorem contDiffAt_legendreValue {z₀ : ComplexModel N} (hz₀ : z₀ ∈ D) {lam₀ : ℝ}
    (hlam₀ : lam₀ ∈ Ioo α β) :
    ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℝ => legendreValue F q.1 q.2) (z₀, lam₀) := by
  have hY := h.contDiffAt_legendreArg hz₀ hlam₀
  have hF : ContDiffAt ℝ ∞ F (z₀, legendreArg F z₀ lam₀) := h.contDiffAt hz₀ _
  have h1 : ContDiffAt ℝ ∞ (fun q : ComplexModel N × ℝ => F (q.1, legendreArg F q.1 q.2))
      (z₀, lam₀) := hF.comp (z₀, lam₀) (contDiffAt_fst.prodMk hY)
  exact h1.sub (contDiffAt_snd.mul hY)

theorem contDiffOn_legendreValue_slice {lam : ℝ} (hlam : lam ∈ Ioo α β) :
    ContDiffOn ℝ ∞ (fun z => legendreValue F z lam) D := fun z hz =>
  ((h.contDiffAt_legendreValue hz hlam).comp z
    (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt

/-! ### The Hessian of the transform -/

/-- `∂Y/∂z` from `∂F/∂y (z, Y(z)) = λ`. -/
theorem fderiv_legendreArg_apply {z₀ : ComplexModel N} (hz₀ : z₀ ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) (v : ComplexModel N) :
    fderiv ℝ (fun z => legendreArg F z lam) z₀ v =
      -realHessian F (z₀, legendreArg F z₀ lam) (v, 0) (0, 1) /
        partialYY F (z₀, legendreArg F z₀ lam) := by
  set Y : ComplexModel N → ℝ := fun z => legendreArg F z lam with hYdef
  set p₀ : ComplexModel N × ℝ := (z₀, Y z₀) with hp₀
  have hY : HasFDerivAt Y (fderiv ℝ Y z₀) z₀ :=
    ((h.contDiffAt_legendreArg_slice hz₀ hlam).differentiableAt (by simp)).hasFDerivAt
  have hpath : HasFDerivAt (fun z => ((z, Y z) : ComplexModel N × ℝ))
      ((ContinuousLinearMap.id ℝ (ComplexModel N)).prod (fderiv ℝ Y z₀)) z₀ :=
    (hasFDerivAt_id z₀).prodMk hY
  have hcomp := (hasFDerivAt_partialY (h.contDiffAt_two hz₀ (Y z₀))).comp z₀ hpath
  have hconst : (fun z => partialY F (z, Y z)) =ᶠ[𝓝 z₀] fun _ => lam := by
    filter_upwards [h.isOpen.mem_nhds hz₀] with z hz
    exact h.partialY_legendreArg hz hlam
  have hzero : HasFDerivAt (fun z => partialY F (z, Y z)) (0 : ComplexModel N →L[ℝ] ℝ) z₀ :=
    (hasFDerivAt_const lam z₀).congr_of_eventuallyEq hconst
  have huniq := hcomp.unique hzero
  have hv := congrArg (fun T : ComplexModel N →L[ℝ] ℝ => T v) huniq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.flip_apply, zero_apply] at hv
  have hs := realHessian_split_left (F := F) p₀ v (fderiv ℝ Y z₀ v) (0, 1)
  rw [realHessian_eq_fderiv, realHessian_eq_fderiv, realHessian_eq_fderiv] at hs
  rw [hv] at hs
  have hc : 0 < partialYY F p₀ := h.partialYY_pos z₀ hz₀ _
  rw [partialYY, realHessian_eq_fderiv] at hc ⊢
  rw [realHessian_eq_fderiv]
  field_simp
  linarith

/-- `∂(F(z, Y) - λ Y)/∂z = ∂F/∂z (z, Y)`. -/
theorem hasFDerivAt_legendreValue_slice {z : ComplexModel N} (hz : z ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) :
    HasFDerivAt (fun z => legendreValue F z lam)
      ((fderiv ℝ F (z, legendreArg F z lam)).comp
        (ContinuousLinearMap.inl ℝ (ComplexModel N) ℝ)) z := by
  set Y : ComplexModel N → ℝ := fun z => legendreArg F z lam with hYdef
  have hY : HasFDerivAt Y (fderiv ℝ Y z) z :=
    ((h.contDiffAt_legendreArg_slice hz hlam).differentiableAt (by simp)).hasFDerivAt
  have hF : HasFDerivAt F (fderiv ℝ F (z, Y z)) (z, Y z) :=
    ((h.contDiffAt_two hz (Y z)).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasFDerivAt (fun z => F (z, Y z))
      ((fderiv ℝ F (z, Y z)).comp
        ((ContinuousLinearMap.id ℝ (ComplexModel N)).prod (fderiv ℝ Y z))) z :=
    hF.comp z ((hasFDerivAt_id z).prodMk hY)
  have h2 : HasFDerivAt (fun z => F (z, Y z) - lam * Y z)
      ((fderiv ℝ F (z, Y z)).comp
        ((ContinuousLinearMap.id ℝ (ComplexModel N)).prod (fderiv ℝ Y z)) -
          lam • fderiv ℝ Y z) z :=
    h1.sub (hY.const_mul lam)
  refine h2.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
    sub_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id',
    id_eq, smul_apply, smul_eq_mul]
  have hsplit : fderiv ℝ F (z, Y z) (v, fderiv ℝ Y z v) =
      fderiv ℝ F (z, Y z) (v, 0) + fderiv ℝ Y z v * partialY F (z, Y z) := by
    have hv : ((v, fderiv ℝ Y z v) : ComplexModel N × ℝ) =
        (v, 0) + fderiv ℝ Y z v • ((0 : ComplexModel N), (1 : ℝ)) := by ext <;> simp
    rw [hv, map_add, map_smul, smul_eq_mul, partialY]
  rw [hsplit, h.partialY_legendreArg hz hlam]
  ring

end IsSmoothLegendreData

/-- The **Schur form** `F_{zz}(v, v') - F_{zy}(v) F_{zy}(v') / F_{yy}` at `p`. -/
def schurForm (F : ComplexModel N × ℝ → ℝ) (p : ComplexModel N × ℝ) (v v' : ComplexModel N) : ℝ :=
  realHessian F p (v, 0) (v', 0) -
    realHessian F p (v, 0) (0, 1) * realHessian F p (v', 0) (0, 1) / partialYY F p

/-- The complex Hessian matrix of the Schur form (same formula as `complexHessian`). -/
def schurMatrix (F : ComplexModel N × ℝ → ℝ) (p : ComplexModel N × ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fun j k =>
  ((schurForm F p (coordinateVector j) (coordinateVector k) +
      schurForm F p (Complex.I • coordinateVector j) (Complex.I • coordinateVector k) : ℝ) :
      ℂ) / 4 +
    Complex.I * ((schurForm F p (coordinateVector j) (Complex.I • coordinateVector k) -
      schurForm F p (Complex.I • coordinateVector j) (coordinateVector k) : ℝ) : ℂ) / 4

namespace IsSmoothLegendreData

variable {D : Set (ComplexModel N)} {F : ComplexModel N × ℝ → ℝ} {α β : ℝ}
  (h : IsSmoothLegendreData D F α β)
include h

/-- **The real Hessian of the transform is the Schur form** (`tok-wn-leg:smooth-family`(3)). -/
theorem realHessian_legendreValue {z₀ : ComplexModel N} (hz₀ : z₀ ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) (v v' : ComplexModel N) :
    realHessian (fun z => legendreValue F z lam) z₀ v v' =
      schurForm F (z₀, legendreArg F z₀ lam) v v' := by
  set Y : ComplexModel N → ℝ := fun z => legendreArg F z lam with hYdef
  set p₀ : ComplexModel N × ℝ := (z₀, Y z₀) with hp₀
  rw [realHessian_eq_fderiv]
  have hfd : fderiv ℝ (fun z => legendreValue F z lam) =ᶠ[𝓝 z₀]
      fun z => (fderiv ℝ F (z, Y z)).comp (ContinuousLinearMap.inl ℝ (ComplexModel N) ℝ) := by
    filter_upwards [h.isOpen.mem_nhds hz₀] with z hz
    exact (h.hasFDerivAt_legendreValue_slice hz hlam).fderiv
  rw [hfd.fderiv_eq]
  have hY : HasFDerivAt Y (fderiv ℝ Y z₀) z₀ :=
    ((h.contDiffAt_legendreArg_slice hz₀ hlam).differentiableAt (by simp)).hasFDerivAt
  have hD : HasFDerivAt (fun z => fderiv ℝ F (z, Y z))
      ((fderiv ℝ (fderiv ℝ F) p₀).comp
        ((ContinuousLinearMap.id ℝ (ComplexModel N)).prod (fderiv ℝ Y z₀))) z₀ :=
    (hasFDerivAt_fderiv (h.contDiffAt_two hz₀ (Y z₀))).comp z₀
      ((hasFDerivAt_id z₀).prodMk hY)
  have hD2 : HasFDerivAt
      (fun z => (fderiv ℝ F (z, Y z)).comp (ContinuousLinearMap.inl ℝ (ComplexModel N) ℝ))
      ((ContinuousLinearMap.compL ℝ (ComplexModel N) (ComplexModel N × ℝ) ℝ
          (fderiv ℝ F (z₀, Y z₀))).comp 0 +
        ((ContinuousLinearMap.compL ℝ (ComplexModel N) (ComplexModel N × ℝ) ℝ).flip
          (ContinuousLinearMap.inl ℝ (ComplexModel N) ℝ)).comp
          ((fderiv ℝ (fderiv ℝ F) p₀).comp
            ((ContinuousLinearMap.id ℝ (ComplexModel N)).prod (fderiv ℝ Y z₀)))) z₀ :=
    hD.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inl ℝ (ComplexModel N) ℝ) z₀)
  rw [hD2.fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.inl_apply]
  have hs := realHessian_split_left (F := F) p₀ v (fderiv ℝ Y z₀ v) (v', 0)
  rw [realHessian_eq_fderiv, realHessian_eq_fderiv, realHessian_eq_fderiv] at hs
  rw [hs, h.fderiv_legendreArg_apply hz₀ hlam v]
  have hsym := realHessian_symm (h.contDiffAt_two hz₀ (Y z₀)) (0, 1) (v', 0)
  rw [realHessian_eq_fderiv, realHessian_eq_fderiv] at hsym
  rw [hsym, schurForm]
  simp only [realHessian_eq_fderiv]
  ring

theorem complexHessian_legendreValue {z₀ : ComplexModel N} (hz₀ : z₀ ∈ D) {lam : ℝ}
    (hlam : lam ∈ Ioo α β) :
    complexHessian (fun z => legendreValue F z lam) z₀ =
      schurMatrix F (z₀, legendreArg F z₀ lam) := by
  ext j k
  simp only [complexHessian, schurMatrix, h.realHessian_legendreValue hz₀ hlam]

end IsSmoothLegendreData

end SGPT.Okounkov.TranscendentalWN
