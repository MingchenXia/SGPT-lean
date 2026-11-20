import SGPT.PSH.BookHermitianLineForms
import SGPT.PSH.BookMultiplierSections
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Hermitian metrics on holomorphic line bundles and their first Chern forms

Source: `def:Hermmetric` of the chapter *Plurisubharmonic functions*. A *Hermitian metric* `h` on
a holomorphic line bundle `L → X` is a family of Hermitian forms `h_x` on the fibres `L_x`
(`def:pshfunctions:L1743`) such that `x ↦ |s(x)|²_{h_x}` is smooth for every local holomorphic
section `s`. Its first Chern form `ddᶜh = c₁(L,h)` is the closed real `(1,1)`-form with

`(ddᶜh)|_U = ddᶜ(-log |s|²_h)`

on every open `U` carrying a nowhere vanishing holomorphic section `s`.

The holomorphic line bundle is a Mathlib vector bundle with model fibre `ℂ` and holomorphic
(complex-smooth) coordinate changes over a complex manifold of the SGPT.Foundations.Analysis native
atlas; local holomorphic sections are holomorphic maps into the total space. The Chern form is a
genuine `ClosedRealOneOneForm` (`firstChernForm`), constructed from the trivialization frames;
`isFirstChernForm_firstChernForm` proves the defining local identity for EVERY nowhere vanishing
holomorphic section, and `IsFirstChernForm.geometricallyEq` its uniqueness (on all chart
targets, which is the project's equality of forms). Frame independence is the pluriharmonicity of
`log |g|²` for holomorphic `g ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.LineBundleMetric

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (L : X → Type*) [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- `s` is a holomorphic section of `L` over `U`. -/
def IsHolomorphicSectionOn (s : (x : X) → L x) (U : Set X) : Prop :=
  MDifferentiableOn 𝓘(ℂ, ComplexModel n) (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ))
    (fun x => TotalSpace.mk' ℂ x (s x)) U

/-- A real function is smooth on `U` (in every holomorphic chart). -/
def ChartSmoothOn (f : X → ℝ) (U : Set X) : Prop :=
  ∀ e : ComplexChart n X,
    ContDiffOn ℝ ∞ (fun z => f (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)

/-- `def:Hermmetric`. A Hermitian metric on the holomorphic line bundle `L`: a Hermitian form
`h_x` on every fibre `L_x` such that `x ↦ |s(x)|²_{h_x}` is smooth for every local holomorphic
section `s`. -/
structure HermitianMetric where
  /-- The Hermitian form `h_x` on `L_x`. -/
  form : (x : X) → HermitianForm (L x)
  /-- `x ↦ |s(x)|²_{h_x}` is smooth for every local holomorphic section. -/
  smooth : ∀ (s : (x : X) → L x) (U : Set X), IsOpen U → IsHolomorphicSectionOn (n := n) L s U →
    ChartSmoothOn (n := n) (fun x => (form x).normSq (s x)) U

variable {L}

/-- The local weight `-log |s|²_h` in the coordinates of a chart. -/
def localWeight (h : HermitianMetric (n := n) L) (s : (x : X) → L x) (e : ComplexChart n X) :
    ComplexModel n → ℝ :=
  fun w => -Real.log ((h.form (e.val.symm w)).normSq (s (e.val.symm w)))

variable (L) in
/-- `def:Hermmetric`, the first Chern form: `θ = ddᶜh = c₁(L,h)` means that on every open `U`
with a nowhere vanishing holomorphic section `s`, `θ|_U = ddᶜ(-log |s|²_h)` (in every chart). -/
def IsFirstChernForm (h : HermitianMetric (n := n) L) (θ : ClosedRealOneOneForm n X) : Prop :=
  ∀ (s : (x : X) → L x) (U : Set X), IsOpen U → IsHolomorphicSectionOn (n := n) L s U →
    (∀ x ∈ U, s x ≠ 0) → ∀ (e : ComplexChart n X) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U → θ.val.coeff e z = smoothDDC (localWeight h s e) z

/-! ### Trivialization frames -/

variable (L) in
/-- The holomorphic frame `x ↦ e.symm x 1` of the trivialization at `p`. -/
def frame (p : X) : (x : X) → L x := fun x => (trivializationAt ℂ L p).symm x 1

variable (L) in
/-- The domain of the frame at `p`. -/
abbrev frameDomain (p : X) : Set X := (trivializationAt ℂ L p).baseSet

theorem isOpen_frameDomain (p : X) : IsOpen (frameDomain L p) :=
  (trivializationAt ℂ L p).open_baseSet

theorem mem_frameDomain (p : X) : p ∈ frameDomain L p :=
  FiberBundle.mem_baseSet_trivializationAt' p

theorem trivialization_frame {p x : X} (hx : x ∈ frameDomain L p) :
    ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (frame L p x))).2 = 1 := by
  simp only [frame, TotalSpace.mk']
  rw [(trivializationAt ℂ L p).apply_mk_symm hx]

theorem frame_ne_zero {p x : X} (hx : x ∈ frameDomain L p) : frame L p x ≠ 0 := by
  intro h0
  have h1 := trivialization_frame (L := L) hx
  rw [h0] at h1
  have : ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (0 : L x))).2 = 0 := by
    exact ((trivializationAt ℂ L p).continuousLinearEquivAt ℂ x hx).map_zero
  rw [this] at h1
  exact zero_ne_one h1

theorem frame_holomorphic (p : X) : IsHolomorphicSectionOn (n := n) L (frame L p) (frameDomain L p) := by
  rw [IsHolomorphicSectionOn, (trivializationAt ℂ L p).mdifferentiableOn_section_baseSet_iff]
  apply (mdifferentiableOn_const (c := (1 : ℂ))).congr
  intro x hx
  exact trivialization_frame (L := L) hx

/-- Every section over a frame domain is its trivialization coefficient times the frame. -/
theorem eq_coeff_smul_frame (p : X) (s : (x : X) → L x) {x : X} (hx : x ∈ frameDomain L p) :
    s x = ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (s x))).2 • frame L p x := by
  set t := trivializationAt ℂ L p
  have h1 : t.symm x ((t (TotalSpace.mk' ℂ x (s x))).2) = s x :=
    t.symm_apply_apply_mk hx (s x)
  have h2 : ∀ c : ℂ, t.symm x c = c • t.symm x 1 := by
    intro c
    rw [← t.symmL_apply (R := ℂ) hx c, ← t.symmL_apply (R := ℂ) hx 1, ← map_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [← h1]
  rw [h2]
  rfl

/-! ### Frame independence -/

theorem chartSmooth_localWeight (h : HermitianMetric (n := n) L) {s : (x : X) → L x} {U : Set X}
    (hU : IsOpen U) (hs : IsHolomorphicSectionOn (n := n) L s U) (hs0 : ∀ x ∈ U, s x ≠ 0)
    (e : ComplexChart n X) :
    ContDiffOn ℝ ∞ (localWeight h s e) (e.val.target ∩ e.val.symm ⁻¹' U) := by
  have hsm := h.smooth s U hU hs e
  refine (hsm.log ?_).neg
  intro z hz
  exact ((h.form _).normSq_pos (hs0 _ hz.2)).ne'

/-- **Frame independence.** For a nowhere vanishing holomorphic section `s` on `U` and the
trivialization frame at `p`, `ddᶜ(-log |s|²_h) = ddᶜ(-log |σ_p|²_h)` on the common domain. -/
theorem smoothDDC_localWeight_eq_frame (h : HermitianMetric (n := n) L) {s : (x : X) → L x} {U : Set X}
    (hU : IsOpen U) (hs : IsHolomorphicSectionOn (n := n) L s U) (hs0 : ∀ x ∈ U, s x ≠ 0) (p : X)
    (e : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzU : e.val.symm z ∈ U) (hzp : e.val.symm z ∈ frameDomain L p) :
    smoothDDC (localWeight h s e) z = smoothDDC (localWeight h (frame L p) e) z := by
  set W : Set X := U ∩ frameDomain L p with hWdef
  have hW : IsOpen W := hU.inter (isOpen_frameDomain p)
  set S : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' W with hSdef
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm hW
  have hzS : z ∈ S := ⟨hz, hzU, hzp⟩
  set g : X → ℂ := fun x => ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (s x))).2 with hgdef
  have hgW : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g W := by
    have := (trivializationAt ℂ L p).mdifferentiableOn_section_iff
      (IB := 𝓘(ℂ, ComplexModel n)) (s := s) hW inter_subset_right
    exact this.mp (hs.mono inter_subset_left)
  have hg0 : ∀ x ∈ W, g x ≠ 0 := by
    intro x hx h0
    have := eq_coeff_smul_frame (L := L) p s hx.2
    have h0' : ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (s x))).2 = 0 := h0
    rw [h0', zero_smul] at this
    exact hs0 x hx.1 this
  -- the two smooth weights and the holomorphic transition coefficient in the chart
  set U₁ : ComplexModel n → ℝ := fun w => (h.form (e.val.symm w)).normSq (frame L p (e.val.symm w))
  set U₂ : ComplexModel n → ℝ := fun w => (h.form (e.val.symm w)).normSq (s (e.val.symm w))
  have hU₁ : ContDiffOn ℝ ∞ U₁ S :=
    (h.smooth _ _ (isOpen_frameDomain p) (frame_holomorphic p) e).mono
      fun w hw => ⟨hw.1, hw.2.2⟩
  have hU₂ : ContDiffOn ℝ ∞ U₂ S :=
    (h.smooth _ _ hU hs e).mono fun w hw => ⟨hw.1, hw.2.1⟩
  have hpos₁ : ∀ w ∈ S, 0 < U₁ w := fun w hw => (h.form _).normSq_pos (frame_ne_zero hw.2.2)
  have hpos₂ : ∀ w ∈ S, 0 < U₂ w := fun w hw => (h.form _).normSq_pos (hs0 _ hw.2.1)
  have hh₁ : DifferentiableOn ℂ (fun w => g (e.val.symm w)) S := by
    intro w hw
    exact (differentiableAt_comp_chart_symm e hw.1
      ((hgW _ hw.2).mdifferentiableAt (hW.mem_nhds hw.2))).differentiableWithinAt
  have hh₂ : DifferentiableOn ℂ (fun _ : ComplexModel n => (1 : ℂ)) S :=
    differentiableOn_const 1
  have heq : ∀ w ∈ S, Complex.normSq (g (e.val.symm w)) * U₁ w =
      Complex.normSq ((fun _ : ComplexModel n => (1 : ℂ)) w) * U₂ w := by
    intro w hw
    simp only [U₁, U₂, map_one, one_mul]
    rw [eq_coeff_smul_frame (L := L) p s hw.2.2, HermitianForm.normSq_smul,
      Complex.normSq_eq_norm_sq]
  have hdense : S ⊆ closure {w | w ∈ S ∧ g (e.val.symm w) ≠ 0} :=
    fun w hw => subset_closure ⟨hw, hg0 _ hw.2⟩
  have hkey := Pending.LogWeightFactorization.smoothDDC_log_eq_of_normSq_mul_eq hS hU₁ hU₂
    hpos₁ hpos₂ hh₁ hh₂ heq hdense hzS
  have hl₁ : ContDiffOn ℝ ∞ (fun w => Real.log (U₁ w)) S :=
    hU₁.log fun w hw => (hpos₁ w hw).ne'
  have hl₂ : ContDiffOn ℝ ∞ (fun w => Real.log (U₂ w)) S :=
    hU₂.log fun w hw => (hpos₂ w hw).ne'
  change smoothDDC (fun w => -Real.log (U₂ w)) z = smoothDDC (fun w => -Real.log (U₁ w)) z
  rw [smoothDDC_neg hS hl₂ hzS, smoothDDC_neg hS hl₁ hzS, hkey]

/-! ### Construction of the first Chern form -/

/-- The coefficient of `c₁(L,h)` in a chart, computed with the frame at the point. -/
def chernCoeff (h : HermitianMetric (n := n) L) (e : ComplexChart n X) (z : ComplexModel n) :
    (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ :=
  smoothDDC (localWeight h (frame L (e.val.symm z)) e) z

theorem chernCoeff_eq_of_mem (h : HermitianMetric (n := n) L) (e : ComplexChart n X) (p : X)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (hzp : e.val.symm z ∈ frameDomain L p) :
    chernCoeff h e z = smoothDDC (localWeight h (frame L p) e) z :=
  smoothDDC_localWeight_eq_frame h (isOpen_frameDomain _) (frame_holomorphic _)
    (fun _ hx => frame_ne_zero hx) p e hz (mem_frameDomain _) hzp

theorem chernCoeff_eventuallyEq (h : HermitianMetric (n := n) L) (e : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    chernCoeff h e =ᶠ[𝓝 z] smoothDDC (localWeight h (frame L (e.val.symm z)) e) := by
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' frameDomain L (e.val.symm z)) :=
    e.val.isOpen_inter_preimage_symm (isOpen_frameDomain _)
  filter_upwards [hS.mem_nhds ⟨hz, mem_frameDomain _⟩] with w hw
  exact chernCoeff_eq_of_mem h e _ hw.1 hw.2

theorem chernCoeff_contDiffOn (h : HermitianMetric (n := n) L) (e : ComplexChart n X) :
    ContDiffOn ℝ ∞ (chernCoeff h e) e.val.target := by
  apply contDiffOn_of_locally_contDiffOn
  intro z hz
  set p := e.val.symm z
  set S := e.val.target ∩ e.val.symm ⁻¹' frameDomain L p
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm (isOpen_frameDomain _)
  refine ⟨S, hS, ⟨hz, mem_frameDomain _⟩, ?_⟩
  have hsm : ContDiffOn ℝ ∞ (smoothDDC (localWeight h (frame L p) e)) S :=
    Pending.LogWeightFactorization.smoothDDC_contDiffOn hS
      (chartSmooth_localWeight h (isOpen_frameDomain _) (frame_holomorphic _)
        (fun _ hx => frame_ne_zero hx) e)
  refine (hsm.mono inter_subset_right).congr ?_
  intro w hw
  exact chernCoeff_eq_of_mem h e p hw.1 hw.2.2

theorem chernCoeff_compatible (h : HermitianMetric (n := n) L) (e f : ComplexChart n X)
    (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source) (v : Fin 2 → ComplexModel n) :
    chernCoeff h e z v =
      chernCoeff h f (chartTransition e f z) (fun i => chartTransitionDerivative e f z (v i)) := by
  set p := e.val.symm z
  have hzt : z ∈ e.val.target := hz.1
  have hpf : p ∈ f.val.source := hz.2
  have hτ : chartTransition e f z = f.val p := rfl
  have hfp : f.val.symm (chartTransition e f z) = p := by rw [hτ]; exact f.val.left_inv hpf
  have hτt : chartTransition e f z ∈ f.val.target := by rw [hτ]; exact f.val.map_source hpf
  rw [chernCoeff, chernCoeff, hfp]
  -- the chart expressions of the same frame are related by the transition map
  set ρ := localWeight h (frame L p) f
  set A := e.val.target ∩ e.val.symm ⁻¹' (f.val.source ∩ frameDomain L p) with hAdef
  set V := f.val.target ∩ f.val.symm ⁻¹' frameDomain L p with hVdef
  have hA : IsOpen A :=
    e.val.isOpen_inter_preimage_symm (f.val.open_source.inter (isOpen_frameDomain p))
  have hV : IsOpen V := f.val.isOpen_inter_preimage_symm (isOpen_frameDomain p)
  have hzA : z ∈ A := ⟨hzt, hpf, mem_frameDomain p⟩
  have hτC : ContDiffOn ℂ ∞ (chartTransition e f) A := by
    have h1 := HolomorphicMaps.coordinateMap_contDiffOn (f := (id : X → X)) contMDiff_id e f
    exact h1.mono fun w hw => ⟨hw.1, hw.2.1⟩
  have hρ : ContDiffOn ℝ ∞ ρ V :=
    chartSmooth_localWeight h (isOpen_frameDomain _) (frame_holomorphic _)
      (fun _ hx => frame_ne_zero hx) f
  have hmaps : MapsTo (chartTransition e f) A V := by
    intro w hw
    refine ⟨f.val.map_source hw.2.1, ?_⟩
    change f.val.symm (f.val (e.val.symm w)) ∈ frameDomain L p
    rw [f.val.left_inv hw.2.1]
    exact hw.2.2
  have hcomp := HolomorphicDDC.smoothDDC_comp hA hV hτC hρ hmaps hzA
  have hloc : localWeight h (frame L p) e =ᶠ[𝓝 z] fun y => ρ (chartTransition e f y) := by
    filter_upwards [hA.mem_nhds hzA] with y hy
    change -Real.log ((h.form (e.val.symm y)).normSq (frame L p (e.val.symm y))) =
      -Real.log ((h.form (f.val.symm (f.val (e.val.symm y)))).normSq
        (frame L p (f.val.symm (f.val (e.val.symm y)))))
    rw [f.val.left_inv hy.2.1]
  rw [smoothDDC_congr hloc, hcomp]
  rfl

/-- The first Chern form `c₁(L,h)` as a genuine smooth real two-form. -/
def chernSmoothForm (h : HermitianMetric (n := n) L) : SmoothRealForm n X 2 where
  coeff := chernCoeff h
  smooth := chernCoeff_contDiffOn h
  compatible := chernCoeff_compatible h

theorem chernSmoothForm_isClosed (h : HermitianMetric (n := n) L) :
    (chernSmoothForm h).IsClosed := by
  intro e z hz
  change extDeriv (chernCoeff h e) z = 0
  rw [(chernCoeff_eventuallyEq h e hz).extDeriv_eq]
  set S := e.val.target ∩ e.val.symm ⁻¹' frameDomain L (e.val.symm z)
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm (isOpen_frameDomain _)
  have hzS : z ∈ S := ⟨hz, mem_frameDomain _⟩
  have hsm := chartSmooth_localWeight h (isOpen_frameDomain (e.val.symm z))
    (frame_holomorphic (e.val.symm z)) (fun _ hx => frame_ne_zero hx) e
  have hdc : ContDiffAt ℝ ∞ (smoothDc (localWeight h (frame L (e.val.symm z)) e)) z :=
    ((smoothDc_contDiffOn hS hsm) z hzS).contDiffAt (hS.mem_nhds hzS)
  exact extDeriv_extDeriv_apply hdc
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem chernSmoothForm_isTypeOneOne (h : HermitianMetric (n := n) L) :
    (chernSmoothForm h).IsTypeOneOne := by
  intro e z hz u v
  set S := e.val.target ∩ e.val.symm ⁻¹' frameDomain L (e.val.symm z)
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm (isOpen_frameDomain _)
  have hzS : z ∈ S := ⟨hz, mem_frameDomain _⟩
  have hsm := chartSmooth_localWeight h (isOpen_frameDomain (e.val.symm z))
    (frame_holomorphic (e.val.symm z)) (fun _ hx => frame_ne_zero hx) e
  exact MongeAmpere.smoothDDC_isOneOne
    (((hsm z hzS).contDiffAt (hS.mem_nhds hzS)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) u v

/-- `def:Hermmetric`: the first Chern form `ddᶜh = c₁(L,h)`, a closed real `(1,1)`-form. -/
def firstChernForm (h : HermitianMetric (n := n) L) : ClosedRealOneOneForm n X :=
  ⟨chernSmoothForm h, chernSmoothForm_isClosed h, chernSmoothForm_isTypeOneOne h⟩

/-- `c₁(L,h)` satisfies the defining identity `c₁(L,h)|_U = ddᶜ(-log |s|²_h)` for every nowhere
vanishing holomorphic section `s` on an open `U`. -/
theorem isFirstChernForm_firstChernForm (h : HermitianMetric (n := n) L) :
    IsFirstChernForm L h (firstChernForm h) := by
  intro s U hU hs hs0 e z hz hzU
  change chernCoeff h e z = _
  rw [chernCoeff]
  exact (smoothDDC_localWeight_eq_frame h hU hs hs0 (e.val.symm z) e hz hzU
    (mem_frameDomain _)).symm

/-- Uniqueness of the first Chern form: any two forms with the defining local identity agree on
every chart target (equality of geometric forms). -/
theorem IsFirstChernForm.geometricallyEq {h : HermitianMetric (n := n) L}
    {θ θ' : ClosedRealOneOneForm n X} (hθ : IsFirstChernForm L h θ)
    (hθ' : IsFirstChernForm L h θ') : θ.val.GeometricallyEq θ'.val := by
  intro e z hz
  have h1 := hθ (frame L (e.val.symm z)) _ (isOpen_frameDomain _) (frame_holomorphic _)
    (fun _ hx => frame_ne_zero hx) e z hz (mem_frameDomain _)
  have h2 := hθ' (frame L (e.val.symm z)) _ (isOpen_frameDomain _) (frame_holomorphic _)
    (fun _ hx => frame_ne_zero hx) e z hz (mem_frameDomain _)
  rw [h1, h2]

/-- Existence and uniqueness of `c₁(L,h)` (well-definedness of the notation `ddᶜh`). -/
theorem existsUnique_firstChernForm (h : HermitianMetric (n := n) L) :
    ∃ θ : ClosedRealOneOneForm n X, IsFirstChernForm L h θ ∧
      ∀ θ', IsFirstChernForm L h θ' → θ'.val.GeometricallyEq θ.val :=
  ⟨firstChernForm h, isFirstChernForm_firstChernForm h,
    fun _ hθ' => hθ'.geometricallyEq (isFirstChernForm_firstChernForm h)⟩

/-! ### The class of `c₁(L,h)` does not depend on `h` -/

/-- On a complex line, the ratio `|v|²_h / |v|²_{h'}` does not depend on `v ≠ 0`. -/
theorem normSq_ratio_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (hV : Module.finrank ℂ V = 1)
    (h h' : HermitianForm V) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    h.normSq w / h'.normSq w = h.normSq v / h'.normSq v := by
  obtain ⟨c, rfl⟩ := HermitianForm.exists_smul_eq_of_finrank_eq_one hV hv w
  have hc : c ≠ 0 := by rintro rfl; exact hw (zero_smul _ _)
  have hc2 : ‖c‖ ^ 2 ≠ 0 := by positivity
  rw [HermitianForm.normSq_smul, HermitianForm.normSq_smul, mul_div_mul_left _ _ hc2]

/-- The fibres of a line bundle are complex lines. -/
theorem finrank_fiber (x : X) : Module.finrank ℂ (L x) = 1 :=
  ((trivializationAt ℂ L x).continuousLinearEquivAt ℂ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq.trans
      (Module.finrank_self ℂ)

/-- The logarithm of the ratio of two Hermitian metrics, `log (h/h')`. -/
def logRatio (h h' : HermitianMetric (n := n) L) (x : X) : ℝ :=
  Real.log ((h.form x).normSq (frame L x x) / (h'.form x).normSq (frame L x x))

theorem logRatio_eq_frame (h h' : HermitianMetric (n := n) L) {p x : X}
    (hx : x ∈ frameDomain L p) :
    logRatio h h' x = Real.log ((h.form x).normSq (frame L p x) / (h'.form x).normSq (frame L p x)) := by
  rw [logRatio, normSq_ratio_eq (finrank_fiber x) (h.form x) (h'.form x)
    (frame_ne_zero hx) (frame_ne_zero (mem_frameDomain x))]

theorem chartSmooth_logRatio (h h' : HermitianMetric (n := n) L) :
    ChartSmooth (n := n) (logRatio h h') := by
  intro e
  apply contDiffOn_of_locally_contDiffOn
  intro z hz
  set p := e.val.symm z
  set S := e.val.target ∩ e.val.symm ⁻¹' frameDomain L p
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm (isOpen_frameDomain _)
  refine ⟨S, hS, ⟨hz, mem_frameDomain _⟩, ?_⟩
  have h1 := h.smooth _ _ (isOpen_frameDomain p) (frame_holomorphic p) e
  have h2 := h'.smooth _ _ (isOpen_frameDomain p) (frame_holomorphic p) e
  have hq : ContDiffOn ℝ ∞ (fun w => (h.form (e.val.symm w)).normSq (frame L p (e.val.symm w)) /
      (h'.form (e.val.symm w)).normSq (frame L p (e.val.symm w))) S :=
    h1.div h2 fun w hw => ((h'.form _).normSq_pos (frame_ne_zero hw.2)).ne'
  have hlog := hq.log fun w hw =>
    (div_pos ((h.form _).normSq_pos (frame_ne_zero hw.2))
      ((h'.form _).normSq_pos (frame_ne_zero hw.2))).ne'
  refine (hlog.mono inter_subset_right).congr ?_
  intro w hw
  exact logRatio_eq_frame h h' hw.2.2

/-- The first Chern forms of two Hermitian metrics differ by `ddᶜ log (h/h')`:
`c₁(L,h') = c₁(L,h) + ddᶜ log (h/h')` in every chart. -/
theorem firstChernForm_coeff_eq_add (h h' : HermitianMetric (n := n) L) (e : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (firstChernForm h').val.coeff e z =
      (firstChernForm h).val.coeff e z + smoothDDC (fun y => logRatio h h' (e.val.symm y)) z := by
  set p := e.val.symm z
  set S := e.val.target ∩ e.val.symm ⁻¹' frameDomain L p
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm (isOpen_frameDomain _)
  have hzS : z ∈ S := ⟨hz, mem_frameDomain _⟩
  change chernCoeff h' e z = chernCoeff h e z + _
  rw [chernCoeff, chernCoeff]
  have hw := chartSmooth_localWeight h (isOpen_frameDomain p) (frame_holomorphic p)
    (fun _ hx => frame_ne_zero hx) e
  have hl := (chartSmooth_logRatio h h' e).mono (inter_subset_left : S ⊆ e.val.target)
  have heq : localWeight h' (frame L p) e =ᶠ[𝓝 z]
      fun w => localWeight h (frame L p) e w + logRatio h h' (e.val.symm w) := by
    filter_upwards [hS.mem_nhds hzS] with w hw'
    rw [logRatio_eq_frame h h' hw'.2]
    simp only [localWeight]
    rw [Real.log_div ((h.form _).normSq_pos (frame_ne_zero hw'.2)).ne'
      ((h'.form _).normSq_pos (frame_ne_zero hw'.2)).ne']
    ring
  rw [smoothDDC_congr heq, smoothDDC_add hS hw hl hzS]

/-- The first Chern forms of two Hermitian metrics are Bott--Chern equivalent. -/
theorem bottChernRel_firstChernForm (h h' : HermitianMetric (n := n) L) :
    ClosedRealOneOneForm.BottChernRel (firstChernForm h) (firstChernForm h') :=
  ⟨logRatio h h', chartSmooth_logRatio h h', fun e _ hz => firstChernForm_coeff_eq_add h h' e hz⟩

/-- The real `(1,1)`-class `{c₁(L,h)}` does not depend on the Hermitian metric `h` (the class
`c₁(L)` of the normalization `[c₁(L,h)] = c₁(L)`). -/
theorem firstChernClass_eq (h h' : HermitianMetric (n := n) L) :
    RealBottChern.ofRepresentative (firstChernForm h) =
      RealBottChern.ofRepresentative (firstChernForm h') :=
  (RealBottChern.ofRepresentative_eq_iff _ _).mpr (bottChernRel_firstChernForm h h')

end SGPT.PSH.LineBundleMetric
