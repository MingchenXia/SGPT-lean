import SGPT.PSH.BookLineBundleMetrics
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology

/-!
# The Lelong–Poincaré formula for a holomorphic section (`prop:LelongPoincare`)

Source: `prop:LelongPoincare` of the chapter *Plurisubharmonic functions*. Let `X` be a connected
complex manifold, `L` a holomorphic line bundle with a Hermitian metric `h` (`def:Hermmetric`), and
`s ∈ H⁰(X, L)` non-zero. Then

`c₁(L, h) + ddᶜ log |s|²_h = [Z(s)]`,

where `[Z(s)]` is the current of integration of the zero divisor of `s`.

On the domain `U` of a local frame `σ` of `L` one writes `s = f σ` with `f` holomorphic, so
`log |s|²_h = log |f|² + log |σ|²_h` and `c₁(L, h)|_U = -ddᶜ log |σ|²_h`; hence the left side is
`ddᶜ log |f|²` on `U`, which is the current of integration `[div f]` over the regular part of
`{f = 0}`, counted with multiplicities (the flat Lelong–Poincaré equation of
`SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent`). Globally, `(log |s|²_h, c₁(L, h))`
is a metered effective divisor in the sense of `MeteredEffectiveQDivisor` (`zeroDivisor`), whose
integration current `[Z(s)]` (`zeroDivisorCurrent`) is `ddᶜ log |s|²_h + c₁(L, h)` and is, on every
frame domain and in every chart, the current of integration `[div f]`
(`LelongPoincareDivisor.lelongPoincare`). Since the frame domains cover `X` and global currents
are determined by their chart coefficients, this characterizes `[Z(s)]`.

The only input beyond the local computation is the identity theorem: a non-zero holomorphic
section of a line bundle on a connected manifold does not vanish identically on any non-empty
open set (`exists_ne_zero_of_isOpen`), which makes `log |s|²_h` locally integrable.

Main declarations:

* `SGPT.PSH.BookDeepLelongPoincare.sectionLogNormSq` — `log |s|²_h`;
* `SGPT.PSH.BookDeepLelongPoincare.zeroDivisor`, `zeroDivisorCurrent` — `Z(s)` and `[Z(s)]`;
* `SGPT.PSH.BookDeepLelongPoincare.lelongPoincare` — `prop:LelongPoincare`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.BookDeepLelongPoincare

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves LelongPoincareDivisor GlobalCurrents CanonicalCurrentFrame
open SGPT.PSH.LineBundleMetric

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]
  {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel (m + 1))]

/-- `log |s|²_h`, with value `-∞` on the zero set of `s`. -/
def sectionLogNormSq (h : HermitianMetric (n := m + 1) L) (s : (x : X) → L x) : X → EReal :=
  fun x => ENNReal.log (ENNReal.ofReal ((h.form x).normSq (s x)))

/-- The coefficient `f` of `s = f σ_p` in the trivialization frame `σ_p` at `p`. -/
def coeff (p : X) (s : (x : X) → L x) : X → ℂ :=
  fun x => ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (s x))).2

/-- `log |σ_p|²_h` for the trivialization frame `σ_p` at `p`. -/
def frameLogNormSq (h : HermitianMetric (n := m + 1) L) (p : X) : X → ℝ :=
  fun x => Real.log ((h.form x).normSq (frame L p x))

theorem coeff_mdifferentiableOn {s : (x : X) → L x}
    (hs : IsHolomorphicSectionOn (n := m + 1) L s univ) (p : X) :
    MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (coeff p s) (frameDomain L p) := by
  have := (trivializationAt ℂ L p).mdifferentiableOn_section_iff
    (IB := 𝓘(ℂ, ComplexModel (m + 1))) (s := s) (isOpen_frameDomain p) Subset.rfl
  exact this.mp (hs.mono (subset_univ _))

theorem coeff_eq_zero_iff (p : X) (s : (x : X) → L x) {x : X} (hx : x ∈ frameDomain L p) :
    coeff p s x = 0 ↔ s x = 0 := by
  constructor
  · intro h0
    rw [eq_coeff_smul_frame (L := L) p s hx]
    change coeff p s x • frame L p x = 0
    rw [h0, zero_smul]
  · intro h0
    change ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x (s x))).2 = 0
    rw [h0]
    exact ((trivializationAt ℂ L p).continuousLinearEquivAt ℂ x hx).map_zero

theorem normSq_eq_coeff (h : HermitianMetric (n := m + 1) L) (p : X) (s : (x : X) → L x)
    {x : X} (hx : x ∈ frameDomain L p) :
    (h.form x).normSq (s x) = ‖coeff p s x‖ ^ 2 * (h.form x).normSq (frame L p x) := by
  conv_lhs => rw [eq_coeff_smul_frame (L := L) p s hx]
  exact HermitianForm.normSq_smul _ _ _

/-! ### The identity theorem for sections -/

/-- **Identity theorem.** On a connected manifold, a holomorphic section of a line bundle which is
not identically zero does not vanish identically on any non-empty open set. -/
theorem exists_ne_zero_of_isOpen [ConnectedSpace X] {s : (x : X) → L x}
    (hs : IsHolomorphicSectionOn (n := m + 1) L s univ) (hne : ∃ x, s x ≠ 0)
    {W : Set X} (hW : IsOpen W) (hWne : W.Nonempty) : ∃ y ∈ W, s y ≠ 0 := by
  set Z : Set X := interior {x | s x = 0} with hZdef
  have hZclosed : IsClosed Z := by
    refine isClosed_of_closure_subset fun x hx => ?_
    set e := complexChartAt (n := m + 1) x with he
    set V : Set (ComplexModel (m + 1)) :=
      e.val.target ∩ e.val.symm ⁻¹' frameDomain L x with hVdef
    have hV : IsOpen V := e.val.isOpen_inter_preimage_symm (isOpen_frameDomain x)
    have hxs : x ∈ e.val.source := mem_complexChartAt_source x
    have hexV : e.val x ∈ V := ⟨e.val.map_source hxs, by
      change e.val.symm (e.val x) ∈ frameDomain L x
      rw [e.val.left_inv hxs]; exact mem_frameDomain x⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV _ hexV
    set f : ComplexModel (m + 1) → ℂ := fun z => coeff x s (e.val.symm z) with hfdef
    have hf : DifferentiableOn ℂ f (Metric.ball (e.val x) r) :=
      (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e
        (coeff_mdifferentiableOn hs x)).mono hball
    -- the open neighbourhood of `x` read in the ball
    set O : Set X := e.val.source ∩ e.val ⁻¹' Metric.ball (e.val x) r with hOdef
    have hO : IsOpen O := e.val.isOpen_inter_preimage Metric.isOpen_ball
    have hxO : x ∈ O := ⟨hxs, Metric.mem_ball_self hr⟩
    obtain ⟨y, hyO, hyZ⟩ := mem_closure_iff.mp hx O hO hxO
    -- `f` vanishes on the image of the open set `Z ∩ O`
    set U' : Set (ComplexModel (m + 1)) := e.val '' (Z ∩ O) with hU'def
    have hU' : IsOpen U' :=
      e.val.isOpen_image_of_subset_source (isOpen_interior.inter hO) fun z hz => hz.2.1
    have hU'ball : U' ⊆ Metric.ball (e.val x) r := by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2.2
    have hfU' : EqOn f 0 U' := by
      rintro _ ⟨z, hz, rfl⟩
      have hzs : s z = 0 := (interior_subset hz.1 : z ∈ {x | s x = 0})
      have hzV : z ∈ frameDomain L x := by
        have := (hball (hU'ball ⟨z, hz, rfl⟩)).2
        change e.val.symm (e.val z) ∈ frameDomain L x at this
        rwa [e.val.left_inv hz.2.1] at this
      change coeff x s (e.val.symm (e.val z)) = 0
      rw [e.val.left_inv hz.2.1]
      exact (coeff_eq_zero_iff x s hzV).mpr hzs
    have hfball := eqOn_zero_of_isOpen_convex Metric.isOpen_ball (convex_ball _ _) hf hU' hU'ball
      ⟨e.val y, y, ⟨hyZ, hyO⟩, rfl⟩ hfU'
    -- hence `s` vanishes on the neighbourhood `O ∩ frameDomain` of `x`
    apply mem_interior.mpr
    refine ⟨O ∩ frameDomain L x, fun z hz => ?_, hO.inter (isOpen_frameDomain x),
      ⟨hxO, mem_frameDomain x⟩⟩
    have h0 := hfball hz.1.2
    change coeff x s (e.val.symm (e.val z)) = 0 at h0
    rw [e.val.left_inv hz.1.1] at h0
    exact (coeff_eq_zero_iff x s hz.2).mp h0
  have hZopen : IsOpen Z := isOpen_interior
  rcases isClopen_iff.mp ⟨hZclosed, hZopen⟩ with hZ | hZ
  · by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := hWne
    have : y ∈ Z := interior_maximal (fun z hz => hall z hz) hW hy
    rw [hZ] at this
    exact this
  · obtain ⟨x, hx⟩ := hne
    have hxZ : x ∈ Z := by rw [hZ]; exact mem_univ x
    exact absurd (interior_subset hxZ) hx

/-! ### The zero divisor of `s` as a metered effective divisor -/

theorem frameLogNormSq_smooth (h : HermitianMetric (n := m + 1) L) (p : X)
    (e : ComplexChart (m + 1) X) :
    ContDiffOn ℝ ∞ (fun z => frameLogNormSq h p (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' frameDomain L p) := by
  have h1 := chartSmooth_localWeight h (isOpen_frameDomain p) (frame_holomorphic p)
    (fun _ hx => frame_ne_zero hx) e
  have h2 := h1.neg
  refine h2.congr fun z _ => ?_
  simp [localWeight, frameLogNormSq]

theorem firstChernForm_coeff_eq (h : HermitianMetric (n := m + 1) L) (p : X)
    (e : ComplexChart (m + 1) X) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target)
    (hzp : e.val.symm z ∈ frameDomain L p) :
    (firstChernForm h).val.coeff e z =
      -smoothDDC (fun y => frameLogNormSq h p (e.val.symm y)) z := by
  change chernCoeff h e z = _
  rw [chernCoeff_eq_of_mem h e p hz hzp]
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' frameDomain L p) :=
    e.val.isOpen_inter_preimage_symm (isOpen_frameDomain p)
  have hneg := smoothDDC_neg hS (frameLogNormSq_smooth h p e) (z := z) ⟨hz, hzp⟩
  rw [← hneg]
  rfl

theorem sectionLogNormSq_eq (h : HermitianMetric (n := m + 1) L) (p : X) (s : (x : X) → L x)
    {x : X} (hx : x ∈ frameDomain L p) :
    sectionLogNormSq h s x =
      (∑ _i : Fin 1, (((1 : ℚ) : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => coeff p s) x) +
      (frameLogNormSq h p x : EReal) := by
  rw [Fin.sum_univ_one]
  have hN : 0 < (h.form x).normSq (frame L p x) := (h.form x).normSq_pos (frame_ne_zero hx)
  rw [generatorLog_eq_log_sum, Fin.sum_univ_one, sectionLogNormSq, normSq_eq_coeff h p s hx,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hN]
  simp [frameLogNormSq]

variable (L) in
/-- **The zero divisor `Z(s)`** of a non-zero holomorphic section `s` of `L` over a connected
manifold, with the smooth metric induced by `h`: the metered effective divisor with weight
`log |s|²_h` and curvature `c₁(L, h)`, presented on the domain of every trivialization frame `σ_p`
by `log |s|²_h = log |f_p|² + log |σ_p|²_h`, `s = f_p σ_p`. -/
def zeroDivisor [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L) {s : (x : X) → L x}
    (hs : IsHolomorphicSectionOn (n := m + 1) L s univ) (hne : ∃ x, s x ≠ 0) :
    MeteredEffectiveQDivisor (m + 1) X where
  weight := sectionLogNormSq h s
  curvature := firstChernForm h
  local_presentation x := by
    refine ⟨frameDomain L x, isOpen_frameDomain x, mem_frameDomain x, 1, fun _ => 1,
      fun _ => coeff x s, frameLogNormSq h x, fun _ => zero_le_one,
      fun _ => coeff_mdifferentiableOn hs x, ?_, frameLogNormSq_smooth h x,
      fun y hy => sectionLogNormSq_eq h x s hy,
      fun e z hz hzU => firstChernForm_coeff_eq h x e hz hzU⟩
    intro _ W hW hWU hWne
    obtain ⟨y, hyW, hy⟩ := exists_ne_zero_of_isOpen hs hne hW hWne
    exact ⟨y, hyW, fun h0 => hy ((coeff_eq_zero_iff x s (hWU hyW)).mp h0)⟩

variable (L) in
/-- The presentation of `Z(s)` on the domain of the trivialization frame at `p`:
`log |s|²_h = log |f_p|² + log |σ_p|²_h`. -/
def framePresentation [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) (p : X) : LocalPresentation (zeroDivisor L h hs hne) where
  U := frameDomain L p
  isOpen := isOpen_frameDomain p
  N := 1
  a := fun _ => 1
  g := fun _ => coeff p s
  h := frameLogNormSq h p
  a_nonneg := fun _ => zero_le_one
  g_holo := fun _ => coeff_mdifferentiableOn hs p
  g_ne := fun _ W hW hWU hWne => by
    obtain ⟨y, hyW, hy⟩ := exists_ne_zero_of_isOpen hs hne hW hWne
    exact ⟨y, hyW, fun h0 => hy ((coeff_eq_zero_iff p s (hWU hyW)).mp h0)⟩
  h_smooth := frameLogNormSq_smooth h p
  weight_eq := fun y hy => sectionLogNormSq_eq h p s hy
  curvature_eq := fun e z hz hzU => firstChernForm_coeff_eq h p e hz hzU

theorem framePresentation_chartG [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) (p : X) (e : ComplexChart (m + 1) X) (i : Fin 1) :
    (framePresentation L h hs hne p).chartG e i = fun z => coeff p s (e.val.symm z) := rfl

theorem framePresentation_chartDomain [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) (p : X) (e : ComplexChart (m + 1) X) :
    ((framePresentation L h hs hne p).chartDomain e : Set (ComplexModel (m + 1))) =
      e.val.target ∩ e.val.symm ⁻¹' frameDomain L p := rfl

variable (L) in
/-- `ddᶜ log |s|²_h` as a global current (`log |s|²_h` is locally integrable). -/
def logNormSqCurrent [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)) :=
  ddCWeight (canonicalBasis (m + 1)) (Nat.succ_pos m) (zeroDivisor L h hs hne)

variable (L) in
/-- **The current of integration `[Z(s)]`** of the zero divisor of `s`. -/
def zeroDivisorCurrent [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)) :=
  integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) (zeroDivisor L h hs hne)

/-- **`prop:LelongPoincare`** (Lelong–Poincaré). Let `X` be connected, `h` a Hermitian metric on
`L` and `s ∈ H⁰(X, L)` non-zero. Then

1. `log |s|²_h` is locally integrable in every chart, and the chart coefficients of
   `logNormSqCurrent` are the distributional `ddᶜ log |s|²_h`;
2. `c₁(L, h) + ddᶜ log |s|²_h = [Z(s)]` as global currents;
3. `[Z(s)]` is the current of integration of the zero divisor: on the domain of the trivialization
   frame `σ_p` at every `p`, in every chart, it is the integration current `[div f_p]` over the
   regular part of `{f_p = 0}` with multiplicities, where `s = f_p σ_p`;
4. `[Z(s)]` is closed and of type `(1,1)`. -/
theorem lelongPoincare [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) :
    ∃ hloc : ChartLocallyIntegrable (canonicalBasis (m + 1)) (sectionLogNormSq h s),
      (∀ e, (logNormSqCurrent L h hs hne).coefficients (canonicalBasis (m + 1)) e =
        chartDDC (canonicalBasis (m + 1)) (sectionLogNormSq h s) e (hloc e)) ∧
      smoothGlobalCurrent (canonicalBasis (m + 1)) (k := degreeTwo (Nat.succ_pos m))
          (firstChernForm h).val + logNormSqCurrent L h hs hne = zeroDivisorCurrent L h hs hne ∧
      (∀ (p : X) (e : ComplexChart (m + 1) X),
        restrictForm ((zeroDivisorCurrent L h hs hne).coefficients (canonicalBasis (m + 1)) e)
            ((framePresentation L h hs hne p).chartDomain_le e) =
          DivisorIntegrationCurrent.divisorCurrent
            ((framePresentation L h hs hne p).differentiableOn_chartG e ⟨0, Nat.one_pos⟩)
            ((framePresentation L h hs hne p).frequently_chartG_ne e ⟨0, Nat.one_pos⟩)) ∧
      (zeroDivisorCurrent L h hs hne).IsClosed (canonicalBasis (m + 1)) ∧
      (zeroDivisorCurrent L h hs hne).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) := by
  obtain ⟨hloc, hddc, hclosed, htype, -, hlocal⟩ :=
    LelongPoincareDivisor.lelongPoincare (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (zeroDivisor L h hs hne)
  refine ⟨hloc, fun e => coefficients_ddCWeight _ _ _ e, ?_, fun p e => ?_, hclosed, htype⟩
  · have hcurv : (zeroDivisor L h hs hne).curvature = firstChernForm h := rfl
    rw [hcurv] at hddc
    change smoothGlobalCurrent _ _ + ddCWeight _ _ _ = integrationCurrent _ _ _
    rw [hddc]
    have key : ∀ A B : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)), A + (B - A) = B :=
      fun A B => add_sub_cancel A B
    exact key _ _
  · rw [show zeroDivisorCurrent L h hs hne = integrationCurrent (canonicalBasis (m + 1))
      (Nat.succ_pos m) (zeroDivisor L h hs hne) from rfl,
      hlocal (framePresentation L h hs hne p) e,
      ActualCanonicalComplementaryCurrentCalibration.haarFactor_canonicalBasis]
    rw [NNReal.coe_one, one_smul]
    erw [Fin.sum_univ_one]
    simp only [framePresentation, Rat.cast_one]
    exact one_smul _ _

/-- `[Z(s)]` is the unique global current which, on the domain of every trivialization frame
`σ_p` and in every chart, is the current of integration `[div f_p]` (`s = f_p σ_p`). -/
theorem eq_zeroDivisorCurrent_of_local [ConnectedSpace X] (h : HermitianMetric (n := m + 1) L)
    {s : (x : X) → L x} (hs : IsHolomorphicSectionOn (n := m + 1) L s univ)
    (hne : ∃ x, s x ≠ 0) (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hT : ∀ (p : X) (e : ComplexChart (m + 1) X),
      restrictForm (T.coefficients (canonicalBasis (m + 1)) e)
          ((framePresentation L h hs hne p).chartDomain_le e) =
        DivisorIntegrationCurrent.divisorCurrent
          ((framePresentation L h hs hne p).differentiableOn_chartG e ⟨0, Nat.one_pos⟩)
          ((framePresentation L h hs hne p).frequently_chartG_ne e ⟨0, Nat.one_pos⟩)) :
    T = zeroDivisorCurrent L h hs hne := by
  obtain ⟨-, -, -, hZ, -, -⟩ := lelongPoincare h hs hne
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  ext v : 1
  apply eq_of_forall_restrict_eq (fun p => (framePresentation L h hs hne p).chartDomain e)
    (fun p => (framePresentation L h hs hne p).chartDomain_le e)
  · intro z hz
    exact ⟨e.val.symm z, hz, mem_frameDomain _⟩
  · intro p
    have h1 := congrArg (fun A => A v) (hT p e)
    have h2 := congrArg (fun A => A v) (hZ p e)
    simp only [restrictForm_apply'] at h1 h2
    rw [h1, h2]

end SGPT.PSH.BookDeepLelongPoincare
