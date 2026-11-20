import SGPT.NPP.DN9Frame
import SGPT.NPP.DN9Interface
import SGPT.NPP.DN4Slope
import SGPT.NPP.DN5LocalKernel
import SGPT.NPP.DN5Transfer

/-!
# The adapted fibre maps near a point, as a smooth family in the centre

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Steps 2–3, "all bounds are uniform
over the centres"; steps (W), (T) of the hand-off).

Near a point `z₁` of the compact set `K`, with the frames `Λ(z₀, z)` of `SGPT.NPP.DN9Frame`
(built from a frame `S₁` normalizing `α` at `z₁`), the maps
`𝔉(z₀, z, ξ) = Φ(z₀ + z, Λ(z₀, z₀ + z) ξ) - z₀` form a family smooth in `(z₀, z, ξ)`; cut off by a
bump function it becomes globally smooth (`exists_family`).  For every centre `z₀` near `z₁`,
`F = 𝔉(z₀, ·, ·)` is an adapted fibre map at the origin (`SGPT.NPP.DN4.CenterData`) with constants
independent of `z₀` (`exists_local_centerData`), and the chart smoothing near `z₀` is DN4's
`jointSmoothing` of `F` (`localSmoothing_eq_frame`, rotation invariance).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN9

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.NPP.DN5 SGPT.Analysis.KahlerNormal

variable {N : ℕ}

/-! ### Generic helpers -/

theorem leviForm_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℝ)
    (c x a : E) : leviForm (fun y => f (y - c)) x a = leviForm f (x - c) a := by
  have h1 : fderiv ℝ (fun y => f (y - c)) = fun y => fderiv ℝ f (y - c) :=
    funext fun y => fderiv_comp_sub c
  have h2 : fderiv ℝ (fun y => fderiv ℝ f (y - c)) x = fderiv ℝ (fderiv ℝ f) (x - c) :=
    fderiv_comp_sub (f := fderiv ℝ f) c
  simp only [leviForm, realHessian_eq_fderiv, h1, h2]

theorem leviForm_comp_add_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℝ)
    (c x a : E) : leviForm (fun y => f (c + y)) x a = leviForm f (c + x) a := by
  have h1 : fderiv ℝ (fun y => f (c + y)) = fun y => fderiv ℝ f (c + y) :=
    funext fun y => fderiv_comp_add_left c
  have h2 : fderiv ℝ (fun y => fderiv ℝ f (c + y)) x = fderiv ℝ (fderiv ℝ f) (c + x) :=
    fderiv_comp_add_left (f := fderiv ℝ f) c
  simp only [leviForm, realHessian_eq_fderiv, h1, h2]

/-- A smooth function on an open set, cut off by a smooth function supported inside it, is
globally smooth. -/
theorem contDiff_smul_of_tsupport {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set X} (hΩ : IsOpen Ω) {f : X → F}
    (hf : ContDiffOn ℝ ∞ f Ω) {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Ω) :
    ContDiff ℝ ∞ (fun x => ψ x • f x) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ Ω
  · exact hψ.contDiffAt.smul (hf.contDiffAt (hΩ.mem_nhds hx))
  · have hx' : x ∉ tsupport ψ := fun h => hx (hsupp h)
    have hev : (fun y => ψ y • f y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **Uniform invertibility near a compact part of the zero section.** -/
theorem exists_uniform_inverse_bound {X : Type*} [TopologicalSpace X]
    {A : X × ComplexModel N → Op N} {R : Set (X × ComplexModel N)} (hR : IsOpen R)
    (hA : ContinuousOn A R) {Kc : Set X} (hK : IsCompact Kc)
    (hKR : ∀ x ∈ Kc, (x, (0 : ComplexModel N)) ∈ R) (hunit : ∀ x ∈ Kc, (A (x, 0)).IsInvertible) :
    ∃ r > 0, ∃ M : ℝ, ∀ x ∈ Kc, ∀ ξ ∈ closedBall (0 : ComplexModel N) r,
      (A (x, ξ)).IsInvertible ∧ ‖(A (x, ξ)).inverse‖ ≤ M := by
  have hIo : IsOpen {B : Op N | B.IsInvertible} := ContinuousLinearEquiv.isOpen
  have hWo : IsOpen (R ∩ A ⁻¹' {B : Op N | B.IsInvertible}) := hA.isOpen_inter_preimage hR hIo
  have hsub : Kc ×ˢ ({0} : Set (ComplexModel N)) ⊆ R ∩ A ⁻¹' {B : Op N | B.IsInvertible} := by
    intro q hq
    obtain ⟨hx, hξ⟩ := hq
    have hq0 : q = (q.1, 0) := Prod.ext rfl (mem_singleton_iff.mp hξ)
    rw [hq0]
    exact ⟨hKR q.1 hx, hunit q.1 hx⟩
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hWo hsub
  have h0 : (0 : ComplexModel N) ∈ v := h0v (mem_singleton _)
  obtain ⟨ρ, hρ, hρv⟩ := Metric.isOpen_iff.mp hv 0 h0
  have hsub2 : Kc ×ˢ closedBall (0 : ComplexModel N) (ρ / 2) ⊆
      R ∩ A ⁻¹' {B : Op N | B.IsInvertible} :=
    fun q hq => huv ⟨hKu hq.1, hρv (closedBall_subset_ball (by linarith) hq.2)⟩
  have hcont : ContinuousOn (fun q => (A q).inverse) (R ∩ A ⁻¹' {B : Op N | B.IsInvertible}) := by
    intro q hq
    have hqu : (A q).IsInvertible := hq.2
    have h1 : ContinuousAt (ContinuousLinearMap.inverse (R := ℂ) (M := ComplexModel N)
        (M₂ := ComplexModel N)) (A q) := (hqu.contDiffAt_map_inverse (n := 0)).continuousAt
    exact h1.comp_continuousWithinAt ((hA q hq.1).mono inter_subset_left)
  have hKc : IsCompact (Kc ×ˢ closedBall (0 : ComplexModel N) (ρ / 2)) :=
    hK.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hsub2)
  refine ⟨ρ / 2, by linarith, M, fun x hx ξ hξ => ⟨?_, ?_⟩⟩
  · exact (hsub2 (mk_mem_prod hx hξ)).2
  · have := hM (x, ξ) (mk_mem_prod hx hξ)
    exact this

/-! ### The chart smoothing in a normalizing frame -/

variable {α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ}
  {Φ : ComplexModel N → ComplexModel N → ComplexModel N}

/-- **The unitary form of the chart smoothing**: in a frame `L` normalizing `α_z`,
`localSmoothing Φ α f z t = ∫ f(Φ(z, t L s)) χ(‖s‖²) ds`. -/
theorem localSmoothing_eq_frame {z : ComplexModel N} {L : ComplexModel N ≃L[ℂ] ComplexModel N}
    (hL : ∀ u v, α z ![L u, L v] = flatForm N ![u, v]) (f : ComplexModel N → ℝ) (t : ℝ) :
    localSmoothing Φ α f z t = ∫ s, f (Φ z (t • L s)) * DN3.kernel N s := by
  have hden : (∫ ξ, DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ])) =
      |LinearMap.det (L.restrictScalars ℝ).toLinearEquiv.toLinearMap| := by
    rw [integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)]
    have : ∀ s, DN3.chi N (Real.pi * α z ![(L.restrictScalars ℝ) s,
        Complex.I • (L.restrictScalars ℝ) s]) = DN3.kernel N s :=
      fun s => localWeight_frame hL s
    simp_rw [this, DN3.integral_kernel, mul_one]
  unfold localSmoothing
  rw [hden, integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)
    (fun ξ => f (Φ z (t • ξ)) * DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ]))]
  have : ∀ s, f (Φ z (t • (L.restrictScalars ℝ) s)) *
      DN3.chi N (Real.pi * α z ![(L.restrictScalars ℝ) s, Complex.I • (L.restrictScalars ℝ) s]) =
      f (Φ z (t • L s)) * DN3.kernel N s := fun s => by
    change f (Φ z (t • L s)) * localWeight α z (L s) = _
    rw [localWeight_frame hL s]
  simp_rw [this]
  exact mul_div_cancel_left₀ _ (abs_det_pos (L.restrictScalars ℝ)).ne'

/-- **Rotation**: `∫ f(Φ(z, |w| L s)) χ(‖s‖²) ds = ∫ f(Φ(z, L(w s))) χ(‖s‖²) ds`. -/
theorem integral_frame_rotate (L : ComplexModel N ≃L[ℂ] ComplexModel N)
    (g : ComplexModel N → ℝ) (w : ℂ) :
    ∫ s, g (‖w‖ • L s) * DN3.kernel N s = ∫ s, g (L (w • s)) * DN3.kernel N s := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  set a : ℂ := w / (‖w‖ : ℂ)
  have hwn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have ha : ‖a‖ = 1 := by
    simp only [a, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hw)
  have h := DN4.integral_rotate (fun s => g (‖w‖ • L s) * DN3.kernel N s) a ha
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  have hk : DN3.kernel N (a • s) = DN3.kernel N s := by
    simp only [DN3.kernel, norm_smul, ha, one_mul]
  have hv : ‖w‖ • L (a • s) = L (w • s) := by
    rw [← Complex.coe_smul, ← L.map_smul, smul_smul]
    congr 2
    simp only [a]
    field_simp
  rw [hk, hv]

/-! ### The family of adapted fibre maps near a point -/

/-- The family `𝔉(z₀, z, ξ) = Φ(z₀ + z, Λ(z₀, z₀ + z) ξ) - z₀`. -/
def fam (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (Λ : ComplexModel N → ComplexModel N → Op N) (x : ComplexModel N × (ComplexModel N × ComplexModel N)) :
    ComplexModel N :=
  Φ (x.1 + x.2.1) (Λ x.1 (x.1 + x.2.1) x.2.2) - x.1

set_option maxHeartbeats 1000000 in
/-- **The smooth family of adapted fibre maps near `z₁`** (cut off to be globally smooth). -/
theorem exists_family {O : Set (ComplexModel N × ComplexModel N)} {U K : Set (ComplexModel N)}
    (hD : ChartData Φ O α U K) {z₁ : ComplexModel N} (hz₁ : z₁ ∈ U)
    (hz₁O : (z₁, (0 : ComplexModel N)) ∈ O) :
    ∃ (Λ : ComplexModel N → ComplexModel N → Op N)
      (Fh : ComplexModel N × (ComplexModel N × ComplexModel N) → ComplexModel N) (s : ℝ),
      0 < s ∧ ContDiff ℝ ∞ Fh ∧
      (∀ x ∈ ball ((z₁, ((0 : ComplexModel N), (0 : ComplexModel N))) :
          ComplexModel N × (ComplexModel N × ComplexModel N)) s,
        Fh x = fam Φ Λ x ∧ (x.1 + x.2.1, Λ x.1 (x.1 + x.2.1) x.2.2) ∈ O ∧ x.1 + x.2.1 ∈ U ∧
          IsUnit (Λ x.1 (x.1 + x.2.1)) ∧
          ∀ u v, α (x.1 + x.2.1) ![Λ x.1 (x.1 + x.2.1) u, Λ x.1 (x.1 + x.2.1) v] =
            flatForm N ![u, v]) ∧
      (∀ z₀ ∈ ball z₁ s, DifferentiableAt ℝ (Λ z₀) z₀ ∧
        ∀ v, fderiv ℝ (Λ z₀) z₀ (Complex.I • v) = Complex.I • fderiv ℝ (Λ z₀) z₀ v) := by
  obtain ⟨hΦ, hU, hα, hαpos, -, -, -⟩ := hD
  obtain ⟨𝒱, h𝒱o, h1𝒱, G, hG, -, hGn⟩ := exists_frameCorrection (N := N)
  set T : ComplexModel N → Op N := fun z => hermOp (α z) with hTdef
  have hT : ContDiffOn ℝ ∞ T U := contDiff_hermOp.comp_contDiffOn hα
  have hTsa : ∀ z ∈ U, star (T z) = T z := fun z hz => star_hermOp (hαpos z hz).1
  obtain ⟨L, hL⟩ := exists_normalizing_linear (hαpos z₁ hz₁).1 (hαpos z₁ hz₁).2
  set S₁ : Op N := (L : Op N)
  have hS₁ : star S₁ * T z₁ * S₁ = 1 := star_mul_eq_one_of_normalizing (hαpos z₁ hz₁).1 hL
  have hSS : S₁ * (L.symm : Op N) = 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    change L (L.symm x) = x
    exact L.apply_symm_apply x
  have hTu : IsUnit (T z₁) := by
    refine isUnit_of_mul_eq_one (B := S₁ * star S₁) ?_
    have h1 : star S₁ * T z₁ = (L.symm : Op N) := by
      calc star S₁ * T z₁ = star S₁ * T z₁ * (S₁ * (L.symm : Op N)) := by rw [hSS, mul_one]
        _ = (star S₁ * T z₁ * S₁) * (L.symm : Op N) := by simp only [mul_assoc]
        _ = (L.symm : Op N) := by rw [hS₁, one_mul]
    rw [mul_assoc, h1, hSS]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ComplexModel N → ComplexModel N → Op N, Λ = frame G S₁ T := ⟨_, rfl⟩
  have hΛsm : ContDiffOn ℝ ∞ (fun p : ComplexModel N × ComplexModel N => Λ p.1 p.2)
      (frameDom S₁ T 𝒱 U) := by
    rw [hΛ]; exact contDiffOn_frame G hG hU hT
  -- the domain of the family
  obtain ⟨D1, hD1⟩ : ∃ D1 : Set (ComplexModel N × (ComplexModel N × ComplexModel N)),
      D1 = (fun x => ((x.1, x.1 + x.2.1) : ComplexModel N × ComplexModel N)) ⁻¹'
        frameDom S₁ T 𝒱 U := ⟨_, rfl⟩
  have hmap : Continuous (fun x : ComplexModel N × (ComplexModel N × ComplexModel N) =>
      ((x.1, x.1 + x.2.1) : ComplexModel N × ComplexModel N)) :=
    continuous_fst.prodMk (continuous_fst.add (continuous_fst.comp continuous_snd))
  have hD1o : IsOpen D1 := by
    rw [hD1]; exact (isOpen_frameDom h𝒱o hU hT).preimage hmap
  have hΛs : ContDiffOn ℝ ∞ (fun x : ComplexModel N × (ComplexModel N × ComplexModel N) =>
      Λ x.1 (x.1 + x.2.1)) D1 := by
    rw [hD1]
    exact hΛsm.comp
      (contDiff_fst.prodMk (contDiff_fst.add (contDiff_fst.comp contDiff_snd))).contDiffOn
      (fun x hx => hx)
  have hΛv : ContDiffOn ℝ ∞ (fun x : ComplexModel N × (ComplexModel N × ComplexModel N) =>
      Λ x.1 (x.1 + x.2.1) x.2.2) D1 := by
    have hr := (ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel N) (ComplexModel N) ℝ
      ℝ).contDiff.comp_contDiffOn hΛs
    exact hr.clm_apply (contDiff_snd.comp contDiff_snd).contDiffOn
  set inner : ComplexModel N × (ComplexModel N × ComplexModel N) → ComplexModel N × ComplexModel N :=
    fun x => (x.1 + x.2.1, Λ x.1 (x.1 + x.2.1) x.2.2)
  have hin : ContDiffOn ℝ ∞ inner D1 :=
    (contDiff_fst.add (contDiff_fst.comp contDiff_snd)).contDiffOn.prodMk hΛv
  obtain ⟨Dom, hDom⟩ : ∃ Dom : Set (ComplexModel N × (ComplexModel N × ComplexModel N)),
      Dom = D1 ∩ inner ⁻¹' O := ⟨_, rfl⟩
  have hDomo : IsOpen Dom := by
    rw [hDom]; exact hin.continuousOn.isOpen_inter_preimage hD1o hΦ.isOpen
  have hfam : ContDiffOn ℝ ∞ (fam Φ Λ) Dom := by
    rw [hDom]
    exact (hΦ.contDiffOn.comp (hin.mono inter_subset_left) fun x hx => hx.2).sub contDiffOn_fst
  -- the base point
  have hM₁ : frameM S₁ T z₁ z₁ = 1 := by rw [frameM_self]; exact hS₁
  have hz₁D : ((z₁, z₁) : ComplexModel N × ComplexModel N) ∈ frameDom S₁ T 𝒱 U := by
    refine mem_inter ?_ ?_
    · exact ⟨hz₁, hz₁, hTu⟩
    · change frameM S₁ T z₁ z₁ ∈ 𝒱
      rw [hM₁]; exact h1𝒱
  have hx₁ : ((z₁, ((0 : ComplexModel N), (0 : ComplexModel N))) :
      ComplexModel N × (ComplexModel N × ComplexModel N)) ∈ Dom := by
    rw [hDom, hD1]
    refine mem_inter ?_ ?_
    · change ((z₁, z₁ + 0) : ComplexModel N × ComplexModel N) ∈ frameDom S₁ T 𝒱 U
      rw [add_zero]; exact hz₁D
    · change ((z₁ + 0, Λ z₁ (z₁ + 0) 0) : ComplexModel N × ComplexModel N) ∈ O
      rw [map_zero, add_zero]
      exact hz₁O
  obtain ⟨s₃, hs₃, hs₃D⟩ := Metric.isOpen_iff.mp hDomo _ hx₁
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = s₃ / 3 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; positivity
  let ψ : ContDiffBump ((z₁, ((0 : ComplexModel N), (0 : ComplexModel N))) :
      ComplexModel N × (ComplexModel N × ComplexModel N)) := ⟨s, 2 * s, hs, by linarith⟩
  have hψsupp : tsupport ψ ⊆ Dom := by
    rw [ψ.tsupport_eq]
    exact (closedBall_subset_ball (show 2 * s < s₃ by rw [hsdef]; linarith)).trans hs₃D
  refine ⟨Λ, fun x => ψ x • fam Φ Λ x, s, hs,
    contDiff_smul_of_tsupport hDomo hfam ψ.contDiff hψsupp, ?_, ?_⟩
  · intro x hx
    have hxD : x ∈ Dom := hs₃D (ball_subset_ball (show s ≤ s₃ by rw [hsdef]; linarith) hx)
    have hψ1 : ψ x = 1 := ψ.one_of_mem_closedBall (ball_subset_closedBall hx)
    rw [hDom, hD1] at hxD
    obtain ⟨hxF, hO⟩ := hxD
    have hxF' : ((x.1, x.1 + x.2.1) : ComplexModel N × ComplexModel N) ∈ frameDom S₁ T 𝒱 U := hxF
    obtain ⟨hB, hMV⟩ := hxF'
    have hzU : x.1 + x.2.1 ∈ U := hB.2.1
    have hnorm : star (Λ x.1 (x.1 + x.2.1)) * T (x.1 + x.2.1) * Λ x.1 (x.1 + x.2.1) = 1 := by
      rw [hΛ]; exact frame_normalizing G S₁ T hGn hMV (hTsa _ hzU)
    refine ⟨by simp only [hψ1, one_smul], hO, hzU, ?_, ?_⟩
    · exact isUnit_of_mul_eq_one (B := star (Λ x.1 (x.1 + x.2.1)) * T (x.1 + x.2.1)) hnorm
    · exact normalizing_of_star_mul (hαpos _ hzU).1 hnorm
  · intro z₀ hz₀
    have hx : ((z₀, ((0 : ComplexModel N), (0 : ComplexModel N))) :
        ComplexModel N × (ComplexModel N × ComplexModel N)) ∈ Dom := by
      refine hs₃D ?_
      rw [mem_ball, Prod.dist_eq, Prod.dist_eq, dist_self, max_self, max_eq_left dist_nonneg]
      rw [mem_ball] at hz₀
      rw [hsdef] at hz₀
      linarith
    rw [hDom, hD1] at hx
    have hxF' : ((z₀, z₀ + 0) : ComplexModel N × ComplexModel N) ∈ frameDom S₁ T 𝒱 U := hx.1
    rw [add_zero] at hxF'
    obtain ⟨⟨hz₀U, -, hTu₀⟩, hMV⟩ := hxF'
    have hMV' : frameM S₁ T z₀ z₀ ∈ 𝒱 := hMV
    have hTd : DifferentiableAt ℝ T z₀ :=
      (hT.contDiffAt (hU.mem_nhds hz₀U)).differentiableAt (by simp)
    have hsa : ∀ᶠ z in 𝓝 z₀, star (T z) = T z :=
      eventually_of_mem (hU.mem_nhds hz₀U) fun z hz => hTsa z hz
    have hGd : DifferentiableAt ℝ G (frameM S₁ T z₀ z₀) :=
      (hG.contDiffAt (h𝒱o.mem_nhds hMV')).differentiableAt (by simp)
    obtain ⟨L', hL', -⟩ := hasFDerivAt_frame_center G S₁ T hTd hsa hTu₀ hGd
    rw [hΛ]
    exact ⟨hL'.differentiableAt, fderiv_frame_I G S₁ T hTd hsa hTu₀ hGd⟩

end SGPT.NPP.DN9
