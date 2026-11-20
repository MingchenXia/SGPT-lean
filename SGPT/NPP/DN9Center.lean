import SGPT.NPP.DN9Family

/-!
# Adapted fibre maps at every centre near a point, with uniform constants

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Steps 2–3; steps (W), (T) of lane
DN4's hand-off).

For the family `Fh` of `SGPT.NPP.DN9.exists_family` near `z₁ ∈ K`, every centre `z₀` close to
`z₁` gives the adapted fibre map `F = Fh(z₀, ·, ·)`, which satisfies `SGPT.NPP.DN4.CenterData`
with constants independent of `z₀` (`exists_local_centerData`):

* the centre condition `D_ξ ∂̄_v F(0, 0) = 0` follows from `D_ξ F(z, 0) = Λ(z₀, z₀ + z)` and the
  complex linearity of `D_z Λ(z₀, ·)(z₀)` (`centerCondition`), by the symmetry of second
  derivatives;
* the derivative bounds are bounds of continuous functions of `(z₀, z, ξ)` on a compact set, the
  inverse bound comes from `exists_uniform_inverse_bound`;
* the chart smoothing near `z₀` is `jointSmoothing F (p(z₀ + ·))` (normalizing frame, rotation).
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

theorem mem_ball_triple {z₁ z₀ z ξ : ComplexModel N} {s : ℝ} (h0 : dist z₀ z₁ < s) (h1 : ‖z‖ < s)
    (h2 : ‖ξ‖ < s) :
    ((z₀, (z, ξ)) : ComplexModel N × (ComplexModel N × ComplexModel N)) ∈
      ball ((z₁, ((0 : ComplexModel N), (0 : ComplexModel N))) :
        ComplexModel N × (ComplexModel N × ComplexModel N)) s := by
  rw [mem_ball, Prod.dist_eq, Prod.dist_eq, dist_zero_right, dist_zero_right]
  exact max_lt h0 (max_lt h1 h2)

/-- **The centre condition from a frame holomorphic to first order.** -/
theorem centerCondition {F : ComplexModel N → ComplexModel N → ComplexModel N}
    (hF : ContDiff ℝ 2 (DN4.uncurryF F)) {Λ₀ : ComplexModel N → Op N} {z₀ : ComplexModel N}
    (hΛd : DifferentiableAt ℝ Λ₀ z₀)
    (hslice : ∀ e, (fun z => fderiv ℝ (F z) 0 e) =ᶠ[𝓝 0] fun z => Λ₀ (z₀ + z) e)
    (hI : ∀ v, fderiv ℝ Λ₀ z₀ (Complex.I • v) = Complex.I • fderiv ℝ Λ₀ z₀ v)
    (v : ComplexModel N) : fderiv ℂ (DN4.dbarZ F v) 0 = 0 := by
  set H := DN4.uncurryF F
  have hHd : Differentiable ℝ H := hF.differentiable (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ H) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsym := (hF.contDiffAt (x := ((0 : ComplexModel N), (0 : ComplexModel N)))).isSymmSndFDerivAt
    (by simp)
  -- the derivative of `ξ ↦ D H(0, ξ) w` at `0`
  have h1 : ∀ w : ComplexModel N × ComplexModel N, HasFDerivAt
      (fun ξ => fderiv ℝ H (0, ξ) w)
      ((((fderiv ℝ (fderiv ℝ H) (0, 0)).comp
        (ContinuousLinearMap.inr ℝ (ComplexModel N) (ComplexModel N))).flip) w) 0 := by
    intro w
    have h := ((hDd (0, 0)).hasFDerivAt.comp (0 : ComplexModel N)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ComplexModel N) (0 : ComplexModel N))).clm_apply
      (hasFDerivAt_const w (0 : ComplexModel N))
    refine h.congr_fderiv (ContinuousLinearMap.ext fun e => ?_)
    simp
  -- the derivative of `z ↦ D H(z, 0) w` at `0`
  have h2 : ∀ (w : ComplexModel N × ComplexModel N) (u : ComplexModel N),
      fderiv ℝ (fun z => fderiv ℝ H (z, 0) w) 0 u = fderiv ℝ (fderiv ℝ H) (0, 0) (u, 0) w := by
    intro w u
    have hc : HasFDerivAt (fun z : ComplexModel N => fderiv ℝ H (z, 0))
        ((fderiv ℝ (fderiv ℝ H) (0, 0)).comp
          (ContinuousLinearMap.inl ℝ (ComplexModel N) (ComplexModel N))) 0 :=
      HasFDerivAt.comp (f := fun e : ComplexModel N => (e, (0 : ComplexModel N)))
        (0 : ComplexModel N) (hDd (0, 0)).hasFDerivAt
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ComplexModel N) (0 : ComplexModel N))
    have h := hc.clm_apply (hasFDerivAt_const w (0 : ComplexModel N))
    rw [h.fderiv]
    simp
  -- `D²H(0,0)((u,0),(0,e)) = (DΛ₀ u) e`
  have hkey : ∀ u e : ComplexModel N,
      fderiv ℝ (fderiv ℝ H) (0, 0) (0, e) (u, 0) = fderiv ℝ Λ₀ z₀ u e := by
    intro u e
    rw [hsym, ← h2]
    have hev : (fun z => fderiv ℝ H (z, 0) (0, e)) =ᶠ[𝓝 0] fun z => Λ₀ (z₀ + z) e := by
      filter_upwards [hslice e] with z hz
      rw [← hz, DN4.fderiv_partial_right hHd]
    rw [hev.fderiv_eq]
    rw [fderiv_comp_add_left (f := fun y => Λ₀ y e) z₀, add_zero]
    have hev2 : HasFDerivAt (fun y => Λ₀ y e)
        (((ContinuousLinearMap.apply ℂ (ComplexModel N) e).restrictScalars ℝ).comp
          (fderiv ℝ Λ₀ z₀)) z₀ :=
      ((ContinuousLinearMap.apply ℂ (ComplexModel N) e).restrictScalars ℝ).hasFDerivAt.comp
        z₀ hΛd.hasFDerivAt
    rw [hev2.fderiv]
    simp
  have hdbar : DN4.dbarZ F v = fun ξ => (2 : ℝ)⁻¹ • (fderiv ℝ H (0, ξ) (v, 0) +
      Complex.I • fderiv ℝ H (0, ξ) (Complex.I • v, 0)) := by
    funext ξ
    simp only [DN4.dbarZ, DN4.fderiv_partial_left hHd]
    rfl
  have hd := (((h1 (v, 0)).add ((h1 (Complex.I • v, 0)).const_smul Complex.I)).const_smul
    ((2 : ℝ)⁻¹))
  have hd' := hd.congr_of_eventuallyEq (f₁ := DN4.dbarZ F v)
    (Eventually.of_forall fun ξ => by rw [hdbar]; rfl)
  have hzero : fderiv ℝ (DN4.dbarZ F v) 0 = 0 := by
    rw [hd'.fderiv]
    refine ContinuousLinearMap.ext fun e => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.zero_apply]
    rw [hkey, hkey, hI, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
      add_neg_cancel, smul_zero]
  by_cases hdc : DifferentiableAt ℂ (DN4.dbarZ F v) 0
  · have h := hdc.fderiv_restrictScalars ℝ
    rw [hzero] at h
    refine ContinuousLinearMap.ext fun e => ?_
    have := congrArg (fun L : ComplexModel N →L[ℝ] ComplexModel N => L e) h
    simpa using this.symm
  · exact fderiv_zero_of_not_differentiableAt hdc

variable {α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ}
  {Φ : ComplexModel N → ComplexModel N → ComplexModel N}

/-- `ξ ↦ Φ(z', Λ' ξ) - c` has derivative `Λ'` at `0` (complex). -/
theorem hasFDerivAt_fibre_frame {O : Set (ComplexModel N × ComplexModel N)}
    (hΦ : IsLocalFibreMap Φ O) {z' : ComplexModel N} (hO : (z', (0 : ComplexModel N)) ∈ O)
    (Λ' : Op N) (c : ComplexModel N) :
    HasFDerivAt (fun ξ => Φ z' (Λ' ξ) - c) Λ' (0 : ComplexModel N) := by
  have hdc : DifferentiableAt ℂ (Φ z') 0 := hΦ.holo (z', 0) hO
  have hid : fderiv ℂ (Φ z') 0 = ContinuousLinearMap.id ℂ (ComplexModel N) := by
    have h := hdc.fderiv_restrictScalars ℝ
    rw [hΦ.fderiv_zero z' hO] at h
    refine ContinuousLinearMap.ext fun x => ?_
    have := congrArg (fun L : ComplexModel N →L[ℝ] ComplexModel N => L x) h
    simpa using this.symm
  have hd : DifferentiableAt ℂ (Φ z') (Λ' 0) := by rw [map_zero]; exact hdc
  have h := (hd.hasFDerivAt.comp (0 : ComplexModel N) Λ'.hasFDerivAt).sub_const c
  rw [map_zero, hid, ContinuousLinearMap.id_comp] at h
  exact h

/-- **Adapted fibre maps at all centres near `z₁`, with uniform constants** (steps (W), (T)). -/
theorem exists_local_centerData {O : Set (ComplexModel N × ComplexModel N)}
    {U K : Set (ComplexModel N)} (hD : ChartData Φ O α U K) {z₁ : ComplexModel N}
    (hz₁ : z₁ ∈ K) :
    ∃ ε > 0, ∃ σ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ z₀ ∈ ball z₁ ε,
      ∃ F : ComplexModel N → ComplexModel N → ComplexModel N,
        DN4.CenterData F σ σ M M M ∧
        ∀ z' ∈ ball z₀ σ, ∀ (p : ComplexModel N → ℝ) (w : ℂ), ‖w‖ < σ →
          localSmoothing Φ α p z' ‖w‖ = DN4.jointSmoothing F (fun y => p (z₀ + y)) (z' - z₀, w) := by
  have hD' := hD
  obtain ⟨hΦ, hU, hα, hαpos, -, hKU, hKO⟩ := hD'
  obtain ⟨Λ, Fh, s, hs, hFh, hreg, hcen⟩ := exists_family hD (hKU hz₁) (hKO z₁ hz₁)
  -- the family at explicit points
  have hreg' : ∀ z₀ z ξ : ComplexModel N, dist z₀ z₁ < s → ‖z‖ < s → ‖ξ‖ < s →
      Fh (z₀, (z, ξ)) = Φ (z₀ + z) (Λ z₀ (z₀ + z) ξ) - z₀ ∧
        (z₀ + z, Λ z₀ (z₀ + z) ξ) ∈ O ∧ z₀ + z ∈ U ∧ IsUnit (Λ z₀ (z₀ + z)) ∧
        ∀ u v, α (z₀ + z) ![Λ z₀ (z₀ + z) u, Λ z₀ (z₀ + z) v] = flatForm N ![u, v] :=
    fun z₀ z ξ h0 h1 h2 => hreg _ (mem_ball_triple h0 h1 h2)
  have hev : ∀ z₀ z : ComplexModel N, dist z₀ z₁ < s → ‖z‖ < s → ∀ ξ : ComplexModel N, ‖ξ‖ < s →
      (fun ξ' => Fh (z₀, (z, ξ'))) =ᶠ[𝓝 ξ] fun ξ' => Φ (z₀ + z) (Λ z₀ (z₀ + z) ξ') - z₀ := by
    intro z₀ z h0 h1 ξ h2
    have hball : ball (0 : ComplexModel N) s ∈ 𝓝 ξ :=
      isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; exact h2)
    filter_upwards [hball] with ξ' hξ'
    rw [mem_ball, dist_zero_right] at hξ'
    exact (hreg' z₀ z ξ' h0 h1 hξ').1
  have hO0 : ∀ z₀ z : ComplexModel N, dist z₀ z₁ < s → ‖z‖ < s →
      (z₀ + z, (0 : ComplexModel N)) ∈ O := by
    intro z₀ z h0 h1
    have h := (hreg' z₀ z 0 h0 h1 (by simpa using hs)).2.1
    rwa [map_zero] at h
  -- continuity of the derivatives of the family
  have hD1 : ContDiff ℝ ∞ (fun x : ComplexModel N × (ComplexModel N × ComplexModel N) =>
      fderiv ℝ (fun y => Fh (x.1, y)) x.2) :=
    ContDiff.fderiv (f := fun (x : ComplexModel N × (ComplexModel N × ComplexModel N))
      (y : ComplexModel N × ComplexModel N) => Fh (x.1, y))
      (hFh.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd (by simp)
  have hD2 : ContDiff ℝ ∞ (fun x : ComplexModel N × (ComplexModel N × ComplexModel N) =>
      fderiv ℝ (fun y => fderiv ℝ (fun y' => Fh (x.1, y')) y) x.2) :=
    ContDiff.fderiv (f := fun (x : ComplexModel N × (ComplexModel N × ComplexModel N))
      (y : ComplexModel N × ComplexModel N) => fderiv ℝ (fun y' => Fh (x.1, y')) y)
      (hD1.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd (by simp)
  have hKc : IsCompact (closedBall z₁ (s / 2) ×ˢ
      (closedBall (0 : ComplexModel N) (s / 2) ×ˢ closedBall (0 : ComplexModel N) (s / 2))) :=
    (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn hD1.continuous.continuousOn
  have hD2c : Continuous (fun x : ComplexModel N × (ComplexModel N × ComplexModel N) =>
      fderiv ℝ (fun y => fderiv ℝ (fun y' => Fh (x.1, y')) y) x.2) := hD2.continuous
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (E := ComplexModel N × ComplexModel N →L[ℝ]
    ComplexModel N × ComplexModel N →L[ℝ] ComplexModel N) hD2c.continuousOn
  -- holomorphy in the fibre
  have hdiffz : ∀ z₀ z ξ : ComplexModel N, dist z₀ z₁ < s → ‖z‖ < s → ‖ξ‖ < s →
      DifferentiableAt ℂ (fun ξ' => Fh (z₀, (z, ξ'))) ξ := by
    intro z₀ z ξ h0 h1 h2
    have hO := (hreg' z₀ z ξ h0 h1 h2).2.1
    have hd : DifferentiableAt ℂ (fun ξ' => Φ (z₀ + z) (Λ z₀ (z₀ + z) ξ') - z₀) ξ :=
      ((hΦ.holo _ hO).comp ξ (Λ z₀ (z₀ + z)).differentiableAt).sub_const z₀
    exact hd.congr_of_eventuallyEq (hev z₀ z h0 h1 ξ h2)
  have hs0 : ‖(0 : ComplexModel N)‖ < s := by simpa using hs
  -- the inverse bound
  have hAr : Continuous (fun q : ComplexModel N × ComplexModel N =>
      fderiv ℝ (fun ξ => Fh (q.1, (0, ξ))) q.2) :=
    (ContDiff.fderiv (m := ∞) (n := 0)
      (f := fun (q : ComplexModel N × ComplexModel N) (ξ : ComplexModel N) => Fh (q.1, (0, ξ)))
      (hFh.comp ((contDiff_fst.comp contDiff_fst).prodMk
        ((contDiff_const (c := (0 : ComplexModel N))).prodMk contDiff_snd))) contDiff_snd
      (by simp)).continuous
  have hRo : IsOpen (ball z₁ s ×ˢ ball (0 : ComplexModel N) s) := isOpen_ball.prod isOpen_ball
  have hAc : ContinuousOn (fun q : ComplexModel N × ComplexModel N =>
      fderiv ℂ (fun ξ => Fh (q.1, (0, ξ))) q.2) (ball z₁ s ×ˢ ball (0 : ComplexModel N) s) := by
    have hind : Topology.IsInducing (fun B : Op N => B.restrictScalars ℝ) :=
      (ContinuousLinearMap.restrictScalarsIsometry ℂ (ComplexModel N) (ComplexModel N) ℝ
        ℝ).isometry.isUniformInducing.isInducing
    rw [hind.continuousOn_iff]
    refine hAr.continuousOn.congr fun q hq => ?_
    have h0 : dist q.1 z₁ < s := hq.1
    have h2 : ‖q.2‖ < s := mem_ball_zero_iff.mp hq.2
    exact ((hdiffz q.1 0 q.2 h0 hs0 h2).fderiv_restrictScalars ℝ).symm
  have hunit : ∀ x ∈ closedBall z₁ (s / 2),
      (fderiv ℂ (fun ξ => Fh ((x, (0 : ComplexModel N)).1, (0, ξ)))
        (x, (0 : ComplexModel N)).2).IsInvertible := by
    intro x hx
    have h0 : dist x z₁ < s := by rw [mem_closedBall] at hx; linarith
    have hO := hO0 x 0 h0 hs0
    have hf := (hasFDerivAt_fibre_frame hΦ hO (Λ x (x + 0)) x)
    have heq := (hev x 0 h0 hs0 0 hs0).fderiv_eq (𝕜 := ℂ)
    change (fderiv ℂ (fun ξ => Fh (x, (0, ξ))) 0).IsInvertible
    rw [heq, hf.fderiv]
    exact isInvertible_of_isUnit (hreg' x 0 0 h0 hs0 hs0).2.2.2.1
  obtain ⟨r, hr, M₀, hM₀⟩ := exists_uniform_inverse_bound hRo hAc (isCompact_closedBall z₁ (s / 2))
    (fun x hx => mk_mem_prod (show dist x z₁ < s by rw [mem_closedBall] at hx; linarith)
      (mem_ball_self hs)) hunit
  -- the constants
  refine ⟨s / 2, half_pos hs, min (s / 2) r, lt_min (half_pos hs) hr,
    max (max M₀ M₁) (max M₂ 0), le_max_of_le_right (le_max_right _ _), fun z₀ hz₀ => ?_⟩
  have hz₀c : z₀ ∈ closedBall z₁ (s / 2) := ball_subset_closedBall hz₀
  have h0 : dist z₀ z₁ < s := by rw [mem_ball] at hz₀; linarith
  have hσs : min (s / 2) r < s := (min_le_left _ _).trans_lt (half_lt_self hs)
  have hσ2 : min (s / 2) r ≤ s / 2 := min_le_left _ _
  have hσr : min (s / 2) r ≤ r := min_le_right _ _
  have hσpos : 0 < min (s / 2) r := lt_min (half_pos hs) hr
  refine ⟨fun z ξ => Fh (z₀, (z, ξ)), ?_, ?_⟩
  · have hH : ContDiff ℝ ∞ (DN4.uncurryF fun z ξ => Fh (z₀, (z, ξ))) :=
      hFh.comp (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
    have hH2 : ContDiff ℝ 2 (DN4.uncurryF fun z ξ => Fh (z₀, (z, ξ))) :=
      hH.of_le (by norm_cast)
    refine ⟨hσpos, hσpos, hH.of_le (by norm_cast), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz ξ hξ
      exact (hdiffz z₀ z ξ h0 ((mem_ball_zero_iff.mp hz).trans hσs)
        ((mem_ball_zero_iff.mp hξ).trans hσs)).differentiableWithinAt
    · intro z hz
      have h1 : ‖z‖ < s := (mem_ball_zero_iff.mp hz).trans hσs
      change Fh (z₀, (z, 0)) = z
      rw [(hreg' z₀ z 0 h0 h1 hs0).1, map_zero, hΦ.map_zero _ (hO0 z₀ z h0 h1),
        add_sub_cancel_left]
    · intro v
      refine centerCondition hH2 (hcen z₀ (by rw [mem_ball]; exact h0)).1 (fun e => ?_)
        (hcen z₀ (by rw [mem_ball]; exact h0)).2 v
      have hball : ball (0 : ComplexModel N) s ∈ 𝓝 (0 : ComplexModel N) := ball_mem_nhds 0 hs
      filter_upwards [hball] with z hz
      have h1 : ‖z‖ < s := mem_ball_zero_iff.mp hz
      have hf := (hasFDerivAt_fibre_frame hΦ (hO0 z₀ z h0 h1) (Λ z₀ (z₀ + z)) z₀).restrictScalars ℝ
      rw [(hev z₀ z h0 h1 0 hs0).fderiv_eq (𝕜 := ℝ), hf.fderiv]
      rfl
    · intro ξ hξ
      have hξr : ξ ∈ closedBall (0 : ComplexModel N) r :=
        ball_subset_closedBall (ball_subset_ball hσr hξ)
      exact (hM₀ z₀ hz₀c ξ hξr).1
    · intro ξ hξ
      have hξr : ξ ∈ closedBall (0 : ComplexModel N) r :=
        ball_subset_closedBall (ball_subset_ball hσr hξ)
      exact (hM₀ z₀ hz₀c ξ hξr).2.trans (le_max_of_le_left (le_max_left _ _))
    · intro ξ hξ
      have hmem : ((z₀, ((0 : ComplexModel N), ξ)) :
          ComplexModel N × (ComplexModel N × ComplexModel N)) ∈ closedBall z₁ (s / 2) ×ˢ
            (closedBall (0 : ComplexModel N) (s / 2) ×ˢ closedBall (0 : ComplexModel N) (s / 2)) :=
        mk_mem_prod hz₀c (mk_mem_prod (mem_closedBall_self (half_pos hs).le)
          (ball_subset_closedBall (ball_subset_ball hσ2 hξ)))
      exact (hM₁ _ hmem).trans (le_max_of_le_left (le_max_right _ _))
    · intro ξ hξ
      have hmem : ((z₀, ((0 : ComplexModel N), ξ)) :
          ComplexModel N × (ComplexModel N × ComplexModel N)) ∈ closedBall z₁ (s / 2) ×ˢ
            (closedBall (0 : ComplexModel N) (s / 2) ×ˢ closedBall (0 : ComplexModel N) (s / 2)) :=
        mk_mem_prod hz₀c (mk_mem_prod (mem_closedBall_self (half_pos hs).le)
          (ball_subset_closedBall (ball_subset_ball hσ2 hξ)))
      have h := hM₂ _ hmem
      exact h.trans (le_max_of_le_right (le_max_left _ _))
  · intro z' hz' p w hw
    have h1 : ‖z' - z₀‖ < s := by
      rw [mem_ball, dist_eq_norm] at hz'; exact hz'.trans hσs
    have hws : ‖w‖ < s := hw.trans hσs
    obtain ⟨-, -, -, hu, hn⟩ := hreg' z₀ (z' - z₀) 0 h0 h1 hs0
    rw [add_sub_cancel] at hu hn
    set L := ContinuousLinearEquiv.unitsEquiv ℂ (ComplexModel N) hu.unit
    have hL : ∀ x, L x = Λ z₀ z' x := fun x => by
      rw [ContinuousLinearEquiv.unitsEquiv_apply, IsUnit.unit_spec]
    have hnL : ∀ u v, α z' ![L u, L v] = flatForm N ![u, v] := fun u v => by
      rw [hL, hL]; exact hn u v
    rw [localSmoothing_eq_frame (Φ := Φ) hnL, integral_frame_rotate L (fun y => p (Φ z' y)) w]
    unfold DN4.jointSmoothing
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only
    by_cases hζ : ‖ζ‖ < 1
    · have hwζ : ‖w • ζ‖ < s := by
        rw [norm_smul]
        calc ‖w‖ * ‖ζ‖ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hζ.le (norm_nonneg _)
          _ < s := by rw [mul_one]; exact hws
      have hF := (hreg' z₀ (z' - z₀) (w • ζ) h0 h1 hwζ).1
      rw [hF, add_sub_cancel, add_sub_cancel, hL]
      rfl
    · push Not at hζ
      rw [DN3.kernel_eq_zero N hζ, DN4.chi_normSq_eq_zero hζ, mul_zero, mul_zero]

end SGPT.NPP.DN9
