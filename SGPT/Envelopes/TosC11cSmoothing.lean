import SGPT.Envelopes.TosC11cMollify
import SGPT.Envelopes.TosC11bLimit
import SGPT.Okounkov.TranscendentalWNRegBeta
import SGPT.Analysis.KahlerNormalUniform
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax

/-!
# Smoothing `C^{1,1}` obstacles with uniform bounds

Lane TOS-C11c (`claude-tos-c11c`, node `tos-c11c:smoothing`).  Source: Xia, *Foundations of
pluripotential theory*, proof of `thm:kahler-real-c11-envelope` ("using convolution in finitely many
charts and a smooth partition of unity, we obtain smooth functions `f_{j,ρ}` that converge to `f_j`
… and have uniformly bounded covariant Hessians"), for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

Let `D` be chart data on a compact complex manifold `Y` with a Kähler background `A`.  The main
result, `exists_smoothing`, gives a constant `κ` (depending only on `Y, A, D`) such that every
`f ∈ C^{1,1}(Y)` with `‖f‖_{C^{1,1}, D} ≤ B` is, for every `ε > 0`, `ε`-close to a chart-smooth `F` with

* `|F| ≤ B`;
* `‖D(F ∘ e_i⁻¹)‖ ≤ κB` and `‖D²(F ∘ e_i⁻¹)‖ ≤ κB` on every piece `K_i` of `D`;
* `ddᶜF ≤ κB · A` on every complex line, in every chart of the atlas.

`F = Σ_a χ_a · (g_a ∘ e_{i(a)})`, where `(χ_a)` is a chart-smooth partition of unity subordinate to the
cover by the `δ₀`-neighbourhoods of the pieces and `g_a` is the mollification of a cutoff of
`f ∘ e_{i(a)}⁻¹` (`exists_chart_mollify`).  Its derivatives in the charts of `D` are estimated by
Leibniz's and Faà di Bruno's bounds (`norm_iteratedFDerivWithin_mul_comp_le`), and the bound for
`ddᶜF` is transported to arbitrary charts by the transformation law of forms.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.C11Real

section Bounds

variable {n : ℕ}

theorem norm_iteratedFDerivWithin_one_of_isOpen {s : Set (ComplexModel n)} (hs : IsOpen s)
    {x : ComplexModel n} (hx : x ∈ s) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ComplexModel n → F) : ‖iteratedFDerivWithin ℝ 1 f s x‖ = ‖fderiv ℝ f x‖ := by
  rw [iteratedFDerivWithin_of_isOpen 1 hs hx, norm_iteratedFDeriv_one]

theorem norm_iteratedFDerivWithin_two_of_isOpen {s : Set (ComplexModel n)} (hs : IsOpen s)
    {x : ComplexModel n} (hx : x ∈ s) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ComplexModel n → F) :
    ‖iteratedFDerivWithin ℝ 2 f s x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [iteratedFDerivWithin_of_isOpen 2 hs hx, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_one]

/-- **Leibniz and Faà di Bruno** for `p · (g ∘ τ)` up to order two at a point of an open set: if
the derivatives of order `≤ 2` of `p` at `x` are bounded by `P`, those of order `1, 2` of `τ` by
`T ≥ 1`, and those of order `≤ 2` of `g` everywhere by `Γ`, then the derivatives of order `≤ 2` of
`p · (g ∘ τ)` at `x` are bounded by `8 P Γ T²`. -/
theorem norm_iteratedFDerivWithin_mul_comp_le {s : Set (ComplexModel n)} (hs : IsOpen s)
    {p : ComplexModel n → ℝ} {τ : ComplexModel n → ComplexModel n} {g : ComplexModel n → ℝ}
    (hp : ContDiffOn ℝ 2 p s) (hτ : ContDiffOn ℝ 2 τ s) (hg : ContDiff ℝ 2 g)
    {x : ComplexModel n} (hx : x ∈ s) {P T Γ : ℝ} (hT : 1 ≤ T)
    (hP : ∀ l ≤ 2, ‖iteratedFDerivWithin ℝ l p s x‖ ≤ P)
    (hTd : ∀ l, 1 ≤ l → l ≤ 2 → ‖iteratedFDerivWithin ℝ l τ s x‖ ≤ T)
    (hΓ : ∀ l ≤ 2, ∀ y, ‖iteratedFDeriv ℝ l g y‖ ≤ Γ) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDerivWithin ℝ k (fun w => p w * g (τ w)) s x‖ ≤ 8 * P * Γ * T ^ 2 := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (by norm_num))
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0 (by norm_num) 0)
  have hcomp : ∀ m ≤ 2, ‖iteratedFDerivWithin ℝ m (g ∘ τ) s x‖ ≤ 2 * Γ * T ^ 2 := by
    intro m hm
    have h := norm_iteratedFDerivWithin_comp_le (n := m) (N := 2) hg.contDiffOn hτ
      (by exact_mod_cast hm) uniqueDiffOn_univ hs.uniqueDiffOn (mapsTo_univ _ _) hx
      (C := Γ) (D := T) (fun i hi => by rw [iteratedFDerivWithin_univ]; exact hΓ i (hi.trans hm) _)
      (fun i hi1 hi2 => (hTd i hi1 (hi2.trans hm)).trans (le_self_pow₀ hT (by omega)))
    have hf : (m.factorial : ℝ) ≤ 2 := by interval_cases m <;> norm_num
    have hTm : T ^ m ≤ T ^ 2 := pow_le_pow_right₀ hT hm
    calc _ ≤ (m.factorial : ℝ) * Γ * T ^ m := h
      _ ≤ 2 * Γ * T ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hf hΓ0) hTm (by positivity) (by positivity)
  have hmul := norm_iteratedFDerivWithin_mul_le (n := k) (N := 2) hp (hg.comp_contDiffOn hτ)
    hs.uniqueDiffOn hx (by exact_mod_cast hk)
  refine hmul.trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i p s x‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (g ∘ τ) s x‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * P * (2 * Γ * T ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hP i (hi'.trans hk)) (Nat.cast_nonneg _))
          (hcomp (k - i) ((Nat.sub_le k i).trans hk)) (norm_nonneg _) (by positivity)
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (P * (2 * Γ * T ^ 2)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 2 ^ k * (P * (2 * Γ * T ^ 2)) := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    _ ≤ 8 * P * Γ * T ^ 2 := by
        have h4 : (2 : ℝ) ^ k ≤ 4 := by interval_cases k <;> norm_num
        have h0 : 0 ≤ P * (2 * Γ * T ^ 2) := by positivity
        nlinarith

end Bounds

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A chart-smooth function supported in the source of a chart `e`, times a smooth function of the
`e`-coordinates, is chart-smooth. -/
theorem chartSmooth_mul_comp {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ) (e : ComplexChart N Y)
    (hχe : tsupport χ ⊆ e.val.source) {g : ComplexModel N → ℝ} (hg : ContDiff ℝ ∞ g) :
    ChartSmooth (n := N) (fun y => χ y * g (e.val y)) := by
  intro f
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  by_cases hzs : f.val.symm z ∈ e.val.source
  · refine ⟨(chartTransition f e).source, (chartTransition f e).open_source, ⟨hz, hzs⟩, ?_⟩
    have h1 : ContDiffOn ℝ ∞ (fun w => χ (f.val.symm w))
        (f.val.target ∩ (chartTransition f e).source) := (hχ f).mono inter_subset_left
    have h2 : ContDiffOn ℝ ∞ (fun w => g (chartTransition f e w))
        (f.val.target ∩ (chartTransition f e).source) :=
      hg.comp_contDiffOn ((contDiffOn_chartTransition f e).mono inter_subset_right)
    exact h1.mul h2
  · have hnot : f.val.symm z ∉ tsupport χ := fun h => hzs (hχe h)
    refine ⟨f.val.target ∩ f.val.symm ⁻¹' (tsupport χ)ᶜ,
      f.val.continuousOn_symm.isOpen_inter_preimage f.val.open_target
        (isClosed_tsupport χ).isOpen_compl, ⟨hz, hnot⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : ℝ))).congr fun w hw => ?_
    simp [image_eq_zero_of_notMem_tsupport hw.2.2]

/-- **Mollification in one chart of `D`** (FPT, proof of `thm:kahler-real-c11-envelope`).  If the
closed `4δ₀`-thickening of the piece `K_i` lies in the chart target, there is `κ` such that for every
`f` which is `C¹` in every chart with `‖f‖_{C^{1,1}, D} ≤ B` and every `ρ > 0` there is a smooth
`g : ℂᴺ → ℝ` with `|g| ≤ B`, `‖Dg‖, ‖D²g‖ ≤ κB` and `|g - f ∘ e_i⁻¹| ≤ κBρ` on the closed
`2δ₀`-thickening of `K_i`. -/
theorem exists_chart_mollify (D : C11ChartData N Y) (i : Fin D.card) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hδU : cthickening (4 * δ₀) (D.piece i) ⊆ (D.chart i).val.target) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (f : Y → ℝ) (B : ℝ), 0 ≤ B →
      (∀ e' : ComplexChart N Y, ContDiffOn ℝ 1 (fun z => f (e'.val.symm z)) e'.val.target) →
      C11Bound D f B → ∀ ρ : ℝ, 0 < ρ →
      ∃ g : ComplexModel N → ℝ, ContDiff ℝ ∞ g ∧ (∀ z, |g z| ≤ B) ∧
        (∀ z, ‖fderiv ℝ g z‖ ≤ κ * B) ∧ (∀ z, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ κ * B) ∧
        ∀ z ∈ cthickening (2 * δ₀) (D.piece i), |g z - f ((D.chart i).val.symm z)| ≤ κ * B * ρ := by
  set e := D.chart i with he
  set K := D.piece i with hK
  have hKc : IsCompact K := D.isCompact_piece i
  -- the cutoff
  obtain ⟨ψ, hψ, hψ1, hψ0, hψr⟩ := exists_cutoff (s := cthickening (2 * δ₀) K)
    (t := thickening (3 * δ₀) K) isClosed_cthickening isOpen_thickening
    (cthickening_subset_thickening' (by positivity) (by linarith) K)
  have hψs : tsupport ψ ⊆ cthickening (3 * δ₀) K := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening _ _)
    intro z hz
    by_contra h
    exact hz (hψ0 z h)
  have hψc : HasCompactSupport ψ :=
    hKc.cthickening.of_isClosed_subset (isClosed_tsupport ψ) hψs
  obtain ⟨C1, hC1⟩ := (hψc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hψ.continuous_fderiv (by simp))
  have hc2 : HasCompactSupport (iteratedFDeriv ℝ 2 ψ) := hψc.iteratedFDeriv 2
  have hcont2 : Continuous (iteratedFDeriv ℝ 2 ψ) :=
    hψ.continuous_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨C2, hC2'⟩ := hc2.exists_bound_of_continuous hcont2
  have hC2 : ∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ C2 := fun x => by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact hC2' x
  set Cψ := max C1 C2 with hCψ
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans ((hC1 0).trans (le_max_left _ _))
  -- the transfer constant on the `4δ₀`-thickening
  obtain ⟨CT, hCT0, hCT⟩ := exists_c11_transfer D e (hKc.cthickening (r := 4 * δ₀)) hδU
  set κ : ℝ := (Cψ + CT) + (CT + 2 * CT * Cψ + Cψ + 2 * (Cψ + CT) / δ₀) with hκ
  have hb0 : 0 ≤ CT + 2 * CT * Cψ + Cψ + 2 * (Cψ + CT) / δ₀ := by positivity
  refine ⟨κ, by positivity, fun f B hB hf hfB ρ hρ => ?_⟩
  obtain ⟨hgrad, hlip⟩ := hCT f B hB hf hfB
  have hK43 : cthickening δ₀ (cthickening (3 * δ₀) K) ⊆ cthickening (4 * δ₀) K :=
    (cthickening_cthickening_subset hδ₀.le (by positivity) K).trans
      (cthickening_mono (le_of_eq (by ring)) K)
  obtain ⟨hsm, hval, hder, hdlip⟩ := cutoff_mul_bounds (U := e.val.target)
    (K₃ := cthickening (3 * δ₀) K) hδ₀ e.val.open_target (hK43.trans hδU) hψ hψs
    (fun z => abs_le.mpr ⟨by linarith [(hψr z).1], (hψr z).2⟩) (Cψ := Cψ)
    (fun z => (hC1 z).trans (le_max_left _ _)) (fun z => (hC2 z).trans (le_max_right _ _))
    (hf e) (B := B) (G := CT * B) (L := CT * B) hB (by positivity) (by positivity)
    (fun z _ => hfB.1 _) (fun z hz => hgrad z (hK43 hz))
    (fun x hx y hy hseg => hlip y (hK43 hy) x (hK43 hx) (by rw [segment_symm]; exact hseg.trans hK43))
  obtain ⟨g, hg, hgB, hgD, hgD2, hgu⟩ := exists_mollify hsm (by positivity) (by positivity) hval hder
    hdlip hρ
  have hG : B * Cψ + CT * B ≤ κ * B := by
    have : (Cψ + CT) * B ≤ κ * B :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb0) hB
    linarith
  have hL : CT * B + 2 * (CT * B) * Cψ + B * Cψ + 2 * (B * Cψ + CT * B) / δ₀ ≤ κ * B := by
    have h1 : (CT + 2 * CT * Cψ + Cψ + 2 * (Cψ + CT) / δ₀) * B ≤ κ * B :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hB
    have h2 : CT * B + 2 * (CT * B) * Cψ + B * Cψ + 2 * (B * Cψ + CT * B) / δ₀ =
        (CT + 2 * CT * Cψ + Cψ + 2 * (Cψ + CT) / δ₀) * B := by ring
    linarith
  refine ⟨g, hg, hgB, fun z => (hgD z).trans hG, fun z => (hgD2 z).trans hL, fun z hz => ?_⟩
  have h := hgu z
  rw [hψ1 z hz, one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right hG hρ.le)

/-- Bounds for the derivatives of order `≤ 2` of a smooth function on a compact subset of an open set
of `ℂᴺ`. -/
theorem exists_iteratedFDerivWithin_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ComplexModel N → F} {U K : Set (ComplexModel N)} (hU : IsOpen U)
    (hp : ContDiffOn ℝ ∞ p U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ l ≤ 2, ∀ z ∈ K, ‖iteratedFDerivWithin ℝ l p U z‖ ≤ P := by
  have h : ∀ l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖iteratedFDerivWithin ℝ l p U z‖ ≤ C := fun l =>
    exists_norm_le_of_continuousOn ((hp.continuousOn_iteratedFDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl l) hU.uniqueDiffOn).mono hKU) hK
  choose C hC0 hC using h
  refine ⟨C 0 + C 1 + C 2, add_nonneg (add_nonneg (hC0 0) (hC0 1)) (hC0 2), fun l hl z hz => ?_⟩
  have h0 := hC0 0
  have h1 := hC0 1
  have h2 := hC0 2
  interval_cases l
  · linarith [hC 0 z hz]
  · linarith [hC 1 z hz]
  · linarith [hC 2 z hz]

/-- **One term of a partitioned convolution, in another chart**: the derivatives of order `≤ 2` of
`w ↦ χ(e⁻¹ w) g(e'(e⁻¹ w))` at `z` are bounded by `8 P Γ T²`, if `χ` is supported in the source of
`e'`, the derivatives of `χ ∘ e⁻¹` at `z` are bounded by `P`, those of `g` by `Γ`, and those of the
transition `e' ∘ e⁻¹` at `z` by `T ≥ 1` (needed only when `e⁻¹ z` lies in the support of `χ`). -/
theorem norm_iteratedFDerivWithin_chart_term_le {χ : Y → ℝ} (hχ : ChartSmooth (n := N) χ)
    (e e' : ComplexChart N Y) (hχe : tsupport χ ⊆ e'.val.source) {g : ComplexModel N → ℝ}
    (hg : ContDiff ℝ ∞ g) {z : ComplexModel N} (hz : z ∈ e.val.target) {P T Γ : ℝ} (hT : 1 ≤ T)
    (hP0 : 0 ≤ P) (hΓ0 : 0 ≤ Γ)
    (hP : ∀ l ≤ 2, ‖iteratedFDerivWithin ℝ l (fun w => χ (e.val.symm w)) e.val.target z‖ ≤ P)
    (hTd : e.val.symm z ∈ tsupport χ → ∀ l, 1 ≤ l → l ≤ 2 →
      ‖iteratedFDerivWithin ℝ l (chartTransition e e') (chartTransition e e').source z‖ ≤ T)
    (hΓ : ∀ l ≤ 2, ∀ y, ‖iteratedFDeriv ℝ l g y‖ ≤ Γ) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDerivWithin ℝ k (fun w => χ (e.val.symm w) * g (e'.val (e.val.symm w)))
      e.val.target z‖ ≤ 8 * P * Γ * T ^ 2 := by
  have hU : IsOpen e.val.target := e.val.open_target
  by_cases hzQ : e.val.symm z ∈ tsupport χ
  · set τ := chartTransition e e' with hτ
    have hzs : z ∈ τ.source := ⟨hz, hχe hzQ⟩
    have hτsub : τ.source ⊆ e.val.target := fun w hw => hw.1
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
    rw [iteratedFDerivWithin_of_isOpen k hU hz,
      ← iteratedFDerivWithin_of_isOpen k τ.open_source hzs]
    refine norm_iteratedFDerivWithin_mul_comp_le (p := fun w => χ (e.val.symm w)) (τ := τ)
      τ.open_source (((hχ e).mono hτsub).of_le h2) ((contDiffOn_chartTransition e e').of_le h2)
      (hg.of_le h2) hzs hT ?_ (hTd hzQ) hΓ hk
    intro l hl
    rw [iteratedFDerivWithin_of_isOpen l τ.open_source hzs,
      ← iteratedFDerivWithin_of_isOpen l hU hz]
    exact hP l hl
  · have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (tsupport χ)ᶜ) :=
      e.val.continuousOn_symm.isOpen_inter_preimage hU (isClosed_tsupport χ).isOpen_compl
    have hev : (fun w => χ (e.val.symm w) * g (e'.val (e.val.symm w))) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds ⟨hz, hzQ⟩] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw.2]
    rw [iteratedFDerivWithin_of_isOpen k hU hz, (hev.iteratedFDeriv ℝ k).eq_of_nhds,
      iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity

/-- **Transport of a line bound between forms**: if `a ≤ c b` on complex lines at the points of the
pieces of `D`, read in the charts of `D`, then `a ≤ c b` on complex lines in every chart. -/
theorem coeff_line_le_of_pieces (D : C11ChartData N Y) (a b : SmoothRealForm N Y 2) {c : ℝ}
    (h : ∀ j, ∀ z ∈ D.piece j, ∀ v : ComplexModel N,
      a.coeff (D.chart j) z ![v, Complex.I • v] ≤ c * b.coeff (D.chart j) z ![v, Complex.I • v])
    (e : ComplexChart N Y) {z : ComplexModel N} (hz : z ∈ e.val.target) (v : ComplexModel N) :
    a.coeff e z ![v, Complex.I • v] ≤ c * b.coeff e z ![v, Complex.I • v] := by
  set x := e.val.symm z with hx
  have hxe : x ∈ e.val.source := e.val.map_target hz
  have hex : e.val x = z := e.val.right_inv hz
  obtain ⟨j, p, hp, hpx⟩ := D.cover x
  have hxj : x ∈ (D.chart j).val.source := by
    rw [← hpx]; exact (D.chart j).val.map_target (D.piece_subset j hp)
  have hjx : (D.chart j).val x ∈ D.piece j := by
    rw [← hpx, (D.chart j).val.right_inv (D.piece_subset j hp)]; exact hp
  have h1 := RelativeEigenvalueMax.coeff_line_transfer a hxe hxj v
  have h2 := RelativeEigenvalueMax.coeff_line_transfer b hxe hxj v
  simp only [RelativeEigenvalueMax.line] at h1 h2
  rw [hex] at h1 h2
  rw [h1, h2]
  exact h j _ hjx _

/-- The open cover of `Y` by the `δ₀`-neighbourhoods of the pieces of `D`, read in their charts. -/
def pieceNbhd (D : C11ChartData N Y) (δ₀ : ℝ) (i : Fin D.card) : TopologicalSpace.Opens Y :=
  ⟨(D.chart i).val.source ∩ (D.chart i).val ⁻¹' thickening δ₀ (D.piece i),
    (D.chart i).val.continuousOn.isOpen_inter_preimage (D.chart i).val.open_source
      isOpen_thickening⟩

omit [IsComplexManifold N Y] in
theorem mem_pieceNbhd (D : C11ChartData N Y) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (y : Y) :
    ∃ i, y ∈ pieceNbhd D δ₀ i := by
  obtain ⟨i, p, hp, hpy⟩ := D.cover y
  refine ⟨i, ?_, ?_⟩
  · rw [← hpy]; exact (D.chart i).val.map_target (D.piece_subset i hp)
  · show (D.chart i).val y ∈ thickening δ₀ (D.piece i)
    rw [← hpy, (D.chart i).val.right_inv (D.piece_subset i hp)]
    exact self_subset_thickening hδ₀ _ hp

/-- **Smoothing of `C^{1,1}` obstacles with uniform bounds** (FPT, proof of
`thm:kahler-real-c11-envelope`).  On a compact complex manifold with a Kähler background `A` and chart
data `D` there is `κ ≥ 0` such that every `f`, `C¹` in every chart with `‖f‖_{C^{1,1}, D} ≤ B`, is for
every `ε > 0` within `ε` of a chart-smooth `F` with `|F| ≤ B`, `‖D(F ∘ e_i⁻¹)‖, ‖D²(F ∘ e_i⁻¹)‖ ≤ κB`
on the pieces `K_i`, and `ddᶜF ≤ κB · A` on every complex line in every chart. -/
theorem exists_smoothing [CompactSpace Y] (A : KahlerBackground N Y) (D : C11ChartData N Y) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (f : Y → ℝ) (B : ℝ), 0 ≤ B →
      (∀ e' : ComplexChart N Y, ContDiffOn ℝ 1 (fun z => f (e'.val.symm z)) e'.val.target) →
      C11Bound D f B → ∀ ε : ℝ, 0 < ε →
      ∃ (F : Y → ℝ) (hF : ChartSmooth (n := N) F), (∀ y, |F y - f y| ≤ ε) ∧ (∀ y, |F y| ≤ B) ∧
        (∀ i, ∀ z ∈ D.piece i, ‖fderiv ℝ (fun z => F ((D.chart i).val.symm z)) z‖ ≤ κ * B ∧
          ‖fderiv ℝ (fderiv ℝ (fun z => F ((D.chart i).val.symm z))) z‖ ≤ κ * B) ∧
        ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v : ComplexModel N,
          (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
            κ * B * A.form.val.coeff e z ![v, Complex.I • v] := by
  classical
  -- the scale `δ₀`
  obtain ⟨δ, hδ, hδU⟩ := TosC11b.C11ChartData.exists_cthickening_subset D
  have hδ₀ : 0 < δ / 4 := by positivity
  have hδ₀U : ∀ i, cthickening (4 * (δ / 4)) (D.piece i) ⊆ (D.chart i).val.target := fun i => by
    rw [show 4 * (δ / 4) = δ by ring]; exact hδU i
  -- local mollification in every chart of `D`
  choose κl hκl0 hκl using fun i => exists_chart_mollify D i hδ₀ (hδ₀U i)
  have hκ₁0 : 0 ≤ ∑ i, κl i := Finset.sum_nonneg fun i _ => hκl0 i
  have hκl_le : ∀ i, κl i ≤ ∑ i, κl i := fun i =>
    Finset.single_le_sum (f := κl) (fun j _ => hκl0 j) (Finset.mem_univ i)
  -- the partition of unity
  obtain ⟨m, χ, idx, hχ, hχ0, hχs, -, hχ1⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := N) (pieceNbhd D (δ / 4))
      (mem_pieceNbhd D hδ₀)
  have hχsrc : ∀ a, tsupport (χ a) ⊆ (D.chart (idx a)).val.source := fun a =>
    (hχs a).trans inter_subset_left
  -- bounds for the coefficients `χ_a ∘ e_j⁻¹` on the pieces
  choose P hP0 hP using fun j a => exists_iteratedFDerivWithin_bound (p := fun w => χ a
    ((D.chart j).val.symm w)) (D.chart j).val.open_target (hχ a (D.chart j))
    (D.isCompact_piece j) (D.piece_subset j)
  -- bounds for the transitions `e_{i(a)} ∘ e_j⁻¹` over the support of `χ_a`
  have hTb : ∀ j a, ∃ T : ℝ, 1 ≤ T ∧ ∀ z ∈ D.piece j, (D.chart j).val.symm z ∈ tsupport (χ a) →
      ∀ l, 1 ≤ l → l ≤ 2 → ‖iteratedFDerivWithin ℝ l (chartTransition (D.chart j) (D.chart (idx a)))
        (chartTransition (D.chart j) (D.chart (idx a))).source z‖ ≤ T := by
    intro j a
    set Q := D.piece j ∩ (D.chart j).val.symm ⁻¹' tsupport (χ a) with hQ
    have hQc : IsCompact Q := (D.isCompact_piece j).of_isClosed_subset
      (((D.chart j).val.continuousOn_symm.mono (D.piece_subset j)).preimage_isClosed_of_isClosed
        (D.isCompact_piece j).isClosed (isClosed_tsupport _)) inter_subset_left
    have hQs : Q ⊆ (chartTransition (D.chart j) (D.chart (idx a))).source := fun z hz =>
      ⟨D.piece_subset j hz.1, hχsrc a hz.2⟩
    obtain ⟨P', hP'0, hP'⟩ := exists_iteratedFDerivWithin_bound
      (chartTransition (D.chart j) (D.chart (idx a))).open_source
      (contDiffOn_chartTransition (D.chart j) (D.chart (idx a))) hQc hQs
    exact ⟨1 + P', by linarith, fun z hz hzs l _ hl =>
      (hP' l hl z ⟨hz, hzs⟩).trans (by linarith)⟩
  choose T hT1 hT using hTb
  set κ₂ : ℝ := ∑ j, ∑ a, 8 * P j a * (1 + ∑ i, κl i) * T j a ^ 2 with hκ₂
  have hκ₂j : ∀ j, 0 ≤ ∑ a, 8 * P j a * (1 + ∑ i, κl i) * T j a ^ 2 := fun j =>
    Finset.sum_nonneg fun a _ => by have := hP0 j a; positivity
  have hκ₂0 : 0 ≤ κ₂ := Finset.sum_nonneg fun j _ => hκ₂j j
  have hκ₂le : ∀ j, ∑ a, 8 * P j a * (1 + ∑ i, κl i) * T j a ^ 2 ≤ κ₂ := fun j =>
    Finset.single_le_sum (f := fun j => ∑ a, 8 * P j a * (1 + ∑ i, κl i) * T j a ^ 2)
      (fun j _ => hκ₂j j) (Finset.mem_univ j)
  -- positivity of `A` on the pieces
  choose μ hμ0 hμ using fun j => SGPT.Analysis.KahlerNormal.exists_pos_le_apply_I_smul
    ((A.form.val.smooth (D.chart j)).continuousOn)
    (fun z hz => (A.isKahler.1 (D.chart j) z hz).2) (D.isCompact_piece j) (D.piece_subset j)
  have hM0 : 0 ≤ ∑ j, (μ j)⁻¹ := Finset.sum_nonneg fun j _ => (inv_pos.mpr (hμ0 j)).le
  have hMle : ∀ j, (μ j)⁻¹ ≤ ∑ j, (μ j)⁻¹ := fun j =>
    Finset.single_le_sum (f := fun j => (μ j)⁻¹) (fun j _ => (inv_pos.mpr (hμ0 j)).le)
      (Finset.mem_univ j)
  set κ₃ : ℝ := κ₂ * ∑ j, (μ j)⁻¹ with hκ₃
  have hκ₃0 : 0 ≤ κ₃ := mul_nonneg hκ₂0 hM0
  refine ⟨∑ i, κl i + κ₂ + κ₃, by positivity, fun f B hB hf hfB ε hε => ?_⟩
  -- the mollification scale
  set ρ : ℝ := ε / ((∑ i, κl i) * B + 1) with hρdef
  have hden : 0 < (∑ i, κl i) * B + 1 := by positivity
  have hρ : 0 < ρ := div_pos hε hden
  have hκρ : (∑ i, κl i) * B * ρ ≤ ε := by
    rw [hρdef, mul_div_assoc', div_le_iff₀ hden]
    nlinarith
  choose g hg hgB hgD hgD2 hgf using fun i => hκl i f B hB hf hfB ρ hρ
  set F : Y → ℝ := fun y => ∑ a, χ a y * g (idx a) ((D.chart (idx a)).val y) with hFdef
  have hterm_smooth : ∀ a, ChartSmooth (n := N)
      (fun y => χ a y * g (idx a) ((D.chart (idx a)).val y)) := fun a =>
    chartSmooth_mul_comp (hχ a) (D.chart (idx a)) (hχsrc a) (hg (idx a))
  have hF : ChartSmooth (n := N) F := fun e =>
    ContDiffOn.sum fun a _ => hterm_smooth a e
  -- closeness on the support of each `χ_a`
  have hclose : ∀ a y, χ a y ≠ 0 → |g (idx a) ((D.chart (idx a)).val y) - f y| ≤ ε := by
    intro a y hy
    have hys : y ∈ (pieceNbhd D (δ / 4) (idx a) : Set Y) := hχs a (subset_tsupport _ hy)
    have hz : (D.chart (idx a)).val y ∈ cthickening (2 * (δ / 4)) (D.piece (idx a)) :=
      cthickening_mono (by linarith) _ (thickening_subset_cthickening _ _ hys.2)
    have h := hgf (idx a) _ hz
    rw [(D.chart (idx a)).val.left_inv hys.1] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hκl_le _) hB)
      hρ.le).trans hκρ)
  have happrox : ∀ y, |F y - f y| ≤ ε := by
    intro y
    have hsplit : F y - f y = ∑ a, χ a y * (g (idx a) ((D.chart (idx a)).val y) - f y) := by
      have : ∑ a, χ a y * (g (idx a) ((D.chart (idx a)).val y) - f y) =
          F y - (∑ a, χ a y) * f y := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [this, hχ1 y, one_mul]
    rw [hsplit]
    calc |∑ a, χ a y * (g (idx a) ((D.chart (idx a)).val y) - f y)|
        ≤ ∑ a, |χ a y * (g (idx a) ((D.chart (idx a)).val y) - f y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, χ a y * ε := Finset.sum_le_sum fun a _ => by
          rw [abs_mul, abs_of_nonneg (hχ0 a y)]
          by_cases h0 : χ a y = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left (hclose a y h0) (hχ0 a y)
      _ = ε := by rw [← Finset.sum_mul, hχ1 y, one_mul]
  have hbound : ∀ y, |F y| ≤ B := by
    intro y
    calc |F y| ≤ ∑ a, |χ a y * g (idx a) ((D.chart (idx a)).val y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, χ a y * B := Finset.sum_le_sum fun a _ => by
          rw [abs_mul, abs_of_nonneg (hχ0 a y)]
          exact mul_le_mul_of_nonneg_left (hgB _ _) (hχ0 a y)
      _ = B := by rw [← Finset.sum_mul, hχ1 y, one_mul]
  -- derivative bounds in the charts of `D`
  have hΓ : ∀ a, ∀ l ≤ 2, ∀ y, ‖iteratedFDeriv ℝ l (g (idx a)) y‖ ≤ (1 + ∑ i, κl i) * B := by
    intro a l hl y
    have h1 : B ≤ (1 + ∑ i, κl i) * B := by nlinarith
    have h2 : κl (idx a) * B ≤ (1 + ∑ i, κl i) * B :=
      mul_le_mul_of_nonneg_right (by linarith [hκl_le (idx a)]) hB
    interval_cases l
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact (hgB _ y).trans h1
    · rw [norm_iteratedFDeriv_one]; exact (hgD _ y).trans h2
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]; exact (hgD2 _ y).trans h2
  have hsum : ∀ j, ∀ z ∈ D.piece j, ∀ k ≤ 2, ‖iteratedFDerivWithin ℝ k
      (fun w => F ((D.chart j).val.symm w)) (D.chart j).val.target z‖ ≤ κ₂ * B := by
    intro j z hz k hk
    have hzt := D.piece_subset j hz
    have heq : iteratedFDerivWithin ℝ k (fun w => F ((D.chart j).val.symm w))
        (D.chart j).val.target z = ∑ a, iteratedFDerivWithin ℝ k
          (fun w => χ a ((D.chart j).val.symm w) *
            g (idx a) ((D.chart (idx a)).val ((D.chart j).val.symm w)))
          (D.chart j).val.target z :=
      iteratedFDerivWithin_fun_sum_apply (D.chart j).val.open_target.uniqueDiffOn hzt
        fun a _ => (hterm_smooth a (D.chart j) z hzt).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
    rw [heq]
    calc _ ≤ ∑ a, ‖iteratedFDerivWithin ℝ k
          (fun w => χ a ((D.chart j).val.symm w) *
            g (idx a) ((D.chart (idx a)).val ((D.chart j).val.symm w)))
          (D.chart j).val.target z‖ := norm_sum_le _ _
      _ ≤ ∑ a, 8 * P j a * ((1 + ∑ i, κl i) * B) * T j a ^ 2 :=
          Finset.sum_le_sum fun a _ => norm_iteratedFDerivWithin_chart_term_le (hχ a) (D.chart j)
            (D.chart (idx a)) (hχsrc a) (hg (idx a)) hzt (hT1 j a) (hP0 j a) (by positivity)
            (fun l hl => hP j a l hl z hz) (hT j a z hz) (hΓ a) hk
      _ = (∑ a, 8 * P j a * (1 + ∑ i, κl i) * T j a ^ 2) * B := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
      _ ≤ κ₂ * B := mul_le_mul_of_nonneg_right (hκ₂le j) hB
  have hκ₂κ : κ₂ * B ≤ (∑ i, κl i + κ₂ + κ₃) * B :=
    mul_le_mul_of_nonneg_right (by linarith) hB
  -- the bound for `ddᶜF` on the pieces
  have hddcD : ∀ j, ∀ z ∈ D.piece j, ∀ v : ComplexModel N,
      (ddcClosedForm F hF).val.coeff (D.chart j) z ![v, Complex.I • v] ≤
        (∑ i, κl i + κ₂ + κ₃) * B * A.form.val.coeff (D.chart j) z ![v, Complex.I • v] := by
    intro j z hz v
    have hzt := D.piece_subset j hz
    rw [ddc_line_eq hF (D.chart j) hzt v]
    have hH : ‖fderiv ℝ (fderiv ℝ (fun w => F ((D.chart j).val.symm w))) z‖ ≤ κ₂ * B := by
      rw [← norm_iteratedFDerivWithin_two_of_isOpen (D.chart j).val.open_target hzt]
      exact hsum j z hz 2 le_rfl
    have hquad : ∀ u : ComplexModel N,
        fderiv ℝ (fderiv ℝ (fun w => F ((D.chart j).val.symm w))) z u u ≤ κ₂ * B * ‖u‖ ^ 2 := by
      intro u
      have h := ContinuousLinearMap.le_opNorm₂
        (fderiv ℝ (fderiv ℝ (fun w => F ((D.chart j).val.symm w))) z) u u
      have h' := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ h)
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ (fun w => F ((D.chart j).val.symm w))) z‖ * ‖u‖ * ‖u‖ := h'
        _ ≤ κ₂ * B * ‖u‖ * ‖u‖ := by gcongr
        _ = κ₂ * B * ‖u‖ ^ 2 := by ring
    have hlevi : leviForm (fun w => F ((D.chart j).val.symm w)) z v ≤ κ₂ * B * ‖v‖ ^ 2 := by
      rw [leviForm, realHessian_eq_fderiv, realHessian_eq_fderiv]
      have h1 := hquad v
      have h2 := hquad (Complex.I • v)
      rw [norm_smul, Complex.norm_I, one_mul] at h2
      have h0 : 0 ≤ κ₂ * B * ‖v‖ ^ 2 := by positivity
      linarith
    have hA := hμ j z hz v
    have hAnn : 0 ≤ A.form.val.coeff (D.chart j) z ![v, Complex.I • v] :=
      (mul_nonneg (hμ0 j).le (by positivity) : (0 : ℝ) ≤ μ j * ‖v‖ ^ 2).trans hA
    have hv : ‖v‖ ^ 2 ≤ (∑ j, (μ j)⁻¹) * A.form.val.coeff (D.chart j) z ![v, Complex.I • v] := by
      have : ‖v‖ ^ 2 ≤ (μ j)⁻¹ * A.form.val.coeff (D.chart j) z ![v, Complex.I • v] := by
        rw [inv_mul_eq_div, le_div_iff₀ (hμ0 j)]; linarith
      exact this.trans (mul_le_mul_of_nonneg_right (hMle j) hAnn)
    have hpi : leviForm (fun w => F ((D.chart j).val.symm w)) z v / Real.pi ≤
        κ₂ * B * ‖v‖ ^ 2 := by
      have h0 : 0 ≤ κ₂ * B * ‖v‖ ^ 2 := by positivity
      rcases le_or_gt (leviForm (fun w => F ((D.chart j).val.symm w)) z v) 0 with hle | hgt
      · exact (div_nonpos_of_nonpos_of_nonneg hle Real.pi_pos.le).trans h0
      · rw [div_le_iff₀ Real.pi_pos]
        nlinarith [Real.two_le_pi]
    calc _ ≤ κ₂ * B * ‖v‖ ^ 2 := hpi
      _ ≤ κ₂ * B * ((∑ j, (μ j)⁻¹) * A.form.val.coeff (D.chart j) z ![v, Complex.I • v]) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = κ₃ * B * A.form.val.coeff (D.chart j) z ![v, Complex.I • v] := by rw [hκ₃]; ring
      _ ≤ (∑ i, κl i + κ₂ + κ₃) * B * A.form.val.coeff (D.chart j) z ![v, Complex.I • v] :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hB) hAnn
  refine ⟨F, hF, happrox, hbound, fun i z hz => ⟨?_, ?_⟩,
    fun e z hz v => coeff_line_le_of_pieces D _ _ hddcD e hz v⟩
  · rw [← norm_iteratedFDerivWithin_one_of_isOpen (D.chart i).val.open_target (D.piece_subset i hz)]
    exact (hsum i z hz 1 (by norm_num)).trans hκ₂κ
  · rw [← norm_iteratedFDerivWithin_two_of_isOpen (D.chart i).val.open_target (D.piece_subset i hz)]
    exact (hsum i z hz 2 le_rfl).trans hκ₂κ

end SGPT.Envelopes.TosC11c
