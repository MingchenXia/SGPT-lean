import SGPT.Envelopes.C11RealStatement

/-!
# Chart transfer of first- and second-order bounds

Lane TOS-C11c (`claude-tos-c11c`, node `tos-c11c:transfer`).  Source: Xia, *Foundations of
pluripotential theory*, `sec:real-hessian-envelopes` ("the Christoffel symbols of a metric and the
derivatives of coordinate changes are bounded on compact subsets of the charts, and they multiply
only first derivatives, so different smooth metrics give equivalent `C^{1,1}` norms"), for SGPT
`thm:Tos_C11` (Tosatti, Chu–Zhou).

The `C^{1,1}` norm of `C11RealStatement` is attached to chart data `D` (finitely many compact pieces
`K_i` of chart targets covering `X`).  We show that it controls the first and second derivatives in
*every* chart of the atlas on every compact subset of its target:

* `norm_sub_le_of_finset_cover`, `norm_sub_le_of_closed_cover` — a map which is `L`-Lipschitz on each
  of finitely many closed sets covering a segment satisfies the Lipschitz bound between the end points
  of the segment (chaining along the segment).
* `exists_c11_transfer` — for a chart `e` and a compact `K` in its target there is `C` (depending only
  on `D, e, K`) with `‖D(f ∘ e⁻¹)‖ ≤ C B` on `K` and `‖D(f ∘ e⁻¹)(z') - D(f ∘ e⁻¹)(z)‖ ≤ C B ‖z' - z‖`
  whenever the segment `[z, z']` lies in `K`, for every `C¹` function `f` with `‖f‖_{C^{1,1}, D} ≤ B`.
* `exists_hessian_transfer` — for `C²` functions, bounds `|u| ≤ M`, `‖D(u ∘ e_i⁻¹)‖ ≤ M` and
  `‖D²(u ∘ e_i⁻¹)‖ ≤ M` on the pieces give `‖D²(u ∘ e⁻¹)‖ ≤ C M` on `K` (second-order chain rule,
  Faà di Bruno's bound).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Envelopes.C11Real

section Segment

/-- **Chaining along an interval**: a map which is `L`-Lipschitz on each of finitely many closed
sets covering `[a, b]` satisfies `‖g b - g a‖ ≤ L (b - a)`. -/
theorem norm_sub_le_of_finset_cover {F : Type*} [SeminormedAddCommGroup F] {ι : Type*}
    (g : ℝ → F) (S : ι → Set ℝ) (hS : ∀ i, IsClosed (S i)) (L : ℝ)
    (hlip : ∀ i, ∀ s ∈ S i, ∀ t ∈ S i, ‖g t - g s‖ ≤ L * |t - s|) (T : Finset ι) :
    ∀ a b : ℝ, a ≤ b → Icc a b ⊆ ⋃ i ∈ T, S i → ‖g b - g a‖ ≤ L * (b - a) := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
  intro a b hab hcov
  obtain ⟨j, hjT, haj⟩ : ∃ j ∈ T, a ∈ S j := by
    have := hcov ⟨le_rfl, hab⟩
    simp only [mem_iUnion, exists_prop] at this
    exact this
  set P := S j ∩ Icc a b with hP
  have hPne : P.Nonempty := ⟨a, haj, le_rfl, hab⟩
  have hPbdd : BddAbove P := ⟨b, fun t ht => ht.2.2⟩
  have hcP : sSup P ∈ P := ((hS j).inter isClosed_Icc).csSup_mem hPne hPbdd
  set c := sSup P with hc
  have hac : a ≤ c := hcP.2.1
  have h1 : ‖g c - g a‖ ≤ L * (c - a) := by
    have := hlip j a haj c hcP.1
    rwa [abs_of_nonneg (by linarith)] at this
  rcases eq_or_lt_of_le hcP.2.2 with hcb | hcb
  · rw [← hcb]; exact h1
  have hopen : Ioc c b ⊆ ⋃ i ∈ T.erase j, S i := by
    intro t ht
    have := hcov ⟨by linarith [ht.1], ht.2⟩
    simp only [mem_iUnion, exists_prop] at this ⊢
    obtain ⟨i, hiT, hti⟩ := this
    refine ⟨i, Finset.mem_erase.mpr ⟨?_, hiT⟩, hti⟩
    rintro rfl
    have : t ≤ c := le_csSup hPbdd ⟨hti, by linarith [ht.1], ht.2⟩
    linarith [ht.1]
  have hclosed : IsClosed (⋃ i ∈ T.erase j, S i) := isClosed_biUnion_finset fun i _ => hS i
  have hcov' : Icc c b ⊆ ⋃ i ∈ T.erase j, S i := by
    rw [← closure_Ioc hcb.ne]
    exact hclosed.closure_subset_iff.mpr hopen
  have h2 := ih (T.erase j) (Finset.erase_ssubset hjT) c b hcb.le hcov'
  calc ‖g b - g a‖ ≤ ‖g b - g c‖ + ‖g c - g a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * (b - c) + L * (c - a) := add_le_add h2 h1
    _ = L * (b - a) := by ring

/-- **Chaining along a segment**: if `G` is `L`-Lipschitz on each of finitely many closed sets
covering the segment `[z, z']`, then `‖G z' - G z‖ ≤ L ‖z' - z‖`. -/
theorem norm_sub_le_of_closed_cover {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] {ι : Type*} [Fintype ι] (G : E → F) (C : ι → Set E)
    (hC : ∀ i, IsClosed (C i)) (L : ℝ)
    (hlip : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, ‖G x - G y‖ ≤ L * ‖x - y‖) {z z' : E}
    (hcov : segment ℝ z z' ⊆ ⋃ i, C i) : ‖G z' - G z‖ ≤ L * ‖z' - z‖ := by
  classical
  set p : ℝ → E := fun t => z + t • (z' - z) with hp
  have hpc : Continuous p := continuous_const.add (continuous_id.smul continuous_const)
  have h := norm_sub_le_of_finset_cover (fun t => G (p t)) (fun i => p ⁻¹' C i)
    (fun i => (hC i).preimage hpc) (L * ‖z' - z‖) ?_ Finset.univ 0 1 zero_le_one ?_
  · simpa [hp] using h
  · intro i s hs t ht
    have hdiff : p t - p s = (t - s) • (z' - z) := by
      simp only [hp, sub_smul]; abel
    calc ‖G (p t) - G (p s)‖ ≤ L * ‖p t - p s‖ := hlip i _ ht _ hs
      _ = L * ‖z' - z‖ * |t - s| := by
        rw [hdiff, norm_smul, Real.norm_eq_abs]; ring
  · intro t ht
    have hmem : p t ∈ segment ℝ z z' := by
      rw [segment_eq_image']
      exact ⟨t, ht, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hmem)
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and]
    exact ⟨i, hi⟩

end Segment

section Compact

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A `C¹` map on an open set is Lipschitz on every compact subset. -/
theorem exists_lipschitz_of_contDiffOn {f : E → F} {U s : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hs : IsCompact s) (hsU : s ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  have hloc : LocallyLipschitzOn s f := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := ((hf x (hsU hx)).contDiffAt (hU.mem_nhds (hsU hx))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hs
  refine ⟨K, K.2, fun x hx y hy => ?_⟩
  have := hK.dist_le_mul x hx y hy
  rwa [dist_eq_norm, dist_eq_norm] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A continuous map is bounded on a compact set, by a nonnegative constant. -/
theorem exists_norm_le_of_continuousOn {f : E → F} {s : Set E} (hf : ContinuousOn f s)
    (hs : IsCompact s) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-- `‖A ∘ B - A' ∘ B'‖ ≤ ‖A - A'‖ ‖B‖ + ‖A'‖ ‖B - B'‖`. -/
theorem norm_comp_sub_comp_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A' : F →L[ℝ] G) (B B' : E →L[ℝ] F) :
    ‖A.comp B - A'.comp B'‖ ≤ ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  have h : A.comp B - A'.comp B' = (A - A').comp B + A'.comp (B - B') := by
    ext v; simp
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

end Compact

section Chart

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- Chart transitions are smooth on their sources. -/
theorem contDiffOn_chartTransition (e e' : ComplexChart N Y) :
    ContDiffOn ℝ ∞ (chartTransition e e') (chartTransition e e').source :=
  fun _ hz => (chartTransition_contDiffAt_real e e' hz).contDiffWithinAt

omit [IsComplexManifold N Y] in
/-- Chart transitions map their sources into the target of the second chart. -/
theorem chartTransition_mem_target (e e' : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ (chartTransition e e').source) : chartTransition e e' z ∈ e'.val.target :=
  e'.val.map_source hz.2

omit [IsComplexManifold N Y] in
/-- **Reading a function in two charts**: near a point of the overlap, `g ∘ e⁻¹ = (g ∘ e'⁻¹) ∘ τ`
for the transition `τ = e' ∘ e⁻¹`. -/
theorem chart_eventuallyEq (g : Y → ℝ) (e e' : ComplexChart N Y) {z : ComplexModel N}
    (hz : z ∈ (chartTransition e e').source) :
    (fun w => g (e.val.symm w)) =ᶠ[𝓝 z]
      (fun w => g (e'.val.symm w)) ∘ chartTransition e e' := by
  filter_upwards [(chartTransition e e').open_source.mem_nhds hz] with w hw
  have hw2 : e.val.symm w ∈ e'.val.source := hw.2
  show g (e.val.symm w) = g (e'.val.symm (e'.val (e.val.symm w)))
  rw [e'.val.left_inv hw2]

/-- The points of `K` lying over the `i`-th piece of the chart data. -/
def pieceSet (D : C11ChartData N Y) (e : ComplexChart N Y) (K : Set (ComplexModel N))
    (i : Fin D.card) : Set (ComplexModel N) :=
  K ∩ e.val.symm ⁻¹' ((D.chart i).val.symm '' D.piece i)

variable (D : C11ChartData N Y) (e : ComplexChart N Y) {K : Set (ComplexModel N)}

theorem isClosed_pieceSet (hK : IsClosed K) (hKt : K ⊆ e.val.target) (i : Fin D.card) :
    IsClosed (pieceSet D e K i) := by
  have hP : IsCompact ((D.chart i).val.symm '' D.piece i) :=
    (D.isCompact_piece i).image_of_continuousOn
      ((D.chart i).val.continuousOn_symm.mono (D.piece_subset i))
  exact (e.val.continuousOn_symm.mono hKt).preimage_isClosed_of_isClosed hK hP.isClosed

theorem isCompact_pieceSet (hK : IsCompact K) (hKt : K ⊆ e.val.target) (i : Fin D.card) :
    IsCompact (pieceSet D e K i) :=
  hK.of_isClosed_subset (isClosed_pieceSet D e hK.isClosed hKt i) inter_subset_left

omit [IsComplexManifold N Y] in
theorem pieceSet_subset_source (hKt : K ⊆ e.val.target) (i : Fin D.card) :
    pieceSet D e K i ⊆ (chartTransition e (D.chart i)).source := by
  rintro w ⟨hwK, p, hp, hpw⟩
  refine ⟨hKt hwK, ?_⟩
  show e.val.symm w ∈ (D.chart i).val.source
  rw [← hpw]
  exact (D.chart i).val.map_target (D.piece_subset i hp)

omit [IsComplexManifold N Y] in
theorem chartTransition_mem_piece {i : Fin D.card} {w : ComplexModel N}
    (hw : w ∈ pieceSet D e K i) : chartTransition e (D.chart i) w ∈ D.piece i := by
  obtain ⟨-, p, hp, hpw⟩ := hw
  show (D.chart i).val (e.val.symm w) ∈ D.piece i
  rw [← hpw, (D.chart i).val.right_inv (D.piece_subset i hp)]
  exact hp

omit [IsComplexManifold N Y] in
theorem subset_iUnion_pieceSet : K ⊆ ⋃ i, pieceSet D e K i := by
  intro w hw
  obtain ⟨i, hi⟩ := D.cover (e.val.symm w)
  exact mem_iUnion.mpr ⟨i, hw, hi⟩

/-- Uniform bounds for the chart transitions `τ_i = e_i ∘ e⁻¹` over the compact sets `pieceSet`:
`‖Dτ_i‖ ≤ C`, `‖D²τ_i‖ ≤ C`, and `τ_i`, `Dτ_i` are `C`-Lipschitz there. -/
theorem exists_transition_bounds (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ w ∈ pieceSet D e K i, ∀ w' ∈ pieceSet D e K i,
      ‖fderiv ℝ (chartTransition e (D.chart i)) w‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (chartTransition e (D.chart i))) w‖ ≤ C ∧
      ‖chartTransition e (D.chart i) w - chartTransition e (D.chart i) w'‖ ≤ C * ‖w - w'‖ ∧
      ‖fderiv ℝ (chartTransition e (D.chart i)) w -
        fderiv ℝ (chartTransition e (D.chart i)) w'‖ ≤ C * ‖w - w'‖ := by
  have hloc : ∀ i : Fin D.card, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ pieceSet D e K i,
      ∀ w' ∈ pieceSet D e K i,
      ‖fderiv ℝ (chartTransition e (D.chart i)) w‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (chartTransition e (D.chart i))) w‖ ≤ C ∧
      ‖chartTransition e (D.chart i) w - chartTransition e (D.chart i) w'‖ ≤ C * ‖w - w'‖ ∧
      ‖fderiv ℝ (chartTransition e (D.chart i)) w -
        fderiv ℝ (chartTransition e (D.chart i)) w'‖ ≤ C * ‖w - w'‖ := by
    intro i
    set τ := chartTransition e (D.chart i)
    have hU : IsOpen τ.source := τ.open_source
    have hS := isCompact_pieceSet D e hK hKt i
    have hSU := pieceSet_subset_source D e hKt i
    have hτ : ContDiffOn ℝ ∞ τ τ.source := contDiffOn_chartTransition e (D.chart i)
    have hDτ : ContDiffOn ℝ ∞ (fderiv ℝ τ) τ.source := hτ.fderiv_of_isOpen hU (by simp)
    have hD2τ : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ τ)) τ.source :=
      hDτ.fderiv_of_isOpen hU (by simp)
    obtain ⟨C1, hC10, hC1⟩ := exists_norm_le_of_continuousOn (hDτ.continuousOn.mono hSU) hS
    obtain ⟨C2, hC20, hC2⟩ := exists_norm_le_of_continuousOn (hD2τ.continuousOn.mono hSU) hS
    obtain ⟨L1, hL10, hL1⟩ := exists_lipschitz_of_contDiffOn hU (hτ.of_le (by simp)) hS hSU
    obtain ⟨L2, hL20, hL2⟩ := exists_lipschitz_of_contDiffOn hU (hDτ.of_le (by simp)) hS hSU
    refine ⟨C1 + C2 + L1 + L2, by positivity, fun w hw w' hw' => ⟨?_, ?_, ?_, ?_⟩⟩
    · linarith [hC1 w hw]
    · linarith [hC2 w hw]
    · have := hL1 w hw w' hw'
      have h : L1 * ‖w - w'‖ ≤ (C1 + C2 + L1 + L2) * ‖w - w'‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith
    · have := hL2 w hw w' hw'
      have h : L2 * ‖w - w'‖ ≤ (C1 + C2 + L1 + L2) * ‖w - w'‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith
  choose C hC0 hC using hloc
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i w hw w' hw' => ?_⟩
  have hle : C i ≤ ∑ i, C i :=
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  obtain ⟨h1, h2, h3, h4⟩ := hC i w hw w' hw'
  exact ⟨h1.trans hle, h2.trans hle,
    h3.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _)),
    h4.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))⟩

/-- The derivative of `g ∘ e⁻¹` at a point of the overlap, by the chain rule through `τ`. -/
theorem fderiv_chart_eq {g : Y → ℝ} (e' : ComplexChart N Y) {w : ComplexModel N}
    (hw : w ∈ (chartTransition e e').source)
    (hg : DifferentiableAt ℝ (fun z => g (e'.val.symm z)) (chartTransition e e' w)) :
    fderiv ℝ (fun z => g (e.val.symm z)) w =
      (fderiv ℝ (fun z => g (e'.val.symm z)) (chartTransition e e' w)).comp
        (fderiv ℝ (chartTransition e e') w) := by
  rw [(chart_eventuallyEq g e e' hw).fderiv_eq]
  exact fderiv_comp w hg
    ((chartTransition_contDiffAt_real e e' hw).differentiableAt (by simp))

/-- **Transfer of `C^{1,1}` bounds to an arbitrary chart.**  For chart data `D`, a chart `e` and a
compact `K` in its target, there is `C` such that every function `f`, `C¹` in every chart with
`‖f‖_{C^{1,1}, D} ≤ B`, satisfies `‖D(f ∘ e⁻¹)‖ ≤ C B` on `K` and
`‖D(f ∘ e⁻¹)(z') - D(f ∘ e⁻¹)(z)‖ ≤ C B ‖z' - z‖` whenever the segment `[z, z']` lies in `K`. -/
theorem exists_c11_transfer (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Y → ℝ) (B : ℝ), 0 ≤ B →
      (∀ e' : ComplexChart N Y, ContDiffOn ℝ 1 (fun z => f (e'.val.symm z)) e'.val.target) →
      C11Bound D f B →
      (∀ z ∈ K, ‖fderiv ℝ (fun z => f (e.val.symm z)) z‖ ≤ C * B) ∧
      ∀ z ∈ K, ∀ z' ∈ K, segment ℝ z z' ⊆ K →
        ‖fderiv ℝ (fun z => f (e.val.symm z)) z' - fderiv ℝ (fun z => f (e.val.symm z)) z‖ ≤
          C * B * ‖z' - z‖ := by
  obtain ⟨Cτ, hCτ0, hCτ⟩ := exists_transition_bounds D e hK hKt
  refine ⟨Cτ + Cτ * Cτ, by positivity, fun f B hB hf hfB => ?_⟩
  set g : ComplexModel N → ℝ := fun z => f (e.val.symm z) with hgdef
  -- the derivative on `pieceSet i`
  have hform : ∀ i, ∀ w ∈ pieceSet D e K i, fderiv ℝ g w =
      (fderiv ℝ (fun z => f ((D.chart i).val.symm z)) (chartTransition e (D.chart i) w)).comp
        (fderiv ℝ (chartTransition e (D.chart i)) w) := by
    intro i w hw
    have hws := pieceSet_subset_source D e hKt i hw
    have ht := chartTransition_mem_target e (D.chart i) hws
    refine fderiv_chart_eq e (D.chart i) hws ?_
    exact ((hf (D.chart i)) _ ht).differentiableWithinAt (by simp)
      |>.differentiableAt ((D.chart i).val.open_target.mem_nhds ht)
  refine ⟨fun z hz => ?_, fun z hz z' hz' hseg => ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (subset_iUnion_pieceSet D e hz)
    rw [hform i z hi]
    have h1 := (hfB.2 i).1 _ (chartTransition_mem_piece D e hi)
    have h2 := (hCτ i z hi z hi).1
    calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * Cτ := mul_le_mul h1 h2 (norm_nonneg _) hB
      _ ≤ (Cτ + Cτ * Cτ) * B := by nlinarith
  · refine norm_sub_le_of_closed_cover (fderiv ℝ g) (pieceSet D e K)
      (isClosed_pieceSet D e hK.isClosed hKt) ((Cτ + Cτ * Cτ) * B) ?_
      ((hseg.trans (subset_iUnion_pieceSet D e)))
    intro i w hw w' hw'
    rw [hform i w hw, hform i w' hw']
    have hp := chartTransition_mem_piece D e hw
    have hp' := chartTransition_mem_piece D e hw'
    obtain ⟨hD1, -, hτL, hDτL⟩ := hCτ i w hw w' hw'
    have hLip := (hfB.2 i).2 _ hp _ hp'
    have hbd' := (hfB.2 i).1 _ hp'
    refine (norm_comp_sub_comp_le _ _ _ _).trans ?_
    have hn : 0 ≤ ‖w - w'‖ := norm_nonneg _
    calc _ ≤ B * (Cτ * ‖w - w'‖) * Cτ + B * (Cτ * ‖w - w'‖) :=
          add_le_add (mul_le_mul (hLip.trans (mul_le_mul_of_nonneg_left hτL hB)) hD1
            (norm_nonneg _) (by positivity))
            (mul_le_mul hbd' hDτL (norm_nonneg _) hB)
      _ = (Cτ + Cτ * Cτ) * B * ‖w - w'‖ := by ring

/-- **Transfer of Hessian bounds to an arbitrary chart.**  For chart data `D`, a chart `e` and a
compact `K` in its target, there is `C` such that every function `u`, `C²` in every chart, with
`|u| ≤ M` and `‖D(u ∘ e_i⁻¹)‖, ‖D²(u ∘ e_i⁻¹)‖ ≤ M` on the pieces `K_i`, satisfies
`‖D²(u ∘ e⁻¹)‖ ≤ C M` on `K`. -/
theorem exists_hessian_transfer (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Y → ℝ) (M : ℝ),
      (∀ e' : ComplexChart N Y, ContDiffOn ℝ 2 (fun z => u (e'.val.symm z)) e'.val.target) →
      (∀ y, |u y| ≤ M) →
      (∀ i, ∀ z ∈ D.piece i, ‖fderiv ℝ (fun z => u ((D.chart i).val.symm z)) z‖ ≤ M ∧
        ‖fderiv ℝ (fderiv ℝ (fun z => u ((D.chart i).val.symm z))) z‖ ≤ M) →
      ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ (fun z => u (e.val.symm z))) z‖ ≤ C * M := by
  obtain ⟨Cτ, hCτ0, hCτ⟩ := exists_transition_bounds D e hK hKt
  refine ⟨2 * (1 + Cτ) ^ 2, by positivity, fun u M hu huM hpiece z hz => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (subset_iUnion_pieceSet D e hz)
  set τ := chartTransition e (D.chart i) with hτdef
  set gi : ComplexModel N → ℝ := fun z => u ((D.chart i).val.symm z) with hgi
  have hzs := pieceSet_subset_source D e hKt i hi
  have hU : IsOpen τ.source := τ.open_source
  have hT : IsOpen (D.chart i).val.target := (D.chart i).val.open_target
  have hτz := chartTransition_mem_piece D e hi
  -- the second derivative of `u ∘ e⁻¹` is that of `gi ∘ τ`
  have heq : iteratedFDeriv ℝ 2 (fun z => u (e.val.symm z)) z =
      iteratedFDerivWithin ℝ 2 (gi ∘ τ) τ.source z := by
    rw [iteratedFDerivWithin_of_isOpen 2 hU hzs]
    exact ((chart_eventuallyEq u e (D.chart i) hzs).iteratedFDeriv ℝ 2).eq_of_nhds
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (huM (e.val.symm z))
  have hbound := norm_iteratedFDerivWithin_comp_le (n := 2) (N := 2) (hu (D.chart i))
    ((contDiffOn_chartTransition e (D.chart i)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    le_rfl hT.uniqueDiffOn
    hU.uniqueDiffOn (fun w hw => chartTransition_mem_target e (D.chart i) hw) hzs
    (C := M) (D := 1 + Cτ) ?_ ?_
  · -- `‖D²(u ∘ e⁻¹)‖ = ‖iteratedFDeriv 2 …‖`
    have h2 : ‖fderiv ℝ (fderiv ℝ (fun z => u (e.val.symm z))) z‖ =
        ‖iteratedFDeriv ℝ 2 (fun z => u (e.val.symm z)) z‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    rw [h2, heq]
    calc _ ≤ (Nat.factorial 2 : ℝ) * M * (1 + Cτ) ^ 2 := hbound
      _ = 2 * (1 + Cτ) ^ 2 * M := by norm_num; ring
  · intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hT (chartTransition_mem_target e (D.chart i) hzs)]
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact huM _
    · rw [norm_iteratedFDeriv_one]; exact (hpiece i _ hτz).1
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]; exact (hpiece i _ hτz).2
  · intro j hj1 hj2
    rw [iteratedFDerivWithin_of_isOpen j hU hzs]
    obtain ⟨h1, h2, -, -⟩ := hCτ i z hi z hi
    interval_cases j
    · rw [norm_iteratedFDeriv_one]; linarith
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]; nlinarith

end Chart

end SGPT.Envelopes.TosC11c
