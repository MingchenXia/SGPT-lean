import SGPT.Foundations.Analysis.Pending.DivisorSingularProjection

set_option autoImplicit false

/-!
# The coarea formula for the transverse part of a divisor

Let `g : ℂⁿ → ℂ`, `Ω ⊆ ℂⁿ` open, `u` a unit vector and `ℂⁿ = ℂ u ⊕ ι(ℂᵐ)` an orthogonal
splitting.  On the transverse locus `Z_tr` of the divisor of `g` (regular points where the divisor
is transverse to `u`), the `2m`-dimensional Euclidean Hausdorff measure weighted by the transverse
density `τ(u, i u)` disintegrates along the lines parallel to `u`:

  `∫_{Z_tr ∩ Ω} τ(u, iu) m F dμHE = ∫_w ∑_{s : su + ιw ∈ Z_tr ∩ Ω} m F (su + ιw) dw`

(`lintegral_transverse_eq`), for every nonnegative Borel `F`, with `m` the multiplicity.

## Proof

Every transverse point has a *graph piece* (`GraphPiece`, `exists_graphPiece`): a neighbourhood in
which the zero set is a holomorphic graph `G(w) = k(w) u + ι w` over an open `W ⊆ ℂᵐ`, with
constant multiplicity, and with area factor times `τ(u, i u)` equal to `1`
(`DivisorRegularLocus`).  Cover
`Z_tr ∩ Ω` by countably many pieces, make them disjoint, and apply the area formula
(`HausdorffAreaFormula`) on each: the piece over `P ⊆ W` contributes `∫_P m F (G w) dw`.  On the
right, a line meets a piece at most once, over `P`, at `s = k(w)`.
-/

open Set Filter Function MeasureTheory Metric Module
open scoped Topology InnerProductSpace ContDiff ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.DivisorCoarea

open DivisorRegularLocus HausdorffAreaFormula

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Restrict a regular presentation to an open set containing the point. -/
def _root_.SGPT.Foundations.Analysis.Pending.DivisorRegularLocus.RegularPresentation.restrictOpen
    {g : V → ℂ} {x : V} (P : RegularPresentation g x) {O : Set V} (hO : IsOpen O)
    (hx : x ∈ O) : RegularPresentation g x where
  U := P.U ∩ O
  isOpen := P.isOpen.inter hO
  mem := ⟨P.mem, hx⟩
  m := P.m
  m_pos := P.m_pos
  h := P.h
  v := P.v
  h_diff := P.h_diff.mono inter_subset_left
  v_diff := P.v_diff.mono inter_subset_left
  h_zero := P.h_zero
  dh_ne := fun y hy => P.dh_ne y hy.1
  v_ne := fun y hy => P.v_ne y hy.1
  eq := fun y hy => P.eq y hy.1

end General

section Pieces

variable {n m : ℕ}


/-- A graph piece of the transverse locus: a neighbourhood in which the zero set of `g` is a
holomorphic graph over the complement of `u`, with constant multiplicity and unit area density. -/
structure GraphPiece (g : EuclideanSpace ℂ (Fin n) → ℂ) (Ω : Set (EuclideanSpace ℂ (Fin n)))
    {u : EuclideanSpace ℂ (Fin n)} (S : Splitting u (EuclideanSpace ℂ (Fin m))) where
  /-- the neighbourhood -/
  N : Set (EuclideanSpace ℂ (Fin n))
  /-- the parameter domain -/
  W : Set (EuclideanSpace ℂ (Fin m))
  /-- the graph function -/
  k : EuclideanSpace ℂ (Fin m) → ℂ
  /-- the local defining function -/
  h : EuclideanSpace ℂ (Fin n) → ℂ
  /-- the multiplicity -/
  mult : ℕ
  isOpen_N : IsOpen N
  isOpen_W : IsOpen W
  N_sub : N ⊆ Ω
  k_diff : DifferentiableOn ℂ k W
  mem_graph : ∀ w ∈ W, k w • u + S.ι w ∈ N ∧ g (k w • u + S.ι w) = 0
  slice : ∀ (w : (EuclideanSpace ℂ (Fin m))) (s : ℂ), s • u + S.ι w ∈ N →
    (g (s • u + S.ι w) = 0 ↔ w ∈ W ∧ s = k w)
  divisorMult_eq : ∀ y ∈ N, g y = 0 → divisorMult g y = mult
  transverseForm_eq : ∀ y ∈ N, g y = 0 → transverseForm g y = lineForm (fderiv ℂ h y)
  transverse : ∀ y ∈ N, g y = 0 → y ∈ transverseLocus g u
  jacobian : ∀ w ∈ W, ((fderiv ℝ (fun w => k w • u + S.ι w) w :
      EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)).normDet *
    transverseForm g (k w • u + S.ι w) u (Complex.I • u) = 1
  g_cont : ContinuousOn g N

namespace GraphPiece

variable {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
  {u : EuclideanSpace ℂ (Fin n)} {S : Splitting u (EuclideanSpace ℂ (Fin m))}

theorem graph_contDiffOn (P : GraphPiece g Ω S) :
    ContDiffOn ℝ 1 (fun w => P.k w • u + S.ι w) P.W := by
  have hk : ContDiffOn ℝ 1 P.k P.W :=
    ((FirstPass.contDiffOn_of_differentiableOn_complex P.k_diff P.isOpen_W).restrict_scalars
      ℝ).of_le (by simp)
  exact (hk.smul contDiffOn_const).add
    ((S.ι.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffOn)

theorem graph_injOn (P : GraphPiece g Ω S) (s : Set (EuclideanSpace ℂ (Fin m))) :
    InjOn (fun w => P.k w • u + S.ι w) s := by
  intro w hw w' hw' h
  have := congrArg S.π h
  simpa [S.π_smul_add] using this

theorem graph_fderiv_injective (P : GraphPiece g Ω S) {w : EuclideanSpace ℂ (Fin m)}
    (hw : w ∈ P.W) :
    Injective (fderiv ℝ (fun w => P.k w • u + S.ι w) w) := by
  have hkd : HasFDerivAt P.k (fderiv ℂ P.k w) w :=
    (P.k_diff.differentiableAt (P.isOpen_W.mem_nhds hw)).hasFDerivAt
  have hGd : HasFDerivAt (fun w => P.k w • u + S.ι w)
      ((fderiv ℂ P.k w).smulRight u + S.ι.toContinuousLinearMap) w :=
    (hkd.smul_const u).add S.ι.toContinuousLinearMap.hasFDerivAt
  rw [(hGd.restrictScalars ℝ).fderiv]
  intro e e' h
  have := congrArg S.π h
  simpa [S.π_smul_add] using this

end GraphPiece

theorem exists_graphPiece {g : EuclideanSpace ℂ (Fin n) → ℂ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    (hΩ : IsOpen Ω) {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1)
    (S : Splitting u (EuclideanSpace ℂ (Fin m))) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ transverseLocus g u) (hxΩ : x ∈ Ω) :
    ∃ P : GraphPiece g Ω S, x ∈ P.N := by
  have hreg := hx.1
  let P₀ : RegularPresentation g x := (Classical.choice hreg).restrictOpen hΩ hxΩ
  have hgx : g x = 0 := P₀.g_x
  have hxu : fderiv ℂ P₀.h x u ≠ 0 := (P₀.mem_transverseLocus_iff P₀.mem hgx u).mp hx
  obtain ⟨N, W, k, hNo, hxN, hNU, hNtr, hWo, hxW, hk, hgraph, hslice, -⟩ :=
    P₀.exists_graph_slices hu S hxu
  refine ⟨{
    N := N
    W := W
    k := k
    h := P₀.h
    mult := P₀.m
    isOpen_N := hNo
    isOpen_W := hWo
    N_sub := fun y hy => (hNU hy).2
    k_diff := hk
    mem_graph := ?_
    slice := hslice
    divisorMult_eq := fun y hy hgy => P₀.divisorMult_of_mem (hNU hy) hgy
    transverseForm_eq := fun y hy hgy => funext₂ fun v w =>
      P₀.transverseForm_of_mem (hNU hy) hgy v w
    transverse := fun y hy hgy => (P₀.mem_transverseLocus_iff (hNU hy) hgy u).mpr (hNtr y hy)
    jacobian := ?_
    g_cont := ?_ }, hxN⟩
  · intro w hw
    obtain ⟨h1, h2⟩ := hgraph w hw
    exact ⟨h1, (P₀.g_eq_zero_iff (hNU h1)).mpr h2⟩
  · intro w hw
    exact P₀.normDet_mul_transverseForm hu S hWo hk
      (fun w hw => ⟨hNU (hgraph w hw).1, (hgraph w hw).2⟩)
      (fun w hw => hNtr _ (hgraph w hw).1) hw
  · intro y hy
    have hU := hNU hy
    have hcont : ContinuousAt g y := by
      have hev : g =ᶠ[𝓝 y] fun z => P₀.h z ^ P₀.m * P₀.v z := by
        filter_upwards [P₀.isOpen.mem_nhds hU] with z hz
        exact P₀.eq z hz
      refine ContinuousAt.congr ?_ hev.symm
      exact (((P₀.h_diff y hU).differentiableAt (P₀.isOpen.mem_nhds hU)).continuousAt.pow
        _).mul ((P₀.v_diff y hU).differentiableAt (P₀.isOpen.mem_nhds hU)).continuousAt
    exact hcont.continuousWithinAt

end Pieces

section Coarea

variable {n m : ℕ}

/-- The indicator of a disjoint union is the sum of the indicators. -/
theorem indicator_iUnion_eq_tsum {α : Type*} {Q : ℕ → Set α} (hQ : Pairwise (Disjoint on Q))
    (H : α → ℝ≥0∞) (y : α) : (⋃ i, Q i).indicator H y = ∑' i, (Q i).indicator H y := by
  classical
  by_cases hy : y ∈ ⋃ i, Q i
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    rw [indicator_of_mem hy, tsum_eq_single j, indicator_of_mem hj]
    intro i hij
    exact indicator_of_notMem (fun hi => (hQ hij).le_bot ⟨hi, hj⟩) H
  · rw [indicator_of_notMem hy]
    symm
    refine ENNReal.tsum_eq_zero.mpr fun i => indicator_of_notMem ?_ H
    exact fun hi => hy (mem_iUnion.mpr ⟨i, hi⟩)

theorem measurable_lineForm_apply_I {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    Measurable fun ℓ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ => lineForm ℓ u (Complex.I • u) := by
  have : (fun ℓ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ => lineForm ℓ u (Complex.I • u)) =
      fun ℓ => ‖ℓ u‖ ^ 2 / ‖ℓ‖ ^ 2 := funext fun ℓ => lineForm_apply_I ℓ u
  rw [this]
  exact (((continuous_norm.comp (continuous_id.clm_apply continuous_const)).pow 2).measurable).div
    ((continuous_norm.pow 2).measurable)

/-- **Coarea formula for the transverse locus.**  For `g` continuous on the open set `Ω` and a
nonnegative Borel `F`, the `2m`-dimensional Hausdorff integral over the transverse locus of
`τ(u, iu) · m · F` equals the integral over `w ∈ ℂᵐ` of the sum of `m F` over the transverse zeros
on the line `{s u + ι w}`. -/
theorem lintegral_transverse_eq {g : EuclideanSpace ℂ (Fin n) → ℂ}
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω) (hgc : ContinuousOn g Ω)
    {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (S : Splitting u (EuclideanSpace ℂ (Fin m)))
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in transverseLocus g u ∩ Ω, ENNReal.ofReal (transverseForm g x u (Complex.I • u)) *
        (divisorMult g x * F x) ∂(μHE[finrank ℝ (EuclideanSpace ℂ (Fin m))] :
          Measure (EuclideanSpace ℂ (Fin n))) =
      ∫⁻ w, ∑' s : ℂ, (transverseLocus g u ∩ Ω).indicator
        (fun y => (divisorMult g y : ℝ≥0∞) * F y) (s • u + S.ι w) := by
  classical
  set Zt := transverseLocus g u ∩ Ω with hZt
  set H : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ := fun y => (divisorMult g y : ℝ≥0∞) * F y with hH
  -- measurability of `Zt`
  have hZtm : MeasurableSet Zt := by
    obtain ⟨O, hOo, hO⟩ := exists_isOpen_transverseLocus g u
    have h0 : MeasurableSet (g ⁻¹' {0} ∩ Ω) :=
      measurableSet_inter_preimage_of_continuousOn hΩ.measurableSet hgc
        (measurableSet_singleton 0)
    have : Zt = (g ⁻¹' {0} ∩ Ω) ∩ O := by
      rw [hZt, hO]
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      tauto
    rw [this]
    exact h0.inter hOo.measurableSet
  rcases Zt.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]
    simp
  -- graph pieces
  choose P hP using fun x (hx : x ∈ Zt) => exists_graphPiece hΩ hu S hx.1 hx.2
  set f : EuclideanSpace ℂ (Fin n) → Set (EuclideanSpace ℂ (Fin n)) :=
    fun x => if hx : x ∈ Zt then (P x hx).N else univ with hfdef
  have hf : ∀ x (hx : x ∈ Zt), f x = (P x hx).N := fun x hx => by simp [hfdef, hx]
  obtain ⟨t, htZ, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (f := f) (s := Zt)
    fun x hx => by
      rw [hf x hx]
      exact mem_nhdsWithin_of_mem_nhds ((P x hx).isOpen_N.mem_nhds (hP x hx))
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp (hcov hx)
    exact ⟨y, hy⟩
  obtain ⟨c, rfl⟩ := htc.exists_eq_range htne
  have hc : ∀ i, c i ∈ Zt := fun i => htZ (mem_range_self i)
  set Pc : ℕ → GraphPiece g Ω S := fun i => P (c i) (hc i) with hPc
  set Q : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => Zt ∩ disjointed (fun j => (Pc j).N) i
    with hQ
  have hQN : ∀ i, Q i ⊆ (Pc i).N := fun i => inter_subset_right.trans (disjointed_subset _ i)
  have hQZ : ∀ i, Q i ⊆ Zt := fun i => inter_subset_left
  have hQm : ∀ i, MeasurableSet (Q i) := fun i =>
    hZtm.inter (MeasurableSet.disjointed (fun j => (Pc j).isOpen_N.measurableSet) i)
  have hQd : Pairwise (Disjoint on Q) := fun i j hij =>
    (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right
  have hZQ : Zt = ⋃ i, Q i := by
    apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ ⋃ i, (Pc i).N := by
        obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.mp (hcov hx)
        rw [hf _ (hc i)] at hxy
        exact mem_iUnion.mpr ⟨i, hxy⟩
      rw [← iUnion_disjointed] at hx'
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
      exact mem_iUnion.mpr ⟨i, hx, hi⟩
    · exact iUnion_subset hQZ
  -- the graph maps and their domains
  set G : ℕ → EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin n) :=
    fun i w => (Pc i).k w • u + S.ι w with hGdef
  set Pw : ℕ → Set (EuclideanSpace ℂ (Fin m)) := fun i => G i ⁻¹' Q i ∩ (Pc i).W with hPwdef
  have hGc : ∀ i, ContinuousOn (G i) (Pc i).W := fun i => (Pc i).graph_contDiffOn.continuousOn
  have hPwm : ∀ i, MeasurableSet (Pw i) := fun i =>
    measurableSet_inter_preimage_of_continuousOn (Pc i).isOpen_W.measurableSet (hGc i) (hQm i)
  have hzero : ∀ i, ∀ y ∈ Q i, g y = 0 := fun i y hy =>
    eq_zero_of_mem_regularLocus (hQZ i hy).1.1
  have himage : ∀ i, G i '' Pw i = Q i := by
    intro i
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.1
    · intro y hy
      have hdec := S.decomp y
      have h := ((Pc i).slice (S.π y) (⟪u, y⟫_ℂ) (by rw [← hdec]; exact hQN i hy)).mp
        (by rw [← hdec]; exact hzero i y hy)
      refine ⟨S.π y, ⟨?_, h.1⟩, ?_⟩
      · show G i (S.π y) ∈ Q i
        simp only [hGdef]
        rw [← h.2, ← hdec]
        exact hy
      · simp only [hGdef]
        rw [← h.2, ← hdec]
  -- the piecewise computation
  have hpiece : ∀ i, ∫⁻ x in Q i, ENNReal.ofReal (transverseForm g x u (Complex.I • u)) *
      (divisorMult g x * F x) ∂(μHE[finrank ℝ (EuclideanSpace ℂ (Fin m))] :
        Measure (EuclideanSpace ℂ (Fin n))) =
      ∫⁻ w in Pw i, ((Pc i).mult : ℝ≥0∞) * F (G i w) := by
    intro i
    set φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ := fun x =>
      ENNReal.ofReal (lineForm (fderiv ℂ (Pc i).h x) u (Complex.I • u)) *
        (((Pc i).mult : ℝ≥0∞) * F x) with hφ
    have hφm : Measurable φ :=
      (ENNReal.measurable_ofReal.comp ((measurable_lineForm_apply_I u).comp
        (measurable_fderiv ℂ (Pc i).h))).mul (measurable_const.mul hF)
    rw [setLIntegral_congr_fun (hQm i) (g := φ) fun x hx => by
        rw [(Pc i).transverseForm_eq x (hQN i hx) (hzero i x hx),
          (Pc i).divisorMult_eq x (hQN i hx) (hzero i x hx)],
      ← himage i, lintegral_image_eq_lintegral (Pc i).isOpen_W (Pc i).graph_contDiffOn (hPwm i)
        inter_subset_right ((Pc i).graph_injOn _)
        (fun w hw => (Pc i).graph_fderiv_injective hw.2) hφm]
    refine setLIntegral_congr_fun (hPwm i) fun w hw => ?_
    have hGw : G i w ∈ (Pc i).N := ((Pc i).mem_graph w hw.2).1
    have hgw : g (G i w) = 0 := ((Pc i).mem_graph w hw.2).2
    have hjac := (Pc i).jacobian w hw.2
    rw [(Pc i).transverseForm_eq _ hGw hgw] at hjac
    simp only [hφ, detFactor, ← mul_assoc]
    rw [← ENNReal.ofReal_mul (LinearMap.normDet_nonneg _)]
    have : ((fderiv ℝ (G i) w : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)).normDet *
        lineForm (fderiv ℂ (Pc i).h (G i w)) u (Complex.I • u) = 1 := hjac
    rw [this, ENNReal.ofReal_one, one_mul]
  -- the left side as a sum over pieces
  have hLHS : ∫⁻ x in Zt, ENNReal.ofReal (transverseForm g x u (Complex.I • u)) *
      (divisorMult g x * F x) ∂(μHE[finrank ℝ (EuclideanSpace ℂ (Fin m))] :
        Measure (EuclideanSpace ℂ (Fin n))) =
      ∑' i, ∫⁻ w in Pw i, ((Pc i).mult : ℝ≥0∞) * F (G i w) := by
    conv_lhs => rw [hZQ]
    rw [lintegral_iUnion hQm hQd]
    exact tsum_congr hpiece
  -- the right side, pointwise
  have hpt : ∀ w, ∑' s : ℂ, Zt.indicator H (s • u + S.ι w) =
      ∑' i, (Pw i).indicator (fun w => ((Pc i).mult : ℝ≥0∞) * F (G i w)) w := by
    intro w
    simp_rw [hZQ, indicator_iUnion_eq_tsum hQd]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun i => ?_
    by_cases hw : w ∈ Pw i
    · rw [indicator_of_mem hw, tsum_eq_single ((Pc i).k w)]
      · have hGw : G i w ∈ Q i := hw.1
        rw [show (Pc i).k w • u + S.ι w = G i w from rfl, indicator_of_mem hGw]
        simp only [hH]
        rw [(Pc i).divisorMult_eq _ (hQN i hGw) (hzero i _ hGw)]
      · intro s hs
        refine indicator_of_notMem (fun hsQ => hs ?_) H
        exact (((Pc i).slice w s (hQN i hsQ)).mp (hzero i _ hsQ)).2
    · rw [indicator_of_notMem hw]
      refine ENNReal.tsum_eq_zero.mpr fun s => indicator_of_notMem (fun hsQ => hw ?_) H
      obtain ⟨hwW, rfl⟩ := ((Pc i).slice w s (hQN i hsQ)).mp (hzero i _ hsQ)
      exact ⟨hsQ, hwW⟩
  -- measurability of the summands
  have hmeas : ∀ i, Measurable ((Pw i).indicator fun w => ((Pc i).mult : ℝ≥0∞) * F (G i w)) := by
    intro i
    have hGm : Measurable ((Pc i).W.piecewise (G i) fun _ => (0 : EuclideanSpace ℂ (Fin n))) :=
      (hGc i).measurable_piecewise continuousOn_const (Pc i).isOpen_W.measurableSet
    have heq : ((Pw i).indicator fun w => ((Pc i).mult : ℝ≥0∞) * F (G i w)) =
        (Pw i).indicator fun w => ((Pc i).mult : ℝ≥0∞) *
          F ((Pc i).W.piecewise (G i) (fun _ => (0 : EuclideanSpace ℂ (Fin n))) w) := by
      refine indicator_congr fun w hw => ?_
      rw [piecewise_eq_of_mem _ _ _ hw.2]
    rw [heq]
    exact (measurable_const.mul (hF.comp hGm)).indicator (hPwm i)
  rw [hLHS]
  simp_rw [hpt]
  rw [lintegral_tsum fun i => (hmeas i).aemeasurable]
  exact tsum_congr fun i => (lintegral_indicator (hPwm i) _).symm

end Coarea

end SGPT.Foundations.Analysis.Pending.DivisorCoarea
