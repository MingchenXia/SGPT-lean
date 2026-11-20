import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Lowering the order and pushing forward from a chart in `C^{k,r}(M, F)`

Complements to the Hölder spaces `A.HolderMap k r F` of a Hölder atlas `A` of a complex manifold
`M` (`ManifoldHolderSpace`), used by the solvability of the Laplace equation on a compact Kähler
manifold (TN.4 B5 linear track L4, blueprint `bou:kahler-laplacian-solvability`).

* `BoundedContDiffHolderMap.toZero`, `toZeroCLM`: for `1 ≤ k` and `r ≤ 1` the inclusion
  `C^{k,r}_b(E, F) → C^{0,r}_b(E, F)` (`f` is bounded and Lipschitz), of norm `≤ 3`.
* `HolderAtlas.HolderMap.toZero`, `toZeroCLM`: the same inclusion `C^{k,r}(M, F) → C^{0,r}(M, F)`.
* `HolderAtlas.HolderMap.continuous`: the elements of `C^{k,r}(M, F)` are continuous.
* `HolderAtlas.HolderMap.exists_pushforward` (**push-forward from a chart**): for an atlas chart `e`
  and a compact set `K` in its target there is `C` such that every `w ∈ C^{k,r}_b(ℂⁿ, F)` with
  `tsupport w ⊆ K` defines `W = (w ∘ e on the chart source, 0 elsewhere) ∈ C^{k,r}(M, F)` with
  `‖W‖ ≤ C ‖w‖` (`r ≤ 1`).  Proof: in the chart `e_a` of the atlas the local representative of `W` is
  `σ_a · (w ∘ τ_a)` with the chart transition `τ_a = e ∘ e_a⁻¹` and a smooth cut-off `σ_a` with
  compact support in the domain of `τ_a`; then the localized composition estimate
  `BoundedContDiffHolderMap.exists_smul_comp_of_contDiffOn`.  (`M` is Hausdorff, so
  `e⁻¹(K) ∩ tsupport χ_a` is compact.)
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending

open FirstPass FirstPass.HolomorphicMaps

namespace BoundedContDiffHolderMap

variable {k : ℕ} {r : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inclusion `C^{k,r}_b → C^{0,r}_b` for `1 ≤ k`, `r ≤ 1`. -/
def toZero (hr : r ≤ 1) (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    BoundedContDiffHolderMap 0 r E F :=
  ofContDiff hr f (f.contDiff.of_le (by exact_mod_cast hk)) (M := ‖f‖)
    fun i hi x => f.norm_iteratedFDeriv_apply_le (hi.trans hk) x

@[simp]
theorem coe_toZero (hr : r ≤ 1) (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    ⇑(toZero hr hk f) = f :=
  rfl

theorem norm_toZero_le (hr : r ≤ 1) (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    ‖toZero hr hk f‖ ≤ 3 * ‖f‖ := by
  have h := norm_ofContDiff_le (k := 0) hr (f : E → F) (f.contDiff.of_le (by exact_mod_cast hk))
    (M := ‖f‖) fun i hi x => f.norm_iteratedFDeriv_apply_le (hi.trans hk) x
  exact h.trans_eq (by push_cast; ring)

/-- The inclusion `C^{k,r}_b → C^{0,r}_b` as a continuous linear map. -/
def toZeroCLM (hr : r ≤ 1) (hk : 1 ≤ k) :
    BoundedContDiffHolderMap k r E F →L[ℝ] BoundedContDiffHolderMap 0 r E F :=
  LinearMap.mkContinuous
    { toFun := toZero hr hk
      map_add' := fun _ _ => ext fun _ => rfl
      map_smul' := fun _ _ => ext fun _ => rfl }
    3 fun f => norm_toZero_le hr hk f

@[simp]
theorem toZeroCLM_apply (hr : r ≤ 1) (hk : 1 ≤ k) (f : BoundedContDiffHolderMap k r E F) :
    toZeroCLM hr hk f = toZero hr hk f :=
  rfl

end BoundedContDiffHolderMap

namespace HolderAtlas

namespace HolderMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : HolderAtlas n M} {F : Type} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {k : ℕ} {r : ℝ≥0}

/-! ### The inclusion `C^{k,r}(M) → C^{0,r}(M)` -/

/-- The inclusion `C^{k,r}(M, F) → C^{0,r}(M, F)` for `1 ≤ k`, `r ≤ 1`. -/
def toZero (hr : r ≤ 1) (hk : 1 ≤ k) (u : A.HolderMap k r F) : A.HolderMap 0 r F :=
  ⟨u, fun a => ⟨BoundedContDiffHolderMap.toZero hr hk (u.rep a), by
    rw [BoundedContDiffHolderMap.coe_toZero, coe_rep]⟩⟩

@[simp]
theorem coe_toZero (hr : r ≤ 1) (hk : 1 ≤ k) (u : A.HolderMap k r F) : ⇑(toZero hr hk u) = u :=
  rfl

theorem rep_toZero (hr : r ≤ 1) (hk : 1 ≤ k) (u : A.HolderMap k r F) (a : Fin A.m) :
    (toZero hr hk u).rep a = BoundedContDiffHolderMap.toZero hr hk (u.rep a) :=
  BoundedContDiffHolderMap.ext fun _ => rfl

theorem norm_toZero_le (hr : r ≤ 1) (hk : 1 ≤ k) (u : A.HolderMap k r F) :
    ‖toZero hr hk u‖ ≤ 3 * ‖u‖ := by
  rw [norm_def, norm_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [rep_toZero]
  exact BoundedContDiffHolderMap.norm_toZero_le hr hk _

/-- The inclusion `C^{k,r}(M, F) → C^{0,r}(M, F)` as a continuous linear map. -/
def toZeroCLM (hr : r ≤ 1) (hk : 1 ≤ k) : A.HolderMap k r F →L[ℝ] A.HolderMap 0 r F :=
  LinearMap.mkContinuous
    { toFun := toZero hr hk
      map_add' := fun _ _ => ext fun _ => rfl
      map_smul' := fun _ _ => ext fun _ => rfl }
    3 fun u => norm_toZero_le hr hk u

@[simp]
theorem coe_toZeroCLM (hr : r ≤ 1) (hk : 1 ≤ k) (u : A.HolderMap k r F) :
    ⇑(toZeroCLM (A := A) hr hk u) = u :=
  rfl

/-! ### Continuity -/

/-- `χ_a u` is continuous on `M`. -/
theorem continuous_χ_smul (u : A.HolderMap k r F) (a : Fin A.m) :
    Continuous fun y => A.χ a y • u y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ (A.chart a).val.source
  · have hc : ContinuousAt (fun y => A.localRep a u ((A.chart a).val y)) y :=
      ((u.rep a).contDiff.continuous.continuousAt).comp
        ((A.chart a).val.continuousAt hy)
    refine hc.congr ?_
    filter_upwards [(A.chart a).val.open_source.mem_nhds hy] with y' hy'
    exact localRep_chart (A := A) (u : M → F) hy'
  · have hyt : y ∉ tsupport (A.χ a) := fun h => hy (A.tsupport_subset a h)
    refine (continuousAt_const (y := (0 : F))).congr ?_
    filter_upwards [(isClosed_tsupport (A.χ a)).isOpen_compl.mem_nhds hyt] with y' hy'
    rw [image_eq_zero_of_notMem_tsupport hy', zero_smul]

/-- **The elements of `C^{k,r}(M, F)` are continuous.** -/
theorem continuous (u : A.HolderMap k r F) : Continuous u := by
  have h : ⇑u = fun y => ∑ a, A.χ a y • u y := funext fun y => by
    rw [← Finset.sum_smul, A.sum_eq_one, one_smul]
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_χ_smul u a

/-! ### Push-forward from a chart -/

/-- The push-forward of `w` from the chart `e`: `w ∘ e` on the chart source, `0` elsewhere. -/
def pushforward (e : ComplexChart n M) (w : ComplexModel n → F) : M → F :=
  e.val.source.indicator (w ∘ e.val)

theorem pushforward_of_mem {e : ComplexChart n M} (w : ComplexModel n → F) {y : M}
    (hy : y ∈ e.val.source) : pushforward e w y = w (e.val y) :=
  indicator_of_mem hy _

theorem pushforward_of_notMem {e : ComplexChart n M} (w : ComplexModel n → F) {y : M}
    (hy : y ∉ e.val.source) : pushforward e w y = 0 :=
  indicator_of_notMem hy _

theorem pushforward_symm {e : ComplexChart n M} (w : ComplexModel n → F) {z : ComplexModel n}
    (hz : z ∈ e.val.target) : pushforward e w (e.val.symm z) = w z := by
  rw [pushforward_of_mem w (e.val.map_target hz), e.val.right_inv hz]

/-- The push-forward vanishes off `e⁻¹(K)` when `tsupport w ⊆ K ⊆ target`. -/
theorem pushforward_eq_zero_of_notMem {e : ComplexChart n M} {w : ComplexModel n → F}
    {K : Set (ComplexModel n)} (hw : tsupport w ⊆ K) {y : M}
    (hy : y ∉ e.val.symm '' K) : pushforward e w y = 0 := by
  by_cases hys : y ∈ e.val.source
  · rw [pushforward_of_mem w hys]
    refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨e.val y, hw h, e.val.left_inv hys⟩
  · exact pushforward_of_notMem w hys

/-- **Push-forward from a chart** (`r ≤ 1`): for an atlas chart `e` and a compact `K` inside its
target there is `C` such that every `w ∈ C^{k,r}_b(ℂⁿ, F)` with `tsupport w ⊆ K` defines an element
`W` of `C^{k,r}(M, F)`, `W = w ∘ e` on the chart source and `0` elsewhere, with `‖W‖ ≤ C ‖w‖`. -/
theorem exists_pushforward (hr : r ≤ 1) (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C, ∀ w : BoundedContDiffHolderMap k r (ComplexModel n) F, tsupport w ⊆ K →
      ∃ W : A.HolderMap k r F, ⇑W = pushforward e w ∧ ‖W‖ ≤ C * ‖w‖ := by
  -- the compact set `e⁻¹(K)` of `M`
  have hKM : IsCompact (e.val.symm '' K) :=
    hK.image_of_continuousOn (e.val.continuousOn_symm.mono hKt)
  have hKMs : e.val.symm '' K ⊆ e.val.source := by
    rintro _ ⟨z, hz, rfl⟩; exact e.val.map_target (hKt hz)
  -- the estimate chart by chart
  have key : ∀ a : Fin A.m, ∃ C, ∀ w : BoundedContDiffHolderMap k r (ComplexModel n) F,
      tsupport w ⊆ K → ∃ h : BoundedContDiffHolderMap k r (ComplexModel n) F,
        ⇑h = A.localRep a (pushforward e w) ∧ ‖h‖ ≤ C * ‖w‖ := by
    intro a
    set ea := A.chart a with hea
    set τ := chartTransition ea e with hτ
    set L := ea.val '' (tsupport (A.χ a) ∩ e.val.symm '' K) with hL
    have hLc : IsCompact L :=
      ((A.isCompact_tsupport a).inter_right hKM.isClosed).image_of_continuousOn
        (ea.val.continuousOn.mono (inter_subset_left.trans (A.tsupport_subset a)))
    have hLτ : L ⊆ τ.source := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hya : y ∈ ea.val.source := A.tsupport_subset a hy1
      rw [hτ, chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source]
      exact ⟨ea.val.map_source hya, by rw [mem_preimage, ea.val.left_inv hya]; exact hKMs hy2⟩
    obtain ⟨ρ, hρs, hρc, hρU, hρ1⟩ := exists_contDiff_eq_one_of_isCompact hLc τ.open_source hLτ
    obtain ⟨hχs, hχc, hχt⟩ := contDiff_indicator_comp_symm ea (A.chartSmooth a)
      (A.isCompact_tsupport a) (A.tsupport_subset a)
    set χt := ea.val.target.indicator (A.χ a ∘ ea.val.symm) with hχt
    have hτs : ContDiffOn ℝ (k + 1 : ℕ) τ τ.source := fun z hz =>
      ((chartTransition_contDiffAt_real ea e hz).of_le
        (by exact_mod_cast le_top)).contDiffWithinAt
    have hσ : ContDiff ℝ (k + 1 : ℕ) fun z => χt z * ρ z :=
      (hχs.of_le (by exact_mod_cast le_top)).mul (hρs.of_le (by exact_mod_cast le_top))
    obtain ⟨C, hC⟩ := BoundedContDiffHolderMap.exists_smul_comp_of_contDiffOn (F := F) hr
      τ.open_source hτs hσ hχc.mul_right (tsupport_mul_subset_right.trans hρU)
    refine ⟨C, fun w hw => ?_⟩
    obtain ⟨h, hh, hhn⟩ := hC w
    refine ⟨h, funext fun z => ?_, hhn⟩
    rw [hh]
    by_cases hzt : z ∈ ea.val.target
    · rw [localRep_of_mem _ hzt]
      have hχz : χt z = A.χ a (ea.val.symm z) := by
        rw [hχt, indicator_of_mem hzt, comp_apply]
      by_cases hχ0 : A.χ a (ea.val.symm z) = 0
      · rw [hχz, hχ0, zero_mul, zero_smul, zero_smul]
      by_cases hys : ea.val.symm z ∈ e.val.source
      · rw [pushforward_of_mem w hys]
        have hτz : τ z = e.val (ea.val.symm z) := rfl
        by_cases hw0 : w (e.val (ea.val.symm z)) = 0
        · rw [hτz, hw0, smul_zero, smul_zero]
        · have hzL : z ∈ L := ⟨ea.val.symm z,
            ⟨subset_tsupport _ hχ0, ⟨e.val (ea.val.symm z), hw (subset_tsupport _ hw0),
              e.val.left_inv hys⟩⟩, ea.val.right_inv hzt⟩
          rw [hρ1 z hzL, mul_one, hχz, hτz]
      · rw [pushforward_of_notMem w hys, smul_zero]
        have hρ0 : ρ z = 0 := by
          by_contra hρ0
          have hzs := hρU (subset_tsupport _ hρ0)
          rw [hτ, chartTransition, OpenPartialHomeomorph.trans_source,
            OpenPartialHomeomorph.symm_source] at hzs
          exact hys hzs.2
        rw [hρ0, mul_zero, zero_smul]
    · rw [localRep_of_notMem _ hzt, hχt, indicator_of_notMem hzt, zero_mul, zero_smul]
  choose C hC using key
  refine ⟨∑ a, C a, fun w hw => ?_⟩
  choose h hh hhn using fun a => hC a w hw
  refine ⟨⟨pushforward e w, fun a => ⟨h a, hh a⟩⟩, rfl, ?_⟩
  rw [norm_def, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have : (⟨pushforward e w, fun a => ⟨h a, hh a⟩⟩ : A.HolderMap k r F).rep a = h a :=
    BoundedContDiffHolderMap.ext fun z => by rw [coe_rep, hh a]; rfl
  rw [this]
  exact hhn a

end HolderMap

end HolderAtlas

end SGPT.Foundations.Analysis.Pending
