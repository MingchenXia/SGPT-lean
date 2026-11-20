import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

/-! # Actual compact-test and chart localization maps into Hölder spaces -/

open Set Filter Function TopologicalSpace
open scoped Topology ContDiff NNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoLocalTestHolder

open FirstPass FirstPass.HolomorphicMaps ChartPartition HolderAtlas.HolderMap

noncomputable section

section CompactTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Compacts E} {r : ℝ≥0}

private theorem compactTest_derivative_bound (f : 𝓓_{K}(E, ℝ)) :
    ∀ i ≤ (0 : ℕ) + 1, ∀ x,
      ‖iteratedFDeriv ℝ i f x‖ ≤
        (({0, 1} : Finset ℕ).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) f := by
  intro i hi x
  refine (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans ?_
  apply Seminorm.le_def.mp (Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) ?_) f
  interval_cases i <;> simp

/-- The actual compactly supported smooth function as a bounded order-zero Hölder function. -/
def compactTestHolder (hr : r ≤ 1) (f : 𝓓_{K}(E, ℝ)) :
    BoundedContDiffHolderMap 0 r E ℝ :=
  BoundedContDiffHolderMap.ofContDiff hr f
    (f.contDiff.of_le (by exact_mod_cast le_top)) (compactTest_derivative_bound f)

@[simp] theorem compactTestHolder_apply (hr : r ≤ 1) (f : 𝓓_{K}(E, ℝ)) (x : E) :
    compactTestHolder hr f x = f x := rfl

/-- The genuine Hölder norm is controlled by two actual compact-test seminorms. -/
theorem norm_compactTestHolder_le (hr : r ≤ 1) (f : 𝓓_{K}(E, ℝ)) :
    ‖compactTestHolder hr f‖ ≤ 3 *
      (({0, 1} : Finset ℕ).sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) f := by
  simpa only [compactTestHolder, Nat.cast_zero, zero_add] using
    BoundedContDiffHolderMap.norm_ofContDiff_le hr f
    (f.contDiff.of_le (by exact_mod_cast le_top)) (compactTest_derivative_bound f)

/-- The actual compact-test inclusion is continuous for the existing compact-test topology. -/
def compactTestHolderCLM (hr : r ≤ 1) :
    𝓓_{K}(E, ℝ) →L[ℝ] BoundedContDiffHolderMap 0 r E ℝ :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ (compactTestHolder hr)
    (fun f g => by ext x; rfl)
    (fun c f => by ext x; rfl)
    ⟨{0, 1}, 3, by norm_num, norm_compactTestHolder_le hr⟩

@[simp] theorem compactTestHolderCLM_apply (hr : r ≤ 1) (f : 𝓓_{K}(E, ℝ)) (x : E) :
    compactTestHolderCLM hr f x = f x := rfl

end CompactTest

section ChartExtension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {r : ℝ≥0}

private theorem exists_chartCutoffHolder (A : HolderAtlas n M) (hr : r ≤ 1)
    (e : ComplexChart n M) (β : ComplexModel n → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) (hβt : tsupport β ⊆ e.val.target) :
    ∃ C, ∀ f : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ,
      ∃ u : A.HolderMap 0 r ℝ,
        (∀ x, u x = chartExtend e (fun z => β z * f z) x) ∧ ‖u‖ ≤ C * ‖f‖ := by
  classical
  let b := chartExtend e β
  have hbc : IsCompact (e.val.symm '' tsupport β) :=
    hβc.image_of_continuousOn (e.val.continuousOn_symm.mono hβt)
  have hbsub : tsupport b ⊆ e.val.symm '' tsupport β := by
    exact (support_chartExtend_subset e).trans (by rw [hbc.isClosed.closure_eq])
  have hbs : tsupport b ⊆ e.val.source := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hbsub hx
    exact e.val.map_target (hβt hz)
  have hbsmooth : ChartSmooth (n := n) b := chartSmooth_chartExtend e hβ hβc hβt
  have key : ∀ a : Fin A.m, ∃ C, ∀ f : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ,
      ∃ g : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ,
        (∀ z, g z = A.localRep a (chartExtend e (fun z => β z * f z)) z) ∧
        ‖g‖ ≤ C * ‖f‖ := by
    intro a
    let η : M → ℝ := fun x => A.χ a x * b x
    have hηs : ChartSmooth (n := n) η := fun f => (A.chartSmooth a f).mul (hbsmooth f)
    have hηχ : tsupport η ⊆ tsupport (A.χ a) := tsupport_mul_subset_left
    have hηb : tsupport η ⊆ tsupport b := tsupport_mul_subset_right
    have hηc : IsCompact (tsupport η) :=
      (A.isCompact_tsupport a).of_isClosed_subset (isClosed_tsupport _) hηχ
    have hηa : tsupport η ⊆ (A.chart a).val.source := hηχ.trans (A.tsupport_subset a)
    let σ : ComplexModel n → ℝ := (A.chart a).val.target.indicator (η ∘ (A.chart a).val.symm)
    obtain ⟨hσs, hσc, hσa⟩ := contDiff_indicator_comp_symm (A.chart a) hηs hηc hηa
    let L := (A.chart a).val '' tsupport η
    have hLc : IsCompact L :=
      hηc.image_of_continuousOn ((A.chart a).val.continuousOn.mono hηa)
    have hσL : tsupport σ ⊆ L := by
      refine closure_minimal ?_ hLc.isClosed
      intro z hz
      by_cases hzt : z ∈ (A.chart a).val.target
      · refine ⟨(A.chart a).val.symm z, ?_, (A.chart a).val.right_inv hzt⟩
        apply subset_tsupport η
        have hne : σ z ≠ 0 := hz
        change η ((A.chart a).val.symm z) ≠ 0
        simpa only [σ, indicator_of_mem hzt, comp_apply] using hne
      · exact (hz (by simp only [σ, indicator_of_notMem hzt])).elim
    let τ := chartTransition (A.chart a) e
    have hσU : tsupport σ ⊆ τ.source := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hσL hz
      change (A.chart a).val x ∈ (A.chart a).val.target ∩
        (A.chart a).val.symm ⁻¹' e.val.source
      refine ⟨(A.chart a).val.map_source (hηa hx), ?_⟩
      change (A.chart a).val.symm ((A.chart a).val x) ∈ e.val.source
      rw [(A.chart a).val.left_inv (hηa hx)]
      exact hbs (hηb hx)
    have hτs : ContDiffOn ℝ (0 + 1 : ℕ) τ τ.source := fun z hz =>
      ((chartTransition_contDiffAt_real (A.chart a) e hz).of_le
        (by exact_mod_cast le_top)).contDiffWithinAt
    obtain ⟨C, hC⟩ := BoundedContDiffHolderMap.exists_smul_comp_of_contDiffOn (F := ℝ) hr
      τ.open_source hτs (hσs.of_le (by exact_mod_cast le_top)) hσc hσU
    refine ⟨|C|, fun f => ?_⟩
    obtain ⟨g, hg, hgn⟩ := hC f
    refine ⟨g, fun z => ?_, hgn.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))⟩
    rw [hg]
    by_cases hzt : z ∈ (A.chart a).val.target
    · rw [HolderAtlas.localRep_of_mem _ hzt]
      by_cases hxe : (A.chart a).val.symm z ∈ e.val.source
      · simp only [indicator_of_mem hzt, comp_apply, η, b, chartExtend_of_mem hxe,
          smul_eq_mul, τ, chartTransition, OpenPartialHomeomorph.trans_apply]
        ring
      · simp only [indicator_of_mem hzt, comp_apply, η, b, chartExtend_of_notMem hxe,
          mul_zero, zero_smul, smul_zero]
    · simp only [indicator_of_notMem hzt, zero_smul,
        HolderAtlas.localRep_of_notMem _ hzt]
  choose C hC using key
  refine ⟨∑ a, C a, fun f => ?_⟩
  choose g hg hgn using fun a => hC a f
  let u : A.HolderMap 0 r ℝ :=
    ⟨chartExtend e (fun z => β z * f z), fun a => ⟨g a, funext (hg a)⟩⟩
  refine ⟨u, fun _ => rfl, ?_⟩
  rw [HolderAtlas.HolderMap.norm_def, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  have heq : u.rep a = g a := by
    ext z
    rw [HolderAtlas.HolderMap.coe_rep]
    exact (hg a z).symm
  rw [heq]
  exact hgn a

/-- The actual fixed-cutoff zero extension as a global Hölder function. -/
def chartCutoffHolder (A : HolderAtlas n M) (hr : r ≤ 1) (e : ComplexChart n M)
    (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβt : tsupport β ⊆ e.val.target) (f : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ) :
    A.HolderMap 0 r ℝ :=
  ((exists_chartCutoffHolder A hr e β hβ hβc hβt).choose_spec f).choose

@[simp] theorem chartCutoffHolder_apply (A : HolderAtlas n M) (hr : r ≤ 1)
    (e : ComplexChart n M) (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβt : tsupport β ⊆ e.val.target)
    (f : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ) (x : M) :
    chartCutoffHolder A hr e β hβ hβc hβt f x = chartExtend e (fun z => β z * f z) x :=
  ((exists_chartCutoffHolder A hr e β hβ hβc hβt).choose_spec f).choose_spec.1 x

/-- The actual fixed-cutoff chart extension is bounded and genuinely continuous. -/
def chartCutoffHolderCLM (A : HolderAtlas n M) (hr : r ≤ 1) (e : ComplexChart n M)
    (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβt : tsupport β ⊆ e.val.target) :
    BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ →L[ℝ] A.HolderMap 0 r ℝ := by
  refine LinearMap.mkContinuous
    { toFun := chartCutoffHolder A hr e β hβ hβc hβt
      map_add' := ?_
      map_smul' := ?_ }
    (exists_chartCutoffHolder A hr e β hβ hβc hβt).choose ?_
  · intro f g
    ext x
    simp only [chartCutoffHolder_apply, coe_add, Pi.add_apply]
    by_cases hx : x ∈ e.val.source
    · simp only [chartExtend_of_mem hx, BoundedContDiffHolderMap.coe_add, Pi.add_apply, mul_add]
    · simp only [chartExtend_of_notMem hx, add_zero]
  · intro c f
    ext x
    simp only [chartCutoffHolder_apply, coe_smul, Pi.smul_apply, RingHom.id_apply]
    by_cases hx : x ∈ e.val.source
    · simp only [chartExtend_of_mem hx, BoundedContDiffHolderMap.coe_smul, Pi.smul_apply,
        smul_eq_mul]
      ring
    · simp only [chartExtend_of_notMem hx, smul_zero]
  · intro f
    exact ((exists_chartCutoffHolder A hr e β hβ hβc hβt).choose_spec f).choose_spec.2

@[simp] theorem chartCutoffHolderCLM_apply (A : HolderAtlas n M) (hr : r ≤ 1)
    (e : ComplexChart n M) (β : ComplexModel n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβt : tsupport β ⊆ e.val.target)
    (f : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ) (x : M) :
    chartCutoffHolderCLM A hr e β hβ hβc hβt f x =
      chartExtend e (fun z => β z * f z) x :=
  chartCutoffHolder_apply A hr e β hβ hβc hβt f x

/-- The actual smooth zero extension of a local test, viewed in the global Hölder space. -/
def localTestHolder (A : HolderAtlas n M) (hr : r ≤ 1) (e : ComplexChart n M)
    (φ : 𝓓(chartTarget e, ℝ)) : A.HolderMap 0 r ℝ :=
  HolderAtlas.HolderMap.ofChartSmooth hr (chartExtend e φ)
    (chartSmooth_chartExtend e φ.contDiff φ.hasCompactSupport φ.tsupport_subset)

@[simp] theorem localTestHolder_apply (A : HolderAtlas n M) (hr : r ≤ 1)
    (e : ComplexChart n M) (φ : 𝓓(chartTarget e, ℝ)) (x : M) :
    localTestHolder A hr e φ x = chartExtend e φ x := rfl

/-- Genuine LF continuity of the local-test to global-Hölder zero extension. -/
def localTestHolderCLM (A : HolderAtlas n M) (hr : r ≤ 1) (e : ComplexChart n M) :
    𝓓(chartTarget e, ℝ) →L[ℝ] A.HolderMap 0 r ℝ := by
  refine TestFunction.mkCLM ℝ (localTestHolder A hr e) ?_ ?_ ?_
  · intro φ ψ
    ext x
    simp only [localTestHolder_apply, coe_add, Pi.add_apply]
    by_cases hx : x ∈ e.val.source
    · simp only [chartExtend_of_mem hx, FunLike.coe_add, Pi.add_apply]
    · simp only [chartExtend_of_notMem hx, add_zero]
  · intro c φ
    ext x
    simp only [localTestHolder_apply, coe_smul, Pi.smul_apply]
    by_cases hx : x ∈ e.val.source
    · simp only [chartExtend_of_mem hx, FunLike.coe_smul, Pi.smul_apply]
    · simp only [chartExtend_of_notMem hx, smul_zero]
  · intro K hK
    obtain ⟨β, hβ, hβc, hβt, hβ1⟩ :=
      exists_contDiff_eq_one_of_isCompact K.isCompact e.val.open_target hK
    let L := (chartCutoffHolderCLM A hr e β hβ hβc hβt).comp
      (compactTestHolderCLM (K := K) hr)
    refine L.continuous.congr ?_
    intro φ
    ext x
    change L φ x = localTestHolder A hr e (TestFunction.ofSupportedIn hK φ) x
    rw [localTestHolder_apply]
    change chartCutoffHolderCLM A hr e β hβ hβc hβt
        (compactTestHolderCLM hr φ) x = _
    rw [chartCutoffHolderCLM_apply]
    by_cases hx : x ∈ e.val.source
    · rw [chartExtend_of_mem hx, chartExtend_of_mem hx, compactTestHolderCLM_apply]
      change β (e.val x) * φ (e.val x) = φ (e.val x)
      by_cases hxK : e.val x ∈ K
      · rw [hβ1 _ hxK, one_mul]
      · rw [φ.zero_on_compl hxK]
        exact mul_zero _
    · rw [chartExtend_of_notMem hx, chartExtend_of_notMem hx]

@[simp] theorem localTestHolderCLM_apply (A : HolderAtlas n M) (hr : r ≤ 1)
    (e : ComplexChart n M) (φ : 𝓓(chartTarget e, ℝ)) (x : M) :
    localTestHolderCLM A hr e φ x = chartExtend e φ x := rfl

end ChartExtension

end

end SGPT.Foundations.Analysis.Pending.XiaoLocalTestHolder
