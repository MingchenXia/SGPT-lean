import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMapComp
import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMapCompact

set_option autoImplicit false

/-!
# Hölder spaces `C^{k,r}(M, F)` on a compact complex manifold

A *Hölder atlas* `A` of a complex manifold `M` (`HolderAtlas`) is a finite family of atlas charts
`e_a` with a chart-smooth partition of unity `χ_a`, `tsupport χ_a` compact inside the source of
`e_a`.  Every compact complex manifold has one (`HolderAtlas.nonempty`, from
`ChartPartition.exists_chartSmooth_partitionOfUnity`).

For such an atlas, `A.HolderMap k r F` is the space of maps `u : M → F` whose local
representatives

`A.localRep a u = (χ_a u) ∘ e_a⁻¹` (extended by zero off the chart target)

lie in `C^{k,r}_b(ℂⁿ, F)`, normed by `‖u‖ = ∑_a ‖(χ_a u) ∘ e_a⁻¹‖_{C^{k,r}_b}`.

## Main results

* `HolderAtlas.HolderMap.instNormedAddCommGroup`, `instNormedSpace`, `instCompleteSpace`: a Banach
  space (closedness through pointwise limits: `u = ∑_a (localRep a u) ∘ e_a` on the chart sources,
  `HolderAtlas.eq_sum_localRep`).
* `HolderAtlas.HolderMap.exists_smul_comp_symm` (**chart independence**): for every atlas chart `e`
  and every `C^{k+1}` cut-off `σ` with compact support in the chart target, `σ · (u ∘ e⁻¹)` lies in
  `C^{k,r}_b(ℂⁿ, F)` with norm `≤ C ‖u‖` (`r ≤ 1`).  Proof: `σ · (u ∘ e⁻¹) = ∑_a σ_a · (localRep a u ∘ τ_a)`
  with the chart transitions `τ_a = e_a ∘ e⁻¹` and cut-offs `σ_a` with compact support in their
  domains; then the localized composition estimate `exists_smul_comp_of_contDiffOn`.
* `HolderAtlas.HolderMap.ofChartSmooth`: chart-smooth real functions (e.g. constants) belong to
  `C^{k,r}(M, ℝ)`.
* `HolderAtlas.HolderMap.toAtlas`: consequently the spaces of two Hölder atlases coincide, with
  equivalent norms (a bounded linear map in each direction): `C^{k,r}(M, F)` does not depend on the
  atlas.
* `HolderAtlas.HolderMap.ofLECLM` and `isCompactOperator_ofLE`: the inclusion
  `C^{k,r}(M, F) → C^{k,s}(M, F)`, `s ≤ r`, is bounded, and compact for `s < r ≤ 1` and `F`
  finite-dimensional (the local representatives have the fixed compact supports `e_a(tsupport χ_a)`;
  `BoundedContDiffHolderMap.exists_subseq_tendsto_ofLE`).

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending

open FirstPass FirstPass.HolomorphicMaps

/-- A finite family of atlas charts with a subordinate chart-smooth partition of unity: the fixed
data defining the Hölder norms on a compact complex manifold. -/
structure HolderAtlas (n : ℕ) (M : Type*) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] where
  /-- The number of charts. -/
  m : ℕ
  /-- The charts. -/
  chart : Fin m → ComplexChart n M
  /-- The partition of unity. -/
  χ : Fin m → M → ℝ
  chartSmooth : ∀ a, ChartSmooth (n := n) (χ a)
  tsupport_subset : ∀ a, tsupport (χ a) ⊆ (chart a).val.source
  isCompact_tsupport : ∀ a, IsCompact (tsupport (χ a))
  sum_eq_one : ∀ y, ∑ a, χ a y = 1

/-- A `C^∞` cut-off equal to `1` on a compact set `K`, with compact support inside an open set
`U ⊇ K`, on a finite-dimensional real normed space. -/
theorem exists_contDiff_eq_one_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧ ∀ x ∈ K, ρ x = 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ρ, hρ1, hρV, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞))
    𝓘(ℝ, E) hK.isClosed (by rwa [hVo.interior_eq])
  have hρsupp : support (ρ : E → ℝ) ⊆ V := fun x hx => by
    by_contra hxV
    exact hx (hρV x hxV)
  exact ⟨ρ, ρ.contMDiff.contDiff,
    HasCompactSupport.of_support_subset_isCompact hVc (hρsupp.trans subset_closure),
    (closure_mono hρsupp).trans hVU, fun x hx => hρ1.self_of_nhdsSet x hx⟩

namespace HolderAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Every compact complex manifold has a Hölder atlas. -/
theorem nonempty [CompactSpace M] : Nonempty (HolderAtlas n M) := by
  obtain ⟨m, χ, idx, hχs, -, hχS, hχc, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : TopologicalSpace.Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  exact ⟨⟨m, fun a => complexChartAt (n := n) (idx a), χ, hχs, hχS, hχc, hsum⟩⟩

variable (A : HolderAtlas n M) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem χ_eq_zero_of_notMem {a : Fin A.m} {y : M} (hy : y ∉ (A.chart a).val.source) :
    A.χ a y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hy (A.tsupport_subset a h)

/-- The local representative `(χ_a u) ∘ e_a⁻¹` of `u`, extended by zero off the chart target. -/
def localRep (a : Fin A.m) (u : M → F) : ComplexModel n → F :=
  (A.chart a).val.target.indicator fun z =>
    A.χ a ((A.chart a).val.symm z) • u ((A.chart a).val.symm z)

variable {A}

theorem localRep_of_mem {a : Fin A.m} (u : M → F) {z : ComplexModel n}
    (hz : z ∈ (A.chart a).val.target) :
    A.localRep a u z = A.χ a ((A.chart a).val.symm z) • u ((A.chart a).val.symm z) :=
  indicator_of_mem hz _

theorem localRep_of_notMem {a : Fin A.m} (u : M → F) {z : ComplexModel n}
    (hz : z ∉ (A.chart a).val.target) : A.localRep a u z = 0 :=
  indicator_of_notMem hz _

theorem localRep_chart {a : Fin A.m} (u : M → F) {y : M} (hy : y ∈ (A.chart a).val.source) :
    A.localRep a u ((A.chart a).val y) = A.χ a y • u y := by
  rw [localRep_of_mem u ((A.chart a).val.map_source hy), (A.chart a).val.left_inv hy]

theorem localRep_add (a : Fin A.m) (u v : M → F) :
    A.localRep a (u + v) = A.localRep a u + A.localRep a v := by
  funext z
  by_cases hz : z ∈ (A.chart a).val.target
  · simp only [Pi.add_apply, localRep_of_mem _ hz, smul_add]
  · simp only [Pi.add_apply, localRep_of_notMem _ hz, add_zero]

theorem localRep_smul (a : Fin A.m) (c : ℝ) (u : M → F) :
    A.localRep a (c • u) = c • A.localRep a u := by
  funext z
  by_cases hz : z ∈ (A.chart a).val.target
  · simp only [Pi.smul_apply, localRep_of_mem _ hz, smul_comm c]
  · simp only [Pi.smul_apply, localRep_of_notMem _ hz, smul_zero]

theorem localRep_zero (a : Fin A.m) : A.localRep a (0 : M → F) = 0 := by
  funext z
  by_cases hz : z ∈ (A.chart a).val.target
  · simp only [localRep_of_mem _ hz, Pi.zero_apply, smul_zero]
  · simp only [localRep_of_notMem _ hz, Pi.zero_apply]

/-- **Reconstruction**: `u = ∑_a (localRep a u) ∘ e_a` on the chart sources (`∑ χ_a = 1`). -/
theorem eq_sum_localRep (u : M → F) (y : M) :
    u y = ∑ a, (A.chart a).val.source.indicator (fun y => A.localRep a u ((A.chart a).val y)) y := by
  conv_lhs => rw [← one_smul ℝ (u y), ← A.sum_eq_one y, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hy : y ∈ (A.chart a).val.source
  · rw [indicator_of_mem hy, localRep_chart u hy]
  · rw [indicator_of_notMem hy, A.χ_eq_zero_of_notMem hy, zero_smul]

/-- The local representative vanishes off the compact set `e_a(tsupport χ_a)`. -/
theorem localRep_eq_zero_of_notMem {a : Fin A.m} (u : M → F) {z : ComplexModel n}
    (hz : z ∉ (A.chart a).val '' tsupport (A.χ a)) : A.localRep a u z = 0 := by
  by_cases hzt : z ∈ (A.chart a).val.target
  · rw [localRep_of_mem u hzt]
    have : A.χ a ((A.chart a).val.symm z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hz ⟨_, h, (A.chart a).val.right_inv hzt⟩
    rw [this, zero_smul]
  · exact localRep_of_notMem u hzt

theorem isCompact_image_tsupport (a : Fin A.m) :
    IsCompact ((A.chart a).val '' tsupport (A.χ a)) :=
  (A.isCompact_tsupport a).image_of_continuousOn
    ((A.chart a).val.continuousOn.mono (A.tsupport_subset a))

variable (A)

/-- The Hölder space `C^{k,r}(M, F)` defined through the Hölder atlas `A`: the maps whose local
representatives lie in `C^{k,r}_b(ℂⁿ, F)`. -/
structure HolderMap (k : ℕ) (r : ℝ≥0) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The underlying map. Use the coercion instead. -/
  toFun : M → F
  exists_rep' : ∀ a, ∃ g : BoundedContDiffHolderMap k r (ComplexModel n) F, ⇑g = A.localRep a toFun

namespace HolderMap

variable {A} {k : ℕ} {r : ℝ≥0}

instance instFunLike : FunLike (A.HolderMap k r F) M F where
  coe u := u.toFun
  coe_injective u v h := by cases u; cases v; congr

@[ext]
theorem ext {u v : A.HolderMap k r F} (h : ∀ y, u y = v y) : u = v :=
  DFunLike.ext _ _ h

/-- The local representative of `u` in the chart `e_a`, as an element of `C^{k,r}_b`. -/
def rep (u : A.HolderMap k r F) (a : Fin A.m) : BoundedContDiffHolderMap k r (ComplexModel n) F :=
  (u.exists_rep' a).choose.copy (A.localRep a u) (u.exists_rep' a).choose_spec.symm

@[simp]
theorem coe_rep (u : A.HolderMap k r F) (a : Fin A.m) : ⇑(u.rep a) = A.localRep a u :=
  rfl

/-! ### Algebraic structure -/

instance instZero : Zero (A.HolderMap k r F) :=
  ⟨⟨0, fun a => ⟨0, (localRep_zero a).symm⟩⟩⟩

instance instAdd : Add (A.HolderMap k r F) :=
  ⟨fun u v => ⟨⇑u + ⇑v, fun a => ⟨u.rep a + v.rep a, by
    rw [BoundedContDiffHolderMap.coe_add, coe_rep, coe_rep, localRep_add]⟩⟩⟩

instance instSMul : SMul ℝ (A.HolderMap k r F) :=
  ⟨fun c u => ⟨c • ⇑u, fun a => ⟨c • u.rep a, by
    rw [BoundedContDiffHolderMap.coe_smul, coe_rep, localRep_smul]⟩⟩⟩

instance instNeg : Neg (A.HolderMap k r F) :=
  ⟨fun u => (-1 : ℝ) • u⟩

instance instSub : Sub (A.HolderMap k r F) :=
  ⟨fun u v => u + -v⟩

instance instSMulNat : SMul ℕ (A.HolderMap k r F) :=
  ⟨fun j u => (j : ℝ) • u⟩

instance instSMulInt : SMul ℤ (A.HolderMap k r F) :=
  ⟨fun j u => (j : ℝ) • u⟩

@[simp] theorem coe_zero : ⇑(0 : A.HolderMap k r F) = 0 := rfl

@[simp] theorem coe_add (u v : A.HolderMap k r F) : ⇑(u + v) = ⇑u + ⇑v := rfl

@[simp] theorem coe_smul (c : ℝ) (u : A.HolderMap k r F) : ⇑(c • u) = c • ⇑u := rfl

@[simp] theorem coe_neg (u : A.HolderMap k r F) : ⇑(-u) = -⇑u := by
  change (-1 : ℝ) • ⇑u = _
  rw [neg_one_smul]

@[simp] theorem coe_sub (u v : A.HolderMap k r F) : ⇑(u - v) = ⇑u - ⇑v := by
  change ⇑u + ⇑(-v) = _
  rw [coe_neg, sub_eq_add_neg]

theorem coe_nsmul (j : ℕ) (u : A.HolderMap k r F) : ⇑(j • u) = j • ⇑u := by
  change (j : ℝ) • ⇑u = _
  rw [Nat.cast_smul_eq_nsmul]

theorem coe_zsmul (j : ℤ) (u : A.HolderMap k r F) : ⇑(j • u) = j • ⇑u := by
  change (j : ℝ) • ⇑u = _
  rw [Int.cast_smul_eq_zsmul]

instance instAddCommGroup : AddCommGroup (A.HolderMap k r F) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun u j => coe_nsmul j u) (fun u j => coe_zsmul j u)

/-- The coercion to `M → F` as an additive group homomorphism. -/
def coeAddHom : A.HolderMap k r F →+ (M → F) where
  toFun u := u
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module ℝ (A.HolderMap k r F) :=
  DFunLike.coe_injective.module ℝ coeAddHom coe_smul

theorem rep_add (u v : A.HolderMap k r F) (a : Fin A.m) : (u + v).rep a = u.rep a + v.rep a :=
  BoundedContDiffHolderMap.ext fun z => by
    simp only [coe_rep, coe_add, localRep_add, BoundedContDiffHolderMap.coe_add]

theorem rep_smul (c : ℝ) (u : A.HolderMap k r F) (a : Fin A.m) : (c • u).rep a = c • u.rep a :=
  BoundedContDiffHolderMap.ext fun z => by
    simp only [coe_rep, coe_smul, localRep_smul, BoundedContDiffHolderMap.coe_smul]

/-- `u ↦ (χ_a u) ∘ e_a⁻¹` as a linear map. -/
def repLM (a : Fin A.m) : A.HolderMap k r F →ₗ[ℝ] BoundedContDiffHolderMap k r (ComplexModel n) F
    where
  toFun u := u.rep a
  map_add' u v := rep_add u v a
  map_smul' c u := rep_smul c u a

theorem rep_sub (u v : A.HolderMap k r F) (a : Fin A.m) : (u - v).rep a = u.rep a - v.rep a :=
  (repLM a).map_sub u v

theorem rep_zero (a : Fin A.m) : (0 : A.HolderMap k r F).rep a = 0 :=
  (repLM a).map_zero

/-! ### The norm -/

/-- The norm `∑_a ‖(χ_a u) ∘ e_a⁻¹‖_{C^{k,r}_b}`. -/
instance instNorm : Norm (A.HolderMap k r F) :=
  ⟨fun u => ∑ a, ‖u.rep a‖⟩

theorem norm_def (u : A.HolderMap k r F) : ‖u‖ = ∑ a, ‖u.rep a‖ :=
  rfl

theorem norm_rep_le (u : A.HolderMap k r F) (a : Fin A.m) : ‖u.rep a‖ ≤ ‖u‖ :=
  Finset.single_le_sum (f := fun b => ‖u.rep b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)

private theorem normedSpaceCore : NormedSpace.Core ℝ (A.HolderMap k r F) where
  norm_nonneg u := Finset.sum_nonneg fun a _ => norm_nonneg (u.rep a)
  norm_smul c u := by
    rw [norm_def, norm_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [rep_smul, norm_smul]
  norm_triangle u v := by
    rw [norm_def, norm_def, norm_def, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by rw [rep_add]; exact norm_add_le _ _
  norm_eq_zero_iff u := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h0 : ∀ a, u.rep a = 0 := fun a =>
        norm_eq_zero.1 (le_antisymm (h ▸ norm_rep_le u a) (norm_nonneg _))
      refine ext fun y => ?_
      rw [eq_sum_localRep (A := A) u y, coe_zero, Pi.zero_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have : A.localRep a u = 0 := by rw [← coe_rep, h0 a]; rfl
      simp [this]
    · subst h
      simp [norm_def, rep_zero]

instance instNormedAddCommGroup : NormedAddCommGroup (A.HolderMap k r F) :=
  NormedAddCommGroup.ofCore normedSpaceCore

instance instNormedSpace : NormedSpace ℝ (A.HolderMap k r F) :=
  NormedSpace.ofCore normedSpaceCore

/-- `u ↦ (χ_a u) ∘ e_a⁻¹` as a continuous linear map (norm `≤ 1`). -/
def repCLM (a : Fin A.m) :
    A.HolderMap k r F →L[ℝ] BoundedContDiffHolderMap k r (ComplexModel n) F :=
  (repLM a).mkContinuous 1 fun u => by rw [one_mul]; exact norm_rep_le u a

/-! ### Completeness -/

/-- If the local representatives of a sequence converge in `C^{k,r}_b`, the sequence converges in
`C^{k,r}(M, F)`. -/
theorem exists_tendsto_of_tendsto_rep {u : ℕ → A.HolderMap k r F}
    {v : Fin A.m → BoundedContDiffHolderMap k r (ComplexModel n) F}
    (hv : ∀ a, Tendsto (fun j => (u j).rep a) atTop (𝓝 (v a))) :
    ∃ U : A.HolderMap k r F, Tendsto u atTop (𝓝 U) ∧ ∀ a, U.rep a = v a := by
  -- pointwise convergence of the representatives
  have hpt : ∀ a z, Tendsto (fun j => (u j).rep a z) atTop (𝓝 (v a z)) := fun a z => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.1 (hv a))
    have h := ((u j).rep a - v a).norm_apply_le z
    rwa [BoundedContDiffHolderMap.coe_sub, Pi.sub_apply] at h
  set U₀ : M → F := fun y =>
    ∑ a, (A.chart a).val.source.indicator (fun y => v a ((A.chart a).val y)) y with hU₀
  have hU : ∀ y, Tendsto (fun j => u j y) atTop (𝓝 (U₀ y)) := fun y => by
    have he : (fun j => u j y) = fun j => ∑ a, (A.chart a).val.source.indicator
        (fun y => A.localRep a (u j) ((A.chart a).val y)) y :=
      funext fun j => eq_sum_localRep (A := A) (u j) y
    rw [he, hU₀]
    refine tendsto_finsetSum _ fun a _ => ?_
    by_cases hy : y ∈ (A.chart a).val.source
    · simp only [indicator_of_mem hy]
      exact hpt a _
    · simp only [indicator_of_notMem hy]
      exact tendsto_const_nhds
  have hloc : ∀ a, A.localRep a U₀ = ⇑(v a) := fun a => by
    funext z
    by_cases hz : z ∈ (A.chart a).val.target
    · refine tendsto_nhds_unique ?_ (hpt a z)
      rw [localRep_of_mem _ hz]
      have h := ((tendsto_const_nhds (x := A.χ a ((A.chart a).val.symm z))).smul
        (hU ((A.chart a).val.symm z)))
      refine h.congr fun j => ?_
      rw [coe_rep, localRep_of_mem _ hz]
    · rw [localRep_of_notMem _ hz]
      refine tendsto_nhds_unique ?_ (hpt a z)
      refine tendsto_const_nhds.congr fun j => ?_
      rw [coe_rep, localRep_of_notMem _ hz]
  let U : A.HolderMap k r F := ⟨U₀, fun a => ⟨v a, (hloc a).symm⟩⟩
  have hUrep : ∀ a, U.rep a = v a := fun a =>
    BoundedContDiffHolderMap.ext fun z => by rw [coe_rep]; exact congrFun (hloc a) z
  refine ⟨U, ?_, hUrep⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun j => ∑ a, ‖(u j).rep a - v a‖) atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin A.m)))]
    exact tendsto_finsetSum _ fun a _ => tendsto_iff_norm_sub_tendsto_zero.1 (hv a)
  refine hs.congr fun j => ?_
  rw [norm_def]
  exact Finset.sum_congr rfl fun a _ => by rw [rep_sub, hUrep]

/-- `C^{k,r}(M, F)` is a Banach space when `F` is complete. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (A.HolderMap k r F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcau : ∀ a, CauchySeq fun j => (u j).rep a := fun a =>
    (repCLM (A := A) (k := k) (r := r) (F := F) a).uniformContinuous.comp_cauchySeq hu
  choose v hv using fun a => cauchySeq_tendsto_of_complete (hcau a)
  obtain ⟨U, hU, -⟩ := exists_tendsto_of_tendsto_rep hv
  exact ⟨U, hU⟩

/-! ### Chart independence -/

/-- The local representative evaluated through a chart transition. -/
theorem localRep_chartTransition {a : Fin A.m} (u : M → F) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ (chartTransition e (A.chart a)).source) :
    A.localRep a u (chartTransition e (A.chart a) z) = A.χ a (e.val.symm z) • u (e.val.symm z) := by
  have hz' : e.val.symm z ∈ (A.chart a).val.source := by
    have h := hz
    rw [chartTransition, OpenPartialHomeomorph.trans_source] at h
    exact h.2
  exact localRep_chart u hz'

/-- **Chart independence.** For an atlas chart `e` and a `C^{k+1}` cut-off `σ` with compact
support in the target of `e`, `z ↦ σ z • u (e⁻¹ z)` lies in `C^{k,r}_b(ℂⁿ, F)` with norm
`≤ C ‖u‖` (`r ≤ 1`). -/
theorem exists_smul_comp_symm (hr : r ≤ 1) (e : ComplexChart n M) {σ : ComplexModel n → ℝ}
    (hσ : ContDiff ℝ (k + 1 : ℕ) σ) (hσc : HasCompactSupport σ) (hσt : tsupport σ ⊆ e.val.target) :
    ∃ C, ∀ u : A.HolderMap k r F,
      ∃ h : BoundedContDiffHolderMap k r (ComplexModel n) F,
        (∀ z, h z = σ z • u (e.val.symm z)) ∧ ‖h‖ ≤ C * ‖u‖ := by
  -- the estimate chart by chart
  have key : ∀ a : Fin A.m, ∃ C, ∀ u : A.HolderMap k r F,
      ∃ h : BoundedContDiffHolderMap k r (ComplexModel n) F,
        (∀ z, h z = σ z • (A.χ a (e.val.symm z) • u (e.val.symm z))) ∧ ‖h‖ ≤ C * ‖u‖ := by
    intro a
    set τ := chartTransition e (A.chart a) with hτ
    set K : Set (ComplexModel n) := tsupport σ ∩ e.val.symm ⁻¹' tsupport (A.χ a) with hK
    have hKc : IsCompact K :=
      hσc.of_isClosed_subset ((e.val.continuousOn_symm.mono hσt).preimage_isClosed_of_isClosed
        (isClosed_tsupport σ) (isClosed_tsupport _)) inter_subset_left
    have hKU : K ⊆ τ.source := fun z hz => by
      rw [hτ, chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source]
      exact ⟨hσt hz.1, A.tsupport_subset a hz.2⟩
    obtain ⟨ρ, hρs, hρc, hρU, hρ1⟩ :=
      exists_contDiff_eq_one_of_isCompact hKc τ.open_source hKU
    have hτs : ContDiffOn ℝ (k + 1 : ℕ) τ τ.source := fun z hz =>
      ((chartTransition_contDiffAt_real e (A.chart a) hz).of_le
        (by exact_mod_cast le_top)).contDiffWithinAt
    have hσρ : ContDiff ℝ (k + 1 : ℕ) fun z => σ z * ρ z :=
      hσ.mul (hρs.of_le (by exact_mod_cast le_top))
    obtain ⟨C, hC⟩ := BoundedContDiffHolderMap.exists_smul_comp_of_contDiffOn (F := F) hr
      τ.open_source hτs hσρ hσc.mul_right (tsupport_mul_subset_right.trans hρU)
    refine ⟨|C|, fun u => ?_⟩
    obtain ⟨h, hh, hhn⟩ := hC (u.rep a)
    refine ⟨h, fun z => ?_, hhn.trans (mul_le_mul (le_abs_self C) (norm_rep_le u a)
      (norm_nonneg _) (abs_nonneg C))⟩
    rw [hh, coe_rep]
    by_cases hσz : σ z = 0
    · simp [hσz]
    have hzt : z ∈ tsupport σ := subset_tsupport _ hσz
    by_cases hχz : A.χ a (e.val.symm z) = 0
    · rw [hχz, zero_smul, smul_zero]
      by_cases hρz : ρ z = 0
      · rw [hρz, mul_zero, zero_smul]
      · rw [localRep_chartTransition u e (hρU (subset_tsupport _ hρz)), hχz, zero_smul, smul_zero]
    · have hzK : z ∈ K := ⟨hzt, subset_tsupport _ hχz⟩
      rw [hρ1 z hzK, mul_one, localRep_chartTransition u e (hKU hzK)]
  choose C hC using key
  refine ⟨∑ a, C a, fun u => ?_⟩
  choose h hh hhn using fun a => hC a u
  refine ⟨∑ a, h a, fun z => ?_, ?_⟩
  · have hc : ⇑(∑ a, h a) = ∑ a, ⇑(h a) :=
      map_sum (BoundedContDiffHolderMap.coeAddHom (k := k) (r := r) (E := ComplexModel n)
        (F := F)) h Finset.univ
    rw [hc, Finset.sum_apply]
    simp only [hh]
    rw [← Finset.smul_sum, ← Finset.sum_smul]
    by_cases hz : z ∈ e.val.target
    · rw [A.sum_eq_one, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hz (hσt h), zero_smul, zero_smul]
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ => hhn a

/-! ### Independence of the atlas -/

/-- The chart representative of a chart-smooth function with compact support inside the chart
source, extended by zero: a smooth function with compact support inside the chart target. -/
theorem contDiff_indicator_comp_symm (e : ComplexChart n M) {χ : M → ℝ}
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source) :
    ContDiff ℝ ∞ (e.val.target.indicator (χ ∘ e.val.symm)) ∧
      HasCompactSupport (e.val.target.indicator (χ ∘ e.val.symm)) ∧
      tsupport (e.val.target.indicator (χ ∘ e.val.symm)) ⊆ e.val.target := by
  set L := e.val '' tsupport χ with hL
  have hLc : IsCompact L := hc.image_of_continuousOn (e.val.continuousOn.mono hs)
  have hLt : L ⊆ e.val.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.val.map_source (hs hy)
  have hzero : ∀ z ∉ L, e.val.target.indicator (χ ∘ e.val.symm) z = 0 := fun z hz => by
    by_cases hzt : z ∈ e.val.target
    · rw [indicator_of_mem hzt, comp_apply]
      exact image_eq_zero_of_notMem_tsupport fun h => hz ⟨_, h, e.val.right_inv hzt⟩
    · exact indicator_of_notMem hzt _
  have hsupp : support (e.val.target.indicator (χ ∘ e.val.symm)) ⊆ L := fun z hz => by
    by_contra h
    exact hz (hzero z h)
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_,
    HasCompactSupport.of_support_subset_isCompact hLc hsupp,
    (closure_minimal hsupp hLc.isClosed).trans hLt⟩
  by_cases hzt : z ∈ e.val.target
  · have heq : e.val.target.indicator (χ ∘ e.val.symm) =ᶠ[𝓝 z] χ ∘ e.val.symm := by
      filter_upwards [e.val.open_target.mem_nhds hzt] with w hw using indicator_of_mem hw _
    exact ((hχ e).contDiffAt (e.val.open_target.mem_nhds hzt)).congr_of_eventuallyEq heq
  · have hzL : z ∉ L := fun h => hzt (hLt h)
    have heq : e.val.target.indicator (χ ∘ e.val.symm) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hLc.isClosed.isOpen_compl.mem_nhds hzL] with w hw using hzero w hw
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Chart-smooth real functions belong to `C^{k,r}(M, ℝ)` (`r ≤ 1`); e.g. the constants, so the
space is not degenerate. -/
def ofChartSmooth (hr : r ≤ 1) (u : M → ℝ) (hu : ChartSmooth (n := n) u) : A.HolderMap k r ℝ :=
  ⟨u, fun a => by
    have hs : ChartSmooth (n := n) fun y => A.χ a y * u y := fun e =>
      (A.chartSmooth a e).mul (hu e)
    have hsub : tsupport (fun y => A.χ a y * u y) ⊆ tsupport (A.χ a) := tsupport_mul_subset_left
    obtain ⟨h1, h2, -⟩ := contDiff_indicator_comp_symm (A.chart a) hs
      ((A.isCompact_tsupport a).of_isClosed_subset (isClosed_tsupport _) hsub)
      (hsub.trans (A.tsupport_subset a))
    refine ⟨BoundedContDiffHolderMap.ofHasCompactSupport hr _
      (h1.of_le (by exact_mod_cast le_top)) h2, ?_⟩
    funext z
    rw [BoundedContDiffHolderMap.coe_ofHasCompactSupport]
    by_cases hz : z ∈ (A.chart a).val.target
    · rw [indicator_of_mem hz, localRep_of_mem _ hz, smul_eq_mul]
      rfl
    · rw [indicator_of_notMem hz, localRep_of_notMem _ hz]⟩

@[simp]
theorem coe_ofChartSmooth (hr : r ≤ 1) (u : M → ℝ) (hu : ChartSmooth (n := n) u) :
    ⇑(ofChartSmooth (A := A) (k := k) hr u hu) = u :=
  rfl

/-- **Independence of the atlas** (`r ≤ 1`): the maps of `C^{k,r}(M, F)` for the atlas `A` belong
to `C^{k,r}(M, F)` for any other Hölder atlas `A'`, with norm `≤ C ‖u‖`. -/
theorem exists_toAtlas (hr : r ≤ 1) (A' : HolderAtlas n M) :
    ∃ C, ∀ u : A.HolderMap k r F, ∃ v : A'.HolderMap k r F, ⇑v = ⇑u ∧ ‖v‖ ≤ C * ‖u‖ := by
  have key : ∀ b : Fin A'.m, ∃ C, ∀ u : A.HolderMap k r F,
      ∃ h : BoundedContDiffHolderMap k r (ComplexModel n) F,
        ⇑h = A'.localRep b u ∧ ‖h‖ ≤ C * ‖u‖ := fun b => by
    obtain ⟨hs, hc, ht⟩ := contDiff_indicator_comp_symm (A'.chart b) (A'.chartSmooth b)
      (A'.isCompact_tsupport b) (A'.tsupport_subset b)
    obtain ⟨C, hC⟩ := exists_smul_comp_symm (A := A) (F := F) hr (A'.chart b)
      (hs.of_le (by exact_mod_cast le_top)) hc ht
    refine ⟨C, fun u => ?_⟩
    obtain ⟨h, hh, hhn⟩ := hC u
    refine ⟨h, funext fun z => ?_, hhn⟩
    rw [hh]
    by_cases hz : z ∈ (A'.chart b).val.target
    · rw [indicator_of_mem hz, localRep_of_mem _ hz]
      rfl
    · rw [indicator_of_notMem hz, zero_smul, localRep_of_notMem _ hz]
  choose C hC using key
  refine ⟨∑ b, C b, fun u => ?_⟩
  choose h hh hhn using fun b => hC b u
  let v : A'.HolderMap k r F := ⟨u, fun b => ⟨h b, hh b⟩⟩
  refine ⟨v, rfl, ?_⟩
  rw [norm_def, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  have hvb : v.rep b = h b := BoundedContDiffHolderMap.ext fun z => by
    rw [coe_rep]
    exact (congrFun (hh b) z).symm
  rw [hvb]
  exact hhn b

/-- The identity `C^{k,r}(M, F)` (atlas `A`) `→ C^{k,r}(M, F)` (atlas `A'`), `r ≤ 1`. -/
def toAtlasFun (hr : r ≤ 1) (A' : HolderAtlas n M) (u : A.HolderMap k r F) :
    A'.HolderMap k r F :=
  ⟨u, fun b => ⟨(((exists_toAtlas hr A').choose_spec u).choose).rep b, by
    rw [coe_rep, ((exists_toAtlas hr A').choose_spec u).choose_spec.1]⟩⟩

@[simp]
theorem coe_toAtlasFun (hr : r ≤ 1) (A' : HolderAtlas n M) (u : A.HolderMap k r F) :
    ⇑(toAtlasFun hr A' u) = u :=
  rfl

/-- The identity map between the Hölder spaces of two Hölder atlases, as a bounded linear map:
`C^{k,r}(M, F)` does not depend on the atlas, up to equivalent norms (`r ≤ 1`). -/
def toAtlas (hr : r ≤ 1) (A' : HolderAtlas n M) : A.HolderMap k r F →L[ℝ] A'.HolderMap k r F :=
  LinearMap.mkContinuous
    { toFun := toAtlasFun hr A'
      map_add' _ _ := ext fun _ => rfl
      map_smul' _ _ := ext fun _ => rfl }
    (exists_toAtlas (A := A) (k := k) (F := F) hr A').choose fun u => by
      have h := ((exists_toAtlas hr A').choose_spec u).choose_spec
      have he : toAtlasFun hr A' u = ((exists_toAtlas hr A').choose_spec u).choose :=
        ext fun y => (congrFun h.1 y).symm
      change ‖toAtlasFun hr A' u‖ ≤ _
      rw [he]
      exact h.2

@[simp]
theorem coe_toAtlas (hr : r ≤ 1) (A' : HolderAtlas n M) (u : A.HolderMap k r F) :
    ⇑(toAtlas hr A' u) = u :=
  rfl

/-! ### Lowering the exponent; compactness -/

/-- The inclusion `C^{k,r}(M, F) → C^{k,s}(M, F)` for `s ≤ r`. -/
def ofLE {s : ℝ≥0} (hsr : s ≤ r) (u : A.HolderMap k r F) : A.HolderMap k s F :=
  ⟨u, fun a => ⟨BoundedContDiffHolderMap.ofLE hsr (u.rep a), by
    rw [BoundedContDiffHolderMap.coe_ofLE, coe_rep]⟩⟩

@[simp]
theorem coe_ofLE {s : ℝ≥0} (hsr : s ≤ r) (u : A.HolderMap k r F) : ⇑(ofLE hsr u) = u :=
  rfl

theorem rep_ofLE {s : ℝ≥0} (hsr : s ≤ r) (u : A.HolderMap k r F) (a : Fin A.m) :
    (ofLE hsr u).rep a = BoundedContDiffHolderMap.ofLE hsr (u.rep a) :=
  BoundedContDiffHolderMap.ext fun _ => rfl

theorem norm_ofLE_le {s : ℝ≥0} (hsr : s ≤ r) (u : A.HolderMap k r F) :
    ‖ofLE hsr u‖ ≤ 3 * ‖u‖ := by
  rw [norm_def, norm_def, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    rw [rep_ofLE]
    exact BoundedContDiffHolderMap.norm_ofLE_le hsr _

/-- The inclusion `C^{k,r}(M, F) →L[ℝ] C^{k,s}(M, F)`, `s ≤ r` (norm `≤ 3`). -/
def ofLECLM {s : ℝ≥0} (hsr : s ≤ r) : A.HolderMap k r F →L[ℝ] A.HolderMap k s F :=
  LinearMap.mkContinuous
    { toFun := ofLE hsr
      map_add' _ _ := ext fun _ => rfl
      map_smul' _ _ := ext fun _ => rfl } 3 (norm_ofLE_le hsr)

@[simp]
theorem ofLECLM_apply {s : ℝ≥0} (hsr : s ≤ r) (u : A.HolderMap k r F) :
    ofLECLM hsr u = ofLE hsr u :=
  rfl

/-- **Compactness** (`s < r ≤ 1`, `F` finite-dimensional): a bounded sequence of `C^{k,r}(M, F)`
has a subsequence converging in `C^{k,s}(M, F)`. -/
theorem exists_subseq_tendsto_ofLE [FiniteDimensional ℝ F] {s : ℝ≥0} (hr : r ≤ 1) (hsr : s < r)
    (u : ℕ → A.HolderMap k r F) {R : ℝ} (hR : ∀ j, ‖u j‖ ≤ R) :
    ∃ U : A.HolderMap k s F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => ofLE hsr.le (u (φ j))) atTop (𝓝 U) := by
  have hfin : ∀ S : Finset (Fin A.m), ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a ∈ S,
      ∃ w : BoundedContDiffHolderMap k s (ComplexModel n) F,
        Tendsto (fun j => BoundedContDiffHolderMap.ofLE hsr.le ((u (φ j)).rep a)) atTop (𝓝 w) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    | insert a S _ ih =>
      obtain ⟨φ, hφ, hS⟩ := ih
      obtain ⟨w, ψ, hψ, hw⟩ := BoundedContDiffHolderMap.exists_subseq_tendsto_ofLE hr hsr
        (isCompact_image_tsupport a) (fun j => (u (φ j)).rep a)
        (fun j z hz => localRep_eq_zero_of_notMem _ hz) (fun j => (norm_rep_le _ a).trans (hR _))
      refine ⟨φ ∘ ψ, hφ.comp hψ, fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact ⟨w, hw⟩
      · obtain ⟨w', hw'⟩ := hS b hb
        exact ⟨w', hw'.comp hψ.tendsto_atTop⟩
  obtain ⟨φ, hφ, hall⟩ := hfin Finset.univ
  choose w hw using fun a => hall a (Finset.mem_univ a)
  obtain ⟨U, hU, -⟩ := exists_tendsto_of_tendsto_rep (u := fun j => ofLE hsr.le (u (φ j)))
    (v := w) fun a => by simpa only [rep_ofLE] using hw a
  exact ⟨U, φ, hφ, hU⟩

/-- **Compact embedding** `C^{k,r}(M, F) ⊂⊂ C^{k,s}(M, F)` for `s < r ≤ 1` and `F`
finite-dimensional. -/
theorem isCompactOperator_ofLE [FiniteDimensional ℝ F] {s : ℝ≥0} (hr : r ≤ 1) (hsr : s < r) :
    IsCompactOperator (ofLE (A := A) (k := k) (F := F) hsr.le) := by
  let T : A.HolderMap k r F → A.HolderMap k s F := ofLE hsr.le
  have hSc : IsCompact (closure (T '' Metric.closedBall 0 1)) := by
    refine IsSeqCompact.isCompact fun y hy => ?_
    have hy' : ∀ j : ℕ, ∃ f ∈ Metric.closedBall (0 : A.HolderMap k r F) 1,
        dist (y j) (T f) < 1 / ((j : ℝ) + 1) := fun j => by
      obtain ⟨b, ⟨f, hf, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 (hy j) (1 / ((j : ℝ) + 1))
        Nat.one_div_pos_of_nat
      exact ⟨f, hf, hb⟩
    choose f hf hfy using hy'
    have hfM : ∀ j, ‖f j‖ ≤ 1 := fun j => mem_closedBall_zero_iff.1 (hf j)
    obtain ⟨g, φ, hφ, hg⟩ := exists_subseq_tendsto_ofLE hr hsr f hfM
    have hmem : ∀ j, T (f (φ j)) ∈ T '' Metric.closedBall 0 1 := fun j =>
      ⟨f (φ j), hf (φ j), rfl⟩
    have hgS : g ∈ closure (T '' Metric.closedBall 0 1) :=
      mem_closure_of_tendsto hg (Eventually.of_forall hmem)
    refine ⟨g, hgS, φ, hφ, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun j => dist (T (f (φ j))) g) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hg
    have h3 : Tendsto (fun j => 1 / ((φ j : ℝ) + 1) + dist (T (f (φ j))) g) atTop (𝓝 0) := by
      have := h1.add h2
      rwa [add_zero] at this
    refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) h3
    exact (dist_triangle _ _ _).trans (add_le_add (hfy (φ j)).le le_rfl)
  exact (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, _, hSc, subset_closure⟩

end HolderMap

end HolderAtlas

end SGPT.Foundations.Analysis.Pending
