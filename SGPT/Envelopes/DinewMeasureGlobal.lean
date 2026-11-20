import SGPT.Envelopes.DinewMeasureLocal
import SGPT.NPP.LogConcavityDinew

/-!
# Dinew's inequality for global non-pluripolar products against a common measure

Xia, *Foundations of pluripotential theory* (FPT), `prop:nonpluripolar-multifactor-common-measure`:
let `T₁, …, Tₙ` be closed positive `(1,1)`-currents on a compact complex manifold `X` of
dimension `n ≥ 1`, `ν` a positive Radon (here: finite) measure and `f₁, …, fₙ ≥ 0` Borel
functions with `⟨Tᵢⁿ⟩ ≥ fᵢ ν`. Then `⟨T₁ ∧ ⋯ ∧ Tₙ⟩ ≥ (∏ᵢ fᵢ^{1/n}) ν`.

`globalMixedMeasure_ge_withDensity_prod` proves this for `Tᵢ = θᵢ + ddᶜwᵢ` (TN's global mixed
non-pluripolar measure `globalMixedMeasure`), **conditional on** the bounded coordinate
inequality `BoundedMultifactorCommonMeasure n` (FPT `thm:bounded-multifactor-common-measure`,
`SGPT.Envelopes.DinewMeasureLocal`). As in FPT, the global statement is local: near every
point, all the measures are push-forwards of coordinate non-pluripolar products of one common
potential patch (TN `globalMixedMeasure_restrict_patch`), the measure `ν` and the densities are
transported to the chart (`map_restrict_withDensity_indicator_apply`), the coordinate inequality
`mixedTruncationLimitMeasure_ge_withDensity_prod` applies, and the local inequalities glue over the
compact manifold (S57's `restrict_le_restrict_of_isLindelof`). No Kähler hypothesis is needed.
In dimension `1` the bounded input holds (`boundedMultifactorCommonMeasure_one`), so the
statement is unconditional there (`globalMixedMeasure_ge_withDensity_prod_one`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

universe u

namespace SGPT.Envelopes.DinewMeasure

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

/-! ### Transport of a measure with density to a chart -/

section Transport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Let `χ : X → Y` and `ψ : Y → X` be measurable with `χ(S) ⊆ D` and `ψ ∘ χ = id` on `S`. Then the
image of `ν|_S` under `χ`, with the transported density `𝟙_D (g ∘ ψ)`, gives a measurable set `t`
the mass that `g ν` gives `S ∩ χ⁻¹ t`. -/
theorem map_restrict_withDensity_indicator_apply (ν : Measure X) {S : Set X} {D : Set Y}
    (hS : MeasurableSet S) (hD : MeasurableSet D) {χ : X → Y} {ψ : Y → X} (hχ : Measurable χ)
    (hψ : Measurable ψ) (hmaps : ∀ y ∈ S, χ y ∈ D ∧ ψ (χ y) = y) {g : X → ℝ≥0∞}
    (hg : Measurable g) {t : Set Y} (ht : MeasurableSet t) :
    ((ν.restrict S).map χ).withDensity (D.indicator (g ∘ ψ)) t =
      ν.withDensity g (S ∩ χ ⁻¹' t) := by
  rw [withDensity_apply _ ht, withDensity_apply _ (hS.inter (hχ ht)),
    Measure.restrict_map hχ ht, lintegral_map ((hg.comp hψ).indicator hD) hχ,
    Measure.restrict_restrict (hχ ht), inter_comm]
  refine setLIntegral_congr_fun (hS.inter (hχ ht)) fun y hy => ?_
  obtain ⟨h1, h2⟩ := hmaps y hy.1
  simp only [indicator_of_mem h1, Function.comp_apply, h2]

end Transport

/-! ### Near a point -/

section Patches

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Dinew's inequality against a common measure near a point** (conditional on
`BoundedMultifactorCommonMeasure n`). -/
theorem exists_nhds_globalMixedMeasure_ge_withDensity_prod
    (hB : BoundedMultifactorCommonMeasure n) (hn : 0 < n)
    (θ : Fin n → ClosedRealOneOneForm n M) (w : Fin n → M → EReal)
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i)) (ν : Measure M) [IsFiniteMeasure ν]
    (f : Fin n → M → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (h : ∀ i, ν.withDensity (f i) ≤
      globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      (ν.withDensity (fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹))).restrict U ≤
        (globalMixedMeasure θ w hw).restrict U := by
  classical
  set e := complexChartAt (n := n) x with he
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  choose W ρ hzW hρ hpsh using fun i => hw i e (e.val x) hz
  let V : Opens (ComplexModel n) :=
    ⟨e.val.target ∩ ⋂ i, W i, e.val.open_target.inter (isOpen_iInter_of_finite fun i => (hρ i).1)⟩
  have hVt : (V : Set (ComplexModel n)) ⊆ e.val.target := fun y hy => hy.1
  have hVW : ∀ i, (V : Set (ComplexModel n)) ⊆ W i := fun i y hy => mem_iInter.mp hy.2 i
  have hzV : e.val x ∈ V := ⟨hz, mem_iInter.mpr hzW⟩
  let Pi : ∀ i, Patch (fun _ : Fin n => θ i) (fun _ => w i) := fun i =>
    { chart := e, domain := V, domain_le_target := hVt, potential := fun _ => ρ i
      localPotential := fun _ => (hρ i).mono V.isOpen (hVW i)
      plurisubharmonic := fun _ => (hpsh i).mono (hVW i) }
  let P : Patch θ w :=
    { chart := e, domain := V, domain_le_target := hVt, potential := ρ
      localPotential := fun i => (hρ i).mono V.isOpen (hVW i)
      plurisubharmonic := fun i => (hpsh i).mono (hVW i) }
  set S : Set M := (P.source : Set M) with hS
  have hSm : MeasurableSet S := P.source.isOpen.measurableSet
  have hVm : MeasurableSet (V : Set (ComplexModel n)) := V.isOpen.measurableSet
  set v : Fin n → ComplexModel n → EReal :=
    fun i y => chartFunction (w i) e y + (ρ i y : EReal) with hvdef
  have hv : ∀ i, PlurisubharmonicOn (v i) V := fun i => (hpsh i).mono (hVW i)
  -- coordinate maps
  set χ : M → ComplexModel n := S.piecewise e.val (fun _ => 0) with hχ
  set ψ : ComplexModel n → M := (V : Set (ComplexModel n)).piecewise e.val.symm (fun _ => x)
    with hψ
  have hχm : Measurable χ :=
    ContinuousOn.measurable_piecewise (e.val.continuousOn.mono P.source_subset)
      continuousOn_const hSm
  have hψm : Measurable ψ :=
    ContinuousOn.measurable_piecewise (e.val.symm.continuousOn.mono hVt) continuousOn_const hVm
  have hχS : ∀ y ∈ S, χ y = e.val y := fun y hy => piecewise_eq_of_mem _ _ _ hy
  have hψV : ∀ z ∈ (V : Set (ComplexModel n)), ψ z = e.val.symm z :=
    fun z hz => piecewise_eq_of_mem _ _ _ hz
  have hmaps : ∀ y ∈ S, χ y ∈ (V : Set (ComplexModel n)) ∧ ψ (χ y) = y := by
    intro y hy
    rw [hχS y hy]
    exact ⟨P.map_source hy, by rw [hψV _ (P.map_source hy)]; exact e.val.left_inv (P.source_subset hy)⟩
  set μ : Measure (ComplexModel n) := (ν.restrict S).map χ with hμdef
  set F : Fin n → ComplexModel n → ℝ≥0∞ := fun i => (V : Set (ComplexModel n)).indicator (f i ∘ ψ)
    with hFdef
  have hFm : ∀ i, Measurable (F i) := fun i => ((hf i).comp hψm).indicator hVm
  have hpre : ∀ t, S ∩ χ ⁻¹' t = e.val.source ∩ e.val ⁻¹' ((V : Set (ComplexModel n)) ∩ t) := by
    intro t
    ext y
    constructor
    · rintro ⟨hyS, hyt⟩
      exact ⟨hyS.1, hyS.2, by rw [← hχS y hyS]; exact hyt⟩
    · rintro ⟨hy1, hy2, hy3⟩
      have hyS : y ∈ S := ⟨hy1, hy2⟩
      exact ⟨hyS, show χ y ∈ t by rw [hχS y hyS]; exact hy3⟩
  -- restrictions of the global measures to the patch
  have hRi : ∀ i, (globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)).restrict S =
      (Pi i).pushMeasure (mixedTruncationLimitMeasure V (fun _ => v i) (fun _ => hv i)) :=
    fun i => globalMixedMeasure_restrict_patch (fun _ : Fin n => hw i) (Pi i)
  have hR : (globalMixedMeasure θ w hw).restrict S =
      P.pushMeasure (mixedTruncationLimitMeasure V v hv) :=
    globalMixedMeasure_restrict_patch hw P
  -- the hypotheses in coordinates
  have hcoord : ∀ i, (μ.withDensity (F i)).restrict V ≤
      mixedTruncationLimitMeasure V (fun _ => v i) (fun _ => hv i) := by
    intro i
    refine Measure.le_iff.mpr fun t ht => ?_
    rw [Measure.restrict_apply ht, hμdef,
      map_restrict_withDensity_indicator_apply ν hSm hVm hχm hψm hmaps (hf i) (ht.inter hVm),
      hpre]
    set A : Set M := e.val.source ∩ e.val ⁻¹' ((V : Set (ComplexModel n)) ∩ (t ∩ V)) with hA
    have hAS : A ⊆ S := fun y hy => ⟨hy.1, hy.2.1⟩
    calc ν.withDensity (f i) A
        ≤ globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i) A := h i A
      _ = (globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)).restrict S A :=
          (Measure.restrict_eq_self _ hAS).symm
      _ = mixedTruncationLimitMeasure V (fun _ => v i) (fun _ => hv i)
            ((V : Set (ComplexModel n)) ∩ ((V : Set (ComplexModel n)) ∩ (t ∩ V))) := by
          rw [hRi i, hA]
          exact SGPT.NPP.LogConcavityDinew.pushMeasure_source_inter_preimage (Pi i) _ _
      _ ≤ mixedTruncationLimitMeasure V (fun _ => v i) (fun _ => hv i) t :=
          measure_mono fun z hz => hz.2.2.1
  have hmain := mixedTruncationLimitMeasure_ge_withDensity_prod hB hn hv μ
    (fun K _ _ => measure_lt_top μ K) F hFm hcoord
  have hdens : (fun z => ∏ i, F i z ^ ((n : ℝ)⁻¹)) = (V : Set (ComplexModel n)).indicator
      ((fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹)) ∘ ψ) :=
    funext fun z => prod_rpow_inv_indicator hn V (fun i => f i ∘ ψ) z
  rw [hdens] at hmain
  have hPm : Measurable (fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹)) :=
    Finset.measurable_prod _ fun i _ => (hf i).pow_const _
  refine ⟨S, P.source.isOpen, ⟨hx, hzV⟩, ?_⟩
  rw [hR]
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.restrict_apply hs, Patch.pushMeasure_apply]
  set t : Set (ComplexModel n) := (V : Set (ComplexModel n)) ∩ ψ ⁻¹' s with ht
  have htm : MeasurableSet t := hVm.inter (hψm hs)
  have hst : s ∩ S = S ∩ χ ⁻¹' t := by
    ext y
    constructor
    · rintro ⟨hys, hyS⟩
      obtain ⟨h1, h2⟩ := hmaps y hyS
      exact ⟨hyS, h1, show ψ (χ y) ∈ s by rw [h2]; exact hys⟩
    · rintro ⟨hyS, hyt⟩
      obtain ⟨-, h2⟩ := hmaps y hyS
      have : ψ (χ y) ∈ s := hyt.2
      rw [h2] at this
      exact ⟨this, hyS⟩
  have htV : t = (P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' s := by
    ext z
    constructor
    · rintro ⟨hzV, hzs⟩
      exact ⟨hzV, show e.val.symm z ∈ s by rw [← hψV z hzV]; exact hzs⟩
    · rintro ⟨hzV, hzs⟩
      exact ⟨hzV, show ψ z ∈ s by rw [hψV z hzV]; exact hzs⟩
  calc ν.withDensity (fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹)) (s ∩ S)
      = (μ.withDensity ((V : Set (ComplexModel n)).indicator
          ((fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹)) ∘ ψ))) t := by
        rw [hst, hμdef, map_restrict_withDensity_indicator_apply ν hSm hVm hχm hψm hmaps hPm htm]
    _ = ((μ.withDensity ((V : Set (ComplexModel n)).indicator
          ((fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹)) ∘ ψ))).restrict V) t :=
        (Measure.restrict_eq_self _ inter_subset_left).symm
    _ ≤ mixedTruncationLimitMeasure V v hv t := hmain t
    _ = _ := by rw [htV]

end Patches

/-! ### The global inequality -/

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Dinew's inequality for non-pluripolar products against a common measure** (Xia,
*Foundations of pluripotential theory*, `prop:nonpluripolar-multifactor-common-measure`,
conditional on its bounded coordinate case `BoundedMultifactorCommonMeasure n`): on a compact
complex manifold of dimension `n ≥ 1`, for closed real `(1,1)`-forms `θᵢ`, `θᵢ`-psh `wᵢ`, a finite
measure `ν` and measurable `fᵢ ≥ 0` with `⟨(θᵢ + ddᶜwᵢ)ⁿ⟩ ≥ fᵢ ν`,
`⟨(θ₁ + ddᶜw₁) ∧ ⋯ ∧ (θₙ + ddᶜwₙ)⟩ ≥ (∏ᵢ fᵢ^{1/n}) ν`. -/
theorem globalMixedMeasure_ge_withDensity_prod (hB : BoundedMultifactorCommonMeasure n)
    (hn : 0 < n) (θ : Fin n → ClosedRealOneOneForm n M) (w : Fin n → M → EReal)
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i)) (ν : Measure M) [IsFiniteMeasure ν]
    (f : Fin n → M → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (h : ∀ i, ν.withDensity (f i) ≤
      globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)) :
    ν.withDensity (fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹)) ≤ globalMixedMeasure θ w hw := by
  have hglue := SGPT.NPP.LogConcavityDinew.restrict_le_restrict_of_isLindelof
    (μ := ν.withDensity (fun y => ∏ i, f i y ^ ((n : ℝ)⁻¹))) (ν := globalMixedMeasure θ w hw)
    isCompact_univ.isLindelof
    (fun x _ => exists_nhds_globalMixedMeasure_ge_withDensity_prod hB hn θ w hw ν f hf h x)
  rwa [Measure.restrict_univ, Measure.restrict_univ] at hglue

/-- **Dinew's inequality against a common measure in dimension `1`** (unconditional): FPT
`prop:nonpluripolar-multifactor-common-measure` for `n = 1`. -/
theorem globalMixedMeasure_ge_withDensity_prod_one {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] (θ : Fin 1 → ClosedRealOneOneForm 1 M) (w : Fin 1 → M → EReal)
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i)) (ν : Measure M) [IsFiniteMeasure ν]
    (f : Fin 1 → M → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (h : ∀ i, ν.withDensity (f i) ≤
      globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)) :
    ν.withDensity (fun y => ∏ i, f i y ^ (((1 : ℕ) : ℝ)⁻¹)) ≤ globalMixedMeasure θ w hw :=
  globalMixedMeasure_ge_withDensity_prod boundedMultifactorCommonMeasure_one one_pos θ w hw ν f
    hf h

end SGPT.Envelopes.DinewMeasure
