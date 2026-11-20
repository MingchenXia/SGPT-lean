import SGPT.Trace.CohFibreIdeal
import SGPT.Trace.CohInvariance
import SGPT.Trace.DirectImgABT
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierCoherence
import Mathlib.Analysis.Real.Cardinality

/-!
# The reverse Bertini theorem (`lma:fibIeq`): reduction to the almost-everywhere reverse inclusion

Source: `chapter_trace.tex`, `lma:fibIeq` (lines 1166--1193); blueprint `claude-coherent.tex`.

This file assembles the proof of `lma:fibIeq` from

* the rigidity of invariant coherent ideals (`SGPT.GAGA.Coherent.eq_of_dense_sup_eq`),
* the invariance of the multiplier ideals of invariant metrics
  (`isInvariantIdeal_multiplierIdeal`),
* the Ohsawa–Takegoshi inclusion on smooth fibres
  (`SGPT.Trace.DirectImg.fibre_multiplier_le_restStalk`),
* the Lebesgue-almost-everywhere reverse inclusion `Rest_{X_z} 𝓘(cφ) ⊆ 𝓘(cφ|_{X_z})`
  (`AEReverseInclusion`, Fubini; `CohFubini`),

via `lma_fibIeq_of_ae`: for a dense set of `z` the restrictions of `𝓘(kφ)` and `𝓘(kφ')` to
`X_z` agree, and rigidity gives `𝓘(kφ) = 𝓘(kφ')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Trace.CohFib

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi SGPT.GAGA.Coherent
  SGPT.Trace.DirectImg SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The almost-everywhere reverse inclusion** for `f : X → Δ*`, the weight `φ` and the level
`c`: for Lebesgue-almost every `z ∈ Δ*` (in the coordinate of `ℂ¹`), at every point of every
smooth structure on the fibre `X_z`, `Rest_{X_z} 𝓘(cφ) ⊆ 𝓘(cφ|_{X_z})`. -/
def AEReverseInclusion (f : X → puncturedDisc) (hf : Continuous f) (φ : X → EReal) (c : ℝ) :
    Prop :=
  volume {w : ComplexModel 1 | ∃ hw : w ∈ puncturedDisc, ¬ ∀ (k : ℕ) (hk : k ≤ n)
    (hsm : IsSmoothFibreOfDim n 1 f ⟨w, hw⟩ k), FibreReverseInclusion hf hk hsm φ c} = 0

/-- A pluripolar subset of `Δ*` is Lebesgue-null in `ℂ¹`. -/
theorem volume_image_val_eq_zero_of_locallyPluripolar {S : Set puncturedDisc}
    (hS : (SGPT.PSH.VariableComplexAtlas.ofFixedModel 1 puncturedDisc).LocallyPluripolar S)
    (z₀ : puncturedDisc) :
    volume ((Subtype.val : puncturedDisc → ComplexModel 1) '' S) = 0 := by
  have h0 := hS.chart_volume_eq_zero (complexChartAt (n := 1) z₀)
  refine measure_mono_null ?_ h0
  rintro _ ⟨w, hw, rfl⟩
  have hsrc := mem_chartAt_puncturedDisc_source z₀ w
  refine ⟨?_, ?_⟩
  · have := (chartAt (ComplexModel 1) z₀).map_source hsrc
    rwa [chartAt_puncturedDisc_apply] at this
  · show (chartAt (ComplexModel 1) z₀).symm (w : ComplexModel 1) ∈ S
    rw [← chartAt_puncturedDisc_apply z₀ w, (chartAt (ComplexModel 1) z₀).left_inv hsrc]
    exact hw

/-- A subset of `Δ*` whose complement is Lebesgue-null in `ℂ¹` is dense. -/
theorem dense_of_volume_compl {G : Set puncturedDisc}
    (hG : volume ((Subtype.val : puncturedDisc → ComplexModel 1) '' Gᶜ) = 0) : Dense G := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : V ⊆ Gᶜ := fun v hv hvG => (eq_empty_iff_forall_notMem.1 hne) v ⟨hv, hvG⟩
  have hopen : IsOpen ((Subtype.val : puncturedDisc → ComplexModel 1) '' V) :=
    puncturedDisc.isOpen.isOpenMap_subtype_val V hV
  have hpos := hopen.measure_ne_zero volume (hVne.image _)
  exact hpos (measure_mono_null (image_mono hsub) hG)

/-- A complex manifold of dimension `0` is countable, so it has no surjection onto `Δ*`. -/
theorem pos_of_surjective {f : X → puncturedDisc} (hsurj : Function.Surjective f) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exfalso
    have hdisc : DiscreteTopology X := by
      refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
      have hsrc : (chartAt (ComplexModel 0) x).source = {x} := by
        refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_chart_source _ x, fun y hy => ?_⟩
        exact (chartAt (ComplexModel 0) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
      rw [← hsrc]
      exact (chartAt (ComplexModel 0) x).open_source
    have hcount : Countable X := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    have hcd : Countable puncturedDisc := hsurj.countable
    -- the segment `r ↦ r e₀`, `r ∈ (0, 1)`, is uncountable
    set ι : Ioo (0 : ℝ) 1 → puncturedDisc := fun r => ⟨lineEmb (r : ℂ), by
      rw [mem_puncturedDisc, norm_complexModel_one]
      have : (lineEmb (r : ℂ)) 0 = (r : ℂ) := by simp [lineEmb]
      rw [this, Complex.norm_real, Real.norm_of_nonneg r.2.1.le]
      exact ⟨r.2.1, r.2.2⟩⟩ with hι
    have hinj : Function.Injective ι := by
      intro r s hrs
      have h1 := congrArg (fun z : puncturedDisc => (z : ComplexModel 1) 0) hrs
      simp only [hι, lineEmb] at h1
      simp at h1
      exact Subtype.ext h1
    have : Countable (Ioo (0 : ℝ) 1) := hinj.countable
    have h2 := Cardinal.Real.Ioo_countable_iff.1 (Set.countable_coe_iff.1 this)
    norm_num at h2
  · exact hn

/-- A point of `Δ*`. -/
def halfPoint : puncturedDisc :=
  ⟨lineEmb ((1 / 2 : ℝ) : ℂ), by
    rw [mem_puncturedDisc, norm_complexModel_one]
    have : (lineEmb (((1 / 2 : ℝ)) : ℂ)) 0 = ((1 / 2 : ℝ) : ℂ) := by simp [lineEmb]
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    norm_num⟩

section Main

variable {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
  [VectorBundle ℂ ℂ L] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- The fibre hypothesis of `lma:fibIeq` at `z`: the fibre `X_z` is smooth and
`h|_{X_z} ∼_I h'|_{X_z}`, i.e. `𝓘(k φ|_{X_z}) = 𝓘(k φ'|_{X_z})` on the complex manifold `X_z`
for every integer `k ≥ 1`, for the potentials `φ, φ'` of presentations `h = h₀ e^{-φ}`,
`h' = h₀' e^{-φ'}` (`h|_{X_z} = h₀|_{X_z} e^{-φ|_{X_z}}`). -/
def FibreIEquivalent (f : X → puncturedDisc) (φ φ' : X → EReal) (z : puncturedDisc) : Prop :=
  ∃ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n 1 f z k),
    letI := chartedSpace hk hsm.1
    ∀ m : ℕ, 0 < m → multiplierIdeal (n := k) (m : ℝ) (fun q : fibre f z => φ q.1) =
      multiplierIdeal (n := k) (m : ℝ) (fun q : fibre f z => φ' q.1)

/-- **`lma:fibIeq` from the almost-everywhere reverse inclusion.** -/
theorem lma_fibIeq_of_ae {f : X → puncturedDisc} (hf : IsProjectiveMorphism n 1 f)
    (hsurj : Function.Surjective f) (h h' : HermitianPseudoeffective n L)
    (σ : CircleAction n X) (τ : CircleActionLift σ L) (hequiv : IsRotationEquivariant σ f)
    (hinv : IsInvariantMetric τ h.metric) (hinv' : IsInvariantMetric τ h'.metric)
    {h₀ h₀' : HermitianMetric (n := n) L} {φ φ' : X → EReal}
    (hφ : IsPSHMetricWith h.metric h₀ φ) (hφ' : IsPSHMetricWith h'.metric h₀' φ')
    (hfib : (SGPT.PSH.VariableComplexAtlas.ofFixedModel 1 puncturedDisc).CoPluripolar
      {z | FibreIEquivalent (n := n) f φ φ' z})
    (hae : ∀ m : ℕ, 0 < m → AEReverseInclusion (n := n) f hf.1.continuous φ m)
    (hae' : ∀ m : ℕ, 0 < m → AEReverseInclusion (n := n) f hf.1.continuous φ' m)
    (m : ℕ) (hm : 0 < m) :
    multiplierIdeal (n := n) (m : ℝ) φ = multiplierIdeal (n := n) (m : ℝ) φ' := by
  have hn := pos_of_surjective (n := n) hsurj
  have hc : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hq := manifoldQuasiPlurisubharmonic_of_isPSHMetricWith hφ
  have hq' := manifoldQuasiPlurisubharmonic_of_isPSHMetricWith hφ'
  have hI := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    hn hq hc
  have hI' :=
    GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    hn hq' hc
  have hinvI := isInvariantIdeal_multiplierIdeal τ hφ hinv (m : ℝ)
  have hinvI' := isInvariantIdeal_multiplierIdeal τ hφ' hinv' (m : ℝ)
  set G : Set puncturedDisc := {z | FibreIEquivalent (n := n) f φ φ' z} ∩
    {z | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n 1 f z k),
      FibreReverseInclusion hf.1.continuous hk hsm φ m} ∩
    {z | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n 1 f z k),
      FibreReverseInclusion hf.1.continuous hk hsm φ' m} with hGdef
  have hGc : volume ((Subtype.val : puncturedDisc → ComplexModel 1) '' Gᶜ) = 0 := by
    have hsub : (Subtype.val : puncturedDisc → ComplexModel 1) '' Gᶜ ⊆
        (Subtype.val '' {z | FibreIEquivalent (n := n) f φ φ' z}ᶜ) ∪
        ({w : ComplexModel 1 | ∃ hw : w ∈ puncturedDisc, ¬ ∀ (k : ℕ) (hk : k ≤ n)
          (hsm : IsSmoothFibreOfDim n 1 f ⟨w, hw⟩ k),
          FibreReverseInclusion hf.1.continuous hk hsm φ m} ∪
        {w : ComplexModel 1 | ∃ hw : w ∈ puncturedDisc, ¬ ∀ (k : ℕ) (hk : k ≤ n)
          (hsm : IsSmoothFibreOfDim n 1 f ⟨w, hw⟩ k),
          FibreReverseInclusion hf.1.continuous hk hsm φ' m}) := by
      rintro _ ⟨z, hz, rfl⟩
      simp only [hGdef, compl_inter, mem_union, mem_compl_iff, Set.mem_ofPred_eq] at hz
      rcases hz with (hz | hz) | hz
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact Or.inr (Or.inl ⟨z.2, hz⟩)
      · exact Or.inr (Or.inr ⟨z.2, hz⟩)
    refine measure_mono_null hsub (measure_union_null
      (volume_image_val_eq_zero_of_locallyPluripolar hfib halfPoint)
      (measure_union_null (hae m hm) (hae' m hm)))
  have hG : Dense G := dense_of_volume_compl hGc
  refine eq_of_dense_sup_eq σ hf.1 hf.isProperMap hequiv hI hI' hinvI hinvI' hG ?_
  intro y hyG
  obtain ⟨⟨hfibz, hrev⟩, hrev'⟩ := hyG
  obtain ⟨k, hk, hsm, heq⟩ := hfibz
  have hrest : restStalk (multiplierIdeal (n := n) (m : ℝ) φ)
      (submanifoldSubspace (hsm.isClosedSubmanifold f hf.1.continuous)) y =
      restStalk (multiplierIdeal (n := n) (m : ℝ) φ')
        (submanifoldSubspace (hsm.isClosedSubmanifold f hf.1.continuous)) y := by
    let q : fibre f (f y) := ⟨y, rfl⟩
    have h1 := hrev k hk hsm q
    have h1' := hrev' k hk hsm q
    have h2 := fibre_multiplier_le_restStalk hf.1.continuous hk hsm hq (m : ℝ) q
    have h2' := fibre_multiplier_le_restStalk hf.1.continuous hk hsm hq' (m : ℝ) q
    have heqF := heq m hm
    rw [heqF] at h1 h2
    exact le_antisymm (h1.trans h2') (h1'.trans h2)
  exact sup_span_eq_of_restStalk_eq hf.1 hsm rfl hrest

end Main

end SGPT.Trace.CohFib
