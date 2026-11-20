import SGPT.Bergman.SourceTwistedMultiplierSections
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!+# Native section multiplication for the Bertini quotient

Source: `chapter_trace.tex`, proof of `thm:Bert`, Steps 1.2--1.3.
The tensor factors and multiplier-ideal sections below are the original bundles
and full original section spaces. No chosen finite spanning family is assumed.
Identifying the quotient with sections of the hypersurface additionally requires
the exact restriction sequence and its cohomology vanishing.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (E P : HermitianHolomorphicLineBundle n X)

/-- Pointwise tensoring of two genuine holomorphic sections is holomorphic in
the native tensor bundle, as proved in its actual tensor atlas. -/
def nativeTensorSection (s : HolomorphicSections (n := n) E.Fiber)
    (t : HolomorphicSections (n := n) P.Fiber) :
    HolomorphicSections (n := n) (tensor E P).Fiber where
  toFun x := s x ⊗ₜ[ℂ] t x
  contMDiff_toFun := by
    intro x
    let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
    let f : AtlasFrame P := ⟨trivializationAt ℂ P.Fiber x, inferInstance⟩
    let := e.property
    let := f.property
    let q := tensorAtlasFrame e f
    let := q.property
    have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
    have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ P.Fiber x
    apply (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨he, hf⟩)).mpr
    have hs := (e.val.contMDiffAt_section_iff he).mp (s.contMDiff x)
    have ht := (f.val.contMDiffAt_section_iff hf).mp (t.contMDiff x)
    apply (hs.mul ht).congr_of_eventuallyEq
    filter_upwards [e.val.open_baseSet.mem_nhds he, f.val.open_baseSet.mem_nhds hf] with y hyE hyP
    change tensorCoordinate E.Fiber P.Fiber e.val f.val y (s y ⊗ₜ[ℂ] t y) = _
    rw [tensorCoordinate_tmul, Trivialization.coe_linearMapAt_of_mem e.val hyE,
      Trivialization.coe_linearMapAt_of_mem f.val hyP]
    rfl

/-- Exact original-coordinate multiplication, on the whole native tensor atlas. -/
theorem nativeTensorSection_coefficient (e : AtlasFrame E) (f : AtlasFrame P)
    (s : HolomorphicSections (n := n) E.Fiber)
    (t : HolomorphicSections (n := n) P.Fiber) (x : X)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) :
    sectionCoefficient (tensor E P).Fiber (tensorAtlasFrame e f).val
        (nativeTensorSection E P s t) x =
      sectionCoefficient E.Fiber e.val s x * sectionCoefficient P.Fiber f.val t x := by
  let := e.property
  let := f.property
  change tensorCoordinate E.Fiber P.Fiber e.val f.val x (s x ⊗ₜ[ℂ] t x) = _
  rw [tensorCoordinate_tmul, Trivialization.coe_linearMapAt_of_mem e.val he,
    Trivialization.coe_linearMapAt_of_mem f.val hf]
  rfl

/-- The actual multiplier-ideal subspace of all native holomorphic sections. -/
abbrev nativeMultiplierSections (φ : X → EReal) :=
  ↥(fullHolomorphicIdealSections (n := n) E.Fiber (sourceDegreeMultiplierIdeal 1 φ))

/-- Genuine holomorphic tensor multiplication preserves the original multiplier
ideal: its coordinate is a holomorphic multiple of the original coefficient. -/
theorem nativeTensorSection_mem_multiplier {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (s : nativeMultiplierSections E φ) (t : HolomorphicSections (n := n) P.Fiber) :
    nativeTensorSection E P s.val t ∈
      fullHolomorphicIdealSections (n := n) (tensor E P).Fiber (sourceDegreeMultiplierIdeal 1 φ) := by
  let A := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hA : A.IsCoherent := sourceDegreeMultiplierIdeal_isCoherent 1 hφ
  change globalSectionSheafEquiv (n := n) (tensor E P).Fiber
    (nativeTensorSection E P s.val t) ∈
      idealOpenSectionSubmodule (n := n) (tensor E P).Fiber A ⊤
  intro g x hxg
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x.val, inferInstance⟩
  let f : AtlasFrame P := ⟨trivializationAt ℂ P.Fiber x.val, inferInstance⟩
  let q : OriginalFrame (tensor E P).Fiber := tensorAtlasFrame e f
  have he : x.val ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x.val
  have hf : x.val ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ P.Fiber x.val
  have hxq : x.val ∈ q.val.baseSet := ⟨he, hf⟩
  apply (localFrameCoefficientGerm_mem_iff (n := n) (tensor E P).Fiber A ⊤ g q
    (globalSectionSheafEquiv (n := n) (tensor E P).Fiber (nativeTensorSection E P s.val t))
    x hxg hxq).mpr
  apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n)
    (tensor E P).Fiber A hA q (nativeTensorSection E P s.val t) hxq).mpr
  have hs := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n)
    E.Fiber A hA e s.val he).mp (s.property e x he)
  have ht := originalSectionCoefficient_holomorphicAt (n := n) P.Fiber f t hf
  have hp := SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul ht hs
  apply SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison.mem_multiplierIdeal_congr hp
  filter_upwards [e.val.open_baseSet.mem_nhds he, f.val.open_baseSet.mem_nhds hf] with y hyE hyP
  rw [nativeTensorSection_coefficient E P e f s.val t y hyE hyP]
  exact mul_comm _ _

/-- The actual multiplication map occurring in `V/(s_H V')`. -/
def nativeMultiplierSectionMap {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber) :
    nativeMultiplierSections E φ →ₗ[ℂ] nativeMultiplierSections (tensor E P) φ where
  toFun s := ⟨nativeTensorSection E P s.val t, nativeTensorSection_mem_multiplier E P hφ s t⟩
  map_add' s u := by
    apply Subtype.ext
    apply ContMDiffSection.ext
    intro x
    exact TensorProduct.add_tmul _ _ _
  map_smul' a s := by
    apply Subtype.ext
    apply ContMDiffSection.ext
    intro x
    exact TensorProduct.smul_tmul' _ _ _

/-- Compactness supplies finite dimension of the full native ideal section
space; this is inherited from all holomorphic sections, not assumed. -/
theorem nativeMultiplierSections_finiteDimensional [CompactSpace X] (φ : X → EReal) :
    FiniteDimensional ℂ (nativeMultiplierSections E φ) := by
  have := holomorphicSections_finiteDimensional (n := n) E.Fiber
  infer_instance

/-- The literal native quotient has finite rank for every actual defining section. -/
theorem nativeMultiplierQuotient_finiteDimensional [CompactSpace X]
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber) :
    FiniteDimensional ℂ
      ((nativeMultiplierSections (tensor E P) φ) ⧸ (nativeMultiplierSectionMap E P hφ t).range) := by
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  infer_instance

/-- A nonzero original defining section is a non-zero-divisor on ALL native
holomorphic sections. Connectedness is the actual geometric input. -/
theorem nativeTensorSection_eq_zero_iff [ConnectedSpace X]
    (s : HolomorphicSections (n := n) E.Fiber)
    (t : HolomorphicSections (n := n) P.Fiber) (ht : t ≠ 0) :
    nativeTensorSection E P s t = 0 ↔ s = 0 := by
  constructor
  · intro hst
    by_contra hs
    have hZ := sectionZeroSet_isComplexAnalytic E.Fiber s
    have hI := SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
      hZ (sectionZeroSet_ne_univ E.Fiber s hs)
    have hU : IsOpen {x : X | t x ≠ 0} := by
      have hc : Continuous (fun x : X => ‖t x‖) := (sectionNormMap P.Fiber t).continuous
      have heq : {x : X | t x ≠ 0} = {x : X | ‖t x‖ ≠ (0 : ℝ)} := by
        ext x
        exact norm_ne_zero_iff.symm
      rw [heq]
      exact isOpen_ne_fun hc continuous_const
    have hne : {x : X | t x ≠ 0}.Nonempty := by
      by_contra h
      apply ht
      apply ContMDiffSection.ext
      intro x
      have hz : ∀ x : X, t x = 0 := by
        simpa only [Set.nonempty_def, Set.mem_ofPred_eq, not_exists, not_not] using h
      exact hz x
    have hsub : {x : X | t x ≠ 0} ⊆ sectionZeroSet E.Fiber s := by
      intro x htx
      have hzero : s x ⊗ₜ[ℂ] t x = 0 := congrArg (fun u => u x) hst
      have hp : ‖s x‖ * ‖t x‖ = 0 := by
        rw [← TensorProduct.norm_tmul (𝕜 := ℂ), hzero, norm_zero]
      exact norm_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (norm_ne_zero_iff.mpr htx))
    have := hU.subset_interior_iff.mpr hsub
    rw [hI] at this
    exact hne.not_subset_empty this
  · rintro rfl
    apply ContMDiffSection.ext
    intro x
    exact TensorProduct.zero_tmul _ _

/-- Injectivity of the literal multiplier-section map is PRODUCED from a
nonzero native defining section; no abstract injectivity certificate is used. -/
theorem nativeMultiplierSectionMap_injective [ConnectedSpace X]
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber) (ht : t ≠ 0) :
    Function.Injective (nativeMultiplierSectionMap E P hφ t) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro s hs
  apply Subtype.ext
  exact (nativeTensorSection_eq_zero_iff E P s.val t ht).mp (congrArg Subtype.val hs)

/-- Exact finite rank of the native quotient, with the actual source section
space as kernel-image dimension. -/
theorem nativeMultiplierQuotient_finrank [CompactSpace X] [ConnectedSpace X]
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber) (ht : t ≠ 0) :
    Module.finrank ℂ
        ((nativeMultiplierSections (tensor E P) φ) ⧸ (nativeMultiplierSectionMap E P hφ t).range) +
      Module.finrank ℂ (nativeMultiplierSections E φ) =
      Module.finrank ℂ (nativeMultiplierSections (tensor E P) φ) := by
  have := nativeMultiplierSections_finiteDimensional E φ
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  rw [← LinearMap.finrank_range_of_inj (nativeMultiplierSectionMap_injective E P hφ t ht)]
  exact Submodule.finrank_quotient_add_finrank _

/-- The same multiplication on literal global sections of the original sheaf
tensor products, through the already proved BOTH-direction section dictionary. -/
def literalMultiplierSectionMap {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber) :
    TensorIdealGlobalSections (n := n) E.Fiber (sourceDegreeMultiplierIdeal 1 φ) →ₗ[ℂ]
      TensorIdealGlobalSections (n := n) (tensor E P).Fiber (sourceDegreeMultiplierIdeal 1 φ) :=
  (tensorIdealGlobalSectionEquiv (n := n) (tensor E P).Fiber
      (sourceDegreeMultiplierIdeal 1 φ)).symm.toLinearMap.comp
    ((nativeMultiplierSectionMap E P hφ t).comp
      (tensorIdealGlobalSectionEquiv (n := n) E.Fiber
        (sourceDegreeMultiplierIdeal 1 φ)).toLinearMap)

/-- Exact original-fibre formula for multiplication on the LITERAL H0 spaces. -/
theorem literalMultiplierSectionMap_apply {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber)
    (s : TensorIdealGlobalSections (n := n) E.Fiber (sourceDegreeMultiplierIdeal 1 φ))
    (x : X) :
    (tensorIdealGlobalSectionEquiv (n := n) (tensor E P).Fiber
        (sourceDegreeMultiplierIdeal 1 φ) (literalMultiplierSectionMap E P hφ t s)).val x =
      (tensorIdealGlobalSectionEquiv (n := n) E.Fiber
        (sourceDegreeMultiplierIdeal 1 φ) s).val x ⊗ₜ[ℂ] t x := by
  change (tensorIdealGlobalSectionEquiv (n := n) (tensor E P).Fiber
    (sourceDegreeMultiplierIdeal 1 φ)
      ((tensorIdealGlobalSectionEquiv (n := n) (tensor E P).Fiber
        (sourceDegreeMultiplierIdeal 1 φ)).symm _)).val x = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The literal original H0 multiplication is injective by the actual native
non-zero-divisor proof, not by a sheaf or cohomology certificate. -/
theorem literalMultiplierSectionMap_injective [ConnectedSpace X]
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (t : HolomorphicSections (n := n) P.Fiber) (ht : t ≠ 0) :
    Function.Injective (literalMultiplierSectionMap E P hφ t) :=
  (tensorIdealGlobalSectionEquiv (n := n) (tensor E P).Fiber
    (sourceDegreeMultiplierIdeal 1 φ)).symm.injective.comp
      ((nativeMultiplierSectionMap_injective E P hφ t ht).comp
        (tensorIdealGlobalSectionEquiv (n := n) E.Fiber
          (sourceDegreeMultiplierIdeal 1 φ)).injective)

end SGPT.Trace.Bertini
