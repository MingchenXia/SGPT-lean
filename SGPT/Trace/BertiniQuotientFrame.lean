import SGPT.Trace.BertiniSectionMultiplication
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!+# A fixed complement for the original Bertini quotient

The original finite-dimensional spaces are the full multiplier-ideal sections
of `E` and `E ⊗ P`. At every nonzero original section `t₀` of `P`, a SINGLE
subspace of original global sections maps isomorphically to every quotient
`V/(t V')` for `t` near `t₀`. The neighborhood is produced by openness of
invertibility. No quotient frame, rank constancy or complement is assumed.

This is the finite-section part of `thm:Bert`, proof Steps 1.2--1.3. The
adjunction/restriction-sequence identification with the fibre H0 is separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X]
  (E P : HermitianHolomorphicLineBundle n X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)

/-- Actual section multiplication plus inclusion of the fixed complement. -/
def nativeSectionSplitMap (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ))
    (t : HolomorphicSections (n := n) P.Fiber) :
    (nativeMultiplierSections E φ × C) →L[ℂ] nativeMultiplierSections (tensor E P) φ := by
  let := nativeMultiplierSections_finiteDimensional E φ
  let := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  exact ((nativeMultiplierSectionMap E P hφ t).coprod C.subtype).toContinuousLinearMap

/-- The actual operator varies continuously with the original defining
holomorphic section, in the native compact section norm. -/
theorem continuous_nativeSectionSplitMap
    (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ)) :
    Continuous (nativeSectionSplitMap E P hφ C) := by
  have := nativeMultiplierSections_finiteDimensional E φ
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  have := holomorphicSections_finiteDimensional (n := n) P.Fiber
  let : NormedAddCommGroup ((nativeMultiplierSections E φ × C) →L[ℂ]
      nativeMultiplierSections (tensor E P) φ) := ContinuousLinearMap.toNormedAddCommGroup
  let A : HolomorphicSections (n := n) P.Fiber →ₗ[ℂ]
      ((nativeMultiplierSections E φ × C) →L[ℂ] nativeMultiplierSections (tensor E P) φ) := {
    toFun t := ((nativeMultiplierSectionMap E P hφ t).comp
      (LinearMap.fst ℂ (nativeMultiplierSections E φ) C)).toContinuousLinearMap
    map_add' t u := by
      apply ContinuousLinearMap.ext
      intro s
      apply Subtype.ext
      apply ContMDiffSection.ext
      intro x
      change s.1.val x ⊗ₜ[ℂ] (t x + u x) =
        s.1.val x ⊗ₜ[ℂ] t x + s.1.val x ⊗ₜ[ℂ] u x
      exact TensorProduct.tmul_add _ _ _
    map_smul' a t := by
      apply ContinuousLinearMap.ext
      intro s
      apply Subtype.ext
      apply ContMDiffSection.ext
      intro x
      change s.1.val x ⊗ₜ[ℂ] (a • t x) = a • (s.1.val x ⊗ₜ[ℂ] t x)
      exact TensorProduct.tmul_smul _ _ _ }
  let B : (nativeMultiplierSections E φ × C) →L[ℂ] nativeMultiplierSections (tensor E P) φ :=
    (C.subtype.comp (LinearMap.snd ℂ (nativeMultiplierSections E φ) C)).toContinuousLinearMap
  have heq : nativeSectionSplitMap E P hφ C = fun t => A t + B := by
    funext t
    apply ContinuousLinearMap.ext
    intro s
    rfl
  have hA : Continuous (fun t : HolomorphicSections (n := n) P.Fiber => A t) :=
    (A.toContinuousLinearMap).continuous
  rw [heq]
  exact Continuous.add (f := fun t : HolomorphicSections (n := n) P.Fiber => A t)
    (g := fun _ : HolomorphicSections (n := n) P.Fiber => B)
    hA continuous_const

/-- One fixed subspace of original global sections complements all actual
defining-section images in a produced open neighborhood. -/
theorem exists_nativeMultiplier_fixedComplement [ConnectedSpace X]
    (t₀ : HolomorphicSections (n := n) P.Fiber) (ht₀ : t₀ ≠ 0) :
    ∃ C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ),
      ∃ U : Set (HolomorphicSections (n := n) P.Fiber),
        IsOpen U ∧ t₀ ∈ U ∧
        ∀ t ∈ U, IsCompl (nativeMultiplierSectionMap E P hφ t).range C := by
  classical
  have := nativeMultiplierSections_finiteDimensional E φ
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  let M₀ := nativeMultiplierSectionMap E P hφ t₀
  obtain ⟨C, hC⟩ := M₀.range.exists_isCompl
  let e₀ : (nativeMultiplierSections E φ × C) ≃ₗ[ℂ]
      nativeMultiplierSections (tensor E P) φ :=
    (LinearEquiv.prodCongr
      (LinearEquiv.ofInjective M₀ (nativeMultiplierSectionMap_injective E P hφ t₀ ht₀))
      (LinearEquiv.refl ℂ C)).trans (M₀.range.prodEquivOfIsCompl C hC)
  let e₀L := e₀.toContinuousLinearEquiv
  have he₀ : (e₀L : (nativeMultiplierSections E φ × C) →L[ℂ]
      nativeMultiplierSections (tensor E P) φ) = nativeSectionSplitMap E P hφ C t₀ := by
    apply ContinuousLinearMap.ext
    intro s
    rfl
  let U := (nativeSectionSplitMap E P hφ C) ⁻¹'
    Set.range ((↑) : ((nativeMultiplierSections E φ × C) ≃L[ℂ]
      nativeMultiplierSections (tensor E P) φ) → _)
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage
    (continuous_nativeSectionSplitMap E P hφ C)
  have htU : t₀ ∈ U := ⟨e₀L, he₀⟩
  refine ⟨C, U, hU, htU, ?_⟩
  intro t ht
  obtain ⟨e, he⟩ := ht
  have hb : Function.Bijective (nativeSectionSplitMap E P hφ C t) := by
    rw [← he]
    exact e.bijective
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro v hvR hvC
    obtain ⟨u, hu⟩ := hvR
    have hp : nativeSectionSplitMap E P hφ C t (u, 0) =
        nativeSectionSplitMap E P hφ C t (0, ⟨v, hvC⟩) := by
      change nativeMultiplierSectionMap E P hφ t u + (0 : nativeMultiplierSections (tensor E P) φ) =
        nativeMultiplierSectionMap E P hφ t 0 + v
      simpa using hu
    have hz := congrArg (fun p => (p.2 : nativeMultiplierSections (tensor E P) φ)) (hb.1 hp)
    exact hz.symm
  · apply Submodule.eq_top_iff'.mpr
    intro v
    obtain ⟨⟨u, c⟩, huv⟩ := hb.2 v
    rw [← huv]
    exact Submodule.add_mem_sup ⟨u, rfl⟩ c.property

/-- The SAME original global representatives are a frame of EVERY literal
quotient on the produced neighborhood. -/
theorem exists_nativeMultiplier_quotientFrame [ConnectedSpace X]
    (t₀ : HolomorphicSections (n := n) P.Fiber) (ht₀ : t₀ ≠ 0) :
    ∃ C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ),
      ∃ U : Set (HolomorphicSections (n := n) P.Fiber),
        IsOpen U ∧ t₀ ∈ U ∧
        ∀ t ∈ U, Function.Bijective
          (((nativeMultiplierSectionMap E P hφ t).range.mkQ).comp C.subtype) := by
  obtain ⟨C, U, hU, htU, hC⟩ := exists_nativeMultiplier_fixedComplement E P hφ t₀ ht₀
  refine ⟨C, U, hU, htU, ?_⟩
  intro t ht
  let e := (nativeMultiplierSectionMap E P hφ t).range.quotientEquivOfIsCompl C (hC t ht)
  have he : e.symm.toLinearMap =
      ((nativeMultiplierSectionMap E P hφ t).range.mkQ).comp C.subtype :=
    Submodule.toLinearMap_symm_quotientEquivOfIsCompl (hC t ht)
  rw [← he]
  exact e.symm.bijective

/-- A finite list of SAME original global sections gives actual bases of all
the literal quotients on a produced neighborhood of the defining section. -/
theorem exists_nativeMultiplier_quotientBasis [ConnectedSpace X]
    (t₀ : HolomorphicSections (n := n) P.Fiber) (ht₀ : t₀ ≠ 0) :
    ∃ r : ℕ, ∃ S : Fin r → nativeMultiplierSections (tensor E P) φ,
      ∃ U : Set (HolomorphicSections (n := n) P.Fiber),
        IsOpen U ∧ t₀ ∈ U ∧
        ∀ t ∈ U, ∃ b : Module.Basis (Fin r) ℂ
          ((nativeMultiplierSections (tensor E P) φ) ⧸ (nativeMultiplierSectionMap E P hφ t).range),
          ∀ i, b i = (nativeMultiplierSectionMap E P hφ t).range.mkQ (S i) := by
  classical
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  obtain ⟨C, U, hU, htU, hC⟩ := exists_nativeMultiplier_fixedComplement E P hφ t₀ ht₀
  let b := Module.finBasis ℂ C
  refine ⟨Module.finrank ℂ C, fun i => (b i).val, U, hU, htU, ?_⟩
  intro t ht
  let e := (nativeMultiplierSectionMap E P hφ t).range.quotientEquivOfIsCompl C (hC t ht)
  refine ⟨b.map e.symm, ?_⟩
  intro i
  change e.symm (b i) = _
  exact congrArg (fun f => f (b i))
    (Submodule.toLinearMap_symm_quotientEquivOfIsCompl (hC t ht))

end SGPT.Trace.Bertini
