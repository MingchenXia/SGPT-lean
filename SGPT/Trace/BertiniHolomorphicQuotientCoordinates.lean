import SGPT.Trace.BertiniHyperplaneQuotientFrame
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Actual native multiplier splitting and quotient coefficients are
holomorphic. This does not assert restriction or Nadel exactness. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (E P : HermitianHolomorphicLineBundle n X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)

local instance : NormedAddCommGroup (nativeMultiplierSections E φ) := inferInstance
local instance : NormedSpace ℂ (nativeMultiplierSections E φ) := inferInstance
local instance : NormedAddCommGroup (nativeMultiplierSections (tensor E P) φ) := inferInstance
local instance : NormedSpace ℂ (nativeMultiplierSections (tensor E P) φ) := inferInstance
local instance (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ)) :
    NormedAddCommGroup ((nativeMultiplierSections E φ × C) →L[ℂ]
      nativeMultiplierSections (tensor E P) φ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ)) :
    NormedAddCommGroup ((nativeMultiplierSections (tensor E P) φ) →L[ℂ]
      (nativeMultiplierSections E φ × C)) := ContinuousLinearMap.toNormedAddCommGroup

theorem contDiff_nativeSectionSplitMap
    (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ)) :
    ContDiff ℂ ∞ (nativeSectionSplitMap E P hφ C) := by
  have := nativeMultiplierSections_finiteDimensional E φ
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  have := holomorphicSections_finiteDimensional (n := n) P.Fiber
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
  let AL : HolomorphicSections (n := n) P.Fiber →L[ℂ]
      ((nativeMultiplierSections E φ × C) →L[ℂ] nativeMultiplierSections (tensor E P) φ) :=
    A.toContinuousLinearMap
  have hA : ContDiff ℂ ∞ (fun t : HolomorphicSections (n := n) P.Fiber => A t) := by
    change ContDiff ℂ ∞ AL
    exact ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := HolomorphicSections (n := n) P.Fiber)
      (F := (nativeMultiplierSections E φ × C) →L[ℂ] nativeMultiplierSections (tensor E P) φ)
      (n := ∞) AL
  rw [heq]
  exact ContDiff.add (f := fun t : HolomorphicSections (n := n) P.Fiber => A t)
    (g := fun _ : HolomorphicSections (n := n) P.Fiber => B)
    hA contDiff_const

theorem contDiffAt_nativeSectionSplitInverse
    (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ))
    (t : HolomorphicSections (n := n) P.Fiber)
    (ht : (nativeSectionSplitMap E P hφ C t).IsInvertible) :
    ContDiffAt ℂ ∞ (fun s => (nativeSectionSplitMap E P hφ C s).inverse) t := by
  have := nativeMultiplierSections_finiteDimensional E φ
  have := nativeMultiplierSections_finiteDimensional (tensor E P) φ
  exact ht.contDiffAt_map_inverse.comp t (contDiff_nativeSectionSplitMap E P hφ C).contDiffAt

def nativeSectionComplementCoordinate
    (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ))
    (t : HolomorphicSections (n := n) P.Fiber)
    (S : nativeMultiplierSections (tensor E P) φ) : C :=
  ((nativeSectionSplitMap E P hφ C t).inverse S).2

theorem contDiffAt_nativeSectionComplementCoordinate
    (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ))
    (t : HolomorphicSections (n := n) P.Fiber)
    (S : nativeMultiplierSections (tensor E P) φ)
    (ht : (nativeSectionSplitMap E P hφ C t).IsInvertible) :
    ContDiffAt ℂ ∞ (fun q : HolomorphicSections (n := n) P.Fiber ×
      nativeMultiplierSections (tensor E P) φ =>
        nativeSectionComplementCoordinate E P hφ C q.1 q.2) (t,S) := by
  have hi := (contDiffAt_nativeSectionSplitInverse E P hφ C t ht).comp
    (t,S) contDiffAt_fst
  exact contDiffAt_snd.comp (t,S) (hi.clm_apply contDiffAt_snd)

theorem nativeSectionComplementCoordinate_quotient
    (C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ))
    (t : HolomorphicSections (n := n) P.Fiber)
    (S : nativeMultiplierSections (tensor E P) φ)
    (ht : (nativeSectionSplitMap E P hφ C t).IsInvertible) :
    (nativeMultiplierSectionMap E P hφ t).range.mkQ S =
      (nativeMultiplierSectionMap E P hφ t).range.mkQ
        (nativeSectionComplementCoordinate E P hφ C t S).val := by
  let z := (nativeSectionSplitMap E P hφ C t).inverse S
  have hz := ht.self_apply_inverse S
  change nativeMultiplierSectionMap E P hφ t z.1 + z.2.val = S at hz
  have hm : (nativeMultiplierSectionMap E P hφ t).range.mkQ
      (nativeMultiplierSectionMap E P hφ t z.1) = 0 := by
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨z.1,rfl⟩
  calc
    _ = (nativeMultiplierSectionMap E P hφ t).range.mkQ
        (nativeMultiplierSectionMap E P hφ t z.1 + z.2.val) := congrArg _ hz.symm
    _ = (nativeMultiplierSectionMap E P hφ t).range.mkQ z.2.val := by
      rw [map_add, hm, zero_add]
    _ = _ := rfl

theorem exists_nativeMultiplier_holomorphicSplit [ConnectedSpace X]
    (t₀ : HolomorphicSections (n := n) P.Fiber) (ht₀ : t₀ ≠ 0) :
    ∃ C : Submodule ℂ (nativeMultiplierSections (tensor E P) φ),
      ∃ U : Set (HolomorphicSections (n := n) P.Fiber),
        IsOpen U ∧ t₀ ∈ U ∧
        ∀ t ∈ U, (nativeSectionSplitMap E P hφ C t).IsInvertible ∧
          ContDiffAt ℂ ∞ (fun s => (nativeSectionSplitMap E P hφ C s).inverse) t := by
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
  exact ⟨ht, contDiffAt_nativeSectionSplitInverse E P hφ C t ht⟩

theorem contDiff_nativeBertiniAffineSection {N : ℕ}
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞) (j : Fin (N + 1)) :
    ContDiff ℂ ∞ (nativeBertiniAffineSection p j) := by
  apply ContDiff.sum
  intro m hm
  have hc : ContDiff ℂ ∞ (fun ζ : ComplexModel N => affineLift j ζ m) := by
    refine Fin.succAboveCases j ?_ (fun k => ?_) m
    · simp only [affineLift_same]
      exact contDiff_const
    · simp only [affineLift_succAbove]
      exact (EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ).contDiff
  exact hc.smul contDiff_const

theorem contDiffAt_nativeBertiniComplementCoordinate {N : ℕ}
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞)
    (C : Submodule ℂ (nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ))
    (j : Fin (N + 1)) (ζ : ComplexModel N)
    (S : nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ)
    (ht : (nativeSectionSplitMap E (nativeBertiniHyperplaneBundle p) hφ C
      (nativeBertiniAffineSection p j ζ)).IsInvertible) :
    ContDiffAt ℂ ∞ (fun q : ComplexModel N ×
      nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ =>
        nativeSectionComplementCoordinate E (nativeBertiniHyperplaneBundle p) hφ C
          (nativeBertiniAffineSection p j q.1) q.2) (ζ,S) := by
  have hc := contDiffAt_nativeSectionComplementCoordinate E (nativeBertiniHyperplaneBundle p)
    hφ C _ S ht
  have hp : ContDiffAt ℂ ∞ (fun q : ComplexModel N ×
      nativeMultiplierSections (tensor E (nativeBertiniHyperplaneBundle p)) φ =>
        (nativeBertiniAffineSection p j q.1,q.2)) (ζ,S) :=
    ((contDiff_nativeBertiniAffineSection p j).contDiffAt.comp (ζ,S) contDiffAt_fst).prodMk
      contDiffAt_snd
  have hcomp := hc.comp (ζ,S) hp
  exact hcomp

end SGPT.Trace.Bertini
