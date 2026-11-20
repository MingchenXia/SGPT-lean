import SGPT.Projective.SourceNativeCoordinateFamily

/-! Actual native O1 linear-form family, genuine generation and its original projective map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Projective.HyperplaneClassNext

open Set Bundle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Bergman.NativeKodairaPullback HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff BigOperators

variable {N : ℕ}

def projectiveLinearSelfMap
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    ContMDiffMap 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N)
      (ComplexProjectiveSpace N) (ComplexProjectiveSpace N) ∞ :=
  ⟨ComplexProjectiveSpace.linearMap A.toLinearMap A.injective,
    ComplexProjectiveSpace.contMDiff_linearMap A.toLinearMap A.injective⟩

def projectiveLinearFormFamily
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) (i : Fin (N + 1)) :
    HolomorphicSections (n := N) (sourceProjectiveHyperplaneBundle N).Fiber :=
  sourceProjectiveNativeLinearFormSection N (fun j => A (Pi.single j 1) i)

theorem linearMap_coordinate_expansion
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ))
    (v : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    A v i = ∑ j, A (Pi.single j 1) i * v j := by
  classical
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    funext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  calc
    _ = A (∑ j, v j • Pi.single j 1) i := congrArg (fun w => A w i) hv
    _ = ∑ j, v j * A (Pi.single j 1) i := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

theorem projectiveLinearFormFamily_frameVector
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ))
    (e : AtlasFrame (sourceProjectiveHyperplaneBundle N)) (p : ComplexProjectiveSpace N)
    (he : p ∈ e.val.baseSet) :
    (fun i => (e.val ⟨p, projectiveLinearFormFamily A i p⟩).2) =
      A (fun j => (e.val ⟨p, sourceProjectiveCoordinateNativeSection N j p⟩).2) := by
  funext i
  let l := e.val.linearEquivAt ℂ p he
  change l (sourceProjectiveNativeLinearFormSection N (fun j => A (Pi.single j 1) i) p) =
    A (fun j => l (sourceProjectiveCoordinateNativeSection N j p)) i
  rw [sourceProjectiveNativeLinearFormSection_apply, linearMap_coordinate_expansion]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact l.map_smul (A (Pi.single j 1) i) _

theorem projectiveLinearFormFamily_generating
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    ∀ p : ComplexProjectiveSpace N, ∃ i : Fin (N + 1), projectiveLinearFormFamily A i p ≠ 0 := by
  classical
  intro p
  let E := sourceProjectiveHyperplaneBundle N
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber p, inferInstance⟩
  have he : p ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber p
  let v : Fin (N + 1) → ℂ := fun j => (e.val ⟨p, sourceProjectiveCoordinateNativeSection N j p⟩).2
  have hv : v ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ := sourceProjectiveCoordinateNativeSection_generating N p
    have hc := congrFun hz j
    change e.val.linearEquivAt ℂ p he (sourceProjectiveCoordinateNativeSection N j p) = 0 at hc
    apply hj
    apply (e.val.linearEquivAt ℂ p he).injective
    rw [hc, map_zero]
  have hAv : A v ≠ 0 := by simpa only [map_zero] using A.injective.ne hv
  obtain ⟨i, hi⟩ : ∃ i, A v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hAv (funext h)
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  have hc := congrFun (projectiveLinearFormFamily_frameVector A e p he) i
  calc
    _ = (e.val ⟨p, projectiveLinearFormFamily A i p⟩).2 := hc.symm
    _ = 0 := by
      change e.val.linearEquivAt ℂ p he (projectiveLinearFormFamily A i p) = 0
      rw [hz, map_zero]

theorem projectiveLinearFormFamily_projectiveMap
    (A : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) (p : ComplexProjectiveSpace N) :
    sourceNativeFiniteSectionProjectiveMap (sourceProjectiveHyperplaneBundle N)
      (projectiveLinearFormFamily A) (projectiveLinearFormFamily_generating A) p =
        projectiveLinearSelfMap A p := by
  let E := sourceProjectiveHyperplaneBundle N
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber p, inferInstance⟩
  have he : p ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber p
  change _ = ComplexProjectiveSpace.linearMap A.toLinearMap A.injective p
  calc
    _ = ComplexProjectiveSpace.linearMap A.toLinearMap A.injective
        (sourceNativeFiniteSectionProjectiveMap E (sourceProjectiveCoordinateNativeSection N)
          (sourceProjectiveCoordinateNativeSection_generating N) p) := by
      rw [sourceNativeFiniteSectionProjectiveMap_frame E _ _ e p he,
        sourceNativeFiniteSectionProjectiveMap_frame E _ _ e p he,
        ComplexProjectiveSpace.linearMap_mk]
      apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
      refine ⟨1, ?_⟩
      simp only [one_smul]
      change A (fun j => (e.val ⟨p, sourceProjectiveCoordinateNativeSection N j p⟩).2) =
        (fun i => (e.val ⟨p, projectiveLinearFormFamily A i p⟩).2)
      exact (projectiveLinearFormFamily_frameVector A e p he).symm
    _ = _ := congrArg (ComplexProjectiveSpace.linearMap A.toLinearMap A.injective)
      (sourceProjectiveCoordinateNativeSection_projectiveMap_identity N p)

end SGPT.Projective.HyperplaneClassNext
