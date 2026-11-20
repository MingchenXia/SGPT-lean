import SGPT.Foundations.Analysis.Pending.NaturalRealPPSubmodule

/-!
# Faithful reflection from complex span to the original real submodule

The real extension map is the constructed unique complexification of actual
continuous real alternating forms. Span induction constructs its real and
imaginary components inside the same real submodule. No type, basis, span,
or global-current certificate is supplied by the caller.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexifiedRealSpan

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open NaturalRealPPSubmodule

def realExtension (n d : ℕ) :
    (ComplexModel n [⋀^Fin d]→L[ℝ] ℝ) →ₗ[ℝ]
      (complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) where
  toFun A := complexify A.toAlternatingMap
  map_add' A B := by
    simp only [ContinuousAlternatingMap.toAlternatingMap_add, complexify_add]
  map_smul' c A := by
    simp only [ContinuousAlternatingMap.toAlternatingMap_smul, complexify_real_smul,
      RingHom.id_apply]

theorem realExtension_realEmbedding {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→L[ℝ] ℝ) (v : Fin d → ComplexModel n) :
    realExtension n d A (fun j => realEmbedding n (v j)) = (A v : ℂ) :=
  complexify_realEmbedding A.toAlternatingMap v

def complexSpan {n d : ℕ}
    (S : Submodule ℝ (ComplexModel n [⋀^Fin d]→L[ℝ] ℝ)) :
    Submodule ℂ (complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) :=
  Submodule.span ℂ ((realExtension n d) '' (S : Set _))

private theorem complex_smul_components {n d : ℕ} (c : ℂ)
    (A B : ComplexModel n [⋀^Fin d]→L[ℝ] ℝ) :
    c • (realExtension n d A + Complex.I • realExtension n d B) =
      realExtension n d (c.re • A - c.im • B) +
        Complex.I • realExtension n d (c.im • A + c.re • B) := by
  apply AlternatingMap.coe_multilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => (coordinateRealBasis n).baseChange ℂ)
  intro w
  simp only [Module.Basis.baseChange_apply]
  change (c • (realExtension n d A + Complex.I • realExtension n d B))
      (fun j => realEmbedding n (coordinateRealBasis n (w j))) =
    (realExtension n d (c.re • A - c.im • B) +
      Complex.I • realExtension n d (c.im • A + c.re • B))
      (fun j => realEmbedding n (coordinateRealBasis n (w j)))
  simp only [AlternatingMap.smul_apply, AlternatingMap.add_apply,
    realExtension_realEmbedding, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add]
  conv_lhs => rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem mem_complexSpan_components {n d : ℕ}
    (S : Submodule ℝ (ComplexModel n [⋀^Fin d]→L[ℝ] ℝ))
    (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) (hF : F ∈ complexSpan S) :
    ∃ A ∈ S, ∃ B ∈ S,
      F = realExtension n d A + Complex.I • realExtension n d B := by
  unfold complexSpan at hF
  refine Submodule.span_induction (p := fun F _ =>
    ∃ A ∈ S, ∃ B ∈ S,
      F = realExtension n d A + Complex.I • realExtension n d B)
    ?_ ?_ ?_ ?_ hF
  · intro F hF
    obtain ⟨A, hA, rfl⟩ := hF
    exact ⟨A, hA, 0, S.zero_mem, by simp⟩
  · exact ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
  · intro F G _ _ ihF ihG
    obtain ⟨A, hA, B, hB, hAB⟩ := ihF
    obtain ⟨C, hC, D, hD, hCD⟩ := ihG
    refine ⟨A + C, S.add_mem hA hC, B + D, S.add_mem hB hD, ?_⟩
    rw [hAB, hCD, map_add, map_add, smul_add]
    abel
  · intro c F _ ihF
    obtain ⟨A, hA, B, hB, hAB⟩ := ihF
    refine ⟨c.re • A - c.im • B,
      S.sub_mem (S.smul_mem c.re hA) (S.smul_mem c.im hB),
      c.im • A + c.re • B,
      S.add_mem (S.smul_mem c.im hA) (S.smul_mem c.re hB), ?_⟩
    rw [hAB]
    exact complex_smul_components c A B

theorem realExtension_mem_complexSpan_iff {n d : ℕ}
    (S : Submodule ℝ (ComplexModel n [⋀^Fin d]→L[ℝ] ℝ))
    (A : ComplexModel n [⋀^Fin d]→L[ℝ] ℝ) :
    realExtension n d A ∈ complexSpan S ↔ A ∈ S := by
  constructor
  · intro hA
    obtain ⟨B, hB, C, _, hBC⟩ := mem_complexSpan_components S _ hA
    have hAB : A = B := by
      ext v
      have h := congrArg (fun F => F (fun j => realEmbedding n (v j))) hBC
      simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply,
        realExtension_realEmbedding, smul_eq_mul] at h
      have hr := congrArg Complex.re h
      simpa using hr
    exact hAB ▸ hB
  · intro hA
    exact Submodule.subset_span ⟨A, hA, rfl⟩

end SGPT.Foundations.Analysis.Pending.NaturalComplexifiedRealSpan
