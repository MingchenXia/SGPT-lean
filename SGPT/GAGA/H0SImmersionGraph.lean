import SGPT.GAGA.H0ConeExtension
import SGPT.Projective.Basic

/-!
# The image of a holomorphic immersion is locally a graph


Let `φ : ℂⁿ ⊇ U → ℂᴺ` be holomorphic with injective derivative `A = Dφ(z₀)`.

* `exists_adapted_equiv`: there are linear coordinates `L₀ : ℂᴺ ≅ ℂⁿ × ℂ^{N-n}` with
  `L₀ (A v) = (v, 0)` (so `n ≤ N`).
* `exists_local_graph_of_injective_fderiv`: in these coordinates the image of a neighbourhood
  `U₀` of `z₀` is the graph `{(x, g x) : x ∈ O}` of a holomorphic `g`, the first coordinate
  `x = (L₀ φ z)₁` being a biholomorphic coordinate on `U₀` with holomorphic inverse `ψ`
  (holomorphic inverse function theorem).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0S

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- **Coordinates adapted to an injective linear map.**  For an injective `A : ℂⁿ → ℂᴺ` there
are linear coordinates `L₀ : ℂᴺ ≅ ℂⁿ × ℂ^{N-n}` with `L₀ (A v) = (v, 0)`. -/
theorem exists_adapted_equiv {n N : ℕ} (A : ComplexModel n →L[ℂ] ComplexModel N)
    (hA : Function.Injective A) :
    n ≤ N ∧ ∃ L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n),
      ∀ v, L0 (A v) = (v, 0) := by
  classical
  set A' : ComplexModel n →ₗ[ℂ] ComplexModel N := A.toLinearMap
  set R := LinearMap.range A'
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl R
  have hR : Module.finrank ℂ R = n := by
    rw [LinearMap.finrank_range_of_inj (f := A') hA, finrank_euclideanSpace_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl hW
  rw [finrank_euclideanSpace_fin, hR] at hsum
  refine ⟨by omega, ?_⟩
  have hWd : Module.finrank ℂ W = Module.finrank ℂ (ComplexModel (N - n)) := by
    rw [finrank_euclideanSpace_fin]; omega
  let eR : ComplexModel n ≃ₗ[ℂ] R := LinearEquiv.ofInjective A' hA
  let eW : W ≃ₗ[ℂ] ComplexModel (N - n) := LinearEquiv.ofFinrankEq W _ hWd
  let e : ComplexModel N ≃ₗ[ℂ] ComplexModel n × ComplexModel (N - n) :=
    (Submodule.prodEquivOfIsCompl R W hW).symm.trans (eR.symm.prodCongr eW)
  refine ⟨e.toContinuousLinearEquiv, fun v => ?_⟩
  have hAv : (⟨A v, LinearMap.mem_range_self A' v⟩ : R) = eR v := rfl
  change e (A v) = (v, 0)
  simp only [e, LinearEquiv.trans_apply]
  have h1 : (Submodule.prodEquivOfIsCompl R W hW).symm (A v) = (⟨A v, LinearMap.mem_range_self A' v⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left R W hW ⟨A v, LinearMap.mem_range_self A' v⟩
  rw [h1, LinearEquiv.prodCongr_apply, hAv, LinearEquiv.symm_apply_apply, map_zero]

/-- **The image of a holomorphic immersion is locally a holomorphic graph.**  Let
`φ : ℂⁿ → ℂᴺ` be holomorphic on an open `U ∋ z₀` with injective derivative at `z₀`.  Then
`n ≤ N` and there are linear coordinates `L₀ : ℂᴺ ≅ ℂⁿ × ℂ^{N-n}` with `L₀ (Dφ(z₀) v) = (v, 0)`,
an open `U₀ ∋ z₀`, an open `O ⊆ ℂⁿ` and holomorphic `g : O → ℂ^{N-n}`, `ψ : O → U₀` such that
`z ↦ (L₀ φ z)₁` maps `U₀` bijectively onto `O` with inverse `ψ`, and `(L₀ φ z)₂ = g (L₀ φ z)₁`
on `U₀`. -/
theorem exists_local_graph_of_injective_fderiv {n N : ℕ} {φ : ComplexModel n → ComplexModel N}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) (hinj : Function.Injective (fderiv ℂ φ z₀)) :
    n ≤ N ∧ ∃ (L0 : ComplexModel N ≃L[ℂ] ComplexModel n × ComplexModel (N - n))
      (U₀ O : Set (ComplexModel n)) (g : ComplexModel n → ComplexModel (N - n))
      (ψ : ComplexModel n → ComplexModel n),
      IsOpen U₀ ∧ z₀ ∈ U₀ ∧ U₀ ⊆ U ∧ IsOpen O ∧ DifferentiableOn ℂ g O ∧
      DifferentiableOn ℂ ψ O ∧ (∀ v, (L0 (fderiv ℂ φ z₀ v)).2 = 0) ∧
      (∀ z ∈ U₀, (L0 (φ z)).1 ∈ O ∧ ψ (L0 (φ z)).1 = z ∧ (L0 (φ z)).2 = g (L0 (φ z)).1) ∧
      (∀ x ∈ O, ψ x ∈ U₀ ∧ (L0 (φ (ψ x))).1 = x) := by
  obtain ⟨hnN, L0, hL0⟩ := exists_adapted_equiv (fderiv ℂ φ z₀) hinj
  refine ⟨hnN, L0, ?_⟩
  have hcd : ∀ z ∈ U, ContDiffAt ℂ ∞ φ z := fun z hz =>
    contDiffAt_of_differentiableOn_complex hφ hU hz
  -- the first coordinate `h = (L₀ ∘ φ)₁`
  set P : ComplexModel N →L[ℂ] ComplexModel n :=
    (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel (N - n))).comp
      (L0 : ComplexModel N →L[ℂ] ComplexModel n × ComplexModel (N - n)) with hPdef
  set h : ComplexModel n → ComplexModel n := fun z => P (φ z) with hhdef
  have hhcd : ∀ z ∈ U, ContDiffAt ℂ ∞ h z := fun z hz => P.contDiff.contDiffAt.comp z (hcd z hz)
  have hhd : ∀ z ∈ U, HasFDerivAt h (P.comp (fderiv ℂ φ z)) z := fun z hz =>
    P.hasFDerivAt.comp z ((hcd z hz).differentiableAt (by simp)).hasFDerivAt
  have hP0 : P.comp (fderiv ℂ φ z₀) = ContinuousLinearMap.id ℂ (ComplexModel n) := by
    ext1 v
    simp only [hPdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearEquiv.coe_coe, hL0, ContinuousLinearMap.id_apply]
  -- the derivative of `h` is invertible near `z₀`
  have hcont : ContinuousAt (fun z => fderiv ℂ h z) z₀ :=
    (hhcd z₀ hz₀).continuousAt_fderiv (by simp)
  have hfd : ∀ z ∈ U, fderiv ℂ h z = P.comp (fderiv ℂ φ z) := fun z hz => (hhd z hz).fderiv
  have hopen := ContinuousLinearEquiv.isOpen (𝕜 := ℂ) (E := ComplexModel n) (F := ComplexModel n)
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ fderiv ℂ h z ∈
      range ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) → ComplexModel n →L[ℂ] ComplexModel n) := by
    have hmem : fderiv ℂ h z₀ ∈ range ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) →
        ComplexModel n →L[ℂ] ComplexModel n) := by
      rw [hfd z₀ hz₀, hP0]
      exact ⟨ContinuousLinearEquiv.refl ℂ _, rfl⟩
    exact Filter.Eventually.and (hU.mem_nhds hz₀) (hcont.preimage_mem_nhds (hopen.mem_nhds hmem))
  obtain ⟨S, hSgood, hSo, hz₀S⟩ := _root_.eventually_nhds_iff.mp hev
  -- the inverse function theorem
  have hstrict : HasStrictFDerivAt h
      ((ContinuousLinearEquiv.refl ℂ (ComplexModel n) : ComplexModel n ≃L[ℂ] ComplexModel n) :
        ComplexModel n →L[ℂ] ComplexModel n) z₀ := by
    have h1 := hhd z₀ hz₀
    rw [hP0] at h1
    exact (hhcd z₀ hz₀).hasStrictFDerivAt' h1 (by simp)
  set T := hstrict.toOpenPartialHomeomorph h with hTdef
  have hTcoe : (T : ComplexModel n → ComplexModel n) = h := rfl
  set U₀ := T.source ∩ S with hU₀def
  have hU₀o : IsOpen U₀ := T.open_source.inter hSo
  set O := T.target ∩ T.symm ⁻¹' U₀ with hOdef
  have hOo : IsOpen O := T.isOpen_inter_preimage_symm hU₀o
  refine ⟨U₀, O, fun x => (L0 (φ (T.symm x))).2, T.symm, hU₀o,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀S⟩, fun z hz => (hSgood z hz.2).1, hOo,
    ?_, ?_, fun v => by rw [hL0], ?_, ?_⟩
  · -- `g` is holomorphic
    intro x hx
    have hxU : T.symm x ∈ U := (hSgood _ hx.2.2).1
    have h1 : DifferentiableAt ℂ T.symm x := by
      obtain ⟨e, he⟩ := (hSgood _ hx.2.2).2
      have hder : HasFDerivAt T (e : ComplexModel n →L[ℂ] ComplexModel n) (T.symm x) := by
        rw [he, hTcoe]
        exact (hhd _ hxU).congr_fderiv (hfd _ hxU).symm
      exact (T.contDiffAt_symm hx.1 hder (hhcd _ hxU)).differentiableAt (by simp)
    have h2 : DifferentiableAt ℂ φ (T.symm x) := (hcd _ hxU).differentiableAt (by simp)
    exact ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel (N - n))).comp
      (L0 : ComplexModel N →L[ℂ] ComplexModel n × ComplexModel (N - n))).differentiableAt.comp x
      (h2.comp x h1) |>.differentiableWithinAt
  · -- `ψ` is holomorphic
    intro x hx
    have hxU : T.symm x ∈ U := (hSgood _ hx.2.2).1
    obtain ⟨e, he⟩ := (hSgood _ hx.2.2).2
    have hder : HasFDerivAt T (e : ComplexModel n →L[ℂ] ComplexModel n) (T.symm x) := by
      rw [he, hTcoe]
      exact (hhd _ hxU).congr_fderiv (hfd _ hxU).symm
    exact (T.contDiffAt_symm hx.1 hder (hhcd _ hxU)).differentiableAt (by simp)
      |>.differentiableWithinAt
  · intro z hz
    have hzT : T z ∈ T.target := T.map_source hz.1
    have hinv : T.symm (T z) = z := T.left_inv hz.1
    refine ⟨⟨hzT, show T.symm (T z) ∈ U₀ by rw [hinv]; exact hz⟩, hinv, ?_⟩
    change (L0 (φ z)).2 = (L0 (φ (T.symm (T z)))).2
    rw [hinv]
  · intro x hx
    exact ⟨hx.2, T.right_inv hx.1⟩

end SGPT.GAGA.H0S
