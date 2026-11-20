import SGPT.GAGA.SmoothFlagsScheme
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# maps between projective manifolds through their embeddings

Source: `rmk:bdiv:L749` (algebraization of the book's blow-up models).

Let `Φ₂ : M₂ → ℙᴺ` be a holomorphic embedding of a compact complex manifold (lane H0-GAGA2's
`SGPT.GAGA.H0S.IsHolomorphicEmbedding`).  Its image is locally a holomorphic graph and the points
of the image come from `M₂` through a holomorphic map (`SGPT.GAGA.H0S.exists_affine_graph`).
Hence:

* `contMDiff_of_comp_eq_bd5`: a map `φ : M₁ → M₂` with `Φ₂ ∘ φ` holomorphic is holomorphic;
* `mfderiv_injective_of_isHolomorphicEmbedding_bd5`: the manifold derivative of a holomorphic
  embedding is injective;
* `diffeomorphOfRangeEq_bd5`: two holomorphic embeddings of compact manifolds of the same
  dimension with the same image differ by a biholomorphism (`Φ₂ ∘ e = Φ₁`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.BD5

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.GAGA.H0S

universe u v

section Maps

variable {d n N : ℕ} {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (ComplexModel d) M₁]
  [IsComplexManifold d M₁]
  {M₂ : Type v} [TopologicalSpace M₂] [ChartedSpace (ComplexModel n) M₂]
  [IsComplexManifold n M₂] [CompactSpace M₂]

omit [IsComplexManifold d M₁] in
/-- **Maps into the source of a projective embedding.**  If `Φ₂ : M₂ → ℙᴺ` is a holomorphic
embedding of a compact manifold and `φ : M₁ → M₂` is such that `Φ₂ ∘ φ` is holomorphic, then `φ`
is holomorphic. -/
theorem contMDiff_of_comp_eq_bd5 {Φ₁ : M₁ → ComplexProjectiveSpace N}
    {Φ₂ : M₂ → ComplexProjectiveSpace N}
    (h₁ : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel N) ∞ Φ₁)
    (hΦ₂ : IsHolomorphicEmbedding (n := n) Φ₂) (φ : M₁ → M₂) (hφ : ∀ x, Φ₂ (φ x) = Φ₁ x) :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ φ := by
  intro x
  set q := φ x with hq
  set i := chartIndex (Φ₂ q) with hi
  have hqi : Φ₂ q ∈ (affineChart i).source := mem_affineChart_chartIndex _
  obtain ⟨-, L0, ε, O, g, ψ, hε, hO, -, hψ, hψmem, -, hgraph⟩ := exists_affine_graph hΦ₂ q i hqi
  set e := (complexChartAt (n := n) q).val with he
  -- the explicit holomorphic formula for `φ` near `x`
  set G : M₁ → M₂ := fun x' => e.symm (ψ (L0 (affineChart i (Φ₁ x'))).1) with hG
  have hx1 : Φ₁ x ∈ (affineChart i).source := by rw [← hφ x]; exact hqi
  have hball : ∀ᶠ x' in 𝓝 x, Φ₁ x' ∈ (affineChart i).source ∧
      affineChart i (Φ₁ x') ∈ ball (affineChart i (Φ₂ q)) ε := by
    have hc : ContinuousAt (fun x' => affineChart i (Φ₁ x')) x :=
      ((affineChart i).continuousAt hx1).comp (h₁ x).continuousAt
    have hsrc : ∀ᶠ x' in 𝓝 x, Φ₁ x' ∈ (affineChart i).source :=
      (h₁ x).continuousAt.preimage_mem_nhds ((affineChart i).open_source.mem_nhds hx1)
    have hb : ∀ᶠ x' in 𝓝 x, affineChart i (Φ₁ x') ∈ ball (affineChart i (Φ₂ q)) ε := by
      apply hc.preimage_mem_nhds
      apply isOpen_ball.mem_nhds
      rw [← hφ x]
      exact mem_ball_self hε
    exact hsrc.and hb
  have heq : φ =ᶠ[𝓝 x] G := by
    filter_upwards [hball] with x' ⟨hsrc, hb⟩
    obtain ⟨-, hiff, hgr⟩ := hgraph _ hb
    have hpt : affinePoint i (affineChart i (Φ₁ x')) = Φ₁ x' := (affineChart i).left_inv hsrc
    have hmem : affinePoint i (affineChart i (Φ₁ x')) ∈ range Φ₂ := by
      rw [hpt]; exact ⟨φ x', hφ x'⟩
    obtain ⟨-, hΦ⟩ := hgr (hiff.mp hmem)
    apply hΦ₂.injective
    rw [hφ x', hΦ, hpt]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  -- `G` is holomorphic at `x`
  obtain ⟨hO0, -, -⟩ := hgraph (affineChart i (Φ₁ x)) (by rw [← hφ x]; exact mem_ball_self hε)
  have hA : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel N) ∞
      (fun x' => affineChart i (Φ₁ x')) x :=
    (contMDiffAt_affineChart i hx1).comp x (h₁ x)
  have hLc : ContDiff ℂ ∞ (fun y : ComplexModel N => (L0 y).1) :=
    (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel (N - n))).contDiff.comp L0.contDiff
  have hL : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : ComplexModel N => (L0 y).1) (affineChart i (Φ₁ x)) :=
    hLc.contMDiff.contMDiffAt
  have hψd : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ
      (L0 (affineChart i (Φ₁ x))).1 := by
    have hc := (contDiffOn_of_differentiableOn_complex hψ hO).contDiffAt (hO.mem_nhds hO0)
    exact hc.contMDiffAt
  have hψx := (hψmem _ hO0).1
  have hsymm : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm
      (ψ (L0 (affineChart i (Φ₁ x))).1) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := q)).contMDiffAt
      (e.open_target.mem_nhds hψx)
  have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞
      (fun x' => (L0 (affineChart i (Φ₁ x'))).1) x :=
    ContMDiffAt.comp (g := fun y : ComplexModel N => (L0 y).1)
      (f := fun x' => affineChart i (Φ₁ x')) x hL hA
  have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞
      (fun x' => ψ (L0 (affineChart i (Φ₁ x'))).1) x :=
    ContMDiffAt.comp (g := ψ) (f := fun x' => (L0 (affineChart i (Φ₁ x'))).1) x hψd h2
  exact hsymm.comp x h3

omit [IsComplexManifold n M₂] [CompactSpace M₂] in
/-- The manifold derivative of a holomorphic embedding into `ℙᴺ` is injective. -/
theorem mfderiv_injective_of_isHolomorphicEmbedding_bd5 {Φ : M₂ → ComplexProjectiveSpace N}
    (hΦ : IsHolomorphicEmbedding (n := n) Φ) (p : M₂) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) Φ p) := by
  have hD : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) Φ p :=
    (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΦ p).mdifferentiableAt (by simp)
  rw [hD.mfderiv]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, fderivWithin_univ]
  exact hΦ.immersion p (chartIndex (Φ p)) (mem_affineChart_chartIndex _)

end Maps

section Diffeo

variable {n N : ℕ} {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (ComplexModel n) M₁]
  [IsComplexManifold n M₁] [CompactSpace M₁]
  {M₂ : Type v} [TopologicalSpace M₂] [ChartedSpace (ComplexModel n) M₂]
  [IsComplexManifold n M₂] [CompactSpace M₂]

/-- **Two projective embeddings with the same image differ by a biholomorphism.** -/
def diffeomorphOfRangeEq_bd5 {Φ₁ : M₁ → ComplexProjectiveSpace N}
    {Φ₂ : M₂ → ComplexProjectiveSpace N}
    (hΦ₁ : IsHolomorphicEmbedding (n := n) Φ₁) (hΦ₂ : IsHolomorphicEmbedding (n := n) Φ₂)
    (hr : range Φ₁ = range Φ₂) :
    M₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M₂ :=
  have h12 : ∀ x, Φ₁ x ∈ range Φ₂ := fun x => hr ▸ mem_range_self x
  have h21 : ∀ y, Φ₂ y ∈ range Φ₁ := fun y => hr.symm ▸ mem_range_self y
  { toFun := fun x => (h12 x).choose
    invFun := fun y => (h21 y).choose
    left_inv := fun x => hΦ₁.injective (by
      rw [(h21 _).choose_spec, (h12 x).choose_spec])
    right_inv := fun y => hΦ₂.injective (by
      rw [(h12 _).choose_spec, (h21 y).choose_spec])
    contMDiff_toFun := contMDiff_of_comp_eq_bd5
      (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΦ₁) hΦ₂ _
      (fun x => (h12 x).choose_spec)
    contMDiff_invFun := contMDiff_of_comp_eq_bd5
      (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΦ₂) hΦ₁ _
      (fun y => (h21 y).choose_spec) }

theorem diffeomorphOfRangeEq_bd5_apply {Φ₁ : M₁ → ComplexProjectiveSpace N}
    {Φ₂ : M₂ → ComplexProjectiveSpace N}
    (hΦ₁ : IsHolomorphicEmbedding (n := n) Φ₁) (hΦ₂ : IsHolomorphicEmbedding (n := n) Φ₂)
    (hr : range Φ₁ = range Φ₂) (x : M₁) :
    Φ₂ (diffeomorphOfRangeEq_bd5 hΦ₁ hΦ₂ hr x) = Φ₁ x :=
  (show Φ₁ x ∈ range Φ₂ from hr ▸ mem_range_self x).choose_spec

end Diffeo

end SGPT.BDivisor.BD5
