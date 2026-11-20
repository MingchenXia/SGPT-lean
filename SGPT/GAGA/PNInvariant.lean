import SGPT.GAGA.PNStructureSheaf

/-!
# `ℂ*`-invariance of sums, images, preimages, kernels and cokernels

Infrastructure of lane SERRE-PN (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145). The long exact sequences of
`PNSections.coverSystem_les` apply to `ℂ*`-invariant subquotients (coherent sheaves on
`ℙᴺ`). Serre's induction forms kernels, images and cokernels of morphisms given by
homogeneous matrices (e.g. multiplication by a linear form `F(-1) → F`). This file shows that
these stay invariant: invariance is preserved by sums, intersections, images and preimages
under homogeneous matrices (`IsConeInvariant.sup`, `inf`, `map`, `comap`), hence by the
kernel, image and cokernel subquotients of lane SERRE-CORE (`isInvariant_ker`, `isInvariant_im`,
`isInvariant_coker`).

Blueprint: `claude-serre-pn.tex`, node `claude-serre-pn:invariance`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

namespace SGPT.GAGA.PN

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem tendsto_inv_smul_nhds {c : ℂ} (hc : c ≠ 0) (y : X) :
    Tendsto (fun z : X => c⁻¹ • z) (𝓝 (c • y)) (𝓝 y) := by
  have := (continuous_const_smul c⁻¹).tendsto (c • y)
  rwa [inv_smul_smul₀ hc] at this

/-- Invariance follows from one implication (apply it to `c⁻¹`). -/
theorem isConeInvariant_of_imp {P : GermModule X ι}
    (h : ∀ y : X, y ≠ 0 → ∀ c : ℂ, c ≠ 0 → ∀ a : ι → X → ℂ,
      P.mem y a → P.mem (c • y) (fun j z => a j (c⁻¹ • z))) :
    IsConeInvariant P := by
  intro y hy c hc a
  refine ⟨h y hy c hc a, fun ha => ?_⟩
  have h' := h (c • y) (smul_ne_zero hc hy) c⁻¹ (inv_ne_zero hc) _ ha
  have e1 : c⁻¹ • c • y = y := inv_smul_smul₀ hc y
  have e2 : (fun j z => a j (c⁻¹ • (c⁻¹)⁻¹ • z)) = a := by
    funext j z
    rw [inv_inv, inv_smul_smul₀ hc]
  rwa [e1, e2] at h'

theorem IsConeInvariant.inf {P Q : GermModule X ι} (hP : IsConeInvariant P)
    (hQ : IsConeInvariant Q) : IsConeInvariant (P.inf Q) :=
  fun y hy c hc a => and_congr (hP y hy c hc a) (hQ y hy c hc a)

theorem IsConeInvariant.sup {P Q : GermModule X ι} (hP : IsConeInvariant P)
    (hQ : IsConeInvariant Q) : IsConeInvariant (P.sup Q) := by
  refine isConeInvariant_of_imp fun y hy c hc a ha => ?_
  obtain ⟨b, e, hb, he, hbe⟩ := ha
  exact ⟨fun j z => b j (c⁻¹ • z), fun j z => e j (c⁻¹ • z), (hP y hy c hc b).1 hb,
    (hQ y hy c hc e).1 he, fun j => (hbe j).comp_tendsto (tendsto_inv_smul_nhds hc y)⟩

/-- Near a point `w ≠ 0` all points are nonzero. -/
theorem eventually_ne_zero {w : X} (hw : w ≠ 0) : ∀ᶠ z in 𝓝 w, z ≠ 0 :=
  isOpen_ne.mem_nhds hw

theorem IsConeInvariant.map {Q : GermModule X ι} (hQ : IsConeInvariant Q)
    (hQc : Q.IsCoherentOn (puncture X)) {A : κ → ι → X → ℂ} {d : ℤ} (hA : IsHomMatrix A d) :
    IsConeInvariant (Q.map A) := by
  refine isConeInvariant_of_imp fun y hy c hc b hb => ?_
  obtain ⟨a, ha, hba⟩ := hb
  have hcy : c • y ≠ 0 := smul_ne_zero hc hy
  refine ⟨fun j z => (c⁻¹) ^ d * a j (c⁻¹ • z),
    (hQc _ hcy).smul_mem (holAt_const _ _) ((hQ y hy c hc a).1 ha), fun i => ?_⟩
  filter_upwards [(hba i).comp_tendsto (tendsto_inv_smul_nhds hc y), eventually_ne_zero hcy]
    with w hw hw0
  simp only [Function.comp_apply] at hw
  rw [hw]
  simp only [matApply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hA.hom w hw0 c⁻¹ (inv_ne_zero hc) i j]
  ring

theorem IsConeInvariant.comap {N : GermModule X κ} (hN : IsConeInvariant N)
    (hNc : N.IsCoherentOn (puncture X)) {A : κ → ι → X → ℂ} {d : ℤ} (hA : IsHomMatrix A d) :
    IsConeInvariant (N.comap A) := by
  refine isConeInvariant_of_imp fun y hy c hc a ha => ?_
  obtain ⟨hhol, hAa⟩ := ha
  have hcy : c • y ≠ 0 := smul_ne_zero hc hy
  refine ⟨(isConeInvariant_top y hy c hc a).1 hhol, ?_⟩
  have h1 : N.mem (c • y) (fun i z => c ^ d * matApply A a i (c⁻¹ • z)) :=
    (hNc _ hcy).smul_mem (holAt_const _ _) ((hN y hy c hc _).1 hAa)
  refine (hNc _ hcy).congr_mem h1 fun i => ?_
  filter_upwards [eventually_ne_zero hcy] with w hw0
  simp only [matApply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw' : c⁻¹ • w ≠ 0 := smul_ne_zero (inv_ne_zero hc) hw0
  have h2 := hA.hom (c⁻¹ • w) hw' c hc i j
  rw [smul_inv_smul₀ hc] at h2
  rw [h2]
  ring

/-! ### Kernels, images and cokernels of homogeneous morphisms -/

variable {F G : Subquotient X (puncture X)}

/-- The kernel of a homogeneous morphism of invariant subquotients is invariant. -/
theorem isInvariant_ker (hX : OkaProperty X) (hF : IsInvariantSubquotient F)
    (hG : IsInvariantSubquotient G) {φ : Subquotient.Hom F G} {d : ℤ} (hφ : IsHomMatrix φ.A d) :
    IsInvariantSubquotient (Subquotient.ker hX φ) :=
  ⟨hF.1.inf (hG.2.comap G.coherent_N hφ), hF.2⟩

/-- The image of a homogeneous morphism of invariant subquotients is invariant. -/
theorem isInvariant_im (hF : IsInvariantSubquotient F) (hG : IsInvariantSubquotient G)
    {φ : Subquotient.Hom F G} {d : ℤ} (hφ : IsHomMatrix φ.A d) :
    IsInvariantSubquotient (Subquotient.im φ) :=
  ⟨hG.2.sup (hF.1.map F.coherent_M hφ), hG.2⟩

/-- The cokernel of a homogeneous morphism of invariant subquotients is invariant. -/
theorem isInvariant_coker (hF : IsInvariantSubquotient F) (hG : IsInvariantSubquotient G)
    {φ : Subquotient.Hom F G} {d : ℤ} (hφ : IsHomMatrix φ.A d) :
    IsInvariantSubquotient (Subquotient.coker φ) :=
  ⟨hG.1, hG.2.sup (hF.1.map F.coherent_M hφ)⟩

end SGPT.GAGA.PN
