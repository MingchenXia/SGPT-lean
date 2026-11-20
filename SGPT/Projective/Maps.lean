import SGPT.Projective.Basic
import SGPT.Toric.ProjectiveLineNativeManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Holomorphic maps into `ℙᴺ`

* `SGPT.Projective.ComplexProjectiveSpace.contMDiffAt_of_lift`: a map `f : M → ℙᴺ` which near
  `x` is `y ↦ [F(y)]` for a holomorphic nonvanishing homogeneous lift `F` is holomorphic at `x`;
* `linearMap A`: the map `ℙᴹ → ℙᴺ`, `[v] ↦ [A v]`, of an injective linear map
  `A : ℂ^{M+1} → ℂ^{N+1}` (linear subspaces `ℙᴹ ⊆ ℙᴺ`, e.g. lines in `ℙ²`), and its
  holomorphy;
* `fromNativeLine`: the identity map from the native projective line `ℙ¹` of `SGPT.Toric`
  (atlas `{[z : 1]}`, `{[1 : z]}`) to `ℙ¹ = ComplexProjectiveSpace 1`, which is holomorphic; with
  it, `linearMap A ∘ fromNativeLine` embeds the native `ℙ¹` as a line in `ℙᴺ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

namespace SGPT.Projective.ComplexProjectiveSpace

variable {N : ℕ}

section Lift

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]

/-- A map into `ℙᴺ` with a local holomorphic nonvanishing homogeneous lift is holomorphic. -/
theorem contMDiffAt_of_lift {f : M → ComplexProjectiveSpace N} {x : M}
    {F : M → Fin (N + 1) → ℂ}
    (hF : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, Fin (N + 1) → ℂ) ∞ F x) (hx : F x ≠ 0)
    (hfF : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk (F y) hy) :
    ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ f x := by
  obtain ⟨j, hj⟩ : ∃ j, F x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hFj : ∀ᶠ y in 𝓝 x, F y j ≠ 0 :=
    ((continuous_apply j).continuousAt.comp hF.continuousAt).eventually_ne hj
  have hG : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞
      (fun y => affineRatio j (F y)) x :=
    (contDiffAt_affineRatio j hj).contMDiffAt.comp x hF
  have hsymm : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ (affineChart j).symm
      (affineRatio j (F x)) :=
    (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel N)) (n := ∞)
        (affineChart_mem_atlas j))).contMDiffAt (by simp)
  refine (hsymm.comp x hG).congr_of_eventuallyEq ?_
  filter_upwards [hfF, hFj] with y ⟨hy, hfy⟩ hyj
  rw [hfy]
  exact mk_eq_affinePoint j hy hyj

/-- A map into `ℙᴺ` with a global holomorphic nonvanishing homogeneous lift is holomorphic. -/
theorem contMDiff_of_lift {f : M → ComplexProjectiveSpace N} {F : M → Fin (N + 1) → ℂ}
    (hF : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, Fin (N + 1) → ℂ) ∞ F) (hF0 : ∀ x, F x ≠ 0)
    (hfF : ∀ x, f x = mk (F x) (hF0 x)) :
    ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ f := fun x =>
  contMDiffAt_of_lift (hF x) (hF0 x) (Eventually.of_forall fun y => ⟨hF0 y, hfF y⟩)

end Lift

/-! ### The chart lift -/

theorem contMDiffAt_affineChart (i : Fin (N + 1)) {x : ComplexProjectiveSpace N}
    (hx : x ∈ (affineChart i).source) :
    ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ (affineChart i) x :=
  contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel N)) (n := ∞)
      (affineChart_mem_atlas i)) hx

theorem eq_mk_affineLift_affineChart (i : Fin (N + 1)) {y : ComplexProjectiveSpace N}
    (hy : y ∈ (affineChart i).source) :
    y = mk (affineLift i (affineChart i y)) (affineLift_ne_zero i _) := by
  have h := (affineChart i).left_inv hy
  rw [affineChart_symm_apply] at h
  exact h.symm

/-! ### Linear maps -/

variable {M : ℕ}

/-- The map `ℙᴹ → ℙᴺ`, `[v] ↦ [A v]`, of an injective linear map. -/
def linearMap (A : (Fin (M + 1) → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ)) (hA : Function.Injective A) :
    ComplexProjectiveSpace M → ComplexProjectiveSpace N :=
  Projectivization.map A hA

theorem linearMap_mk (A : (Fin (M + 1) → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ)) (hA : Function.Injective A)
    (v : Fin (M + 1) → ℂ) (hv : v ≠ 0) :
    linearMap A hA (mk v hv) = mk (A v) (by simpa using hA.ne hv) :=
  Projectivization.map_mk A hA v hv

/-- Linear maps of projective spaces are holomorphic. -/
theorem contMDiff_linearMap (A : (Fin (M + 1) → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ))
    (hA : Function.Injective A) :
    ContMDiff 𝓘(ℂ, ComplexModel M) 𝓘(ℂ, ComplexModel N) ∞ (linearMap A hA) := by
  intro x
  let i := chartIndex x
  have hxi : x ∈ (affineChart i).source := mem_affineChart_chartIndex x
  have hAne : ∀ z : ComplexModel M, A (affineLift i z) ≠ 0 := fun z => by
    simpa using hA.ne (affineLift_ne_zero i z)
  have hlin : ContDiff ℂ ∞ (fun z : ComplexModel M => A (affineLift i z)) := by
    have hc : ContDiff ℂ ∞ (A.toContinuousLinearMap : (Fin (M + 1) → ℂ) → (Fin (N + 1) → ℂ)) :=
      (LinearMap.toContinuousLinearMap A).contDiff
    exact hc.comp (contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
      (differentiable_affineLift i).differentiableOn isOpen_univ))
  have hF : ContMDiffAt 𝓘(ℂ, ComplexModel M) 𝓘(ℂ, Fin (N + 1) → ℂ) ∞
      (fun y => A (affineLift i (affineChart i y))) x :=
    hlin.contMDiff.contMDiffAt.comp x (contMDiffAt_affineChart i hxi)
  refine contMDiffAt_of_lift hF (hAne _) ?_
  filter_upwards [(affineChart i).open_source.mem_nhds hxi] with y hy
  refine ⟨hAne _, ?_⟩
  conv_lhs => rw [eq_mk_affineLift_affineChart i hy]
  exact linearMap_mk A hA _ _

/-! ### The native projective line -/

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The identity map from the native projective line of `SGPT.Toric` (affine charts
`[z : 1]`, `[1 : z]` via `OnePoint ℂ`) to `ℙ¹ = ComplexProjectiveSpace 1`. -/
def fromNativeLine : P1 → ComplexProjectiveSpace 1 := id

theorem fromNativeLine_mk (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    fromNativeLine (Projectivization.mk ℂ v hv) = mk v hv := rfl

/-- The identity map from the native `ℙ¹` to `ℙ¹ = ComplexProjectiveSpace 1` is holomorphic. -/
theorem contMDiff_fromNativeLine :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ fromNativeLine := by
  intro x
  obtain ⟨b, hb⟩ := SGPT.Toric.projectiveLineAtlas.cover x
  have hb' : x ∈ (SGPT.Toric.projectiveModelChart b).source := hb
  have hchart : ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞
      (SGPT.Toric.projectiveModelChart b) x :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 1)) (n := ∞)
        (SGPT.Toric.projectiveNativeChart b).property) hb'
  have hlift : ContDiff ℂ ∞ (SGPT.Toric.projectiveAffineLift b) := by
    have hd : Differentiable ℂ (SGPT.Toric.projectiveAffineLift b) := by
      cases b
      · refine differentiable_pi.mpr fun m => ?_
        fin_cases m
        · exact SGPT.Toric.projectiveModelEquiv.symm.differentiable
        · exact differentiable_const _
      · refine differentiable_pi.mpr fun m => ?_
        fin_cases m
        · exact differentiable_const _
        · exact SGPT.Toric.projectiveModelEquiv.symm.differentiable
    exact contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex hd.differentiableOn
      isOpen_univ)
  have hF : ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, Fin (1 + 1) → ℂ) ∞
      (fun y => SGPT.Toric.projectiveAffineLift b (SGPT.Toric.projectiveModelChart b y)) x :=
    hlift.contMDiff.contMDiffAt.comp x hchart
  refine contMDiffAt_of_lift hF (SGPT.Toric.projectiveAffineLift_ne_zero b _) ?_
  filter_upwards [(SGPT.Toric.projectiveModelChart b).open_source.mem_nhds hb'] with y hy
  refine ⟨SGPT.Toric.projectiveAffineLift_ne_zero b _, ?_⟩
  have h := (SGPT.Toric.projectiveModelChart b).left_inv hy
  exact h.symm.trans (SGPT.Toric.projectiveModelChart_symm_eq_mk b _)

end SGPT.Projective.ComplexProjectiveSpace
