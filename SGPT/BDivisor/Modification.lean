import SGPT.BDivisor.ClassPullback
import SGPT.PSH.CompactSmoothCommonModel
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

/-!
# The directed system of modifications of a compact complex manifold

The b-divisors of `chap:bdiv` are indexed by the modifications `π : Y → X` of `X`, partially
preordered by domination: `π'` *dominates* `π` if `π' = π ∘ g` for a holomorphic `g`.  Limits
"`lim_{π : Y → X}`" (`def:volb`, `thm:pobbd`) are taken along this directed preorder.

Main declarations:

* `SGPT.BDivisor.Modification n X` — a complex manifold `Y` of dimension `n` with a proper
  holomorphic bimeromorphic map `π : Y → X` (the project's `IsAnalyticModification`, which
  provides closed nowhere dense analytic exceptional sets and a holomorphic inverse off them);
* `SGPT.BDivisor.Modification.Dominates` and the preorder `π ≤ π'` (`π'` dominates `π`);
* `SGPT.BDivisor.Modification.Dominates.unique` — the dominating morphism is unique, so
  "`π'` dominates `π` through `g`" determines `g`;
* `SGPT.BDivisor.Modification.Dominates.isAnalyticModification` — the dominating morphism is
  itself a modification;
* `SGPT.BDivisor.Modification.instIsDirected` — for `X` compact and connected, any two
  modifications are dominated by a third (a resolved common model, proved in
  `SGPT.PSH.CompactSmoothCommonModel`);
* `SGPT.BDivisor.Modification.classPullbackOfLE` — the class pull-back `g^*` along the
  domination morphism, with its functoriality: the direct system
  `π ↦ H^{1,1}(Y_π, ℝ)` along pull-backs.

Convention.  The book (`Conventions`) calls a modification a proper bimeromorphic morphism that is
locally a finite composition of blow-ups with smooth centres.  Here every proper holomorphic
bimeromorphic map from a complex manifold is allowed, as in the project's bimeromorphic-invariance
results (`prop:biminv`, `cor:dSconv_bimero`). The book's modifications form a subfamily, cofinal by
Hironaka's Chow lemma (`thm:HironakaChow`, not formalized), so limits along both systems agree once
that lemma is available.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (n X) in
/-- A modification of `X`: a complex manifold `Y` (same dimension `n`) with a proper holomorphic
bimeromorphic map `π : Y → X`. -/
structure Modification where
  /-- The model `Y`. -/
  carrier : Type u
  [instTopologicalSpace : TopologicalSpace carrier]
  [instChartedSpace : ChartedSpace (ComplexModel n) carrier]
  [instIsComplexManifold : IsComplexManifold n carrier]
  /-- The structure map `π : Y → X`. -/
  map : carrier → X
  /-- `π` is proper, holomorphic and bimeromorphic. -/
  isAnalyticModification : IsAnalyticModification (n := n) map

attribute [instance] Modification.instTopologicalSpace Modification.instChartedSpace
  Modification.instIsComplexManifold

namespace Modification

/-- The identity map `X → X` is a modification. -/
theorem isAnalyticModification_id : IsAnalyticModification (n := n) (id : X → X) := by
  refine ⟨contMDiff_id, isProperMap_id, ∅, ∅, id, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, preimage_empty, contMDiff_id.contMDiffOn,
    (fun _ _ => rfl), (fun _ _ => rfl)⟩

/-- The trivial modification `id : X → X`, the root of the system. -/
def root : Modification n X where
  carrier := X
  map := id
  isAnalyticModification := isAnalyticModification_id

/-- The model of a modification of a compact space is compact. -/
instance instCompactSpace [CompactSpace X] (π : Modification n X) : CompactSpace π.carrier :=
  AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification
    π.isAnalyticModification

/-- The structure map is holomorphic. -/
theorem contMDiff_map (π : Modification n X) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π.map :=
  π.isAnalyticModification.1

/-- `π'` *dominates* `π` if `π' = π ∘ g` for a holomorphic map `g : Y' → Y`. -/
def Dominates (π' π : Modification n X) : Prop :=
  ∃ g : π'.carrier → π.carrier,
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g ∧ π.map ∘ g = π'.map

theorem Dominates.refl (π : Modification n X) : π.Dominates π :=
  ⟨id, contMDiff_id, rfl⟩

theorem Dominates.trans {π'' π' π : Modification n X} (h₂ : π''.Dominates π')
    (h₁ : π'.Dominates π) : π''.Dominates π := by
  obtain ⟨g₂, hg₂, hc₂⟩ := h₂
  obtain ⟨g₁, hg₁, hc₁⟩ := h₁
  exact ⟨g₁ ∘ g₂, hg₁.comp hg₂, by rw [← Function.comp_assoc, hc₁, hc₂]⟩

/-- Domination preorder: `π ≤ π'` iff `π'` dominates `π`. Limits over modifications are taken
along this preorder. -/
instance instPreorder : Preorder (Modification n X) where
  le π π' := π'.Dominates π
  le_refl π := Dominates.refl π
  le_trans _ _ _ h₁ h₂ := Dominates.trans h₂ h₁

theorem le_iff_dominates {π π' : Modification n X} : π ≤ π' ↔ π'.Dominates π := Iff.rfl

/-- Every modification dominates the root `id : X → X`. -/
theorem root_le (π : Modification n X) : root ≤ π :=
  ⟨π.map, π.contMDiff_map, rfl⟩

/-- **Uniqueness of the dominating morphism**: two holomorphic maps `g₁ g₂ : Y' → Y` with
`π ∘ g₁ = π ∘ g₂ = π'` coincide, since they agree off the nowhere dense preimage of the
indeterminacy set of `π⁻¹`. -/
theorem Dominates.unique {π' π : Modification n X} {g₁ g₂ : π'.carrier → π.carrier}
    (hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁)
    (hg₂ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₂)
    (h₁ : π.map ∘ g₁ = π'.map) (h₂ : π.map ∘ g₂ = π'.map) : g₁ = g₂ := by
  obtain ⟨A, B, s, _hAc, _hAa, _hAi, _hBc, _hBa, hBi, hpre, _hs, _hright, hleft⟩ :=
    π.isAnalyticModification.2.2
  have hthin : interior (π'.map ⁻¹' B) = ∅ :=
    AnalyticModelDomination.interior_preimage_eq_empty_of_isAnalyticModification
      π'.isAnalyticModification hBi
  have hdense : Dense (π'.map ⁻¹' B)ᶜ := interior_eq_empty_iff_dense_compl.mp hthin
  refine Continuous.ext_on hdense hg₁.continuous hg₂.continuous ?_
  intro z hz
  have hA (g : π'.carrier → π.carrier) (hg : π.map ∘ g = π'.map) : g z ∉ A := by
    intro hgz
    rw [← hpre] at hgz
    apply hz
    change π'.map z ∈ B
    rw [← hg]
    exact hgz
  have e₁ : s (π'.map z) = g₁ z := by
    rw [← h₁]
    exact hleft _ (hA g₁ h₁)
  have e₂ : s (π'.map z) = g₂ z := by
    rw [← h₂]
    exact hleft _ (hA g₂ h₂)
  exact e₁.symm.trans e₂

/-- The (unique) dominating morphism `g : Y' → Y` of `π ≤ π'`. -/
def homOfLE {π π' : Modification n X} (h : π ≤ π') : π'.carrier → π.carrier :=
  Classical.choose h

theorem contMDiff_homOfLE {π π' : Modification n X} (h : π ≤ π') :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (homOfLE h) :=
  (Classical.choose_spec h).1

theorem map_comp_homOfLE {π π' : Modification n X} (h : π ≤ π') :
    π.map ∘ homOfLE h = π'.map :=
  (Classical.choose_spec h).2

/-- Any holomorphic map over `X` is the dominating morphism. -/
theorem homOfLE_eq {π π' : Modification n X} (h : π ≤ π') {g : π'.carrier → π.carrier}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hc : π.map ∘ g = π'.map) : homOfLE h = g :=
  Dominates.unique (contMDiff_homOfLE h) hg (map_comp_homOfLE h) hc

theorem homOfLE_refl (π : Modification n X) : homOfLE (le_refl π) = id :=
  homOfLE_eq _ contMDiff_id rfl

theorem homOfLE_trans {π π' π'' : Modification n X} (h₁ : π ≤ π') (h₂ : π' ≤ π'') :
    homOfLE (h₁.trans h₂) = homOfLE h₁ ∘ homOfLE h₂ :=
  homOfLE_eq _ ((contMDiff_homOfLE h₁).comp (contMDiff_homOfLE h₂)) (by
    rw [← Function.comp_assoc, map_comp_homOfLE, map_comp_homOfLE])

/-- The dominating morphism is itself a modification. -/
theorem Dominates.isAnalyticModification {π π' : Modification n X} (h : π ≤ π') :
    IsAnalyticModification (n := n) (homOfLE h) :=
  AnalyticModelDomination.isAnalyticModification_of_holomorphic_over
    π.isAnalyticModification π'.isAnalyticModification (contMDiff_homOfLE h)
    (map_comp_homOfLE h)

/-- **Directedness**: for `X` compact and connected, two modifications are dominated by a common
one (a compact connected resolved model of the main component of the fibre product). -/
instance instIsDirected [ConnectedSpace X] [CompactSpace X] :
    IsDirected (Modification n X) (· ≤ ·) where
  directed π₀ π₁ := by
    obtain ⟨Z, iT, iC, iM, _iConn, _iComp, g₀, g₁, hg₀, hg₁, hcomm⟩ :=
      SGPT.PSH.CompactSmoothCommonModel.exists_actual_compact_smooth_common_model
        π₀.isAnalyticModification π₁.isAnalyticModification
    let ρ : Modification n X :=
      { carrier := Z
        map := π₀.map ∘ g₀
        isAnalyticModification :=
          AnalyticModificationComposition.isAnalyticModification_comp
            π₀.isAnalyticModification hg₀ }
    exact ⟨ρ, ⟨g₀, hg₀.1, rfl⟩, ⟨g₁, hg₁.1, hcomm.symm⟩⟩

/-- The class pull-back `g^* : H^{1,1}(Y,ℝ) → H^{1,1}(Y',ℝ)` along the dominating morphism of
`π ≤ π'`. -/
def classPullbackOfLE {π π' : Modification n X} (h : π ≤ π') :
    RealBottChern n π.carrier →ₗ[ℝ] RealBottChern n π'.carrier :=
  classPullback (contMDiff_homOfLE h)

/-- The pull-back along a domination is the pull-back along any holomorphic map over `X`. -/
theorem classPullbackOfLE_eq {π π' : Modification n X} (h : π ≤ π')
    {g : π'.carrier → π.carrier}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hc : π.map ∘ g = π'.map) (α : RealBottChern n π.carrier) :
    classPullbackOfLE h α = classPullback hg α :=
  classPullback_congr (homOfLE_eq h hg hc) _ _ α

theorem classPullbackOfLE_refl (π : Modification n X) (α : RealBottChern n π.carrier) :
    classPullbackOfLE (le_refl π) α = α := by
  rw [classPullbackOfLE_eq (le_refl π) contMDiff_id rfl]
  exact classPullback_id α

/-- Functoriality of the direct system of classes along pull-backs. -/
theorem classPullbackOfLE_trans {π π' π'' : Modification n X} (h₁ : π ≤ π') (h₂ : π' ≤ π'')
    (α : RealBottChern n π.carrier) :
    classPullbackOfLE (h₁.trans h₂) α = classPullbackOfLE h₂ (classPullbackOfLE h₁ α) := by
  rw [classPullbackOfLE_eq (h₁.trans h₂)
    ((contMDiff_homOfLE h₁).comp (contMDiff_homOfLE h₂))
    (by rw [← Function.comp_assoc, map_comp_homOfLE, map_comp_homOfLE])]
  exact classPullback_comp (contMDiff_homOfLE h₁) (contMDiff_homOfLE h₂) α

/-- The pull-back from the root `X` is the pull-back along the structure map. -/
theorem classPullbackOfLE_root (π : Modification n X) (α : RealBottChern n X) :
    classPullbackOfLE (root_le π) α = classPullback π.contMDiff_map α :=
  classPullbackOfLE_eq (root_le π) π.contMDiff_map rfl α

end Modification

end SGPT.BDivisor
