import SGPT.PSH.CompactSmoothCommonModel
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

set_option autoImplicit false

noncomputable section

/-!
# A Kähler common model of two analytic modifications

Source: blueprint node `tok:gentle-sum` (the step "Z is Kähler"): two analytic modifications
`f₀ : Y₀ → X`, `f₁ : Y₁ → X` from compact Kähler manifolds have a common compact connected
Kähler model `Z` with analytic modifications `ℓ₀ : Z → Y₀`, `ℓ₁ : Z → Y₁`, `f₀ ∘ ℓ₀ = f₁ ∘ ℓ₁`.

The model is the one of `SGPT.PSH.CompactSmoothCommonModel` (the strict transform of the
main component of the fibre product in a blow-up sequence of `Y₀ × Y₁`); it is Kähler because
products of Kähler manifolds are Kähler (`prodKahlerBackground`), blow-ups along closed
submanifolds of compact Kähler manifolds are Kähler (Blanchard,
`compactSpace_and_kahler_of_isBlowupSequence`), and closed submanifolds of Kähler manifolds are
Kähler (`SubmanifoldKahlerRestriction.kahlerBackground`). The proof repeats the construction of
`exists_actual_compact_smooth_common_base_model`, keeping track of the Kähler forms.
-/

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending AnalyticModificationLocalDiscrepancy
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

universe u

variable {n : ℕ} {X Y₀ Y₁ : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X] [CompactSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- Two analytic modifications from compact Kähler manifolds have a compact connected smooth
**Kähler** common model, with proper holomorphic maps to both and an analytic modification to
the base. -/
theorem exists_kahler_compact_smooth_common_base_model
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁)
    (hK₀ : Nonempty (KahlerBackground n Y₀)) (hK₁ : Nonempty (KahlerBackground n Y₁)) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀ ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ ∧
      IsProperMap g₀ ∧ IsProperMap g₁ ∧
      IsAnalyticModification (n := n) (c₀ ∘ g₀) ∧ c₀ ∘ g₀ = c₁ ∘ g₁ ∧
      Nonempty (KahlerBackground n Z) := by
  classical
  obtain ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀, hs₁, hright₀, hright₁,
    hleft₀, hleft₁, V, hVdim, _hVcomponent, hVclosure, _hVF, hGreg, _hGimage,
    Xt, instTop, instChart, instMfd, μ, hμ, hiso, hWn, cs, hcanon, hcs, _hincl,
    ρ, _hρeq, _hρproper, _hρsurj, hg₀, hg₁, hgp₀, hgp₁, hbase, _hGlift⟩ :=
    AnalyticCompactMainComponentCanonicalLift.exists_actual_compact_mainComponent_canonical_lift
      hc₀ hc₁
  subst cs
  let W : Set Xt := strictTransform (n + n) μ V.carrier
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right n n) hWn.2.2
  let := hcs
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWn.2.1
  let : CompactSpace Y₀ :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc₀
  let : CompactSpace Y₁ :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc₁
  let : CompactSpace Xt :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ).1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hWn.1.isCompact
  let : Nonempty Xt := ⟨hWn.2.1.nonempty.choose⟩
  let g₀ : W → Y₀ := fun z => (μ z.val).1
  let g₁ : W → Y₁ := fun z => (μ z.val).2
  let π : W → X := c₀ ∘ g₀
  have hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π :=
    hc₀.1.comp hg₀
  have hπproper : IsProperMap π := hc₀.2.1.comp hgp₀
  let G : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B}
  let γ : X → Y₀ × Y₁ := fun x => (s₀ x, s₁ x)
  have hγG (x : X) (hx : x ∉ B) : γ x ∈ G := by
    change c₀ (s₀ x) = c₁ (s₁ x) ∧ c₀ (s₀ x) ∉ B
    rw [hright₀ x hx, hright₁ x hx]
    exact ⟨rfl, hx⟩
  have hGoff {p : Y₀ × Y₁} (hp : p ∈ G) : p ∉ singularLocus V := by
    intro hs
    apply hs.2
    change RegularAtDim (n := n + n) V.carrier p V.dim
    rw [hVdim]
    exact hGreg p hp
  have hSingc : IsClosed (singularLocus V) := EmbeddedFromResolution.isClosed_singularLocus V
  let U : TopologicalSpace.Opens X := ⟨Bᶜ, hBc.isOpen_compl⟩
  let O : TopologicalSpace.Opens (Y₀ × Y₁) := ⟨(singularLocus V)ᶜ, hSingc.isOpen_compl⟩
  let R : Y₀ × Y₁ → Xt := ModificationMassInvariance.invOver μ (singularLocus V)ᶜ
  have hR : ContMDiffOn 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞
      R (singularLocus V)ᶜ :=
    SGPT.Okounkov.contMDiffOn_invOver_of_isIsomorphismOver hμ.contMDiff hSingc.isOpen_compl hiso
  have hRO : ContMDiff 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞
      (fun x : O => R x.val) := by
    intro x
    exact (hR.contMDiffAt (hSingc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  have hs₀U : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : U => s₀ x.val) := by
    intro x
    exact (hs₀.contMDiffAt (hBc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  have hs₁U : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : U => s₁ x.val) := by
    intro x
    exact (hs₁.contMDiffAt (hBc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  have hγU : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞
      (fun x : U => γ x.val) := ProductComplexManifold.contMDiff_prodMk hs₀U hs₁U
  let k : U → O := fun x => ⟨γ x.val, hGoff (hγG x.val x.property)⟩
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ k :=
    BlowupRestrictOpen.contMDiff_opens_mk hγU (fun x => hGoff (hγG x.val x.property))
  have hμR (p : Y₀ × Y₁) (hp : p ∉ singularLocus V) : μ (R p) = p :=
    (ModificationMassInvariance.invOver_mem hiso hp).2
  have hland (x : U) : R (γ x.val) ∈ W := by
    apply subset_closure
    refine ⟨?_, ?_⟩
    · change μ (R (γ x.val)) ∈ V.carrier
      rw [hμR _ (k x).property, hVclosure]
      exact subset_closure (hγG x.val x.property)
    · exact fun he => Set.disjoint_left.mp hiso.2
        (ModificationMassInvariance.invOver_mem hiso (k x).property).1 he
  let σ : U → W := fun x => ⟨R (γ x.val), hland x⟩
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_add_right n n) hWn.2.2
      (hRO.comp hk) hland
  have hμσ (x : U) : μ (σ x).val = γ x.val := hμR _ (k x).property
  have hπσ (x : U) : π (σ x) = x.val := by
    change c₀ (μ (σ x).val).1 = x.val
    rw [hμσ x]
    exact hright₀ x.val x.property
  have hμGraph (z : W) (hz : π z ∉ B) : μ z.val = γ (π z) := by
    apply Prod.ext
    · exact (hleft₀ (μ z.val).1 hz).symm
    · change (μ z.val).2 = s₁ (π z)
      have heq : π z = c₁ (μ z.val).2 := hbase z
      rw [heq]
      exact (hleft₁ (μ z.val).2 (heq ▸ hz)).symm
  have hπinj {w z : W} (hw : π w ∉ B) (hz : π z ∉ B)
      (heq : π w = π z) : w = z := by
    have hwG : μ w.val ∈ G := by rw [hμGraph w hw]; exact hγG (π w) hw
    have hzG : μ z.val ∈ G := by rw [hμGraph z hz]; exact hγG (π z) hz
    exact Subtype.ext (hiso.1.injOn (hGoff hwG) (hGoff hzG) (by
      rw [hμGraph w hw, hμGraph z hz, heq]))
  have hsubrange : Bᶜ ⊆ range π := fun x hx => ⟨σ ⟨x, hx⟩, hπσ ⟨x, hx⟩⟩
  have hdense : Dense (range π) := (interior_eq_empty_iff_dense_compl.mp hBi).mono hsubrange
  have hrange : range π = univ := hπproper.isClosed_range.closure_eq.symm.trans hdense.closure_eq
  have hsurj : Function.Surjective π := by
    intro x
    have hx : x ∈ range π := by rw [hrange]; exact mem_univ x
    exact hx
  let t : X → W := fun x => Classical.choose (hsurj x)
  have hright (x : X) : π (t x) = x := Classical.choose_spec (hsurj x)
  have hsame : (fun x : U => t x.val) = σ := by
    funext x
    exact hπinj (w := t x.val) (z := σ x)
      (by rw [hright x.val]; exact x.property)
      (by rw [hπσ x]; exact x.property)
      ((hright x.val).trans (hπσ x).symm)
  have ht : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ t Bᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : U => t x.val) := hsame.symm ▸ hσ
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest (⟨x, hx⟩ : U))).contMDiffWithinAt
  let A : Set W := π ⁻¹' B
  have hAc : IsClosed A := hBc.preimage hπ.continuous
  have hAa : IsComplexAnalyticSubset (n := n) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ hBa
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hBi).nonempty
  have htA : t x ∉ A := by
    change π (t x) ∉ B
    rw [hright x]
    exact hx
  have hAproper : A ≠ univ := fun heq => htA (heq.symm ▸ mem_univ (t x))
  have hAi : interior A = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    exact fun hint => hAproper (hAa.eq_univ_of_interior_nonempty hint)
  have hπmod : IsAnalyticModification (n := n) π := by
    refine ⟨hπ, hπproper, A, B, t, hAc, hAa, hAi, hBc, hBa, hBi, rfl,
      ht, (fun x _ => hright x), ?_⟩
    intro z hz
    exact hπinj (w := t (π z)) (z := z)
      (by rw [hright (π z)]; exact hz) hz (hright (π z))
  obtain ⟨ω₀⟩ := hK₀
  obtain ⟨ω₁⟩ := hK₁
  have hKXt : Nonempty (KahlerBackground (n + n) Xt) :=
    (LocusProperties.compactSpace_and_kahler_of_isBlowupSequence
      ⟨ProductComplexManifold.prodKahlerBackground ω₀ ω₁⟩ μ hμ).2
  obtain ⟨ωt⟩ := hKXt
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g₀, g₁, hg₀, hg₁, hgp₀, hgp₁, hπmod, ?_,
    ⟨SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_add_right n n) hWn.2.2 ωt⟩⟩
  funext z
  exact hbase z

/-- **Kähler common model** (blueprint `tok:gentle-sum`): two analytic modifications
`c₀ : Y₀ → X`, `c₁ : Y₁ → X` from Kähler manifolds have a compact connected Kähler common
model `Z`, with analytic modifications `g₀ : Z → Y₀`, `g₁ : Z → Y₁` and `c₀ ∘ g₀ = c₁ ∘ g₁`. -/
theorem exists_kahler_compact_smooth_common_model
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁)
    (hK₀ : Nonempty (KahlerBackground n Y₀)) (hK₁ : Nonempty (KahlerBackground n Y₁)) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
      IsAnalyticModification (n := n) (c₀ ∘ g₀) ∧ c₀ ∘ g₀ = c₁ ∘ g₁ ∧
      Nonempty (KahlerBackground n Z) := by
  obtain ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁,
    hg₀, hg₁, _hgp₀, _hgp₁, hπZ, hover, hKZ⟩ :=
    exists_kahler_compact_smooth_common_base_model hc₀ hc₁ hK₀ hK₁
  exact ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁,
    AnalyticModelDomination.isAnalyticModification_of_holomorphic_over hc₀ hπZ hg₀ rfl,
    AnalyticModelDomination.isAnalyticModification_of_holomorphic_over hc₁ hπZ hg₁ hover.symm,
    hπZ, hover, hKZ⟩

end SGPT.Okounkov.TranscendentalCore
