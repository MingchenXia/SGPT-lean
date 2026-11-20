import SGPT.Okounkov.OF12AmbientProjectiveTrace
import SGPT.GAGA.ChowBlEmbed
import SGPT.GAGA.SmoothFlagsScheme
import SGPT.Projective.OkoNov16OriginalRestrictedGoodInverse
import SGPT.Projective.OriginalNativePositiveChowGraph
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedExceptional
import SGPT.Foundations.Analysis.Pending.StokesSingularLocusAnalytic
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-! Embedded resolution of the actual projective image and its algebraic readback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Projective SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.BDivisor.GM
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FirstPass.BlowupSequences FirstPass.RegularLocusDense FirstPass.NonKahlerLocus
open FirstPass.HolomorphicMaps
open Pending.RankDegeneracy
open Pending.StokesSingularLocusAnalytic (injective_fderiv_toFun)
open Pending.HironakaEmbeddedAnalytic Pending.SubmanifoldChartedSpace
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra SGPT.Toric.monomialProjectiveTopology

local instance embeddedPointTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance embeddedPointCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance embeddedPointManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-- Choose a dimension witnessed at an actual regular point of the ambient projective image. -/
theorem exists_ambientPoint_subvariety :
    ∃ V : ClosedIrreducibleAnalyticSubvariety E.ambientDimension
        (ComplexProjectiveSpace E.ambientDimension), V.carrier = range (ambientPoint E) := by
  have h := analyticallyIrreducible_ambientPoint_range E
  obtain ⟨x, hx⟩ := h.nonempty
  obtain ⟨y, _, d, hy⟩ := exists_regularAtDim_mem_nhds h.analytic hx Filter.univ_mem
  exact ⟨⟨range (ambientPoint E), h.analytic.isClosed, h, d, hy.1, ⟨y, hy⟩⟩, rfl⟩

private theorem projective_id_holomorphicEmbedding (n : ℕ) :
    IsHolomorphicEmbedding (n := n) (id : ComplexProjectiveSpace n → ComplexProjectiveSpace n) := by
  apply originalEmbedding_of_native_mfderiv contMDiff_id Function.injective_id
  intro x
  rw [mfderiv_id]
  exact fun _ _ h => h

/-- The embedded resolution of the actual complex-point image has compact projective ambient
space and a smooth connected strict transform. -/
theorem exists_embedded_projective_resolution_of_ambientPoint :
    ∃ (V : ClosedIrreducibleAnalyticSubvariety E.ambientDimension
        (ComplexProjectiveSpace E.ambientDimension))
      (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (ComplexModel E.ambientDimension) M)
      (_ : IsComplexManifold E.ambientDimension M)
      (σ : M → ComplexProjectiveSpace E.ambientDimension)
      (_ : IsBlowupSequence E.ambientDimension (ComplexProjectiveSpace E.ambientDimension) M σ)
      (N : ℕ) (Ψ : M → ComplexProjectiveSpace N),
      V.carrier = range (ambientPoint E) ∧ CompactSpace M ∧
      IsHolomorphicEmbedding (n := E.ambientDimension) Ψ ∧
      IsIsomorphismOver E.ambientDimension σ (singularLocus V)ᶜ ∧
      IsClosedConnectedSubmanifold E.ambientDimension
        (strictTransform E.ambientDimension σ V.carrier) V.dim := by
  obtain ⟨V, hV⟩ := exists_ambientPoint_subvariety E
  obtain ⟨M, tM, cM, mM, σ, hσ, hiso, hsm⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  let := tM
  let := cM
  let := mM
  obtain ⟨hc, N, Ψ, hΨ⟩ := exists_isHolomorphicEmbedding_of_isBlowupSequence
    (projective_id_holomorphicEmbedding E.ambientDimension) hσ
  exact ⟨V, M, tM, cM, mM, σ, hσ, N, Ψ, hV, hc, hΨ, hiso, hsm⟩

private theorem strictTransform_embedding
    {n d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {S : Set M}
    (hd : d ≤ n) (hS : ∀ x ∈ S, RegularAtDim (n := n) S x d)
    {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ) :
    letI := chartedSpace hd hS
    letI := isComplexManifold_chartedSpace hd hS
    IsHolomorphicEmbedding (n := d) (Ψ ∘ (Subtype.val : S → M)) := by
  let := chartedSpace hd hS
  let := isComplexManifold_chartedSpace hd hS
  have hΨ' := SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ
  have hval := contMDiff_val hd hS
  apply originalEmbedding_of_native_mfderiv (hΨ'.comp hval) (hΨ.injective.comp Subtype.val_injective)
  intro x
  have hΨdiff := (hΨ' x.val).mdifferentiableAt (by simp)
  have hvaldiff := (hval x).mdifferentiableAt (by simp)
  have hΨinj : Function.Injective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) Ψ x.val) := by
    rw [SGPT.Bergman.SiuKodaira.mfderiv_eq_fderiv_complexChartAt hΨdiff]
    change Function.Injective
      (fderiv ℂ (chartMap Ψ x.val (ComplexProjectiveSpace.chartIndex (Ψ x.val)))
        ((complexChartAt (n := n) x.val).val x.val))
    exact hΨ.immersion x.val (ComplexProjectiveSpace.chartIndex (Ψ x.val))
      (ComplexProjectiveSpace.mem_affineChart_chartIndex _)
  have hvalinj : Function.Injective
      (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) (Subtype.val : S → M) x) := by
    let e := complexChartAt (n := d) x
    let e' := complexChartAt (n := n) x.val
    have hz : e.val x ∈ coordinateDomain (Subtype.val : S → M) e e' :=
      mem_coordinateDomain (mem_complexChartAt_source x) (mem_complexChartAt_source x.val)
    have hinj := Pending.SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val
      hd hS e e' (e.val x) hz
    rw [coordinateMap_fderiv_restrictScalars hval e e' hz] at hinj
    rw [SGPT.Bergman.SiuKodaira.mfderiv_eq_fderiv_complexChartAt hvaldiff]
    change Function.Injective (fderiv ℂ (coordinateMap (Subtype.val : S → M) e e') (e.val x))
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using hinj
  rw [mfderiv_comp x hΨdiff hvaldiff]
  intro a b hab
  exact hvalinj (hΨinj hab)

/-- The embedded strict transform has an integral smooth projective algebraic model,
and its map to the original projective image is induced by a scheme morphism. -/
theorem exists_projective_model_of_embedded_resolution :
    ∃ (V : ClosedIrreducibleAnalyticSubvariety E.ambientDimension
        (ComplexProjectiveSpace E.ambientDimension))
      (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (ComplexModel E.ambientDimension) M)
      (_ : IsComplexManifold E.ambientDimension M)
      (σ : M → ComplexProjectiveSpace E.ambientDimension)
      (_ : IsBlowupSequence E.ambientDimension (ComplexProjectiveSpace E.ambientDimension) M σ)
      (hS : IsClosedConnectedSubmanifold E.ambientDimension
        (strictTransform E.ambientDimension σ V.carrier) V.dim)
      (Y : Scheme.{0}) (_ : IsIntegral Y) (g : Y ⟶ Spec (.of ℂ))
      (hg : SmoothOfRelativeDimension V.dim g) (EY : ClosedProjectiveEmbedding g)
      (ρ : Y ⟶ X) (hρ : ρ ≫ f = g),
      letI := hg
      letI := EY.isSeparated
      letI := EY.quasiCompact
      letI := chartedSpace V.dim_le hS.2.2
      letI := isComplexManifold_chartedSpace V.dim_le hS.2.2
      V.carrier = range (ambientPoint E) ∧
      IsIsomorphismOver E.ambientDimension σ (singularLocus V)ᶜ ∧
      ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel V.dim), 𝓘(ℂ, ComplexModel V.dim)⟯
          (strictTransform E.ambientDimension σ V.carrier),
        ∀ q, ambientPoint E (schemeComplexPointMap g f ρ hρ q) = σ (e q).val := by
  obtain ⟨V, M, tM, cM, mM, σ, hσ, N, Ψ, hV, hcompact, hΨ, hiso, hS⟩ :=
    exists_embedded_projective_resolution_of_ambientPoint E
  let := tM
  let := cM
  let := mM
  let := hcompact
  let S := strictTransform E.ambientDimension σ V.carrier
  let := chartedSpace V.dim_le hS.2.2
  let := isComplexManifold_chartedSpace V.dim_le hS.2.2
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS.1.isCompact
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS.2.1
  have hΨS := strictTransform_embedding V.dim_le hS.2.2 hΨ
  obtain ⟨m, hm⟩ := chow_image hΨS (isComplexAnalyticSubset_univ (n := V.dim) (M := S))
  obtain ⟨μ, hμ, P, hP, hgen, hzero⟩ := hm m le_rfl
  rw [image_univ] at hgen hzero
  let := hμ
  obtain ⟨Y, g, hg, EY, hY, e, _, _⟩ := OF14.exists_integral_algebraization_of_chow hΨS P hP hgen hzero
  let := hg
  let := EY.isSeparated
  let := EY.quasiCompact
  have hπ := hσ.contMDiff.comp ((contMDiff_val V.dim_le hS.2.2).comp e.contMDiff)
  have hrange (q : SchemeComplexPoint g) : σ (e q).val ∈ range (ambientPoint E) := by
    rw [← hV]
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage hσ.contMDiff.continuous
      V.isClosed_carrier (e q).property
  obtain ⟨ρ, ⟨hρ, hp⟩, _⟩ :=
    exists_unique_morphism_of_mdifferentiable g EY V.dim f E
      (fun q => σ (e q).val) (hπ.mdifferentiable (by simp)) hrange
  exact ⟨V, M, tM, cM, mM, σ, hσ, hS, Y, hY, g, hg, EY, ρ, hρ, hV, hiso, e, hp⟩

omit [IsIntegral X] in
/-- The algebraic map that realizes the embedded resolution is bijective on complex points
over the nonempty algebraic open complementary to the trace of the ambient singular locus. -/
theorem exists_nonempty_open_complexPoint_bijective_of_embedded_projection
    {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel E.ambientDimension) M]
    [IsComplexManifold E.ambientDimension M]
    {V : ClosedIrreducibleAnalyticSubvariety E.ambientDimension
      (ComplexProjectiveSpace E.ambientDimension)}
    {σ : M → ComplexProjectiveSpace E.ambientDimension}
    {Y : Scheme.{0}} (ρ : Y ⟶ X)
    (e : SchemeComplexPoint (ρ ≫ f) ≃ (strictTransform E.ambientDimension σ V.carrier))
    (hV : V.carrier = range (ambientPoint E))
    (hiso : IsIsomorphismOver E.ambientDimension σ (singularLocus V)ᶜ)
    (hπ : ∀ y, ambientPoint E (schemeComplexPointMap (ρ ≫ f) f ρ rfl y) = σ (e y).val) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧
      Function.Bijective
        (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl) := by
  classical
  obtain ⟨Z, hZ, htrace⟩ := exists_closed_trace_of_ambient_analyticSubset E
    (Pending.StokesSingularLocusAnalytic.isComplexAnalyticSubset_singularLocus V)
  let U : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hgood (x : SchemeComplexPoint f) :
      schemeComplexPointImage f x ∈ U ↔ ambientPoint E x ∈ (singularLocus V)ᶜ :=
    not_congr (htrace x)
  obtain ⟨x, hx⟩ := V.regularLocus_nonempty
  have hxV : x ∈ V.carrier := hx.2.1
  rw [hV] at hxV
  obtain ⟨v, hv⟩ := hxV
  have hU : (U : Set X).Nonempty :=
    ⟨schemeComplexPointImage f v, (hgood v).mpr (hv ▸ fun h => h.2 hx)⟩
  let P := schemeComplexPointMap (ρ ≫ f) f ρ rfl
  have hsurj (x : SchemeComplexPoint f) (hxU : schemeComplexPointImage f x ∈ U) :
      ∃ y : SchemeComplexPoint (ρ ≫ f), P y = x := by
    have hxgood := (hgood x).mp hxU
    obtain ⟨z, hz, hzσ⟩ := hiso.1.surjOn hxgood
    have hzV : σ z ∈ V.carrier := hzσ ▸ hV.symm ▸ mem_range_self x
    have hzS : z ∈ strictTransform E.ambientDimension σ V.carrier :=
      subset_closure ⟨hzV, fun hzex => Set.disjoint_left.mp hiso.2 hz hzex⟩
    let y := e.symm ⟨z, hzS⟩
    refine ⟨y, ambientPoint_injective E ?_⟩
    rw [show P y = schemeComplexPointMap (ρ ≫ f) f ρ rfl y from rfl, hπ,
      show e y = ⟨z, hzS⟩ from e.apply_symm_apply _, hzσ]
  let v₀ := (hsurj v ((hgood v).mpr (hv ▸ fun h => h.2 hx))).choose
  let s : SchemeComplexPoint f → SchemeComplexPoint (ρ ≫ f) :=
    fun x => if h : schemeComplexPointImage f x ∈ U then (hsurj x h).choose else v₀
  have hr x (hxU : schemeComplexPointImage f x ∈ U) : P (s x) = x := by
    rw [show s x = (hsurj x hxU).choose by simp only [s, dif_pos hxU]]
    exact (hsurj x hxU).choose_spec
  have hl y (hyU : schemeComplexPointImage f (P y) ∈ U) : s (P y) = y := by
    apply e.injective
    apply Subtype.ext
    apply hiso.1.injOn
    · change σ (e (s (P y))).val ∈ (singularLocus V)ᶜ
      rw [← hπ, show schemeComplexPointMap (ρ ≫ f) f ρ rfl (s (P y)) = P y from hr (P y) hyU]
      exact (hgood (P y)).mp hyU
    · change σ (e y).val ∈ (singularLocus V)ᶜ
      rw [← hπ]
      exact (hgood (P y)).mp hyU
    · rw [← hπ, ← hπ]
      exact congrArg (ambientPoint E) (hr (P y) hyU)
  have hBij := OkoNov16.original_restricted_complexPoint_bijective_of_good_inverse f ρ U s hr hl
  have heq : (ρ ∣_ U) ≫ (U.ι ≫ f) = (ρ ⁻¹ᵁ U).ι ≫ (ρ ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have transport {g : (ρ ⁻¹ᵁ U).toScheme ⟶ Spec (.of ℂ)}
      (h : (ρ ∣_ U) ≫ (U.ι ≫ f) = g)
      (hb : Function.Bijective (schemeComplexPointMap g (U.ι ≫ f) (ρ ∣_ U) h)) :
      Function.Bijective
        (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl) := by
    subst g
    exact hb
  exact ⟨U, hU, transport heq hBij⟩

end SGPT.Okounkov.OF12
