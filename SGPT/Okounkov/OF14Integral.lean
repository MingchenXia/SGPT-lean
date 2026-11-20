import SGPT.Projective.SmoothSchemeClopenComponents
import SGPT.BDivisor.BD5Algebraization

/-!
# Smooth projective complex schemes with connected analytification are integral

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (existence part of
[CFKLRS17, Thm 2.9]): the modification on which the flag lives is the algebraic model `V` of a
blow-up tower `Y → X(ℂ)`; this model must be a *variety*, i.e. integral.

* `dense_range_schemeComplexPointImage`: the complex points of a scheme locally of finite type over
  `ℂ` are dense (every nonempty affine open has a maximal ideal, which is a complex point by the
  Nullstellensatz);
* `connectedSpace_of_connectedSpace_schemeComplexPoint`: if `V(ℂ)` is connected (analytic
  topology), then `V` is connected (Zariski topology): the image of `V(ℂ)` is connected and dense;
* **`isIntegral_of_connectedSpace_schemeComplexPoint`**: a smooth projective complex scheme `V`
  with connected `V(ℂ)` is integral: it is reduced, its irreducible components are disjoint and
  clopen (local rings of a smooth scheme are domains), so a connected `V` has one component;
* **`exists_integral_algebraization_of_chow`**: the algebraization
  (`SGPT.BDivisor.BD5.exists_algebraization_of_chow_bd5`) of a *connected* compact complex
  manifold `Y ⊆ ℙᴺ` cut out by homogeneous equations generating the ideal of its cone is an
  **integral** smooth projective scheme `V` with `V(ℂ) ≃ Y` compatibly with the embeddings.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF14

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set

section Dense

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ))

/-- **The complex points are dense** in a scheme locally of finite type over `ℂ`. -/
theorem dense_range_schemeComplexPointImage [LocallyOfFiniteType g] :
    Dense (range (schemeComplexPointImage g)) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hx hU
  let P := hW.primeIdealOf ⟨x, hxW⟩
  obtain ⟨m, hm, -⟩ := P.asIdeal.exists_le_maximal P.isPrime.ne_top
  obtain ⟨p, hp⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec g hW m hm
  refine ⟨schemeComplexPointImage g p, hWU ?_, p, rfl⟩
  rw [hp]
  have h := hW.range_fromSpec
  rw [← h]
  exact Set.mem_range_self _

/-- **Connectedness descends from `V(ℂ)` to `V`**: if the complex points of a scheme locally of
finite type over `ℂ` form a connected space (analytic topology), then the scheme is connected. -/
theorem connectedSpace_of_connectedSpace_schemeComplexPoint [LocallyOfFiniteType g]
    [hc : @ConnectedSpace (SchemeComplexPoint g) (schemeAnalyticPointTopology g)] :
    ConnectedSpace V := by
  let := schemeAnalyticPointTopology g
  have h1 : _root_.IsConnected (range (schemeComplexPointImage g)) :=
    _root_.isConnected_range (schemeComplexPointImage_continuous g)
  have h2 := h1.closure
  rw [(dense_range_schemeComplexPointImage g).closure_eq] at h2
  exact connectedSpace_iff_univ.mpr h2

end Dense

section Integral

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g]

include n

/-- A connected smooth projective complex scheme is integral. -/
theorem isIntegral_of_connectedSpace (EV : ClosedProjectiveEmbedding g) [ConnectedSpace V] :
    IsIntegral V := by
  have := SGPT.Projective.NumEq.AlgebraicCurveDegree.smoothScheme_isReduced g n
  obtain ⟨x⟩ : Nonempty V := inferInstance
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hclopen :=
    SGPT.Projective.NumEq.AlgebraicCurveDegree.smoothProjective_component_isClopen g n EV _ hC
  have huniv : irreducibleComponent x = univ :=
    (isClopen_iff.mp hclopen).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨x, mem_irreducibleComponent⟩)
  have : IrreducibleSpace V := by
    rw [irreducibleSpace_def]
    change IsIrreducible (univ : Set V)
    rw [← huniv]
    exact isIrreducible_irreducibleComponent
  exact isIntegral_of_irreducibleSpace_of_isReduced V

/-- **A smooth projective complex scheme with connected `V(ℂ)` is integral.** -/
theorem isIntegral_of_connectedSpace_schemeComplexPoint (EV : ClosedProjectiveEmbedding g)
    [@ConnectedSpace (SchemeComplexPoint g) (schemeAnalyticPointTopology g)] :
    IsIntegral V := by
  have : Smooth g := SmoothOfRelativeDimension.smooth n g
  have : ConnectedSpace V := connectedSpace_of_connectedSpace_schemeComplexPoint g
  exact isIntegral_of_connectedSpace g n EV

end Integral

/-! ### the algebraizations of connected manifolds are integral -/

section Chow

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Manifold ContDiff

local instance of14IntTopology {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance of14IntCharts {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance of14IntManifold {A : Scheme.{0}} (h : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-- **Connected projective manifolds are integral algebraic varieties.** A connected compact
complex manifold `Y` of dimension `n` with a holomorphic embedding `Ψ : Y → ℙᴺ` whose image is cut
out by homogeneous `P_k` generating the ideal sheaf of its cone (Chow's theorem) is biholomorphic
to `V(ℂ)` for an **integral** smooth projective complex scheme `V = Proj(ℂ[x]/(P_k))` of relative
dimension `n`, compatibly with the embeddings (`Ψ ∘ e = (V(ℂ) → ℙᴺ)`). -/
theorem exists_integral_algebraization_of_chow {n N : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y]
    {Ψ : Y → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {μ : Type} [Fintype μ] (P : μ → MvPolynomial (Fin (N + 1)) ℂ) {m : ℕ}
    (hP : ∀ k, (P k).IsHomogeneous m)
    (hgen : (coneIdeal (range Ψ)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun k => SGPT.GAGA.PN.polyTuple (P k)))
    (hzero : range Ψ = {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0}) :
    ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension n g)
      (EV : ClosedProjectiveEmbedding g), IsIntegral V ∧
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
        EV.ambientDimension = N ∧ ∀ q, HEq (Ψ (e q)) (projectivePoint g EV n q) := by
  obtain ⟨V, g, hsm, EV, hrest⟩ :=
    SGPT.BDivisor.BD5.exists_algebraization_of_chow_bd5 hΨ P hP hgen hzero
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  obtain ⟨e, hN, he⟩ := hrest
  have : ConnectedSpace (SchemeComplexPoint g) :=
    e.symm.toHomeomorph.surjective.connectedSpace e.symm.continuous
  exact ⟨V, g, hsm, EV, isIntegral_of_connectedSpace_schemeComplexPoint g n EV, e, hN, he⟩

end Chow

end SGPT.Okounkov.OF14
