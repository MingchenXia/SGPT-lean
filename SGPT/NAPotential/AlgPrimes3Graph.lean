import SGPT.NAPotential.AlgPrimes2Divisor
import SGPT.GAGA.AlgPrimes3Submanifold
import SGPT.Foundations.Analysis.Pending.HironakaResolutionKahler
import SGPT.Foundations.Analysis.Pending.AdmissibleBlowupHolomorphicInverse
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedExceptional
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage

/-!
# Realizing an algebraic prime divisor from a graph model, by G11a


Steps (b)–(d) of the plan of `claude-alg-primes:remaining` produce, for an algebraic prime
divisor `D` over `X` centred in codimension `≥ 2`, the closure `Γ = G(ℂ)` of the graph of a
rational map `X ⇢ ℙ^r` inside the compact manifold `M = X(ℂ) × ℙ^r(ℂ)`, smooth along the graph,
together with a local holomorphic model of `Γ` at a smooth point of the centre `D_G` of `ord_D`
on `G`.  This file axiomatizes exactly this output as a structure, `GraphModel D`, and proves the
resolution half of the plan, step (c), with complete proofs:

* `GraphModel D`: a compact complex manifold `M` with a holomorphic `pr : M → X(ℂ)`, a closed
  analytic subset `Γ ⊆ M`, a nowhere dense closed analytic subset `B ⊆ X(ℂ)` and a holomorphic
  section `φ` of `pr` over `X(ℂ) \ B` with `Γ ∩ pr⁻¹(X(ℂ) \ B) = φ(X(ℂ) \ B)`, `Γ` smooth of
  dimension `dim X` along `φ` and equal to the closure of `φ(X(ℂ) \ B)` (the graph closure); a
  holomorphic `ι : N → M` from a complex manifold of dimension `dim X` into the smooth part of
  `Γ` (dimension `dim X`), immersive at `n₀`; a closed analytic `Δ ⊆ M` (the analytic set of
  `D_G`) whose preimage `ι⁻¹ Δ` is a smooth hypersurface at `n₀`, and the order comparison:
  the order along `ι⁻¹ Δ` at `n₀` of `g^an ∘ pr ∘ ι` is `ord_D(g)` for every nonzero germ
  `g ∈ 𝒪_{X, pr(ι n₀)}`.
* `exists_realization_of_graphModel`: a graph model gives the data of
  `SGPT.NAPotential.AlgPrimes2.HypersurfaceRealizationsHighCodim` for `D`.  Proof: `Γ` has pure
  dimension `dim X` (`GraphModel.isPureDim`); G11a
  (`HironakaResolutionSpace.exists_isStrictTransformResolution_of_isAnalytic`) gives a finite
  sequence of blowups `σ : M' → M` whose strict transform `W` of `Γ` is a compact closed
  submanifold of pure dimension `dim X` (`HironakaResolutionKahler.regularAtDim_strictTransform`),
  a complex manifold with the flattening atlas.  `ρ = pr ∘ σ|_W` is an analytic modification:
  its inverse over `X(ℂ) \ B` is `σ⁻¹ ∘ φ` (`σ` is an isomorphism over the smooth part of `Γ`,
  `AdmissibleBlowupHolomorphicInverse.exists_section_compl`, and maps into `W` are holomorphic
  when they are holomorphic into `M'`, `SGPT.GAGA.AlgPrimes3.contMDiff_of_contMDiff_val`), and
  `ρ⁻¹ B` is nowhere dense because `W` is the closure of the part over the graph.  The point
  `w₀ = σ⁻¹(ι n₀)` and `T = (σ|_W)⁻¹ Δ` are transported from `N` along the holomorphic
  `μ = σ⁻¹ ∘ ι : N → W`, whose differential at `n₀` is bijective; regularity and orders are
  invariant (`HironakaEmbeddedExceptional.regularAtDim_of_regularAtDim_preimage`,
  `UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional`).
* `HighCodimGraphModels` (a statement: every algebraic prime divisor centred in codimension
  `≥ 2` has a graph model) implies `HypersurfaceRealizationsHighCodim` and
  `AlgebraicPrimesRealized` (`algebraicPrimesRealized_of_highCodimGraphModels`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3

open Set Filter
open scoped Topology Manifold ContDiff
open AlgebraicGeometry CategoryTheory
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.NAPotential.Berkovich SGPT.NAPotential.FSPos
open SGPT.GAGA.H0S SGPT.NAPotential.TowerAlg SGPT.NAPotential.AlgPrimes
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder
open FirstPass.BlowupSequences BlowupTowers AnalyticModificationLocalDiscrepancy
open AnalyticDimensionBasics HironakaResolutionSpace HolomorphicIdealSheaves

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance algPrimes3GraphPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimes3GraphPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPrimes3GraphPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X]

variable (f m) in
/-- **A graph model of an algebraic prime divisor `D` over `X`** (the output of steps (a), (b)
and (d) of the plan of `claude-alg-primes:remaining`): the closure `Γ` of the graph of a
holomorphic section `φ` of `pr : M → X(ℂ)` over the complement of a nowhere dense analytic set
`B`, in a compact complex manifold `M`, with a local holomorphic model `ι : N → M` of the smooth
part of `Γ` (both of dimension `dim X`) at which `ord_D` is the order of vanishing along the
smooth hypersurface `ι⁻¹ Δ`.  For the intended model `M = X(ℂ) × ℙ^r(ℂ)`, `Γ = G(ℂ)` with `G` the
closure of the graph of `X ⇢ ℙ^r`, `N` the complex points of a smooth affine open of `G` meeting
the centre `D_G` of `ord_D` on `G`, and `Δ = D_G(ℂ)`. -/
structure GraphModel (D : PrimeDivisorOver X) where
  /-- The dimension of the ambient manifold. -/
  K : ℕ
  /-- The ambient compact complex manifold. -/
  M : CMfd.{0} K
  [compactSpace : CompactSpace M]
  /-- The projection to `X(ℂ)`. -/
  pr : M → SchemeComplexPoint f
  contMDiff_pr : ContMDiff 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel (m + 1)) ∞ pr
  /-- The graph closure. -/
  Γ : Set M
  isAnalytic_Γ : IsComplexAnalyticSubset (n := K) Γ
  /-- The locus over which the graph map is not defined. -/
  B : Set (SchemeComplexPoint f)
  isClosed_B : IsClosed B
  isAnalytic_B : IsComplexAnalyticSubset (n := m + 1) B
  interior_B : interior B = ∅
  /-- The graph map, a holomorphic section of `pr` over `X(ℂ) \ B`. -/
  φ : SchemeComplexPoint f → M
  contMDiffOn_φ : ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ∞ φ Bᶜ
  pr_φ : ∀ x ∉ B, pr (φ x) = x
  φ_mem : ∀ x ∉ B, φ x ∈ Γ
  eq_φ : ∀ z ∈ Γ, pr z ∉ B → φ (pr z) = z
  regularAtDim_φ : ∀ x ∉ B, RegularAtDim (n := K) Γ (φ x) (m + 1)
  subset_closure : Γ ⊆ closure (φ '' Bᶜ)
  /-- The local smooth model of `Γ`. -/
  N : CMfd.{0} (m + 1)
  ι : N → M
  contMDiff_ι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ∞ ι
  regularAtDim_ι : ∀ p, RegularAtDim (n := K) Γ (ι p) (m + 1)
  /-- The point of `N` over the centre of `ord_D`. -/
  n₀ : N
  injective_mfderiv_ι :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ι n₀)
  /-- The analytic set of the centre of `ord_D` on the model. -/
  Δ : Set M
  isAnalytic_Δ : IsComplexAnalyticSubset (n := K) Δ
  flattening : DivisorFlattening (m := m) (ι ⁻¹' Δ) n₀
  ord_eq : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (pr (ι n₀))), g ≠ 0 →
    (D.ord ((BerkovichPoint.specializationMap
      (ordVal_support_specializes f D (schemeComplexPointImage f (pr (ι n₀))))).hom g) : ℤ) =
      ((functionNormalOrder flattening (stalkRep m (pr (ι n₀)) g ∘ (pr ∘ ι))
        (HolomorphicIdealSheaves.HolomorphicAt.comp_contMDiff (f := pr ∘ ι) (y := n₀)
          (stalkRep_holomorphicAt (pr (ι n₀)) g)
          (Eventually.of_forall fun _ => (contMDiff_pr.comp contMDiff_ι).contMDiffAt))).toNat : ℤ)

attribute [instance] GraphModel.compactSpace

namespace GraphModel

variable {D : PrimeDivisorOver X} (G : GraphModel f m D)

/-- The graph closure of a graph model has pure dimension `dim X`: every regular point is a limit
of points of the graph, where `Γ` has dimension `dim X`. -/
theorem isPureDim : IsPureDim (n := G.K) G.Γ (m + 1) := by
  intro y j hy
  obtain ⟨z, hz, x, hx, rfl⟩ := mem_closure_iff_nhds.mp (G.subset_closure hy.2.1) _
    (RegularPatchNeighborhood.eventually_regularAtDim hy)
  exact RegularPointDimension.eq_of_regularAtDim (hz (G.φ_mem x hx)) (G.regularAtDim_φ x hx)

/-- **A graph model realizes `D` on the resolved graph closure** (step (c) of the plan of
`claude-alg-primes:remaining`).  The strict transform `W` of `Γ` under the G11a resolution, with
`ρ = pr ∘ σ|_W`, the point `w₀ = σ⁻¹(ι n₀)` and `T = (σ|_W)⁻¹ Δ`, is the data required by
`SGPT.NAPotential.AlgPrimes2.HypersurfaceRealizationsHighCodim` for `D`. -/
theorem exists_realization (G : GraphModel f m D) :
    ∃ (W : CMfd.{0} (m + 1)) (ρ : W → SchemeComplexPoint f)
      (hρ : IsAnalyticModification (n := m + 1) ρ)
      (T : Set W) (_ : IsComplexAnalyticSubset (n := m + 1) T) (w₀ : W)
      (_ : RegularAtDim (n := m + 1) T w₀ m) (Ψ : DivisorFlattening (m := m) T w₀),
      ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ρ w₀)), g ≠ 0 →
        (D.ord ((BerkovichPoint.specializationMap
          (ordVal_support_specializes f D (schemeComplexPointImage f (ρ w₀)))).hom g) : ℤ) =
          ((pullbackNormalOrder hρ Ψ (stalkRep m (ρ w₀) g)
            (stalkRep_holomorphicAt (ρ w₀) g)).toNat : ℤ) := by
  classical
  have hpure := G.isPureDim
  obtain ⟨K, M, pr, hpr, Γ, hΓ, B, hBc, hBa, hBi, φ, hφ, hprφ, hφΓ, heqφ, hregφ, hcl,
    N, ι, hι, hregι, n₀, hinj, Δ, hΔ, Φ, hord⟩ := G
  -- the resolution of the graph closure (G11a)
  obtain ⟨M', _, _, _, σ, E, -, h⟩ := exists_isStrictTransformResolution_of_isAnalytic hΓ
  set S := strictTransform K σ Γ with hSdef
  have hreg : ∀ y ∈ S, RegularAtDim (n := K) S y (m + 1) :=
    HironakaResolutionKahler.regularAtDim_strictTransform h hΓ.isClosed hpure
  have hk : m + 1 ≤ K := (hregι n₀).1
  let cs : ChartedSpace (ComplexModel (m + 1)) S := SubmanifoldChartedSpace.chartedSpace hk hreg
  have mf : IsComplexManifold (m + 1) S :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hreg
  have hval : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ∞
      (Subtype.val : S → M') := SubmanifoldChartedSpace.contMDiff_val hk hreg
  have hσ := h.contMDiff
  -- the inverse of `σ` over the smooth part of `Γ`
  set Sg := HironakaEmbeddedAnalytic.singularSet (n := K) Γ with hSgdef
  have hSgc : IsClosed Sg := HironakaEmbeddedAnalytic.isClosed_singularSet hΓ.isClosed
  have hnotSg : ∀ {z : M} {k : ℕ}, RegularAtDim (n := K) Γ z k → z ∈ Sgᶜ := fun hz hzS =>
    ((HironakaEmbeddedAnalytic.mem_singularSet_iff).mp hzS).2 _ hz
  obtain ⟨τ₀, hτ₀, hστ₀, hτσ₀⟩ :=
    AdmissibleBlowupHolomorphicInverse.exists_section_compl hSgc h.admissible
  let τ : M → M' := fun z => if hz : z ∈ Sgᶜ then τ₀ ⟨z, hz⟩ else τ₀ ⟨ι n₀, hnotSg (hregι n₀)⟩
  have hτz : ∀ z (hz : z ∈ Sgᶜ), τ z = τ₀ ⟨z, hz⟩ := fun z hz => dif_pos hz
  have hστ : ∀ z ∈ Sgᶜ, σ (τ z) = z := fun z hz => by
    rw [hτz z hz]
    exact congrFun hστ₀ ⟨z, hz⟩
  have hτσ : ∀ y, σ y ∈ Sgᶜ → τ (σ y) = y := fun y hy => by
    rw [hτz _ hy]
    exact hτσ₀ y hy
  have hτhol : ∀ z ∈ Sgᶜ, ContMDiffAt 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) ∞ τ z := by
    intro z hz
    have hsd : ContMDiff 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) ∞
        (fun x : (⟨Sgᶜ, hSgc.isOpen_compl⟩ : TopologicalSpace.Opens M) => τ x) := by
      have : (fun x : (⟨Sgᶜ, hSgc.isOpen_compl⟩ : TopologicalSpace.Opens M) => τ x) = τ₀ := by
        funext x
        exact hτz x.1 x.2
      rw [this]
      exact hτ₀
    exact contMDiffAt_subtype_iff.mp (hsd ⟨z, hz⟩)
  have hτS : ∀ z, RegularAtDim (n := K) Γ z (m + 1) → τ z ∈ S := by
    intro z hz
    have hzS : z ∈ Sgᶜ := hnotSg hz
    have hmem : τ z ∈ σ ⁻¹' (Γ \ Sg) := by
      change σ (τ z) ∈ Γ \ Sg
      rw [hστ z hzS]
      exact ⟨hz.2.1, hzS⟩
    rw [← h.inter_preimage_compl] at hmem
    exact hmem.1
  -- the projection `ρ = pr ∘ σ|_W`
  let ρ : S → SchemeComplexPoint f := fun w => pr (σ w.1)
  have hρhol : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ρ :=
    hpr.comp (hσ.comp hval)
  have hScpt : CompactSpace S := isCompact_iff_compactSpace.mp h.isCompact_strictTransform
  -- the points of `W` over the graph
  let μ : N → S := fun p => ⟨τ (ι p), hτS _ (hregι p)⟩
  let w₀ : S := μ n₀
  let s : SchemeComplexPoint f → S := fun x =>
    if hx : x ∈ Bᶜ then ⟨τ (φ x), hτS _ (hregφ x hx)⟩ else w₀
  have hs : ∀ x (hx : x ∈ Bᶜ), s x = ⟨τ (φ x), hτS _ (hregφ x hx)⟩ := fun x hx => dif_pos hx
  -- density of the part of `W` over the graph
  have hdense : ∀ y ∈ S, y ∈ closure (τ '' (φ '' Bᶜ)) := by
    intro y hy
    rw [hSdef, h.eq_closure] at hy
    refine closure_minimal (fun y' hy' => ?_) isClosed_closure hy
    obtain ⟨hy'Γ, hy'S⟩ := hy'
    have hτc : Tendsto τ (𝓝 (σ y')) (𝓝 y') := by
      have := (hτhol _ hy'S).continuousAt.tendsto
      rwa [hτσ y' hy'S] at this
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨_, hzU, x, hx, rfl⟩ := mem_closure_iff_nhds.mp (hcl hy'Γ) _ (hτc hU)
    exact ⟨τ (φ x), hzU, φ x, ⟨x, hx, rfl⟩, rfl⟩
  have hρ : IsAnalyticModification (n := m + 1) ρ := by
    refine ⟨hρhol, hρhol.continuous.isProperMap, ρ ⁻¹' B, B, s, hBc.preimage hρhol.continuous,
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hρhol hBa, ?_, hBc, hBa, hBi, rfl,
      ?_, ?_, ?_⟩
    · -- `ρ⁻¹ B` is nowhere dense
      rw [interior_eq_empty_iff_dense_compl]
      intro w
      rw [closure_subtype]
      refine closure_mono ?_ (hdense w.1 w.2)
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨⟨τ (φ x), hτS _ (hregφ x hx)⟩, ?_, rfl⟩
      change pr (σ (τ (φ x))) ∉ B
      rw [hστ _ (hnotSg (hregφ x hx)), hprφ x hx]
      exact hx
    · -- the inverse is holomorphic
      refine SGPT.GAGA.AlgPrimes3.contMDiffOn_of_contMDiffOn_val hk hreg hBc.isOpen_compl ?_
      intro x hx
      have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ∞ (τ ∘ φ) x :=
        (hτhol _ (hnotSg (hregφ x hx))).comp x (hφ.contMDiffAt (hBc.isOpen_compl.mem_nhds hx))
      refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [hBc.isOpen_compl.mem_nhds hx] with x' hx'
      simp only [Function.comp_apply, hs x' hx']
    · intro x hx
      change pr (σ (s x).1) = x
      rw [hs x hx]
      change pr (σ (τ (φ x))) = x
      rw [hστ _ (hnotSg (hregφ x hx)), hprφ x hx]
    · intro w hw
      have hwB : ρ w ∈ Bᶜ := hw
      have hσw : φ (ρ w) = σ w.1 := heqφ (σ w.1) (h.strictTransform_subset_preimage w.2) hwB
      rw [hs _ hwB]
      apply Subtype.ext
      change τ (φ (ρ w)) = w.1
      rw [hσw]
      apply hτσ
      rw [← hσw]
      exact hnotSg (hregφ _ hwB)
  -- the hypersurface and the point
  let T : Set S := (fun w : S => σ w.1) ⁻¹' Δ
  have hTa : IsComplexAnalyticSubset (n := m + 1) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (hσ.comp hval) hΔ
  have hσμ : ∀ p, σ (μ p).1 = ι p := fun p => hστ _ (hnotSg (hregι p))
  have hμ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ μ := by
    refine SGPT.GAGA.AlgPrimes3.contMDiff_of_contMDiff_val hk hreg fun p => ?_
    exact (hτhol _ (hnotSg (hregι p))).comp p (hι p)
  have hsets : ∀ p, p ∈ ι ⁻¹' Δ ↔ μ p ∈ T := fun p => by
    change ι p ∈ Δ ↔ σ (μ p).1 ∈ Δ
    rw [hσμ]
  -- `μ` is a local biholomorphism at `n₀`
  have hμexc : n₀ ∉ exceptionalLocus (m + 1) μ := by
    have hμd : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) μ n₀ :=
      (hμ n₀).mdifferentiableAt (by simp)
    have hvd : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K)
        (Subtype.val : S → M') (μ n₀) := (hval _).mdifferentiableAt (by simp)
    have hτd : MDifferentiableAt 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) τ (ι n₀) :=
      (hτhol _ (hnotSg (hregι n₀))).mdifferentiableAt (by simp)
    have hιd : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ι n₀ :=
      (hι n₀).mdifferentiableAt (by simp)
    have hσd : MDifferentiableAt 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) σ (τ (ι n₀)) :=
      (hσ _).mdifferentiableAt (by simp)
    -- `mfderiv τ` is injective at `ι n₀`: `σ ∘ τ = id` near `ι n₀`
    have hτinj : Function.Injective
        (mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) τ (ι n₀)) := by
      have heq : (σ ∘ τ) =ᶠ[𝓝 (ι n₀)] id := by
        filter_upwards [hSgc.isOpen_compl.mem_nhds (hnotSg (hregι n₀))] with z hz
        exact hστ z hz
      have h1 := mfderiv_comp (ι n₀) hσd hτd
      rw [heq.mfderiv_eq, mfderiv_id] at h1
      intro v w hvw
      have hv : (mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) σ (τ (ι n₀)))
          ((mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) τ (ι n₀)) v) = v := by
        exact (congrArg (fun L => L v) h1).symm
      have hw : (mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) σ (τ (ι n₀)))
          ((mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel K) τ (ι n₀)) w) = w := by
        exact (congrArg (fun L => L w) h1).symm
      rw [← hv, ← hw, hvw]
    have hcomp : (Subtype.val ∘ μ) = τ ∘ ι := rfl
    have h1 := mfderiv_comp n₀ hvd hμd
    rw [hcomp, mfderiv_comp n₀ hτd hιd] at h1
    have hinjμ : Function.Injective
        (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) μ n₀) := by
      have hinj2 : Function.Injective
          ((mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) (Subtype.val : S → M')
            (μ n₀)).comp (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) μ n₀)) := by
        rw [← h1]
        exact hτinj.comp hinj
      exact Function.Injective.of_comp (f := ⇑(mfderiv 𝓘(ℂ, ComplexModel (m + 1))
        𝓘(ℂ, ComplexModel K) (Subtype.val : S → M') (μ n₀))) hinj2
    intro hexc
    apply hexc
    let L : ComplexModel (m + 1) →ₗ[ℂ] ComplexModel (m + 1) :=
      (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) μ n₀).toLinearMap
    have hL : Function.Injective L := hinjμ
    have hLs : Function.Surjective L := LinearMap.injective_iff_surjective.mp hL
    exact ⟨hinjμ, hLs⟩
  have hTreg : RegularAtDim (n := m + 1) T w₀ m :=
    HironakaEmbeddedExceptional.regularAtDim_of_regularAtDim_preimage hμ hμexc isOpen_univ
      (mem_univ n₀) (fun p _ => hsets p) (IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Φ)
  obtain ⟨Ψ⟩ := DivisorFlattening.nonempty_of_regularAtDim hTreg
  have hρw₀ : pr (ι n₀) = ρ w₀ := by
    change pr (ι n₀) = pr (σ (μ n₀).1)
    rw [hσμ]
  have key : ∀ (x : SchemeComplexPoint f) (hx : pr (ι n₀) = x)
      (g : X.presheaf.stalk (schemeComplexPointImage f x)), g ≠ 0 →
      ∀ hhol : HolomorphicAt (m + 1) (stalkRep m x g ∘ (pr ∘ ι)) n₀,
      (D.ord ((BerkovichPoint.specializationMap
        (ordVal_support_specializes f D (schemeComplexPointImage f x))).hom g) : ℤ) =
        ((functionNormalOrder Φ (stalkRep m x g ∘ (pr ∘ ι)) hhol).toNat : ℤ) := by
    intro x hx
    subst hx
    intro g hg hhol
    exact hord g hg
  refine ⟨@CMfd.of (m + 1) S _ cs mf, ρ, hρ, T, hTa, w₀, hTreg, Ψ, fun g hg => ?_⟩
  have hF : HolomorphicAt (m + 1) (stalkRep m (ρ w₀) g) (μ n₀ |> ρ) :=
    stalkRep_holomorphicAt (ρ w₀) g
  have hcongr := UnramifiedNormalOrder.functionNormalOrder_comp_eq_of_not_exceptional hμ hμexc
    Ψ Φ (Eventually.of_forall hsets) (stalkRep m (ρ w₀) g ∘ ρ)
    (HolomorphicIdealSheaves.HolomorphicAt.comp_contMDiff (f := ρ) (y := w₀) hF
      (Eventually.of_forall fun _ => hρhol.contMDiffAt))
  unfold pullbackNormalOrder
  rw [← hcongr]
  have hfun : (stalkRep m (ρ w₀) g ∘ ρ) ∘ μ = stalkRep m (ρ w₀) g ∘ (pr ∘ ι) := by
    funext p
    simp only [Function.comp_apply]
    change stalkRep m (ρ w₀) g (pr (σ (μ p).1)) = _
    rw [hσμ]
  have h0 : HolomorphicAt (m + 1) (stalkRep m (ρ w₀) g) (pr (ι n₀)) := by
    rw [hρw₀]
    exact stalkRep_holomorphicAt (ρ w₀) g
  have hF' : HolomorphicAt (m + 1) (stalkRep m (ρ w₀) g ∘ (pr ∘ ι)) n₀ :=
    HolomorphicAt.comp_contMDiff (f := pr ∘ ι) (y := n₀) h0
      (Eventually.of_forall fun _ => (hpr.comp hι).contMDiffAt)
  rw [functionNormalOrder_congr Φ _ hF' (Filter.EventuallyEq.of_eq hfun)]
  exact key (ρ w₀) hρw₀ g hg hF'

end GraphModel

variable (f m) in
/-- **Every algebraic prime divisor centred in codimension at least two has a graph model.**  (A
statement; the output of steps (a), (b), (d) of the plan of `claude-alg-primes:remaining`, not
proved here.) -/
def HighCodimGraphModels : Prop :=
  ∀ D : PrimeDivisorOver X, Order.coheight (D.ordVal f 1 one_pos).center ≠ 1 →
    Nonempty (GraphModel f m D)

/-- **Graph models give `HypersurfaceRealizationsHighCodim`.** -/
theorem hypersurfaceRealizationsHighCodim_of_highCodimGraphModels
    (h : HighCodimGraphModels f m) :
    SGPT.NAPotential.AlgPrimes2.HypersurfaceRealizationsHighCodim (f := f) m := by
  intro D hD
  obtain ⟨G⟩ := h D hD
  exact G.exists_realization

/-- **Graph models give `AlgebraicPrimesRealized`**: every algebraic prime divisor over `X` is
realized by an analytic presentation, if those centred in codimension `≥ 2` have graph models
(those centred on a prime divisor of `X` are realized unconditionally, lane ALG-PRIMES2). -/
theorem algebraicPrimesRealized_of_highCodimGraphModels (E : ClosedProjectiveEmbedding f)
    (h : HighCodimGraphModels f m) : AlgebraicPrimesRealized (f := f) m E :=
  SGPT.NAPotential.AlgPrimes2.algebraicPrimesRealized_of_hypersurfaceRealizationsHighCodim E
    (hypersurfaceRealizationsHighCodim_of_highCodimGraphModels h)

end SGPT.NAPotential.AlgPrimes3

end
