import SGPT.Okounkov.ValGen2Atlas
import SGPT.Okounkov.ValGen2Veronese
import SGPT.Okounkov.ValGenCont

/-!
# `prop:suba` for an arbitrary valuation: the analytic Kähler case

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, Section *Basic properties of partial Okounkov bodies*, `prop:suba`:
`Δ_ν(L, h) + Δ_ν(L', h') ⊆ Δ_ν(L ⊗ L', h ⊗ h')`.

The source reduces, through analytic approximation, to potentials with analytic singularities,
then through a log resolution and `rmk:DeltaanaW0` to `prop:subaddOkoun`. For an arbitrary
valuation we avoid the resolution: if `φ, φ'` have analytic singularities and `θ_φ, θ'_{φ'}` are
Kähler currents, then `Γ^∞(θ, φ)`, `Γ^∞(θ', φ')` are full semigroups at `d_sg`-distance `0` from
`Γ(θ, φ)`, `Γ(θ', φ')` (`SGPT.Okounkov.ValGen`, `rmk:DeltaanaW0`), so their bodies are the partial
bodies, and the products of `𝓘_∞`-sections (`SGPT.Okounkov.ValGen2.inftySectionSet_add_mem_tensor`)
form a full semigroup `W ⊆ Γ(θ + θ', φ + φ')` with `Δ(W) ⊇ Δ(Γ^∞(θ, φ)) + Δ(Γ^∞(θ', φ'))`.

## Main results

* `closure_degreeSum_eq_top`: the degreewise sums of two semigroups generating `ℤⁿ⁺¹` generate
  `ℤⁿ⁺¹` (via conductors).
* `isInftySection_degree_zero`, `zero_mem_inftySemigroup`: `(0, 0) ∈ Γ^∞(θ, φ)`.
* `partialBody_eq_euclideanBody_inftySemigroup`: `Δ_ν(θ, φ) = Δ(Γ^∞(θ, φ))` in the analytic
  Kähler case.
* **`partialBody_add_subset_of_analytic`**: `prop:suba` for `ν` when `φ, φ'` have analytic
  singularities and `θ_φ, θ'_{φ'}` are Kähler currents.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology Pointwise

/-! ### Degreewise sums of full semigroups -/

section Sums

variable {n : ℕ}

/-- **Degreewise sums of full semigroups generate `ℤⁿ⁺¹`**: if `A`, `B` are semigroups of
nonnegative degrees generating `ℤⁿ⁺¹` and `W` contains `(x + y, k)` whenever `(x, k) ∈ A` and
`(y, k) ∈ B`, then `W` generates `ℤⁿ⁺¹`. -/
theorem closure_degreeSum_eq_top (A B : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hA : AddSubgroup.closure (A : Set ((Fin n → ℤ) × ℤ)) = ⊤)
    (hB : AddSubgroup.closure (B : Set ((Fin n → ℤ) × ℤ)) = ⊤)
    (hAdeg : ∀ z ∈ A, 0 ≤ z.2) (hBdeg : ∀ z ∈ B, 0 ≤ z.2) (W : Set ((Fin n → ℤ) × ℤ))
    (hW : ∀ (x y : Fin n → ℤ) (k : ℤ), (x, k) ∈ A → (y, k) ∈ B → (x + y, k) ∈ W) :
    AddSubgroup.closure W = ⊤ := by
  have hne : ∀ S : AddSubsemigroup ((Fin n → ℤ) × ℤ),
      AddSubgroup.closure (S : Set ((Fin n → ℤ) × ℤ)) = ⊤ → (S : Set ((Fin n → ℤ) × ℤ)).Nonempty := by
    intro S hS
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, AddSubgroup.closure_empty] at hS
    have : ((0 : Fin n → ℤ), (1 : ℤ)) ∈ (⊥ : AddSubgroup ((Fin n → ℤ) × ℤ)) := by
      rw [hS]; trivial
    rw [AddSubgroup.mem_bot] at this
    exact one_ne_zero (congrArg Prod.snd this)
  -- conductors
  let RA : Set ((Fin n → ℤ) × ℤ) := insert ((0 : Fin n → ℤ), (1 : ℤ))
    (insert ((0 : Fin n → ℤ), (2 : ℤ)) (Set.range fun i : Fin n => ((Pi.single i 1 : Fin n → ℤ), (1 : ℤ))))
  let RB : Set ((Fin n → ℤ) × ℤ) := insert ((0 : Fin n → ℤ), (1 : ℤ)) {((0 : Fin n → ℤ), (2 : ℤ))}
  obtain ⟨fA, hfA, hRA⟩ := SGPT.AlmostSemigroup.Conductor.exists_translate_of_finite A (hne A hA)
    (((Set.finite_range _).insert _).insert _) (by rw [hA]; exact Set.subset_univ RA)
  obtain ⟨fB, hfB, hRB⟩ := SGPT.AlmostSemigroup.Conductor.exists_translate_of_finite B (hne B hB)
    ((Set.finite_singleton _).insert _) (by rw [hB]; exact Set.subset_univ RB)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, fA.2 = a := ⟨fA.2.toNat, (Int.toNat_of_nonneg (hAdeg fA hfA)).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, fB.2 = b := ⟨fB.2.toNat, (Int.toNat_of_nonneg (hBdeg fB hfB)).symm⟩
  have hu0 := hRA _ (Set.mem_insert _ _)
  have hu1 := hRA _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hui : ∀ i : Fin n, ((Pi.single i 1 : Fin n → ℤ), (1 : ℤ)) + fA ∈ A := fun i =>
    hRA _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  have hv0 := hRB _ (Set.mem_insert _ _)
  have hv1 := hRB _ (Set.mem_insert_of_mem _ rfl)
  -- elements of the common degrees `(a+1)(b+1)` and `(a+1)(b+1) + 1`
  have hx0 := SGPT.Okounkov.ValGen2.nsmul_add_mem A hu0 hu0 b
  have hxi := fun i => SGPT.Okounkov.ValGen2.nsmul_add_mem A hu0 (hui i) b
  have hx1 := SGPT.Okounkov.ValGen2.nsmul_add_mem A hu0 hu1 b
  have hy0 := SGPT.Okounkov.ValGen2.nsmul_add_mem B hv0 hv0 a
  have hy1 := SGPT.Okounkov.ValGen2.nsmul_add_mem B hv0 hv1 a
  set D : ℤ := ((a : ℤ) + 1) * ((b : ℤ) + 1) with hD
  have hdeg : ∀ (u : (Fin n → ℤ) × ℤ) (m : ℕ) (w : (Fin n → ℤ) × ℤ),
      (m • u + w).2 = (m : ℤ) * u.2 + w.2 := by
    intro u m w
    simp [nsmul_eq_mul]
  have hpair : ∀ (x : (Fin n → ℤ) × ℤ) (y : (Fin n → ℤ) × ℤ), x ∈ A → y ∈ B → x.2 = y.2 →
      (x.1 + y.1, x.2) ∈ W := by
    intro x y hx hy hxy
    refine hW x.1 y.1 x.2 hx ?_
    rw [hxy]
    exact hy
  set u0 : (Fin n → ℤ) × ℤ := ((0 : Fin n → ℤ), (1 : ℤ)) + fA
  set v0 : (Fin n → ℤ) × ℤ := ((0 : Fin n → ℤ), (1 : ℤ)) + fB
  have hw0 := hpair _ _ hx0 hy0 (by rw [hdeg, hdeg]; simp [u0, v0, ha, hb]; ring)
  have hw1 := hpair _ _ hx1 hy1 (by rw [hdeg, hdeg]; simp [u0, v0, ha, hb]; ring)
  have hwi := fun i => hpair _ _ (hxi i) hy0 (by rw [hdeg, hdeg]; simp [u0, v0, ha, hb]; ring)
  set G := AddSubgroup.closure W
  apply closure_eq_top_of_basis G
  · intro i
    have h := G.sub_mem (AddSubgroup.subset_closure (hwi i)) (AddSubgroup.subset_closure hw0)
    convert h using 1
    refine Prod.ext ?_ ?_
    · simp only [u0, Prod.fst_sub, Prod.fst_add, Prod.smul_fst]
      abel
    · simp only [u0, Prod.snd_sub, Prod.snd_add, Prod.smul_snd]
      abel
  · have h := G.sub_mem (AddSubgroup.subset_closure hw1) (AddSubgroup.subset_closure hw0)
    convert h using 1
    refine Prod.ext ?_ ?_
    · simp only [u0, v0, Prod.fst_sub, Prod.fst_add, Prod.smul_fst]
      abel
    · simp only [u0, Prod.snd_sub, Prod.snd_add, Prod.smul_snd]
      abel

end Sums

/-! ### The analytic Kähler case -/

section Analytic

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance valGen2SubaTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2SubaCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGen2SubaManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

/-- Every section of `L⁰ = 𝒪_X` lies in `H⁰(X, L⁰ ⊗ 𝓘_∞(0 · φ))`. -/
theorem isInftySection_degree_zero {L : X.Modules} (φ : SchemeComplexPoint f → EReal)
    (s : bundlePowerGlobalSections L 0) : IsInftySection f (m + 1) E φ 0 s := by
  intro U α p hp
  have hfun : (fun x => ((0 : ℕ) : EReal) * φ x) = fun _ => (0 : EReal) :=
    funext fun x => by simp
  change (SGPT.PSH.inftyIdeal (n := m + 1) (fun x => ((0 : ℕ) : EReal) * φ x)).mem p _
  rw [hfun]
  exact SGPT.Okounkov.ValGen.mem_inftyIdeal_zero
    (schemeOpenRegularFunction_holomorphicAt f (m + 1) E U _ p hp)

/-- `(0, 0) ∈ Γ^∞(θ, φ)`. -/
theorem zero_mem_inftySemigroup {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    (0 : (Fin (m + 1) → ℤ) × ℤ) ∈ SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ := by
  have h1 := bundlePowerGlobalOne_ne_zero (v := v) c a
  refine ⟨0, bundlePowerGlobalOne L, h1, isInftySection_degree_zero f E φ _, ?_⟩
  have hv := sectionValue_one (v := v) c a
  rw [sectionValue_eq_vector c a 0 _ h1] at hv
  have hv' : toLex (sectionVector v c a 0 (bundlePowerGlobalOne L) h1) = toLex 0 :=
    WithTop.coe_injective hv
  rw [toLex.injective hv']
  rfl

theorem inftySemigroup_degree_nonneg {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) :
    ∀ z ∈ SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ, 0 ≤ z.2 := by
  rintro _ ⟨k, s, hs, -, rfl⟩
  exact Int.natCast_nonneg k

include Y hY in
/-- **`Δ_ν(θ, φ) = Δ(Γ^∞(θ, φ))`** when `φ` has analytic singularities and `θ_φ` is a Kähler
current (`rmk:DeltaanaW0`, first sentence, for `v`). -/
theorem partialBody_eq_euclideanBody_inftySemigroup [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : HasManifoldAnalyticSingularityType (n := m + 1) φ) :
    SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C φ =
      BodyGeometry.euclideanBody (SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ) := by
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨hfull, -, -⟩ := SGPT.Okounkov.ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a H c v
    hS hG hφ hφan
  have hd := SGPT.Okounkov.ValGen.dist_inftySemigroup_multiplierConeSubset_eq_zero f E Y hY a H c v
    hS hG hφ hφan
  have hΓ := (SGPT.Okounkov.ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_analytic f E Y
    hY a H c v hS hG hφ hφan).1
  rw [SGPT.Okounkov.ValGen.partialBody_eq a φ _ hΓ]
  let T : FullSemigroup C := ⟨_, hfull⟩
  have hins : Inseparable (⟨SGPT.Okounkov.ValGen.multiplierConeSubset f E a c v hS φ, hΓ⟩ :
      AlmostSpace C) (fullToAlmost T) := by
    rw [Metric.inseparable_iff, dist_comm]
    exact hd
  have heq := (hins.map (continuous_bodyExtension C)).eq
  have h2 : (bodyExtension (fullToAlmost T) : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      BodyGeometry.euclideanBody (SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ) := by
    rw [bodyExtension_source]
    rfl
  exact (congrArg (fun K : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))) =>
    (K : Set (EuclideanSpace ℝ (Fin (m + 1))))) heq).trans h2

include Y hY in
/-- **Source `prop:suba` for an arbitrary valuation `ν = v`, analytic Kähler case**: under
`Γ(L) ∈ 𝒮'(C)`, `Γ(L') ∈ 𝒮'(C')`, `Γ(L ⊗ L') ∈ 𝒮'(C'')` for `v`, if `φ` (for `θ = c₁(L, H)`) and
`φ'` (for `θ' = c₁(L', H')`) have analytic singularities and `θ_φ`, `θ'_{φ'}` are Kähler currents,
and `φ + φ'` is psh with positive mass for the curvature of a smooth metric `H''` on `L ⊗ L'`
(e.g. `H ⊗ H'`), then `Δ_ν(θ, φ) + Δ_ν(θ', φ') ⊆ Δ_ν(θ + θ', φ + φ')`. -/
theorem partialBody_add_subset_of_analytic [Nonempty (SchemeComplexPoint f)] (hc : IsNonnegAt v c)
    {L L' : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f (m + 1) E L')
    (d : LineBundleAtlas (bundleTensor L L'))
    (H'' : SchemeLineBundleMetric f (m + 1) E (bundleTensor L L'))
    {C C' C'' : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    (hS' : sectionSemigroup v c a' ≤ latticePoints C'.cone)
    (hG' : LatticeSlices.generatedGroup (sectionSemigroup v c a') = ⊤)
    (hS'' : sectionSemigroup v c d ≤ latticePoints C''.cone)
    (hG'' : LatticeSlices.generatedGroup (sectionSemigroup v c d) = ⊤)
    {φ φ' : SchemeComplexPoint f → EReal}
    (hφ : IsKahlerCurrentPotential (H.curvature a) φ)
    (hφan : HasManifoldAnalyticSingularityType (n := m + 1) φ)
    (hφ' : IsKahlerCurrentPotential (H'.curvature a') φ')
    (hφ'an : HasManifoldAnalyticSingularityType (n := m + 1) φ')
    (hsum : IsThetaPshPotential (H''.curvature d).val (fun x => φ x + φ' x))
    (hmass : letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H''.curvature d) (fun x => φ x + φ' x) hsum) :
    SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a C φ +
        SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c a' C' φ' ⊆
      SGPT.Okounkov.ValGen.partialBody f (m + 1) E v c d C'' (fun x => φ x + φ' x) := by
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set A := SGPT.Okounkov.ValGen.inftySemigroup f E a c v φ with hAdef
  set B := SGPT.Okounkov.ValGen.inftySemigroup f E a' c v φ' with hBdef
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hφθ' := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ'
  obtain ⟨hfullA, -, -⟩ := SGPT.Okounkov.ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a H
    c v hS hG hφ hφan
  obtain ⟨hfullB, -, -⟩ := SGPT.Okounkov.ValGen.inftySemigroup_mem_fullSemigroupLocus f E Y hY a' H'
    c v hS' hG' hφ' hφ'an
  -- the degreewise sums
  let W : AddSubsemigroup ((Fin (m + 1) → ℤ) × ℤ) :=
    { carrier := {z | ∃ (x y : Fin (m + 1) → ℤ) (k : ℤ), (x, k) ∈ A ∧ (y, k) ∈ B ∧ z = (x + y, k)}
      add_mem' := by
        rintro _ _ ⟨x, y, k, hx, hy, rfl⟩ ⟨x', y', k', hx', hy', rfl⟩
        refine ⟨x + x', y + y', k + k', A.add_mem hx hx', B.add_mem hy hy', ?_⟩
        refine Prod.ext ?_ rfl
        change x + y + (x' + y') = x + x' + (y + y')
        abel }
  have hWΓ : (W : Set ((Fin (m + 1) → ℤ) × ℤ)) ⊆
      AlgebraicValuation.multiplierSectionSet f (m + 1) E v c d (fun x => φ x + φ' x) := by
    rintro _ ⟨x, y, k, hx, hy, rfl⟩
    exact SGPT.Okounkov.ValGen.inftySectionSet_subset_multiplierSectionSet f E d H'' c v hsum
      (inftySectionSet_add_mem_tensor f (m + 1) E v hc a a' d x y k hx hy)
  have hWC : W ≤ latticePoints C''.cone := fun z hz =>
    SGPT.Okounkov.ValGen.multiplierSectionSet_subset_cone f E d c v hS'' _ (hWΓ hz)
  have hWgen : LatticeSlices.generatedGroup W = ⊤ :=
    closure_degreeSum_eq_top A B hfullA.2 hfullB.2 (inftySemigroup_degree_nonneg f E c v a φ)
      (inftySemigroup_degree_nonneg f E c v a' φ') W
      (fun x y k hx hy => ⟨x, y, k, hx, hy, rfl⟩)
  have hWfull := sourceSubset_mem_fullSemigroupLocus C'' W hWC hWgen
  -- `Γ(θ + θ', φ + φ')` is an almost semigroup
  have hΓ := SGPT.Okounkov.ValGen.multiplierConeSubset_mem_almostSemigroupLocus_of_mass f E Y hY d
    H'' c v hS'' hG'' hsum hmass
  have hmono := SGPT.AlmostSemigroup.OkounkovComparison.bodyExtension_mono
    (fullToAlmost (⟨_, hWfull⟩ : FullSemigroup C''))
    ⟨SGPT.Okounkov.ValGen.multiplierConeSubset f E d c v hS'' (fun x => φ x + φ' x), hΓ⟩ hWΓ
  rw [bodyExtension_source] at hmono
  rw [partialBody_eq_euclideanBody_inftySemigroup f E Y hY c v a H hS hG hφ hφan,
    partialBody_eq_euclideanBody_inftySemigroup f E Y hY c v a' H' hS' hG' hφ' hφ'an,
    SGPT.Okounkov.ValGen.partialBody_eq d _ _ hΓ]
  refine Set.Subset.trans ?_ hmono
  have hadd := SGPT.Okounkov.AlgebraicBody.body_add_subset_of_mul A B W
    (zero_mem_inftySemigroup f E c v a φ) (zero_mem_inftySemigroup f E c v a' φ')
    (inftySemigroup_degree_nonneg f E c v a φ) (inftySemigroup_degree_nonneg f E c v a' φ')
    (fun x y k hx hy => ⟨x, y, k, hx, hy, rfl⟩)
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨x + y, hadd ⟨x, hx, y, hy, rfl⟩, by rw [map_add]⟩

end Analytic

end SGPT.Okounkov.ValGen2
