import SGPT.Checks.Comparison.DXZSurjClasses
import SGPT.Checks.Comparison.DimZeroComparison
import SGPT.Checks.Comparison.DimZeroDXZ
import SGPT.NAPotential.ProjectiveLimit
import SGPT.NAPotential.VolumeContinuity
import SGPT.NAPotential.AnTransBimero

/-!
# Surjectivity in `thm:DXZ` (positive dimension, under `AlgebraicPrimesRealized`)

Source: `chapter_NApotential.tex`, `thm:DXZ`: *The map `eq:analymap` is an order preserving
bijection*, and its proof of surjectivity: *Let `φ ∈ PSH(L^An)`. Let `H` be an ample line bundle
and `(ε_i)_i` be a decreasing sequence of rational numbers with limit `0`,
`φ_i ∈ H^gf_ℚ((L + ε_i H)^An)` such that `φ = inf_i φ_i` (`thm:BJappseq`). Fix a Kähler form
`ω ∈ c₁(H)`. Thanks to `lma:gfinimage`, we can find `Γ^i ∈ PSH^NA(X, θ + ε_i ω)` with
`(Γ^i)^An = φ_i`. It follows from `lma:anaorder` that `Γ^i ≥ P_{θ+ε_iω}[Γ^{i+1}]_𝓘 ≥ Γ^{i+1}` …
`Γ^{θ+ω'} = inf_{i ≫ 1} P_{θ+ω'}[Γ^i]_𝓘` … `(Γ^{θ+ω'})^An = φ` (`prop:anpreinf`) … the
`(Γ^{θ+ω'})_{ω'}` define an element `Γ ∈ PSH^NA(X, θ)` with `Γ^An = φ`.*

## Formalization of the proof

* `H`, `ω_H`: `exists_isAmple_isKahler` (`H = 𝒪_X(1)^{⊗ a} ⊗ S`, Kähler curvature);
* `φ_i`: `bjAppSeq_holds` (`thm:BJappseq`) for this `H`;
* `Γ^i ∈ PSH^NA(X, θ_i)`, `θ_i = θ + ε_i ω_H`: `exists_naPotential_eq_of_isRationalGF_twist`
  (`lma:gfinimage` in the class `L + ε_i H`);
* the infimum is taken, as in the book, after projecting to a fixed background; we take the
  backgrounds `θ_i` themselves (which, unlike `θ + ω'` for an arbitrary Kähler `ω'`, are curvature
  forms of `ℚ`-line bundles, where `prop:anpreinf` on `X^An` is available):
  `Δ^i = inf_{j ≥ 0} P_{θ_i}[Γ^{i+j}]_𝓘 ∈ PSH^NA(X, θ_i)` with `(Δ^i)^An = inf_j φ_{i+j} = φ`;
* the `Δ^i` are pairwise equivalent (`lma:anaorder` after a transition,
  `sourceNAPOrder_equivalent_of_naPotentialAnAt_eq`), and every Kähler `ω'` dominates some
  `ε_i ω_H` (`exists_twistForm_le`), so `P_{θ+ω'}[Δ^{i(ω')}]_𝓘` is a compatible family
  (`prop:NApotential:L222`) whose preimage `Γ ∈ PSH^NA(X, θ)` is equivalent to every `Δ^i`
  (`exists_sourceNAPotential_POrder_equivalent`), hence `Γ^An = φ`
  (`naPotentialAnAt_eq_of_POrder_equivalent`).

## Main results

* **`exists_naPotential_eq_of_isModuleTopologyPSH`**, **`naAnalytification_surjective`**:
  surjectivity of `eq:analymap`;
* **`source_DXZ`**: `thm:DXZ` (order preserving and reflecting bijection), positive dimension,
  with `AlgebraicPrimesRealized` as explicit hypothesis (dimension zero:
  `DimZero.source_DXZ_of_dim_zero`); **`source_DXZ_of_hypothesis`**: every dimension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.BJ.DXZSurj

open Set Filter
open scoped Topology
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

/-! ### Gluing equivalent elements of `PSH^NA(X, θ_i)` into `PSH^NA(X, θ)` -/

section Glue

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- **Gluing over `Kah(X)`** (end of the proof of `thm:DXZ`, via `prop:NApotential:L222`): let
`Δ^i ∈ PSH^NA(X, σ_i)` be pairwise equivalent in the intrinsic order, and assume that for every
Kähler form `ω'` some `σ_i` lies below `θ + ω'`. Then the transitions `P_{θ+ω'}[Δ^{i(ω')}]_𝓘` form
a compatible family, and its preimage `Γ ∈ PSH^NA(X, θ)` is equivalent to every `Δ^i`. -/
theorem exists_sourceNAPotential_POrder_equivalent {ι : Type*}
    (σ : ι → AtlasClosedRealOneOneForm (ofFixedModel n M)) (Δ : ∀ i, SourceNAPotential (σ i))
    (hΔ : ∀ i j, SourceNAPOrder (Δ i) (Δ j))
    (hσ : ∀ κ : SourceKahlerForm n M, ∃ i,
      (atlasClosedFormToNative (sourceNAComponentBackground θ κ) -
        atlasClosedFormToNative (σ i)).val.IsSemipositive)
    (κ₀ : SourceKahlerForm n M) :
    ∃ Γ : SourceNAPotential θ, ∀ i, SourceNAPOrder Γ (Δ i) ∧ SourceNAPOrder (Δ i) Γ := by
  choose idx hidx using hσ
  let fam : ∀ κ : SourceKahlerForm n M, SourceNAPotential (sourceNAComponentBackground θ κ) :=
    fun κ => (Δ (idx κ)).transition (hidx κ)
  have hfam : ∀ κ, SourceNAPOrder (Δ (idx κ)) (fam κ) ∧ SourceNAPOrder (fam κ) (Δ (idx κ)) :=
    fun κ => (Δ (idx κ)).transition_POrder_equivalent (sourceKahlerFormRepresentative κ) (hidx κ)
  let P : SourceNAProjectiveLimit θ :=
    { family := fam
      compatible := fun κ ζ h => by
        have ht := (fam κ).transition_POrder_equivalent (sourceKahlerFormRepresentative ζ)
          (sourceNAComponentBackground_difference θ h)
        exact SourceNAPOrder.antisymm
          (ht.2.trans ((hfam κ).2.trans ((hΔ (idx κ) (idx ζ)).trans (hfam ζ).1)))
          ((hfam ζ).2.trans ((hΔ (idx ζ) (idx κ)).trans ((hfam κ).1.trans ht.1))) }
  have h1 : SourceNAPOrder P.preimage (P.family κ₀) :=
    ⟨κ₀, (P.preimageComponent_POrder_equivalent κ₀ κ₀ κ₀).1⟩
  have h2 : SourceNAPOrder (P.family κ₀) P.preimage :=
    ⟨κ₀, (P.preimageComponent_POrder_equivalent κ₀ κ₀ κ₀).2⟩
  refine ⟨P.preimage, fun i => ⟨h1.trans ((hfam κ₀).2.trans (hΔ (idx κ₀) i)),
    ((hΔ i (idx κ₀)).trans (hfam κ₀).1).trans h2⟩⟩

end Glue

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance dxzSurjLimitProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance dxzSurjLimitPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxzSurjLimitPointCharts :
    ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance dxzSurjLimitPointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-! ### Equal analytifications in comparable backgrounds -/

/-- If `β - α` is semipositive and `Γ ∈ PSH^NA(X, α)`, `Δ ∈ PSH^NA(X, β)` have the same
analytification on `X^An`, then `Γ` and `Δ` are equivalent in the intrinsic order (`lma:anaorder`
applied to `P_β[Γ]_𝓘` and `Δ`). -/
theorem sourceNAPOrder_equivalent_of_naPotentialAnAt_eq
    {α β : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Γ : SourceNAPotential α) (Δ : SourceNAPotential β)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f))
    (h : naPotentialAnAt (k + 1) E Γ ω = naPotentialAnAt (k + 1) E Δ ω) :
    SourceNAPOrder Γ Δ ∧ SourceNAPOrder Δ Γ := by
  have hT := Γ.transition_POrder_equivalent (sourceKahlerFormRepresentative ω) hαβ
  have hTan : ∀ v, naPotentialAnAt (k + 1) E (Γ.transition hαβ) ω v =
      naPotentialAnAt (k + 1) E Δ ω v := by
    intro v
    rw [← congrFun h v, naPotentialAnAt_eq_of_POrder_equivalent (k + 1) E hT.2 hT.1 ω v]
  have h1 : SourceNAPOrder (Γ.transition hαβ) Δ :=
    (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := E) ω).mpr fun v => (hTan v).le
  have h2 : SourceNAPOrder Δ (Γ.transition hαβ) :=
    (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := E) ω).mpr fun v => (hTan v).ge
  exact ⟨hT.1.trans h1, h2.trans hT.2⟩

/-! ### The backgrounds `θ + ε ω_H` -/

section Backgrounds

variable {H : X.Modules} (bH : LineBundleAtlas H) (HH : SchemeLineBundleMetric f (k + 1) E H)
  (θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f)))

/-- `θ + ε ω_H ≤ θ + ε' ω_H` for `ε ≤ ε'` when `ω_H` is semipositive. -/
theorem twistForm_sub_semipositive (hK : (HH.curvature bH).val.IsKahler) {ε ε' : ℝ}
    (h : ε ≤ ε') :
    (atlasClosedFormToNative (twistForm f (k + 1) E bH HH θ ε') -
      atlasClosedFormToNative (twistForm f (k + 1) E bH HH θ ε)).val.IsSemipositive := by
  rw [twistForm_native, twistForm_native]
  have heq : (atlasClosedFormToNative θ + ε' • HH.curvature bH) -
      (atlasClosedFormToNative θ + ε • HH.curvature bH) = (ε' - ε) • HH.curvature bH := by
    module
  rw [heq]
  exact Pending.KahlerDomination.isSemipositive_smul
    (KahlerBackground.isSemipositive ⟨HH.curvature bH, hK⟩) (sub_nonneg.mpr h)

/-- **Every Kähler form dominates some `ε_i ω_H`** (`thm:DXZ`: *after discarding finitely many `i`
so that `ω' ≥ ε_i ω`*): if `ε_i → 0`, then for every Kähler `ω'` some `θ + ε_i ω_H` lies below
`θ + ω'`. -/
theorem exists_twistForm_le (hK : (HH.curvature bH).val.IsKahler) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (κ : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    ∃ i, (atlasClosedFormToNative (sourceNAComponentBackground θ κ) -
      atlasClosedFormToNative (twistForm f (k + 1) E bH HH θ (ε i))).val.IsSemipositive := by
  let ωH : KahlerBackground (k + 1) (SchemeComplexPoint f) := ⟨HH.curvature bH, hK⟩
  obtain ⟨δ, hδ, -, hle⟩ := sourceKahlerForm_exists_smul_le ωH κ one_pos
  have hsemi : ((sourceKahlerFormRepresentative κ).form -
      (KahlerBackground.smul hδ ωH).form).val.IsSemipositive := by
    rw [← sourceKahlerFormRepresentative_class κ] at hle
    exact (sourceKahlerFormLE_ofBackground_iff _ _).mp hle
  obtain ⟨i, hi⟩ := (hε.eventually (gt_mem_nhds hδ)).exists
  refine ⟨i, ?_⟩
  rw [sourceNAComponentBackground_native, twistForm_native]
  have heq : (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form) -
      (atlasClosedFormToNative θ + ε i • HH.curvature bH) =
      ((sourceKahlerFormRepresentative κ).form - (KahlerBackground.smul hδ ωH).form) +
        (δ - ε i) • ωH.form := by
    simp only [KahlerBackground.smul_form, ωH]
    module
  rw [heq]
  have h2 := Pending.KahlerDomination.isSemipositive_smul ωH.isSemipositive
    (sub_nonneg.mpr hi.le)
  intro e z hz v
  simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
    add_nonneg (hsemi e z hz v) (h2 e z hz v)

end Backgrounds

/-! ### Surjectivity -/

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

/-- The infimum of a tail of a decreasing sequence is the infimum of the sequence. -/
theorem iInf_add_eq_of_antitone {g : ℕ → EReal} (hg : Antitone g) (i : ℕ) :
    ⨅ j, g (i + j) = ⨅ j, g j :=
  le_antisymm (le_iInf fun j => (iInf_le _ j).trans (hg (Nat.le_add_left j i)))
    (le_iInf fun j => iInf_le _ (i + j))

include hm hθ in
/-- **Surjectivity in `thm:DXZ`** (positive dimension, under `AlgebraicPrimesRealized`): for `X`
integral, projective and smooth of relative dimension `k + 1` over `ℂ` (closed projective
embedding `E`, `X(ℂ)` connected), `L = m⁻¹ [M]`, `θ = m⁻¹ c₁(M, h_M)`, every `φ ∈ PSH(L^An)`
(`def:BJpshmetric`) is `Γ^An` on all of `X^An` for some `Γ ∈ PSH^NA(X, θ)`. -/
theorem exists_naPotential_eq_of_isModuleTopologyPSH (halg : AlgebraicPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) {φ : BerkovichPoint f → EReal}
    (hφ : IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ Γ : SourceNAPotential θ, naPotentialAnAt (k + 1) E Γ ω = φ := by
  obtain ⟨H, hH, bH, HH, hK⟩ := exists_isAmple_isKahler f (k + 1) E
  obtain ⟨ε, ψ, hεpos, hεanti, hεlim, hψ, hanti, hlim⟩ :=
    bjAppSeq_holds.{0} f H hH ((m : ℚ)⁻¹ • rationalPicardClass b) φ hφ
  have hψ' : ∀ i, IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b +
      ε i • rationalPicardClass bH) (ψ i) := by
    intro i
    rw [rationalPicardClass_atlas_independent bH (atlasOfInvertible hH.isInvertible)]
    exact hψ i
  have hφinf : ∀ v, φ v = ⨅ i, ψ i v := fun v =>
    tendsto_nhds_unique (hlim v) (tendsto_atTop_iInf (hanti v))
  obtain ⟨v₀, hv₀⟩ : ∃ v, φ v ≠ ⊥ := hφ.1
  have hv₀top : φ v₀ ≠ ⊤ :=
    ne_top_of_le_ne_top ((hψ 0).ne_top f v₀) ((hφinf v₀).le.trans (iInf_le _ 0))
  -- the backgrounds `θ_i = θ + ε_i ω_H`
  let σ : ℕ → AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f)) :=
    fun i => twistForm f (k + 1) E bH HH θ (ε i : ℝ)
  have hσ : ∀ i j, i ≤ j →
      (atlasClosedFormToNative (σ i) - atlasClosedFormToNative (σ j)).val.IsSemipositive :=
    fun i j hij => twistForm_sub_semipositive f k E bH HH θ hK
      (by exact_mod_cast hεanti.antitone hij)
  -- `Γ^i ∈ PSH^NA(X, θ_i)` with `(Γ^i)^An = φ_i` (`lma:gfinimage`)
  choose Γ hΓ using fun i => exists_naPotential_eq_of_isRationalGF_twist f k E b HM bH HH hm hθ
    halg ω (ε i) (hεpos i).le (hψ' i)
  -- `P_{θ_i}[Γ^{i+j}]_𝓘`
  let T : ∀ i, ℕ → SourceNAPotential (σ i) := fun i j =>
    (Γ (i + j)).transition (hσ i (i + j) (Nat.le_add_right i j))
  have hT : ∀ i j, naPotentialAnAt (k + 1) E (T i j) ω = ψ (i + j) := by
    intro i j
    have he := (Γ (i + j)).transition_POrder_equivalent (sourceKahlerFormRepresentative ω)
      (hσ i (i + j) (Nat.le_add_right i j))
    funext v
    rw [naPotentialAnAt_eq_of_POrder_equivalent (k + 1) E he.2 he.1 ω v, hΓ]
  have ha : ∀ i j j', j ≤ j' → SourceNAPOrder (T i j') (T i j) := fun i j j' hjj' =>
    (TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := E) ω).mpr fun v => by
      rw [hT i j', hT i j]
      exact hanti v (Nat.add_le_add_left hjj' i)
  set omega := sourceKahlerFormRepresentative ω with homega
  have hr : (((φ v₀).toReal : ℝ) : EReal) = φ v₀ := EReal.coe_toReal hv₀top hv₀
  have hb : ∀ i, BddBelow (range fun j => sourceNAPotentialCutoff omega (T i j)) := by
    intro i
    refine ⟨(φ v₀).toReal, ?_⟩
    rintro _ ⟨j, rfl⟩
    show (φ v₀).toReal ≤ sourceNAPotentialCutoff omega (T i j)
    rw [sourceNAPotentialCutoff_eq_component omega (T i j) ω]
    have h1 := DivDict2.naPotentialAnAt_trivial (E := E) (T i j) ω
    rw [hT] at h1
    have h2 : (((φ v₀).toReal : ℝ) : EReal) ≤ ψ (i + j) (BerkovichPoint.trivial f) := by
      rw [hr, hφinf v₀]
      exact (iInf_le _ (i + j)).trans (GfIm.IsRationalGF.le_trivial f (hψ (i + j)) v₀)
    rw [h1] at h2
    exact_mod_cast h2
  -- `Δ^i = inf_j P_{θ_i}[Γ^{i+j}]_𝓘 ∈ PSH^NA(X, θ_i)` with `(Δ^i)^An = φ` (`prop:anpreinf`)
  let Δ : ∀ i, SourceNAPotential (σ i) := fun i =>
    SourceNAPotential.decreasingInf omega (T i) (ha i) (hb i)
  have hΔ : ∀ i, naPotentialAnAt (k + 1) E (Δ i) ω = φ := by
    intro i
    have hm' : 0 < m * (ε i).den := Nat.mul_pos hm (ε i).den_pos
    rw [Exist.naPotentialAnAt_decreasingInf f k E
      (twistLineAtlas b bH (ε i).den (m * (ε i).num.toNat))
      (twistLineMetric f (k + 1) E b HM bH HH (ε i).den (m * (ε i).num.toNat)) hm'
      (twistForm_geometricallyEq f (k + 1) E b HM bH HH hm hθ (ε i) (hεpos i).le) halg omega
      (T i) (ha i) (hb i) ω]
    funext v
    simp only [hT]
    rw [hφinf v, iInf_add_eq_of_antitone (hanti v) i]
  -- the `Δ^i` are pairwise equivalent (`lma:anaorder`)
  have hequiv : ∀ i j, SourceNAPOrder (Δ i) (Δ j) := by
    intro i j
    rcases le_total i j with hij | hji
    · exact (sourceNAPOrder_equivalent_of_naPotentialAnAt_eq f k E (hσ i j hij) (Δ j) (Δ i) ω
        (by rw [hΔ, hΔ])).2
    · exact (sourceNAPOrder_equivalent_of_naPotentialAnAt_eq f k E (hσ j i hji) (Δ i) (Δ j) ω
        (by rw [hΔ, hΔ])).1
  -- gluing over `Kah(X)` (`prop:NApotential:L222`)
  obtain ⟨Γ₀, hΓ₀⟩ := exists_sourceNAPotential_POrder_equivalent (θ := θ) σ Δ hequiv
    (fun κ => exists_twistForm_le f k E bH HH θ hK hεlim κ) ω
  refine ⟨Γ₀, ?_⟩
  funext v
  rw [naPotentialAnAt_eq_of_POrder_equivalent (k + 1) E (hΓ₀ 0).1 (hΓ₀ 0).2 ω v, hΔ 0]

include hm hθ in
/-- **`thm:DXZ`, surjectivity** (positive dimension, under `AlgebraicPrimesRealized`): the map
`eq:analymap` `PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`, is surjective. -/
theorem naAnalytification_surjective (halg : AlgebraicPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    Function.Surjective (Exist.naAnalytification (θ := θ) f (k + 1) E b HM hm hθ ω) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨Γ, hΓ⟩ := exists_naPotential_eq_of_isModuleTopologyPSH f k E b HM hm hθ halg ω hφ
  exact ⟨Γ, Subtype.ext hΓ⟩

include hm hθ in
/-- **`thm:DXZ`** (positive dimension, with `AlgebraicPrimesRealized` as explicit hypothesis):
for `X` integral, projective and smooth of relative dimension `k + 1` over `ℂ` (closed projective
embedding, `X(ℂ)` connected), `L = m⁻¹ [M]` and `θ = c₁(L, h)`, the map `eq:analymap`
`PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`, is an order preserving (and order reflecting) bijection.
In dimension zero the same statement holds unconditionally (`DimZero.source_DXZ_of_dim_zero`). -/
theorem source_DXZ (halg : AlgebraicPrimesRealized (f := f) k E)
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    (∀ Γ Γ' : SourceNAPotential θ, SourceNAPOrder Γ Γ' ↔
      ∀ v, (Exist.naAnalytification f (k + 1) E b HM hm hθ ω Γ).1 v ≤
        (Exist.naAnalytification f (k + 1) E b HM hm hθ ω Γ').1 v) ∧
      Function.Bijective (Exist.naAnalytification (θ := θ) f (k + 1) E b HM hm hθ ω) :=
  ⟨fun _ _ => (DimZero.naAnalytification_le_iff_dim f (k + 1) E b HM hm hθ ω).symm,
    DimZero.naAnalytification_injective_dim f (k + 1) E b HM hm hθ ω,
    naAnalytification_surjective f k E b HM hm hθ halg ω⟩

/-! ### Every dimension -/

section AllDimensions

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) [IsProjective f]
  [IsIntegral X]

local instance dxzSurjAllProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

/-- The hypothesis under which `thm:DXZ` is proved in relative dimension `n`: none in dimension
zero, the algebraic half `AlgebraicPrimesRealized` of the dictionary of prime divisors in positive
dimension. -/
def DXZHypothesis : (n : ℕ) → [SmoothOfRelativeDimension n f] → Prop
  | 0, _ => True
  | k + 1, _ => AlgebraicPrimesRealized (f := f) k E

variable (n : ℕ) [SmoothOfRelativeDimension n f]

local instance dxzSurjAllPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxzSurjAllPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dxzSurjAllPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`thm:DXZ` in every relative dimension `n`** (unconditional for `n = 0`, under
`AlgebraicPrimesRealized` for `n > 0`): the map `eq:analymap` `PSH^NA(X, θ) → PSH(L^An)` is an
order preserving (and order reflecting) bijection. -/
theorem source_DXZ_of_hypothesis (hyp : DXZHypothesis f E n)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    (∀ Γ Γ' : SourceNAPotential θ, SourceNAPOrder Γ Γ' ↔
      ∀ v, (Exist.naAnalytification f n E b HM hm hθ ω Γ).1 v ≤
        (Exist.naAnalytification f n E b HM hm hθ ω Γ').1 v) ∧
      Function.Bijective (Exist.naAnalytification (θ := θ) f n E b HM hm hθ ω) := by
  cases n with
  | zero => exact DimZero.source_DXZ_of_dim_zero f E b HM hm hθ ω
  | succ k => exact source_DXZ f k E b HM hm hθ hyp ω

end AllDimensions

end SGPT.NAPotential.BJ.DXZSurj
