import SGPT.Checks.Comparison.ThinApprox.SourceDXZGlue
import SGPT.Checks.Comparison.ThinApprox.BJRelAmpleAppSeq
import SGPT.Checks.Comparison.ThinApprox.SourceNet
import SGPT.NAPotential.AlgebraicPrimeDictionaryMain

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


run_cmd Lean.logInfo "SOURCE_DXZ_FINAL: imports-ready"

/-! Positive-dimensional comparison with the actual algebraic-prime dictionary.

This is a fresh source proof of the existing limit argument, using the same
original maps and rational Chern background. Its narrow imports avoid the
independent zero-dimensional approximation development. No dictionary or
surjectivity conclusion is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
open SGPT.NAPotential.BJ.SourceDXZPositive

open Set Filter
open scoped Topology
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed
open SGPT.Foundations.Envelope
open SGPT.NAPotential.BJ.DXZSurj SGPT.NAPotential.BJ.SourceDXZClasses

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension (k + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance dxzSurjFinalProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance dxzSurjFinalPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxzSurjFinalPointCharts :
    ChartedSpace (ComplexModel (k + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (k + 1)
local instance dxzSurjFinalPointManifold : IsComplexManifold (k + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (k + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (k + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (k + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **Surjectivity in `thm:DXZ`** (positive dimension): for `X`
integral, projective and smooth of relative dimension `k + 1` over `ℂ` (closed projective
embedding `E`, `X(ℂ)` connected), `L = m⁻¹ [M]`, `θ = m⁻¹ c₁(M, h_M)`, every `φ ∈ PSH(L^An)`
(`def:BJpshmetric`) is `Γ^An` on all of `X^An` for some `Γ ∈ PSH^NA(X, θ)`. -/
theorem exists_naPotential_eq_of_isModuleTopologyPSH
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) {φ : BerkovichPoint f → EReal}
    (hφ : IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ Γ : SourceNAPotential θ, naPotentialAnAt (k + 1) E Γ ω = φ := by
  have halg := AlgebraicPrimeDictionary.algebraicPrimesRealized (m := k) E
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
    ω (ε i) (hεpos i).le (hψ' i)
  -- `P_{θ_i}[Γ^{i+j}]_𝓘`
  let T : ∀ i, ℕ → SourceNAPotential (σ i) := fun i j =>
    (Γ (i + j)).transition (hσ i (i + j) (Nat.le_add_right i j))
  have hT : ∀ i j, naPotentialAnAt (k + 1) E (T i j) ω = ψ (i + j) := by
    intro i j
    have he := (Γ (i + j)).transition_POrder_equivalent (sourceKahlerFormRepresentative ω)
      (hσ i (i + j) (Nat.le_add_right i j))
    funext v
    rw [SourceDXZPOrder.naPotentialAnAt_eq_of_POrder_equivalent (k + 1) E he.2 he.1 ω v, hΓ]
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
      exact (iInf_le _ (i + j)).trans (rationalGF_le_trivial f (hψ (i + j)) v₀)
    rw [h1] at h2
    exact_mod_cast h2
  -- `Δ^i = inf_j P_{θ_i}[Γ^{i+j}]_𝓘 ∈ PSH^NA(X, θ_i)` with `(Δ^i)^An = φ` (`prop:anpreinf`)
  let Δ : ∀ i, SourceNAPotential (σ i) := fun i =>
    SourceNAPotential.decreasingInf omega (T i) (ha i) (hb i)
  have hΔ : ∀ i, naPotentialAnAt (k + 1) E (Δ i) ω = φ := by
    intro i
    have hm' : 0 < m * (ε i).den := Nat.mul_pos hm (ε i).den_pos
    rw [SGPT.NAPotential.ThinApprox.BJ.SourceNet.naPotentialAnAt_decreasingInf f k E
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
  rw [SourceDXZPOrder.naPotentialAnAt_eq_of_POrder_equivalent (k + 1) E (hΓ₀ 0).1 (hΓ₀ 0).2 ω v, hΔ 0]

include hm hθ in
/-- **`thm:DXZ`, surjectivity** (positive dimension): the map
`eq:analymap` `PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`, is surjective. -/
theorem naAnalytification_surjective
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    Function.Surjective (SGPT.NAPotential.BJ.SourceNet.naAnalytification (θ := θ) f (k + 1) E b HM hm hθ ω) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨Γ, hΓ⟩ := exists_naPotential_eq_of_isModuleTopologyPSH f k E b HM hm hθ ω hφ
  exact ⟨Γ, Subtype.ext hΓ⟩

include hm hθ in
/-- **`thm:DXZ`** (positive dimension, using the actual dictionary):
for `X` integral, projective and smooth of relative dimension `k + 1` over `ℂ` (closed projective
embedding, `X(ℂ)` connected), `L = m⁻¹ [M]` and `θ = c₁(L, h)`, the map `eq:analymap`
`PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An`, is an order preserving (and order reflecting) bijection.
In dimension zero the same statement holds unconditionally (`DimZero.source_DXZ_of_dim_zero`). -/
theorem source_DXZ
    (ω : SourceKahlerForm (k + 1) (SchemeComplexPoint f)) :
    (∀ Γ Γ' : SourceNAPotential θ, SourceNAPOrder Γ Γ' ↔
      ∀ v, (SGPT.NAPotential.BJ.SourceNet.naAnalytification f (k + 1) E b HM hm hθ ω Γ).1 v ≤
        (SGPT.NAPotential.BJ.SourceNet.naAnalytification f (k + 1) E b HM hm hθ ω Γ').1 v) ∧
      Function.Bijective (SGPT.NAPotential.BJ.SourceNet.naAnalytification (θ := θ) f (k + 1) E b HM hm hθ ω) :=
  ⟨fun _ _ => TowerAlg.sourceNAPOrder_iff_naPotentialAnAt_le (E := E) ω,
    fun _ _ h => TowerAlg.naPotentialAnAt_injective (E := E) ω (congrArg Subtype.val h),
    naAnalytification_surjective f k E b HM hm hθ ω⟩


end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
