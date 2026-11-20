import SGPT.Checks.Comparison.SourceDXZClasses
import SGPT.Checks.Comparison.BJOriginalRegularity
import SGPT.NAPotential.TowerAlgReflect
import SGPT.NAPotential.ProjectiveLimit
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Checks.Comparison.SourceDXZPOrder

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


run_cmd Lean.logInfo "SOURCE_DXZ_GLUE: imports-ready"

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

/-! ### Gluing equivalent elements of `PSH^NA(X, θ_i)` into `PSH^NA(X, θ)` -/

section Glue

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Some multiple `δ' ω₀` with `0 < δ' < δ` lies below any given Kähler form. -/
theorem sourceKahlerForm_exists_smul_le (omega : KahlerBackground n M) (κ : SourceKahlerForm n M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (δ' : ℝ) (hδ' : 0 < δ'), δ' < δ ∧
      sourceKahlerFormLE (sourceKahlerFormOfBackground (KahlerBackground.smul hδ' omega)) κ := by
  let ρ := sourceKahlerFormRepresentative κ
  obtain ⟨A, hA, hs⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul ρ (fun _ : Unit => -omega.form)
  let δ' := min (δ / 2) (1 / A)
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by positivity)
  have hδ'lt : δ' < δ := (min_le_left _ _).trans_lt (by linarith)
  have hδ'A : δ' ≤ 1 / A := min_le_right _ _
  refine ⟨δ', hδ'pos, hδ'lt, ?_⟩
  have hsemi : (ρ.form - (KahlerBackground.smul hδ'pos omega).form).val.IsSemipositive := by
    have h : ρ.form - (KahlerBackground.smul hδ'pos omega).form =
        (1 / A) • (-omega.form + A • ρ.form) + (1 / A - δ') • omega.form := by
      simp only [KahlerBackground.smul_form]
      rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ hA.ne', one_smul]
      module
    rw [h]
    have h1 := KahlerDomination.isSemipositive_smul (hs ()) (by positivity : (0 : ℝ) ≤ 1 / A)
    have h2 := KahlerDomination.isSemipositive_smul omega.isSemipositive
      (by linarith : (0 : ℝ) ≤ 1 / A - δ')
    intro e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
      add_nonneg (h1 e z hz v) (h2 e z hz v)
  have h := (sourceKahlerFormLE_ofBackground_iff (KahlerBackground.smul hδ'pos omega) ρ).mpr hsemi
  simpa only [ρ, sourceKahlerFormRepresentative_class] using h

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
    rw [← congrFun h v, SourceDXZPOrder.naPotentialAnAt_eq_of_POrder_equivalent (k + 1) E hT.2 hT.1 ω v]
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

/-- An actual original rational GF package is bounded by its trivial value. -/
theorem rationalGF_le_trivial {L : RationalPicardSpace X} {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f L φ) (v : BerkovichPoint f) :
    φ v ≤ φ (BerkovichPoint.trivial f) := by
  obtain ⟨D, -, rfl⟩ := hφ
  exact D.eval_le_trivial f v

/-- The infimum of a tail of a decreasing sequence is the infimum of the sequence. -/
theorem iInf_add_eq_of_antitone {g : ℕ → EReal} (hg : Antitone g) (i : ℕ) :
    ⨅ j, g (i + j) = ⨅ j, g j :=
  le_antisymm (le_iInf fun j => (iInf_le _ j).trans (hg (Nat.le_add_left j i)))
    (le_iInf fun j => iInf_le _ (i + j))


end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
