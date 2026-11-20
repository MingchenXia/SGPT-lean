import SGPT.Envelopes.RelativeMARooftop
import SGPT.NPP.DimensionZero

/-!
# The relative Aubin–Yau theorem and the rooftop equation in every dimension

`RelativeMAAubinYau` and `RelativeMARooftop` prove the existence parts of `thm:AY_rel`
and `lma:rooftop_MAequation` when `dim X > 0` (the variational method uses the
Euler–Lagrange equation of TN, stated for positive dimension). On a connected
zero-dimensional manifold `X` is one point `x₀`, every `θ`-psh function is a finite
constant and its non-pluripolar product is the Dirac mass at `x₀`
(`SGPT.NPP.DimensionZero`, source `rmk:npp:L275`); the solutions are explicit:
`u = -λ⁻¹ log μ(X)` and `γ = -log(e^{-φ(x₀)} + e^{-ψ(x₀)})`.

The final source theorems `source_relative_aubinYau` and `source_rooftop_MAequation`
hold without any dimension hypothesis. The comparison clause of `thm:AY_rel` never
needed one.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set MeasureTheory
open scoped ENNReal

theorem measure_eq_smul_dirac_of_subsingleton {M : Type*} [MeasurableSpace M] [Subsingleton M]
    (μ : Measure M) (x₀ : M) : μ = μ univ • Measure.dirac x₀ := by
  ext s hs
  by_cases hx : x₀ ∈ s
  · have hse : s = univ := eq_univ_of_forall fun y => Subsingleton.elim x₀ y ▸ hx
    subst hse
    simp
  · have hse : s = ∅ := eq_empty_of_forall_notMem fun y hy => hx (Subsingleton.elim y x₀ ▸ hy)
    subst hse
    simp

theorem withDensity_eq_smul_of_subsingleton {M : Type*} [MeasurableSpace M] [Subsingleton M]
    (μ : Measure M) (f : M → ℝ≥0∞) (x₀ : M) : μ.withDensity f = f x₀ • μ := by
  have hf : f = fun _ => f x₀ := funext fun x => congrArg f (Subsingleton.elim x x₀)
  rw [hf, withDensity_const]

theorem singularityEquiv_of_subsingleton {M : Type*} [Subsingleton M] {u v : M → EReal}
    (hu : ∀ x, u x ≠ ⊤ ∧ u x ≠ ⊥) (hv : ∀ x, v x ≠ ⊤ ∧ v x ≠ ⊥) :
    SGPT.PSH.SingularityEquiv u v := by
  have key : ∀ {a b : M → EReal}, (∀ x, a x ≠ ⊤ ∧ a x ≠ ⊥) → (∀ x, b x ≠ ⊤ ∧ b x ≠ ⊥) →
      SGPT.Foundations.Analysis.MoreSingularOn a b univ := by
    intro a b ha hb
    by_cases hM : Nonempty M
    · obtain ⟨x₀⟩ := hM
      refine ⟨(a x₀).toReal - (b x₀).toReal, fun x _ => ?_⟩
      rw [Subsingleton.elim x x₀, ← EReal.coe_toReal (ha x₀).1 (ha x₀).2,
        ← EReal.coe_toReal (hb x₀).1 (hb x₀).2, ← EReal.coe_add, EReal.toReal_coe,
        EReal.toReal_coe]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · exact ⟨0, fun x _ => absurd ⟨x⟩ hM⟩
  exact ⟨key hu hv, key hv hu⟩

end SGPT.Envelopes.RelativeMA

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.RelativeMA

section DimZero

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)} {φ : M → EReal}

/-- `thm:AY_rel`, existence, in dimension `0`. -/
theorem source_relative_aubinYau_exists_dim_zero (hφ : SourceModelPotential θ φ) {lam : ℝ}
    (hlam : 0 < lam) {μ : Measure M} (hμ : SourceNonPluripolarMeasure (n := 0) μ)
    (hμ0 : 0 < μ univ) :
    ∃ u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesExpEquation θ lam μ u := by
  have : Subsingleton M := SGPT.NPP.subsingleton_of_dim_zero
  have hne : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ.toNative
  obtain ⟨x₀⟩ := hne
  have := hμ.isFiniteMeasure
  set c : ℝ := (μ univ).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hμ0.ne' (measure_ne_top μ univ)
  set a : ℝ := -Real.log c / lam with ha
  let u : M → EReal := fun _ => (a : EReal)
  have hu : (ofFixedModel 0 M).IsThetaPSH θ u := SGPT.NPP.isThetaPSH_const_of_dim_zero θ a
  have hφfin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ φ).mp hφ.thetaPSH
  have hufin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ u).mp hu
  refine ⟨u, ⟨hu, (singularityEquiv_of_subsingleton hufin hφfin).1, ?_⟩, hu, ?_⟩
  · rw [SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ u hu,
      SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ φ hφ.thetaPSH]
  · rw [SGPT.NPP.sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero θ u hu x₀,
      withDensity_eq_smul_of_subsingleton μ _ x₀, measure_eq_smul_dirac_of_subsingleton μ x₀,
      smul_smul]
    simp only [u, ← EReal.coe_mul, EReal.exp_coe]
    have hexp : Real.exp (lam * a) = c⁻¹ := by
      rw [ha, mul_div_cancel₀ _ hlam.ne', Real.exp_neg, Real.exp_log hcpos]
    rw [hexp, show μ univ = ENNReal.ofReal c by rw [hc, ENNReal.ofReal_toReal (measure_ne_top _ _)],
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hcpos.le), inv_mul_cancel₀ hcpos.ne', ENNReal.ofReal_one,
      one_smul]

/-- `lma:rooftop_MAequation` in dimension `0`. -/
theorem source_rooftop_MAequation_dim_zero (hφ : SourceModelPotential θ φ) {u v : M → EReal}
    (hu : SourceRelativeEInfinity θ φ u) (hv : SourceRelativeEInfinity θ φ v) :
    ∃ γ : M → EReal, ∃ hγ : SourceRelativeEInfinity θ φ γ,
      sourcePotentialNonPluripolarMeasure θ γ hγ.1 =
        (sourcePotentialNonPluripolarMeasure θ u hu.1).withDensity
            (fun x => EReal.exp (γ x - u x)) +
          (sourcePotentialNonPluripolarMeasure θ v hv.1).withDensity
            (fun x => EReal.exp (γ x - v x)) := by
  have : Subsingleton M := SGPT.NPP.subsingleton_of_dim_zero
  obtain ⟨x₀⟩ := ModelRaySupremum.nonempty_of_modelPotential hφ.toNative
  have hφfin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ φ).mp hφ.thetaPSH
  have hufin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ u).mp hu.1
  have hvfin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ v).mp hv.1
  set U : ℝ := (u x₀).toReal
  set V : ℝ := (v x₀).toReal
  set G : ℝ := -Real.log (Real.exp (-U) + Real.exp (-V)) with hG
  let γ : M → EReal := fun _ => (G : EReal)
  have hγ : (ofFixedModel 0 M).IsThetaPSH θ γ := SGPT.NPP.isThetaPSH_const_of_dim_zero θ G
  have hγfin := (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ γ).mp hγ
  refine ⟨γ, ⟨hγ, singularityEquiv_of_subsingleton hγfin hφfin⟩, ?_⟩
  rw [SGPT.NPP.sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero θ γ hγ x₀,
    SGPT.NPP.sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero θ u hu.1 x₀,
    SGPT.NPP.sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero θ v hv.1 x₀,
    withDensity_eq_smul_of_subsingleton _ _ x₀, withDensity_eq_smul_of_subsingleton _ _ x₀,
    ← add_smul]
  have hux : u x₀ = (U : EReal) := (EReal.coe_toReal (hufin x₀).1 (hufin x₀).2).symm
  have hvx : v x₀ = (V : EReal) := (EReal.coe_toReal (hvfin x₀).1 (hvfin x₀).2).symm
  simp only [γ, hux, hvx, ← EReal.coe_sub, EReal.exp_coe]
  have hpos : 0 < Real.exp (-U) + Real.exp (-V) := by positivity
  have hsum : Real.exp (G - U) + Real.exp (G - V) = 1 := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add, ← mul_add, hG, Real.exp_neg,
      Real.exp_log hpos, inv_mul_cancel₀ hpos.ne']
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, hsum, ENNReal.ofReal_one,
    one_smul]

end DimZero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- **Source `thm:AY_rel`** (relative Aubin–Yau theorem), in every dimension. Let `θ`
represent a big class, `φ` be a model potential with positive mass, `λ > 0`, and `μ` a
non-pluripolar measure with `μ(X) > 0`. Then there is a unique `u ∈ E(X, θ; φ)` with
`θ_u^n = e^{λ u} μ`; moreover, for every such solution `u`, every `v ∈ E(X, θ; φ)` with
`θ_v^n ≥ e^{λ v} μ` satisfies `v ≤ u`. -/
theorem source_relative_aubinYau (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {lam : ℝ} (hlam : 0 < lam) {μ : Measure M}
    (hμ : SourceNonPluripolarMeasure (n := n) μ) (hμ0 : 0 < μ univ) :
    (∃! u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesExpEquation θ lam μ u) ∧
      ∀ u v : M → EReal, SourceRelativeFullMass θ φ u hφ → SourceSolvesExpEquation θ lam μ u →
        SourceRelativeFullMass θ φ v hφ → SourceExpSubsolution θ lam μ v → v ≤ u := by
  have hex : ∃ u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesExpEquation θ lam μ u := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact source_relative_aubinYau_exists_dim_zero hφ hlam hμ hμ0
    · obtain ⟨u, hu, hus⟩ := source_relative_aubinYau_exists ω hn hbig hφ hlam hμ hμ0
      exact ⟨u, hu.1, hus⟩
  obtain ⟨u, huF, hus⟩ := hex
  refine ⟨⟨u, ⟨huF, hus⟩, ?_⟩, fun u v hu hus hv hvs =>
    source_relative_aubinYau_comparison ω hφ hlam hu hus hv hvs⟩
  rintro v ⟨hv, hvs⟩
  apply le_antisymm
  · exact source_relative_aubinYau_comparison ω hφ hlam huF hus hv
      ⟨hvs.1, hvs.2.symm ▸ le_rfl⟩
  · exact source_relative_aubinYau_comparison ω hφ hlam hv hvs huF
      ⟨hus.1, hus.2.symm ▸ le_rfl⟩

/-- **Source `lma:rooftop_MAequation`**, in every dimension. For a model potential `φ` with
positive mass in a big class and `u, v ∈ E^∞(X, θ; φ)` there is `γ ∈ E^∞(X, θ; φ)` with
`θ_γ^n = e^{γ - u} θ_u^n + e^{γ - v} θ_v^n`. -/
theorem source_rooftop_MAequation (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {u v : M → EReal}
    (hu : SourceRelativeEInfinity θ φ u) (hv : SourceRelativeEInfinity θ φ v) :
    ∃ γ : M → EReal, ∃ hγ : SourceRelativeEInfinity θ φ γ,
      sourcePotentialNonPluripolarMeasure θ γ hγ.1 =
        (sourcePotentialNonPluripolarMeasure θ u hu.1).withDensity
            (fun x => EReal.exp (γ x - u x)) +
          (sourcePotentialNonPluripolarMeasure θ v hv.1).withDensity
            (fun x => EReal.exp (γ x - v x)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact source_rooftop_MAequation_dim_zero hφ hu hv
  · exact source_rooftop_MAequation_of_pos ω hn hbig hφ hu hv

end SGPT.PSH.VariableComplexAtlas
