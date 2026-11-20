import SGPT.Okounkov.OF12EmbeddedProjectiveResolution
import SGPT.Okounkov.OF12NormalProjectiveField
import SGPT.Okounkov.OF12ProjectiveFieldDimension

/-! The algebraic smooth projective model provided by embedded analytic resolution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Okounkov

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}

/-- The original integral projective complex scheme has a proper birational morphism
from an integral smooth projective complex scheme of the original function-field dimension.
The field equivalence is induced by the actual morphism on all stalks. -/
theorem exists_smooth_projective_birational_model (E : ClosedProjectiveEmbedding f) :
    letI := schemeFunctionFieldAlgebra f
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X) (_ : IsProper ρ)
      (n : ℕ) (_ : SmoothOfRelativeDimension n (ρ ≫ f))
      (_ : ClosedProjectiveEmbedding (ρ ≫ f)),
      Algebra.trdeg ℂ X.functionField = n ∧
      IsIso (ρ.stalkMap (genericPoint Y)) ∧
      (∃ e : X.functionField ≃+* Y.functionField, IsStalkCompatible ρ e.toRingHom) ∧
      ∃ U : X.Opens, (U : Set X).Nonempty ∧
        Function.Bijective
          (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl) := by
  let := schemeFunctionFieldAlgebra f
  let := E.isSeparated
  let := E.locallyOfFiniteType
  obtain ⟨V, M, tM, cM, mM, σ, _hσ, hS, Y, hY, g, hg, EY, ρ, hρ, hrest⟩ :=
    exists_projective_model_of_embedded_resolution E
  let := tM
  let := cM
  let := mM
  let := hY
  subst g
  let := hg
  let := EY.isSeparated
  let := EY.quasiCompact
  let : TopologicalSpace (SchemeComplexPoint (ρ ≫ f)) := schemeAnalyticPointTopology _
  let : ChartedSpace (ComplexModel V.dim) (SchemeComplexPoint (ρ ≫ f)) :=
    schemeAnalyticTNChartedSpace (ρ ≫ f) V.dim
  let := SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace.chartedSpace V.dim_le hS.2.2
  let := SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    V.dim_le hS.2.2
  obtain ⟨hV, hiso, e, he⟩ := hrest
  obtain ⟨U, hU, hbij⟩ :=
    exists_nonempty_open_complexPoint_bijective_of_embedded_projection E ρ
      e.toHomeomorph.toEquiv hV hiso he
  let : IsProper (ρ ≫ f) := EY.isProper
  let hproper : IsProper ρ := IsProper.of_comp ρ f
  let := hproper
  let : Nonempty U := hU.to_subtype
  obtain ⟨hbirational, eField, hfield⟩ :=
    birationalData_of_restrict_complexPoint_bijective f ρ U hbij
  have hdim := functionField_trdeg_of_stalkCompatible_smooth_model f ρ eField hfield V.dim
  exact ⟨Y, hY, ρ, hproper, V.dim, hg, EY, hdim, hbirational, ⟨eField, hfield⟩, U, hU, hbij⟩

end SGPT.Okounkov.OF12
