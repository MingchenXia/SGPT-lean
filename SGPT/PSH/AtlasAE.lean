import SGPT.PSH.VariableAtlas
import SGPT.Foundations.Analysis.PlurisubharmonicAE

/-!
# Source almost-everywhere comparison in the genuine variable-dimensional atlas

Manifold nullness is measured in the actual coordinate Lebesgue measures.
Reuse the existing ball-deficit pointwise comparison; do not repeat its proof
or postulate a distribution-to-PSH correspondence.
-/

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Almost-everywhere order in every actual chart's genuine Lebesgue measure. -/
def CoordinateAELE (u v : X → EReal) : Prop :=
  ∀ i : A.Index, ∀ᵐ z ∂volume.restrict (A.chart i).target,
    A.coordinate u i z ≤ A.coordinate v i z

/-- Almost-everywhere equality in the actual coordinate Lebesgue measures. -/
def CoordinateAEEq (u v : X → EReal) : Prop :=
  ∀ i : A.Index, A.coordinate u i =ᵐ[volume.restrict (A.chart i).target] A.coordinate v i

variable {A}

/-- SGPT `prop:pshfuncdetdense`: the genuine coordinate almost-everywhere
order determines order on every actual manifold point. -/
theorem IsPSH.le_of_coordinateAELE {u v : X → EReal}
    (hu : A.IsPSH u) (hv : A.IsPSH v) (hae : A.CoordinateAELE u v) : u ≤ v := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  have h := (hu.chartPlurisubharmonic i).le_of_ae_le
    (A.chart i).open_target (hv.chartPlurisubharmonic i).upperSemicontinuousOn
    volume (hae i) (A.chart i x) ((A.chart i).map_source hi)
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using h

/-- The source's equality consequence includes actual bottom values. -/
theorem IsPSH.eq_of_coordinateAEEq {u v : X → EReal}
    (hu : A.IsPSH u) (hv : A.IsPSH v) (hae : A.CoordinateAEEq u v) : u = v := by
  funext x
  obtain ⟨i, hi⟩ := A.cover x
  have h := (hu.chartPlurisubharmonic i).eqOn_of_ae_eq (hv.chartPlurisubharmonic i)
    (A.chart i).open_target volume (hae i) ((A.chart i).map_source hi)
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hi] using h

end SGPT.PSH.VariableComplexAtlas
