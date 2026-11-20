import SGPT.Toric.GlobalCurrentPotentialConstant
import SGPT.Toric.Toric5IGood
import SGPT.PSH.BiholomorphicGeometricQPullback
import SGPT.PSH.SourceBimeromorphicMixedIVolume
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.Pending.ComponentwiseNormalizedCurrentPotentials

/-!
Actual invariant CURRENT input -> actual invariant potential in its prescribed
class, retaining equality in the SAME original full-test current space.
The invariance hypothesis is equality of actual geometric pullbacks, not a
caller-supplied invariant potential/presentation certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame NaturalThetaPshGeometricCurrent CurrentBottChernClass
open GlobalPositiveCurrentACRestriction AnalyticModificationLocalDiscrepancy
open PositiveCurrentPrescribedBottChernRepresentation ComponentwiseNormalizedCurrentPotentials
open SGPT.PSH.VariableComplexAtlas
open scoped Topology ContDiff Manifold

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every actual torus action is a holomorphic automorphism and hence an
actual analytic modification with empty exceptional sets. -/
theorem isAnalyticModification_polytopeToricAction (a : Fin n → ℂˣ) :
    IsAnalyticModification (n := n) (polytopeToricAction γ hs a) := by
  exact SGPT.PSH.nativeAnalyticModification_of_biholomorphic
    (polytopeToricAction γ hs a)
    (contMDiff_originalPolytopeNativeAction γ hs a ∞)
    (contMDiff_originalPolytopeNativeAction γ hs a⁻¹ ∞)

section PositiveDimension

variable {m : ℕ} {γ : K → Fin (m + 1) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

local notation "X" => PolytopeToricVariety γ hs
local notation "b" => canonicalBasis (m + 1)
local notation "Cur" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- Literal invariance of the ORIGINAL current under all actual compact-torus
geometric pullbacks. There is no chosen potential among the input data. -/
def IsCompactTorusInvariantCurrent
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val) : Prop :=
  ∀ (a : Fin (m + 1) → ℂˣ), IsCompactTorusElement a →
    sourceCurrentModificationPullback (isAnalyticModification_polytopeToricAction a)
      T.val T.property.1 T.property.2 hT = T.val

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- ORIGINAL whole-current class membership and literal geometric invariance
produce one genuine invariant global theta-potential with equality to the
SAME input current, pointwise invariance at every original point including
the boundary/poles, and attained sup normalization.

No invariant-presentation input, a.e.-only conclusion, positive mass or
I-goodness assumption is used. The degree-two current API has dimension m+1;
the final book mixed-volume theorem must treat its empty n=0 tuple separately. -/
theorem exists_normalized_invariant_potential_of_current_class
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass b (Nat.succ_pos m) T =
      RealBottChern.ofRepresentative h.form)
    (hinv : IsCompactTorusInvariantCurrent T hT) :
    ∃ (u : X → EReal) (hu : IsThetaPshPotential h.form.val u),
      T.val = thetaPotentialCurrent h.form.val u hu ∧
      PolytopeToricInvariant γ hs u ∧
      (∀ x, u x ≤ 0) ∧ ∃ x, u x = 0 := by
  obtain ⟨v, hv, hread, _⟩ :=
    exists_theta_representation_of_class_eq T h.form hT hclass
  obtain ⟨u, hu, hnormread, hle, hzero⟩ := exists_normalized_theta_current h.form v hv
  have hreadu : T.val = thetaPotentialCurrent h.form.val u hu :=
    hread.trans hnormread.symm
  have hzero' : ∃ x, u x = 0 := by
    obtain ⟨y, _hy, hyzero⟩ := hzero (polytopeToricEmbedding γ hs 1)
    exact ⟨y, hyzero⟩
  refine ⟨u, hu, hreadu, ?_, hle, hzero'⟩
  intro a ha x
  let hπ := isAnalyticModification_polytopeToricAction (γ := γ) (hs := hs) a
  have hform : ClosedRealOneOneForm.pullback hπ.1 h.form = h.form := by
    apply Subtype.ext
    exact h.form_compact_pullback_eq a ha
  have hcomp : IsThetaPshPotential h.form.val
      (u ∘ polytopeToricAction γ hs a) := by
    have hc := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ h.form hu
    simpa only [Function.comp_def, hform] using hc
  have hgeom := (sourceCurrentModificationPullback_spec hπ T.val
    T.property.1 T.property.2 hT).2.2.2 h.form u hu hreadu
  have hsame : thetaPotentialCurrent h.form.val
      (u ∘ polytopeToricAction γ hs a) hcomp = thetaPotentialCurrent h.form.val u hu := by
    have hc := (hgeom.symm.trans (hinv a ha)).trans hreadu
    simpa only [SGPT.Okounkov.analyticModificationThetaCurrent, Function.comp_def, hform] using hc
  have hzeroComp : ∃ y, (u ∘ polytopeToricAction γ hs a) y = 0 := by
    obtain ⟨y, hy⟩ := hzero'
    obtain ⟨z, hz⟩ := (polytopeToricAction γ hs a).surjective y
    exact ⟨z, by simpa only [Function.comp_apply, hz] using hy⟩
  have heq := CurrentPotential.normalized_eq_of_current_eq hcomp hu hsame
    (fun y => hle (polytopeToricAction γ hs a y)) hle hzeroComp hzero'
  exact congrFun heq x

/-- The produced potential is an actual element of the original toric PSH
space, not merely an invariant scalar representative of the current. -/
theorem exists_mem_PSHTor_of_invariant_current_class
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass b (Nat.succ_pos m) T =
      RealBottChern.ofRepresentative h.form)
    (hinv : IsCompactTorusInvariantCurrent T hT) :
    ∃ (u : X → EReal) (hu : IsThetaPshPotential h.form.val u),
      T.val = thetaPotentialCurrent h.form.val u hu ∧ u ∈ h.PSHTor := by
  obtain ⟨u, hu, hread, hinvu, _hle, _hzero⟩ :=
    h.exists_normalized_invariant_potential_of_current_class T hT hclass hinv
  refine ⟨u, hu, hread, ?_, hinvu⟩
  exact (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mpr hu

end BigToricMetric
end PositiveDimension
end SGPT.Toric
