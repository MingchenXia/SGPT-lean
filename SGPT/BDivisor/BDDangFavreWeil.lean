import SGPT.BDivisor.BDNumericalClasses
import SGPT.BDivisor.DFAlgComparison

/-!
# Dang--Favre's Weil b-divisor classes are the algebraic b-divisors

Lane BD, blueprint `bd.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef
b-divisors are introduced by Dang--Favre [DF20] [...] our transcendental intersection theory
coincides with theirs in the algebraic setting."

Let `X` be a compact connected projective manifold of dimension `m + 1`. Dang--Favre's Weil
b-divisor classes are compatible families `(d_Y)` of numerical classes `d_Y ∈ N¹(Y)_ℝ` of real
divisors on the models `Y`, with `g_* d_{Y'} = d_Y` for the push-forward of divisors along every
domination `g : Y' → Y`. Over the book's models (`ModelSystem.blowup`, every model is a compact
connected projective manifold by `BDBlowupProjective.lean`):

* `dangFavreWeilClasses hX` — the space of these families (`numericalPushforward`,
  `BDNumericalClasses.lean`);
* `algebraicWeilFamilies` — the book's Weil b-divisors all of whose incarnations lie in
  `NS(Y)_ℝ` (`IsAlgebraicAny`, lane DF-ALG);
* `dangFavreWeilEquiv hX` — **the cycle class map `d ↦ (cl(d_Y))_Y` is a linear isomorphism from
  Dang--Favre's Weil classes onto the algebraic Weil b-divisors** (model by model it is the
  isomorphism `N¹(Y)_ℝ ≃ NS(Y)_ℝ`, compatible with push-forward);
* `isAlgebraicAny_iff_exists_dangFavreWeil`: a Weil b-divisor of the book is algebraic iff it is
  the image of a Dang--Favre Weil class.

So `IsAlgebraicAny` is exactly the image of Dang--Favre's Weil b-divisor classes, as asserted
informally in `DFAlgComparison.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.DFAlg

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Hodge.BDivChain.NativeDraft

attribute [local instance] blowup_model_connectedSpace

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- The models of the book's system of a projective manifold are projective. -/
theorem blowup_model_isProjective (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) π.1.carrier :=
  (blowup_model_isProjectiveManifold hX π).2

variable (m X) in
/-- **The algebraic Weil b-divisors** (`IsAlgebraicAny`: every incarnation lies in `NS(Y)_ℝ`), as
a subspace of the book's Weil b-divisors over the blow-up models. -/
def algebraicWeilFamilies : Submodule ℝ (WeilFamilyAny (ModelSystem.blowup (m + 1) X)) where
  carrier := {D | IsAlgebraicAny D}
  zero_mem' := fun π => (neronSeveri (m + 1) π.1.carrier).zero_mem
  add_mem' := fun hD hD' π => (neronSeveri (m + 1) π.1.carrier).add_mem (hD π) (hD' π)
  smul_mem' := fun c _ hD π => (neronSeveri (m + 1) π.1.carrier).smul_mem c (hD π)

/-- **Dang--Favre's Weil b-divisor classes** over the book's models of a compact connected
projective manifold `X`: families `d_π ∈ N¹(Y_π)_ℝ` of numerical classes with `g_* d_{π'} = d_π`
for the push-forward of divisors along every domination `g : Y_{π'} → Y_π`. -/
def dangFavreWeilClasses (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X) :
    Submodule ℝ ((π : (ModelSystem.blowup (m + 1) X).Model) → NumericalClasses m π.1.carrier)
    where
  carrier := {d | ∀ (π π' : (ModelSystem.blowup (m + 1) X).Model) (h : π ≤ π'),
    numericalPushforward (blowup_model_isProjective hX π')
      (Modification.Dominates.isAnalyticModification (show π.1 ≤ π'.1 from h)) (d π') = d π}
  zero_mem' := fun π π' h => map_zero _
  add_mem' := by
    intro d d' hd hd' π π' h
    change numericalPushforward _ _ (d π' + d' π') = d π + d' π
    rw [map_add, hd π π' h, hd' π π' h]
  smul_mem' := by
    intro c d hd π π' h
    change numericalPushforward _ _ (c • d π') = c • d π
    rw [map_smul, hd π π' h]

omit [ConnectedSpace X] in
/-- The push-forward of classes along a domination of blow-up models is the push-forward along
the dominating modification. -/
theorem classPushforwardAny_eq (π π' : (ModelSystem.blowup (m + 1) X).Model) (h : π ≤ π')
    (α : RealBottChern (m + 1) π'.1.carrier) :
    classPushforwardAny (show π.1 ≤ π'.1 from h) α =
      classPushforward (Modification.Dominates.isAnalyticModification
        (show π.1 ≤ π'.1 from h)).1 (canonicalBasis (m + 1)) (Nat.succ_pos m) α := by
  rw [classPushforwardAny_pos (Nat.succ_pos m)]
  rfl

/-- The incarnation-wise cycle classes of a Dang--Favre Weil class form a Weil b-divisor. -/
theorem cycleClassFamily_mem (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (d : dangFavreWeilClasses hX) :
    (fun π => (numericalClassEquiv (blowup_model_isProjective hX π) (d.1 π) :
      RealBottChern (m + 1) π.1.carrier)) ∈ weilFamiliesAny (ModelSystem.blowup (m + 1) X) := by
  intro π π' h
  dsimp only
  rw [classPushforwardAny_eq π π' h, ← numericalClassEquiv_numericalPushforward
    (blowup_model_isProjective hX π) (blowup_model_isProjective hX π')
    (Modification.Dominates.isAnalyticModification (show π.1 ≤ π'.1 from h)), d.2 π π' h]

/-- The numerical classes of the incarnations of an algebraic Weil b-divisor form a Dang--Favre
Weil class. -/
theorem numericalFamily_mem (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (D : algebraicWeilFamilies m X) :
    (fun π => (numericalClassEquiv (blowup_model_isProjective hX π)).symm ⟨D.1.1 π, D.2 π⟩) ∈
      dangFavreWeilClasses hX := by
  intro π π' h
  dsimp only
  apply (numericalClassEquiv (blowup_model_isProjective hX π)).injective
  apply Subtype.ext
  rw [numericalClassEquiv_numericalPushforward (blowup_model_isProjective hX π)
    (blowup_model_isProjective hX π'), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, ← classPushforwardAny_eq π π' h]
  exact D.1.2 π π' h

/-- **Dang--Favre's Weil b-divisor classes are the algebraic b-divisors.** For a compact
connected projective manifold `X`, the cycle class map `d ↦ (cl(d_Y))_Y` is a linear isomorphism
from Dang--Favre's Weil b-divisor classes over the book's models onto the Weil b-divisors all of
whose incarnations lie in the Néron--Severi spaces. -/
def dangFavreWeilEquiv (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X) :
    dangFavreWeilClasses hX ≃ₗ[ℝ] algebraicWeilFamilies m X where
  toFun d := ⟨⟨_, cycleClassFamily_mem hX d⟩, fun π =>
    (numericalClassEquiv (blowup_model_isProjective hX π) (d.1 π)).2⟩
  invFun D := ⟨_, numericalFamily_mem hX D⟩
  map_add' d d' := by
    apply Subtype.ext; apply Subtype.ext; funext π
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' c d := by
    apply Subtype.ext; apply Subtype.ext; funext π
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
  left_inv d := by
    apply Subtype.ext; funext π
    apply (LinearEquiv.symm_apply_eq _).mpr
    rfl
  right_inv D := by
    apply Subtype.ext; apply Subtype.ext; funext π
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply
      (numericalClassEquiv (blowup_model_isProjective hX π)) ⟨D.1.1 π, D.2 π⟩)

@[simp] theorem dangFavreWeilEquiv_apply (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (d : dangFavreWeilClasses hX) (π : (ModelSystem.blowup (m + 1) X).Model) :
    ((dangFavreWeilEquiv hX d).1.1 π : RealBottChern (m + 1) π.1.carrier) =
      numericalClassEquiv (blowup_model_isProjective hX π) (d.1 π) := rfl

/-- **A Weil b-divisor of the book is algebraic iff it is the image of a Dang--Favre Weil class**
under the model-wise cycle class maps. -/
theorem isAlgebraicAny_iff_exists_dangFavreWeil
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (D : WeilFamilyAny (ModelSystem.blowup (m + 1) X)) :
    IsAlgebraicAny D ↔ ∃ d : dangFavreWeilClasses hX, ∀ π,
      (numericalClassEquiv (blowup_model_isProjective hX π) (d.1 π) :
        RealBottChern (m + 1) π.1.carrier) = D.1 π := by
  constructor
  · intro hD
    refine ⟨(dangFavreWeilEquiv hX).symm ⟨D, hD⟩, fun π => ?_⟩
    rw [← dangFavreWeilEquiv_apply, LinearEquiv.apply_symm_apply]
  · rintro ⟨d, hd⟩ π
    rw [← hd π]
    exact (numericalClassEquiv (blowup_model_isProjective hX π) (d.1 π)).2

end SGPT.BDivisor.DFAlg
