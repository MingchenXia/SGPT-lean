/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import SGPT.Support.PublishedPrincipalization.Scheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option maxSynthPendingDepth 3
set_option relaxedAutoImplicit false

/-!
# Schemes with disjoint integral components

The class of reduced schemes with pairwise disjoint irreducible components, finite disjoint unions
of integral schemes: the schemes on which Kollár constructs the resolution functor before gluing
[Kol07, Proposition 37 and the proof of Theorem 36], and the class of Hironaka's Main Theorems on
regular schemes (`SGPT.Support.PublishedPrincipalization.Resolution.Algebraic.Hir64`), whose components are open and integral.
The resolution functor of the library (`SGPT.Support.PublishedPrincipalization.Resolution.BRFunctor`) is constructed and proved
on the class `IsReducedEquidimensional` (`SGPT.Support.PublishedPrincipalization.Scheme.Resolution.Defs`), whose members'
components may meet but have one dimension.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The class of reduced schemes with pairwise disjoint irreducible components: `X` is reduced and
its irreducible components are pairwise disjoint — for a scheme of finite type over a field, a
finite disjoint union of integral schemes (finitely many components, each open by disjointness, each
integral). It is the smallest class containing the integral schemes and closed under the finite
disjoint unions of [Kol07, Proposition 37] (`∐ Uᵢ`, `∐ Uᵢ ∩ Uⱼ`). The empty scheme is in the
class. Hironaka's Main Theorems on regular schemes (`SGPT.Support.PublishedPrincipalization.Resolution.Algebraic.Hir64`) use the
class; the resolution functor `SGPT.Support.PublishedPrincipalization.Resolution.BRFunctor` is proved on the class
`IsReducedEquidimensional`, whose members' components may meet but have one dimension. -/
def Scheme.HasDisjointIntegralComponents (X : Scheme.{u}) : Prop :=
  IsReduced X ∧
    ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X, (C₁ ∩ C₂).Nonempty → C₁ = C₂

end AlgebraicGeometry
