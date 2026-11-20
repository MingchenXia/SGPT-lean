import SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanCoordinateIdealGluing
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold

set_option autoImplicit false

/-!
# Global analytic singularity type from finite shifted Bergman collar gluing

The finite shifted collar recursion already carries analytic singularity type
through a core that avoids all later core closures. If these explicit cores
cover the manifold, that local conclusion covers every genuine chart germ.
This produces one finite theta-PSH candidate with analytic singularity type;
it does not construct a coherent ideal, an approximation sequence, a limiting
potential, or multiplier-ideal inclusions.  Moreover, on a connected manifold
the additional all-later-core separation forces a disjoint open core cover and
hence a single global core (see `FiniteShiftedBergmanSeparationObstruction`).
Accordingly, the strong result below is a conditional one-chart special case,
not a global Demailly gluing construction for a general finite atlas.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanGlobalAnalyticType

open FirstPass
open FirstPass.NumericalRestrictedVolumeScaffold
open FirstPass.QuasiEquisingularApproximation
open QuasiEquisingularBergmanAtlas
open FiniteShiftedBergmanCollarGluing
open FiniteShiftedBergmanCoordinateIdealGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite shifted Bergman collar candidate has analytic singularity type in
all actual complex charts when its explicit inner cores cover the manifold and
each core avoids every later core closure. -/
theorem finiteShiftedBergmanGlued_hasManifoldAnalyticSingularityType
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hsep : ShiftedLaterCoreSeparation H)
    (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    HasManifoldAnalyticSingularityType (n := n)
      (finiteShiftedBergmanGlued A offset g A.count) := by
  intro e z hz
  obtain ⟨i, hcore⟩ := hcover (e.val.symm z)
  exact finiteShiftedBergmanGlued_analyticTypeAt_core_final A offset g H i hz hcore
    (fun j hij => hsep i j hij)

/-- A finite shifted Bergman collar candidate has the strong CT22 analytic
singularities when each point lies in a core whose germ survives all later
collar steps.  The proof uses only that eventual equality with one shifted
Bergman branch, so it retains the branch's smooth remainder. -/
theorem finiteShiftedBergmanGlued_hasManifoldSmoothAnalyticSingularities
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (hsep : ShiftedLaterCoreSeparation H)
    (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    HasManifoldSmoothAnalyticSingularities (n := n)
      (finiteShiftedBergmanGlued A offset g A.count) := by
  intro e z hz
  obtain ⟨i, hcore⟩ := hcover (e.val.symm z)
  exact finiteShiftedBergmanGlued_smoothAnalyticSingularitiesAt_core_final
    A offset g H hm i hz hcore (fun j hij => hsep i j hij)

/-- The same explicit finite data gives one global theta-PSH potential whose
actual chart germs all have analytic singularity type. This is deliberately a
single-term result, not a quasi-equisingular approximation. -/
theorem finiteShiftedBergmanGlued_effectiveTerm
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (hg : IsThetaPshPotential θ g)
    (hsep : ShiftedLaterCoreSeparation H)
    (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    IsThetaPshPotential θ (finiteShiftedBergmanGlued A offset g A.count) ∧
      HasManifoldAnalyticSingularityType (n := n)
        (finiteShiftedBergmanGlued A offset g A.count) := by
  refine ⟨finiteShiftedBergmanGlued_isThetaPshPotential A offset g H hm hg A.count le_rfl,
    finiteShiftedBergmanGlued_hasManifoldAnalyticSingularityType A offset g H hsep hcover⟩

/-- Under the same separated-core finite data, the effective theta-PSH term
also meets the strong smooth-remainder convention used by admissible
restricted-volume currents. -/
theorem finiteShiftedBergmanGlued_effectiveStrongTerm
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (hg : IsThetaPshPotential θ g)
    (hsep : ShiftedLaterCoreSeparation H)
    (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    IsThetaPshPotential θ (finiteShiftedBergmanGlued A offset g A.count) ∧
      HasManifoldSmoothAnalyticSingularities (n := n)
        (finiteShiftedBergmanGlued A offset g A.count) := by
  refine ⟨finiteShiftedBergmanGlued_isThetaPshPotential A offset g H hm hg A.count le_rfl,
    finiteShiftedBergmanGlued_hasManifoldSmoothAnalyticSingularities
      A offset g H hm hsep hcover⟩

end

end SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanGlobalAnalyticType
