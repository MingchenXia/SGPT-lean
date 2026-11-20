import SGPT.Foundations.Analysis.Pending.SingularNativePairedBackground
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionSameLimit

set_option autoImplicit false

/-! # Actual QEA restriction distance in any genuine big target background

SGPT PDF0275--0276 Proposition 8.1.1, including the arbitrary big
target clause immediately following (8.1). The actual common model
limit is internally produced in a separate genuine Kahler background.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionAnyBigBackground

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  RelativeEnergy ThetaPshL1Topology PluripolarCapacityDichotomy
  SingularCanonicalSingularityDistance SingularNativePairedBackground
  QuasiEquisingularRestrictionSameLimit

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The two genuine QEA families internally produce their common native
model limit in another background. The original allowed big background
requires only the actual PSH properties of the two restricted families. -/
theorem restricted_distance_tendsto_zero_in_any_big_background
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ u δ vSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    (η : ClosedRealOneOneForm k V)
    (hbig : IsBigClass (RealBottChern.ofRepresentative η))
    (hUη : ∀ j, IsThetaPshPotential η.val (fun y => uSeq j (ι y)))
    (hVη : ∀ j, IsThetaPshPotential η.val (fun y => vSeq j (ι y))) :
    Tendsto (fun j => (singularityDistance omegaV η hbig
      (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))).toReal) atTop (𝓝 0) ∧
    Tendsto (fun j => singularityDistance omegaV η hbig
      (fun y => uSeq j (ι y)) (fun y => vSeq j (ι y))) atTop (𝓝 0) := by
  obtain ⟨β, _, _, hU, hV, _, A, _, hUA, hVA, _⟩ :=
    exists_common_native_model_limit omegaV hu hv hι hgeneric
  exact ⟨
    tendsto_singularityDistance_toReal_zero_of_common_native_limit
      omegaV η β.form hbig (isBigClass_kahler β) atTop
      hUη hVη hU hV A.property hUA hVA,
    tendsto_singularityDistance_zero_of_common_native_limit
      omegaV η β.form hbig (isBigClass_kahler β) atTop
      hUη hVη hU hV A.property hUA hVA⟩

end
end SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionAnyBigBackground
