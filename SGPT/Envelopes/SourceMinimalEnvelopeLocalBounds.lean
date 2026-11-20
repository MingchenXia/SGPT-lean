import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.IntrinsicRationalAnalytic
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.NonBigSupremumMass

/-! # The original minimal envelope off the original non-Kähler locus

The source locus is the literal polar intersection of ALL original rational
bounded-remainder analytic Kähler currents. It is not defined as the native
all-current positive-Lelong locus. Only the necessary inclusion in positive
dimension is used; dimension zero has a direct minimal-envelope identity.
The complete source route is `source-minimal-envelope-local-bounds.tex`.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original polar intersection, retaining EVERY actual analytic-current
presentation and the original positive rational coefficient/bounded remainder. -/
def sourceNonKahlerLocus (α : RealBottChern n M) : Set M :=
  {x | ∀ T : KahlerCurrent α,
    (ofFixedModel n M).HasRationalAnalyticType T.potential → T.potential x = ⊥}

/-- The existing whole connected-presentation/chart dictionary specializes
to the SAME native charts, rational coefficients, generators and remainders. -/
theorem sourceRationalAnalyticType_iff_native (u : M → EReal) :
    (ofFixedModel n M).HasRationalAnalyticType u ↔
      QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) u := by
  rw [hasRationalAnalyticType_iff_chartType]
  rfl

/-- The original family is exactly the all-chart bounded-remainder family
on the SAME actual current objects, rather than a locus definition alias. -/
theorem sourceNonKahlerLocus_iff_native_analytic (α : RealBottChern n M) (x : M) :
    x ∈ sourceNonKahlerLocus α ↔
      ∀ T : KahlerCurrent α,
        QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) T.potential →
          T.potential x = ⊥ := by
  simp only [sourceNonKahlerLocus, mem_ofPred_eq, sourceRationalAnalyticType_iff_native]

/-- Only this inclusion is needed. Positive Lelong number gives the actual
pole for EVERY current, hence for each original analytic current. -/
theorem nativeNonKahlerLocus_subset_source (hn : 0 < n) (α : RealBottChern n M) :
    nonKahlerLocus α ⊆ sourceNonKahlerLocus α := by
  intro x hx T _han
  exact eq_bot_of_lelongNumber_pos hn T.strictlyPsh.1 (hx T)

/-- The whole zero-dimensional source envelope is zero for EVERY background;
no zero-dimensional Lelong-locus identification is made. -/
theorem sourceMinimalEnvelope_eq_zero_of_dim_zero (hn : n = 0)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    sourceMinimalEnvelope θ = 0 := by
  rw [sourceMinimalEnvelope_eq_native]
  exact NonBigSupremumMass.thetaPshSupremum_eq_zero_of_dim_zero hn _

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Entire original lma:Vthetalocbdd: finite two-sided local bounds outside
the ORIGINAL analytic-current polar intersection, in every dimension. -/
theorem sourceMinimalEnvelope_locallyBounded (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {x : M}
    (hx : x ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ a b : ℝ, ∀ y ∈ U, (a : EReal) ≤ sourceMinimalEnvelope θ y ∧
        sourceMinimalEnvelope θ y ≤ (b : EReal) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine ⟨univ, isOpen_univ, mem_univ x, 0, 0, ?_⟩
    simp only [sourceMinimalEnvelope_eq_zero_of_dim_zero hn, Pi.zero_apply,
      EReal.coe_zero, le_refl, and_self, implies_true]
  · have hxnative : x ∉ nonKahlerLocus
        (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) :=
      fun h => hx (nativeNonKahlerLocus_subset_source hn _ h)
    have hV := (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceMinimalEnvelope_thetaPSH ω θ hbig)
    rw [sourceMinimalEnvelope_eq_native] at hV
    obtain ⟨N, hN, a, b, hab⟩ :=
      BigClassEnvelopeContact.exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus
        hn (atlasClosedFormToNative θ) hbig hV hxnative
    obtain ⟨U, hUN, hU, hxU⟩ := mem_nhds_iff.mp hN
    refine ⟨U, hU, hxU, a, b, ?_⟩
    intro y hy
    simpa only [sourceMinimalEnvelope_eq_native] using hab y (hUN hy)

end SGPT.PSH.VariableComplexAtlas
