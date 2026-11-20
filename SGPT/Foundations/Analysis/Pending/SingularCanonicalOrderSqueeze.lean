import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge

set_option autoImplicit false

/-! # Exact actual distance additivity and squeeze on P-ordered chains -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderSqueeze

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  SingularGlobalPOrder SingularGlobalPEnvelopeBridge
  SingularCanonicalSingularityDistance SingularCanonicalOrderedMixedMassDistance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The three genuine global ordered distance formulas telescope in the
same original background and give exact extended-distance additivity. -/
theorem singularityDistance_eq_add_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {a b c : M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b)
    (hc : IsThetaPshPotential θ.val c)
    (hab : SourcePOrder (n := n) a b) (hbc : SourcePOrder (n := n) b c) :
    singularityDistance omega θ hbig a c =
      singularityDistance omega θ hbig a b + singularityDistance omega θ hbig b c := by
  have hac := hab.trans omega hbc
  rw [singularityDistance_eq_mixedMass_sub_of_sourcePOrder omega θ hbig ha hc hac,
    singularityDistance_eq_mixedMass_sub_of_sourcePOrder omega θ hbig ha hb hab,
    singularityDistance_eq_mixedMass_sub_of_sourcePOrder omega θ hbig hb hc hbc,
    ← EReal.coe_add]
  congr 1
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem distance_bounds_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {a b c : M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b)
    (hc : IsThetaPshPotential θ.val c)
    (hab : SourcePOrder (n := n) a b) (hbc : SourcePOrder (n := n) b c) :
    0 ≤ singularityDistance omega θ hbig a b ∧
      singularityDistance omega θ hbig a b ≤ singularityDistance omega θ hbig a c ∧
      0 ≤ singularityDistance omega θ hbig b c ∧
      singularityDistance omega θ hbig b c ≤ singularityDistance omega θ hbig a c := by
  obtain ⟨r, hr0, _, _, hr⟩ := exists_tendsto_singularityDistance omega θ hbig ha hc
  obtain ⟨s, hs0, _, _, hs⟩ := exists_tendsto_singularityDistance omega θ hbig ha hb
  obtain ⟨t, ht0, _, _, ht⟩ := exists_tendsto_singularityDistance omega θ hbig hb hc
  have hadd := singularityDistance_eq_add_of_sourcePOrder omega θ hbig ha hb hc hab hbc
  rw [hr, hs, ht, ← EReal.coe_add] at hadd
  have hrs : r = s + t := EReal.coe_injective hadd
  rw [hr, hs, ht]
  refine ⟨EReal.coe_nonneg.mpr hs0, ?_, EReal.coe_nonneg.mpr ht0, ?_⟩
  · exact EReal.coe_le_coe_iff.mpr (by linarith)
  · exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- The actual finite nonnegative defining distances and internally
proved ordered bounds supply both limits for an arbitrary filter. -/
theorem tendsto_singularityDistance_zero_of_sourcePOrder
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) {a b c : I → M → EReal}
    (ha : ∀ i, IsThetaPshPotential θ.val (a i))
    (hb : ∀ i, IsThetaPshPotential θ.val (b i))
    (hc : ∀ i, IsThetaPshPotential θ.val (c i))
    (hab : ∀ i, SourcePOrder (n := n) (a i) (b i))
    (hbc : ∀ i, SourcePOrder (n := n) (b i) (c i))
    (hlim : Tendsto (fun i => singularityDistance omega θ hbig (a i) (c i)) F (𝓝 0)) :
    Tendsto (fun i => singularityDistance omega θ hbig (a i) (b i)) F (𝓝 0) ∧
      Tendsto (fun i => singularityDistance omega θ hbig (b i) (c i)) F (𝓝 0) := by
  have hbound (i : I) := distance_bounds_of_sourcePOrder
    omega θ hbig (ha i) (hb i) (hc i) (hab i) (hbc i)
  exact ⟨tendsto_const_nhds.squeeze hlim (fun i => (hbound i).1)
      (fun i => (hbound i).2.1),
    tendsto_const_nhds.squeeze hlim (fun i => (hbound i).2.2.1)
      (fun i => (hbound i).2.2.2)⟩

/-- The original fixed-background order is transported only forwards
to the global relation, retaining the actual functions and distances. -/
theorem tendsto_singularityDistance_zero_of_pOrderWith
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) {a b c : I → M → EReal}
    (ha : ∀ i, IsThetaPshPotential θ.val (a i))
    (hb : ∀ i, IsThetaPshPotential θ.val (b i))
    (hc : ∀ i, IsThetaPshPotential θ.val (c i))
    (hab : ∀ i, POrderWith θ (a i) (b i))
    (hbc : ∀ i, POrderWith θ (b i) (c i))
    (hlim : Tendsto (fun i => singularityDistance omega θ hbig (a i) (c i)) F (𝓝 0)) :
    Tendsto (fun i => singularityDistance omega θ hbig (a i) (b i)) F (𝓝 0) ∧
      Tendsto (fun i => singularityDistance omega θ hbig (b i) (c i)) F (𝓝 0) :=
  tendsto_singularityDistance_zero_of_sourcePOrder omega θ hbig F ha hb hc
    (fun i => sourcePOrder_of_pOrderWith omega θ (ha i) (hb i) (hab i))
    (fun i => sourcePOrder_of_pOrderWith omega θ (hb i) (hc i) (hbc i)) hlim

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderSqueeze
