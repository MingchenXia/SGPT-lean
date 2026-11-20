import SGPT.Foundations.Analysis.Pending.RelativeEnergyMixedComparison

set_option autoImplicit false

/-!
# Actual layout integrals for singular finite-type energy

Xia SGPT PDF0118, Lemma 3.1.3. Genuine singular layout slots, finite actual
mixed measures, and canonical signed integral sums. The potentials themselves
need not be bounded. This module supplies the layout calculus for the
singular energy cocycle; it does not assume or prove that cocycle.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyLayout

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  RelativeEnergyIntegrability BoundedMongeAmpereEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every layout slot selects a genuine theta-PSH potential. -/
theorem lay_genuine {θ : ClosedRealOneOneForm n M} {k j : ℕ}
    {a b : M → EReal} {S : Fin n → M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b)
    (hS : ∀ i, IsThetaPshPotential θ.val (S i)) :
    ∀ i, IsThetaPshPotential θ.val (lay k j a b S i) := by
  intro i
  unfold lay
  split_ifs
  · exact ha
  · exact hb
  · exact hS i

/-- All actual layout measures are finite even for singular slots. -/
theorem layMeasure_finite (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (k j : ℕ) {a b : M → EReal}
    {S : Fin n → M → EReal} (ha : ThetaPlurisubharmonic θ.val a)
    (hb : ThetaPlurisubharmonic θ.val b)
    (hS : ∀ i, ThetaPlurisubharmonic θ.val (S i)) :
    IsFiniteMeasure (layMeasure θ k j a b S ha hb hS) :=
  globalMixedMeasure_isFiniteMeasure omega (lay_psh ha hb hS)

/-- Canonical signed differences split under each genuine layout measure. -/
theorem integral_canonicalDiff_add_layMeasure (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {a b c x y : M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b)
    (hc : IsThetaPshPotential θ.val c)
    (hab : SameSingularityTypeOn a b univ) (hbc : SameSingularityTypeOn b c univ)
    (k j : ℕ) {S : Fin n → M → EReal}
    (hx : ThetaPlurisubharmonic θ.val x) (hy : ThetaPlurisubharmonic θ.val y)
    (hS : ∀ i, ThetaPlurisubharmonic θ.val (S i)) :
    (∫ p, canonicalERealDiffToReal (a p) (c p) ∂layMeasure θ k j x y S hx hy hS) =
      (∫ p, canonicalERealDiffToReal (a p) (b p) ∂layMeasure θ k j x y S hx hy hS) +
        ∫ p, canonicalERealDiffToReal (b p) (c p) ∂layMeasure θ k j x y S hx hy hS := by
  let := layMeasure_finite omega θ k j hx hy hS
  exact integral_canonicalDiff_add_of_sameSingularityType
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable ha.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hb.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hc.1)
    ha.1.quasiPlurisubharmonic.ne_top hb.1.quasiPlurisubharmonic.ne_top
    hc.1.quasiPlurisubharmonic.ne_top hab hbc

/-- The actual finite-type energy is the canonical sum of its layout integrals. -/
theorem relativeEnergyOfMinimalType_mul_canonical
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u) :
    ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ φ u hφ hu =
      ∑ j ∈ Finset.range (n + 1), ∫ x, canonicalERealDiffToReal (u x) (φ x)
        ∂layMeasure θ n j u φ (fun _ => φ) hu.1 hφ.1 (fun _ => hφ.1) := by
  rw [relativeEnergyOfMinimalType, mul_div_cancel₀ _ (by positivity)]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∫ x,
    canonicalERealDiffToReal (u x) (φ x)
    ∂layMeasure θ n j u φ (fun _ => φ) hu.1 hφ.1 (fun _ => hφ.1))]
  exact Finset.sum_congr rfl fun j _ => by
    rw [relativeEnergyTerm, endpointMixedMeasure_eq_layMeasure]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyLayout
