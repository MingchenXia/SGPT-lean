import SGPT.Foundations.Analysis.Pending.RelativeEnergy
import SGPT.Foundations.Analysis.Pending.GlobalSlotComparison

/-!
# Actual mixed integrals for singular relatively minimal potentials

Xia SGPT PDF0118--0119: bounded differences of relatively minimal
potentials are integrable against the actual finite mixed measures. The
potentials and model themselves may be unbounded. Corrected differences
are zero on their common pole locus; no one-sided infinite difference
is used to represent a source integral. This is an analytic input for
the singular-model cocycle, not a proof of that energy formula.
-/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy

noncomputable section

/-- The canonical signed difference is Borel measurable on the whole square. -/
theorem measurable_canonicalERealDiffToReal :
    Measurable (fun p : EReal × EReal => canonicalERealDiffToReal p.1 p.2) := by
  apply EReal.measurable_of_real_real
  · have hdiff : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
      measurable_fst.sub measurable_snd
    simpa only [canonicalERealDiffToReal_coe_coe] using hdiff
  · simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal]
  · simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal]
  · simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal]
  · simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal]

/-- Common poles and absence of positive infinity recover real subtraction,
including the common pole where both realifications and the correction are zero. -/
theorem canonicalDiff_eq_sub_toReal {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hpole : a = ⊥ ↔ b = ⊥) :
    canonicalERealDiffToReal a b = a.toReal - b.toReal := by
  cases a <;> cases b <;>
    simp_all [canonicalERealDiffToReal, poleModifiedERealDiffToReal, ← EReal.coe_sub]

/-- Same singularity type bounds the corrected difference everywhere,
without requiring either potential itself to be bounded. -/
theorem exists_abs_canonicalDiff_le_of_sameSingularityType
    {X : Type*} {u v : X → EReal} (h : SameSingularityTypeOn u v univ)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |canonicalERealDiffToReal (u x) (v x)| ≤ C := by
  obtain ⟨C, D, hCD⟩ := sameSingularityTypeOn_canonicalDiff_bounded h
  refine ⟨|C| + |D|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun x => ?_⟩
  by_cases hux : u x = ⊥
  · have hvx : v x = ⊥ := (sameSingularityTypeOn_eq_bot_iff h (mem_univ x)).mp hux
    simp [hux, hvx, add_nonneg (abs_nonneg C) (abs_nonneg D)]
  · obtain ⟨hlo, hhi⟩ := hCD x (mem_univ x) (hu x) (hv x) hux
    apply abs_le.mpr
    constructor
    · linarith [le_abs_self D, abs_nonneg C]
    · linarith [le_abs_self C, abs_nonneg D]

/-- A same-type signed difference is integrable against every finite measure. -/
theorem integrable_canonicalDiff_of_sameSingularityType
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u v : X → EReal} (hum : Measurable u) (hvm : Measurable v)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤)
    (h : SameSingularityTypeOn u v univ) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x)) μ := by
  obtain ⟨C, _, hC⟩ := exists_abs_canonicalDiff_le_of_sameSingularityType h hu hv
  have hm := measurable_canonicalERealDiffToReal.comp (hum.prodMk hvm)
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- Real signed differences split pointwise even on the common pole locus. -/
theorem canonicalDiff_add_of_sameSingularityType
    {X : Type*} {u v w : X → EReal}
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤) (hw : ∀ x, w x ≠ ⊤)
    (huv : SameSingularityTypeOn u v univ) (hvw : SameSingularityTypeOn v w univ)
    (x : X) :
    canonicalERealDiffToReal (u x) (w x) =
      canonicalERealDiffToReal (u x) (v x) + canonicalERealDiffToReal (v x) (w x) := by
  rw [canonicalDiff_eq_sub_toReal (hu x) (hw x)
      (sameSingularityTypeOn_eq_bot_iff (huv.trans hvw) (mem_univ x)),
    canonicalDiff_eq_sub_toReal (hu x) (hv x)
      (sameSingularityTypeOn_eq_bot_iff huv (mem_univ x)),
    canonicalDiff_eq_sub_toReal (hv x) (hw x)
      (sameSingularityTypeOn_eq_bot_iff hvw (mem_univ x))]
  ring

/-- Integrability justifies splitting a signed difference under a fixed
finite measure. This is a linear integral identity, not the energy cocycle. -/
theorem integral_canonicalDiff_add_of_sameSingularityType
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u v w : X → EReal} (hum : Measurable u) (hvm : Measurable v) (hwm : Measurable w)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤) (hw : ∀ x, w x ≠ ⊤)
    (huv : SameSingularityTypeOn u v univ) (hvw : SameSingularityTypeOn v w univ) :
    (∫ x, canonicalERealDiffToReal (u x) (w x) ∂μ) =
      (∫ x, canonicalERealDiffToReal (u x) (v x) ∂μ) +
        ∫ x, canonicalERealDiffToReal (v x) (w x) ∂μ := by
  simp_rw [canonicalDiff_add_of_sameSingularityType hu hv hw huv hvw]
  exact integral_add (integrable_canonicalDiff_of_sameSingularityType hum hvm hu hv huv)
    (integrable_canonicalDiff_of_sameSingularityType hvm hwm hv hw hvw)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual global mixed non-pluripolar measures integrate all same-type
potential differences; the mixed slots may have independent singularities. -/
theorem integrable_canonicalDiff_globalMixedMeasure
    (omega : KahlerBackground n M) {alpha beta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : ThetaPlurisubharmonic alpha u)
    (hv : ThetaPlurisubharmonic beta v) (h : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (globalMixedMeasure eta s hs) := by
  let := globalMixedMeasure_isFiniteMeasure omega hs
  exact integrable_canonicalDiff_of_sameSingularityType
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv)
    hu.quasiPlurisubharmonic.ne_top hv.quasiPlurisubharmonic.ne_top h

/-- Every signed integrand in the actual finite-type energy is integrable
for an arbitrarily singular reference potential. -/
theorem integrable_relativeEnergyTerm
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi u : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hu : RelativeEInfinity theta phi u) (j : Fin (n + 1)) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (phi x))
      (endpointMixedMeasure theta phi u hphi hu.plurisubharmonic j) :=
  integrable_canonicalDiff_globalMixedMeasure omega hu.plurisubharmonic.1 hphi.1
    hu.sameSingularityType (endpointMixedPotential_thetaPlurisubharmonic theta j u phi
      hu.plurisubharmonic hphi)

/-- All mixed signed-difference integrals in the source cocycle expression
are genuine integrals for relatively minimal endpoints, even for singular models. -/
theorem integrable_endpoint_canonicalDiff_of_relativeEInfinity
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi u v : M → EReal} (hu : RelativeEInfinity theta phi u)
    (hv : RelativeEInfinity theta phi v) (j : Fin (n + 1)) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (endpointMixedMeasure theta v u hv.plurisubharmonic hu.plurisubharmonic j) :=
  integrable_canonicalDiff_globalMixedMeasure omega hu.plurisubharmonic.1 hv.plurisubharmonic.1
    (hu.sameSingularityType.trans hv.sameSingularityType.symm)
    (endpointMixedPotential_thetaPlurisubharmonic theta j u v
      hu.plurisubharmonic hv.plurisubharmonic)

end

end SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
