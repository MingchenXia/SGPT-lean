import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality

/-!
# Actual global mixed-measure locality on ordinary open sets

Tuples agreeing on an ordinary open set have equal restrictions of the
actual global mixed non-pluripolar measures. This is the locality needed
on the open coincidence regions in Lu, Lemma 4.1 Step 1.1, including
closed truncation sublevels contained in those regions. It follows from
the proved coordinate open locality and actual patch transport/gluing;
no finiteness or locality certificate is assumed.
-/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.GlobalOpenLocality

open FirstPass FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar MixedNonPluripolar BoundedGlobalProduct GlobalSlotStokes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {theta : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}

/-- A patch for the second tuple using the first patch's actual smooth corrections. -/
def transferPatch (P : Patch theta u)
    (hv : ∀ i, ThetaPlurisubharmonic (theta i).val (v i)) : Patch theta v where
  chart := P.chart
  domain := P.domain
  domain_le_target := P.domain_le_target
  potential := P.potential
  localPotential := P.localPotential
  plurisubharmonic i := ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hv i)
    P.chart (P.localPotential i)

/-- Actual coordinate locality transports and glues to global open locality. -/
theorem globalMixedMeasure_restrict_eq_of_eqOn
    (hu : ∀ i, ThetaPlurisubharmonic (theta i).val (u i))
    (hv : ∀ i, ThetaPlurisubharmonic (theta i).val (v i))
    {U : Set M} (hU : IsOpen U) (huv : ∀ i, EqOn (u i) (v i) U) :
    (globalMixedMeasure theta u hu).restrict U =
      (globalMixedMeasure theta v hv).restrict U := by
  refine measure_eq_of_restrict_eq_of_openCover (fun P : Patch theta u => (P.source : Set M))
    (fun P => P.source.isOpen) (exists_patch_containing hu) fun P => ?_
  let Q := transferPatch P hv
  rw [Measure.restrict_comm P.source.isOpen.measurableSet,
    Measure.restrict_comm P.source.isOpen.measurableSet,
    globalMixedMeasure_restrict_patch hu P,
    show (P.source : Set M) = (Q.source : Set M) from rfl,
    globalMixedMeasure_restrict_patch hv Q]
  let V : Opens (ComplexModel n) :=
    ⟨(P.domain : Set (ComplexModel n)) ∩ P.chart.val.symm ⁻¹' U,
      (P.chart.val.continuousOn_symm.mono P.domain_le_target).isOpen_inter_preimage
        P.domain.isOpen hU⟩
  have hVP : V ≤ P.domain := fun _ hz => hz.1
  have hVQ : V ≤ Q.domain := hVP
  have hcorr : ∀ i, EqOn (P.corrected i) (Q.corrected i) V := by
    intro i z hz
    change u i (P.chart.val.symm z) + (P.potential i z : EReal) =
      v i (P.chart.val.symm z) + (P.potential i z : EReal)
    rw [huv i hz.2]
  have hloc : (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic).restrict
      (V : Set (ComplexModel n)) =
      (mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic).restrict
        (V : Set (ComplexModel n)) := by
    have hP : ∀ i, PlurisubharmonicOn (P.corrected i) P.domain := P.plurisubharmonic
    have hQ : ∀ i, PlurisubharmonicOn (Q.corrected i) Q.domain := Q.plurisubharmonic
    exact (mixedTruncationLimitMeasure_open_locality (u := P.corrected)
      (v := Q.corrected) hVP hP (fun i => (hQ i).mono hVQ) hcorr).trans
        (mixedTruncationLimitMeasure_restrict_open (u := Q.corrected) hVQ hQ).symm
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  change P.pushMeasure _ (A ∩ U) = Q.pushMeasure _ (A ∩ U)
  rw [P.pushMeasure_apply, Q.pushMeasure_apply]
  let S : Set (ComplexModel n) := (P.domain : Set (ComplexModel n)) ∩
    P.chart.val.symm ⁻¹' (A ∩ U)
  have hSV : S ⊆ V := fun z hz => ⟨hz.1, hz.2.2⟩
  change mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic S =
    mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S
  rw [← Measure.restrict_eq_self _ hSV, hloc, Measure.restrict_eq_self _ hSV]

/-- The restricted measures agree on every subset of the open coincidence region. -/
theorem globalMixedMeasure_restrict_eq_on_subset
    (hu : ∀ i, ThetaPlurisubharmonic (theta i).val (u i))
    (hv : ∀ i, ThetaPlurisubharmonic (theta i).val (v i))
    {U S : Set M} (hU : IsOpen U) (huv : ∀ i, EqOn (u i) (v i) U) (hSU : S ⊆ U) :
    (globalMixedMeasure theta u hu).restrict S =
      (globalMixedMeasure theta v hv).restrict S := by
  rw [← Measure.restrict_restrict_of_subset hSU,
    globalMixedMeasure_restrict_eq_of_eqOn hu hv hU huv,
    Measure.restrict_restrict_of_subset hSU]

/-- Changing one slot equal on an ordinary open set preserves its restriction there. -/
theorem globalMixedMeasure_update_restrict_eq_of_eqOn
    (s : Fin n → M → EReal) (i0 : Fin n) {a b : M → EReal}
    (ha : ∀ i, ThetaPlurisubharmonic (theta i).val (Function.update s i0 a i))
    (hb : ∀ i, ThetaPlurisubharmonic (theta i).val (Function.update s i0 b i))
    {U : Set M} (hU : IsOpen U) (hab : EqOn a b U) :
    (globalMixedMeasure theta (Function.update s i0 a) ha).restrict U =
      (globalMixedMeasure theta (Function.update s i0 b) hb).restrict U := by
  classical
  apply globalMixedMeasure_restrict_eq_of_eqOn ha hb hU
  intro i x hx
  by_cases hi : i = i0
  · subst hi
    simpa using hab hx
  · simp only [Function.update_of_ne hi]

end

end SGPT.Foundations.Analysis.Pending.GlobalOpenLocality
