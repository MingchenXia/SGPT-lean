import SGPT.NPP.MassPushforwardLocalReading
import SGPT.NPP.NonPluripolarMassModification
import SGPT.BDivisor.CurrentPushforwardType
import SGPT.Okounkov.ThetaCurrentPullbackCompatibility

/-!
# Non-pluripolar masses are invariant under push-forward along modifications

Source `prop:nppmassinv` (chapter `chapter_npp.tex`), second identity: for a proper
bimeromorphic morphism `π : Y → X` from a Kähler manifold `Y` and closed positive
`(1,1)`-currents `S_1, …, S_n` on `Y`,

  `∫_Y S_1 ∧ ⋯ ∧ S_n = ∫_X π_*S_1 ∧ ⋯ ∧ π_*S_n`.

The first identity (pull-back) is `SGPT.NPP.sourceCurrentNonPluripolarMass_modification_pullback`.

The proof is the source's: off the exceptional locus `π` is an isomorphism, the products
agree there, and the non-pluripolar products put no mass on the (analytic, hence pluripolar)
exceptional set. In detail, write `S_i = θ_i + ddᶜφ_i` and `π_*S_i = θ'_i + ddᶜu'_i`. Over the
isomorphism locus `Y ∖ π⁻¹E`, in coordinate biholomorphic pairs `τ = d ∘ π ∘ e⁻¹`, the corrected
potentials of `S_i` and of `π^*θ'_i + ddᶜ(u'_i ∘ π)` have the same `ddᶜ`
(`SGPT.NPP.MassPushforward.integral_corrected_pushforward`), so they differ by smooth pluriharmonic
functions, and the coordinate non-pluripolar measures agree (pluriharmonic gauge invariance of
the truncation limit). Hence the global non-pluripolar measures of `(θ, φ)` and of
`(π^*θ', u' ∘ π)` agree on `Y ∖ π⁻¹E` (`globalMixedMeasure_restrict_eq_pullback`); neither charges
`π⁻¹E`, and the total mass of the latter is that of `(θ', u')` on `X` (pull-back invariance).

Main results:
* `SGPT.NPP.sourceMixedNonPluripolarMass_modification_pushforward` — the potential form;
* `SGPT.NPP.sourceCurrentNonPluripolarMass_modification_pushforward` — the current form, with the
  push-forward of currents `SGPT.BDivisor.currentPushforward` (closed, of type `(1,1)` and
  positive by `SGPT.BDivisor.isClosed_currentPushforward`,
  `SGPT.BDivisor.isTypeOneOne_currentPushforward`, `SGPT.BDivisor.isFullPositive_currentPushforward`).

As for the pull-back half, `IsAnalyticModification` (proper holomorphic, with a holomorphic
inverse off closed nowhere dense analytic sets) formalizes a proper bimeromorphic morphism;
the Kähler forms are only used to identify the presentation-independent current masses.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ENNReal

namespace SGPT.NPP

namespace MassPushforward

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.BedfordTaylor
  SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
  SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
  SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor

/-! ### Pluriharmonic gauge equality of patch measures -/

section Gauge

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Two local-potential patches (for possibly different tuples) in the same chart and on the
same coordinate domain, whose corrected potentials differ by smooth pluriharmonic functions,
have the same coordinate non-pluripolar measure. -/
theorem patchMeasure_eq_of_corrected_eq_add {θ η : Fin n → ClosedRealOneOneForm n M}
    {u v : Fin n → M → EReal} (P : Patch θ u) (Q : Patch η v) (hchart : P.chart = Q.chart)
    (hdom : P.domain = Q.domain) (h : Fin n → ComplexModel n → ℝ)
    (hh : ∀ i, IsSmoothPluriharmonicOn P.domain (h i))
    (heq : ∀ i, EqOn (P.corrected i) (fun z => Q.corrected i z + (h i z : EReal)) P.domain) :
    patchMeasure P = patchMeasure Q := by
  have hQ : ∀ i, PlurisubharmonicOn (Q.corrected i) P.domain := fun i => by
    rw [hdom]
    exact Q.plurisubharmonic i
  have hQh : ∀ i, PlurisubharmonicOn (fun z => Q.corrected i z + (h i z : EReal)) P.domain :=
    fun i z hz => (P.plurisubharmonic i z hz).congr
      (Filter.eventually_of_mem (P.domain.isOpen.mem_nhds hz) fun y hy => heq i hy)
  have h1 : mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic =
      mixedTruncationLimitMeasure P.domain (fun i z => Q.corrected i z + (h i z : EReal)) hQh :=
    mixedTruncationLimitMeasure_congr _ _ heq
  have h2 : mixedTruncationLimitMeasure P.domain (fun i z => Q.corrected i z + (h i z : EReal))
      hQh = mixedTruncationLimitMeasure P.domain Q.corrected hQ :=
    mixedTruncationLimitMeasure_add_pluriharmonic hQ hh hQh
  have key : ∀ (D : Opens (ComplexModel n)) (_hD : D = Q.domain)
      (hq : ∀ i, PlurisubharmonicOn (Q.corrected i) D),
      mixedTruncationLimitMeasure D Q.corrected hq =
        mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic := by
    rintro D rfl hq
    rfl
  have h3 := key _ hdom hQ
  change P.pushMeasure _ = Q.pushMeasure _
  rw [h1, h2, h3]
  ext s
  rw [Patch.pushMeasure_apply, Patch.pushMeasure_apply, hchart, hdom]

/-- A smooth function with vanishing Levi form is pluriharmonic. -/
theorem isSmoothPluriharmonicOn_of_levi {W : Opens (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hlevi : ∀ z ∈ W, ∀ w : ComplexModel n, leviForm h z w = 0) :
    IsSmoothPluriharmonicOn W h := by
  refine ⟨hh.contDiffOn, fun z hz => ?_⟩
  have h2 : ContDiffAt ℝ 2 h z := hh.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [← normalizedHermitianMatrix_smoothDDC h2,
    SGPT.Okounkov.smoothDDC_eq_zero_of_levi_zero h2 (hlevi z hz)]
  ext j k
  simp [normalizedHermitianMatrix]

end Gauge

/-! ### Local agreement over the isomorphism locus -/

section Local

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- A corrected chart potential of a `θ`-psh function is a local quasi-psh potential. -/
theorem corrected_localQuasiPsh {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {e : ComplexChart (m + 1) M}
    {A : Opens (ComplexModel (m + 1))} {ρ : ComplexModel (m + 1) → ℝ}
    (hA : A ≤ chartTarget e)
    (hp : PlurisubharmonicOn (fun x => chartFunction u e x + (ρ x : EReal)) A) :
    LocalQuasiPshPotentialOn (fun x => chartFunction u e x + (ρ x : EReal)) A := by
  refine ⟨A.isOpen, fun x hx => (hp x hx).quasiPlurisubharmonicAt, ?_⟩
  intro x hx B hB hxB
  obtain ⟨y, hy, hyfin⟩ := hu.2.exists_chart_ne_bot e (A.isOpen.inter hB)
    (fun y hy => hA hy.1) ⟨hx, hxB⟩
  exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hyfin, EReal.coe_ne_bot _⟩⟩

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- **Local agreement of the non-pluripolar measures over the isomorphism locus.** With
`π_*(θ_i + ddᶜφ_i) = θ'_i + ddᶜu'_i`, every point `y` with `π y ∉ E` has an open neighbourhood
`O ⊆ π⁻¹(Eᶜ)` on which the global mixed non-pluripolar measures of `(θ, φ)` and of
`(π^*θ', u' ∘ π)` agree. -/
theorem exists_open_restrict_eq {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) (φ : Fin (m + 1) → Y → EReal)
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (θ' : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) (u' : Fin (m + 1) → X → EReal)
    (hu' : ∀ i, IsThetaPshPotential (θ' i).val (u' i))
    (heq : ∀ i, currentPushforward hπ.1 (thetaPotentialCurrent (θ i).val (φ i) (hφ i)) =
      thetaPotentialCurrent (θ' i).val (u' i) (hu' i))
    {E : Set X} {s : X → Y} (hleft : ∀ y, π y ∉ E → s (π y) = y)
    (hpairs : ∀ (y : Y), π y ∉ E →
        ∀ (e : ComplexChart (m + 1) Y) (d : ComplexChart (m + 1) X),
          y ∈ e.val.source → π y ∈ d.val.source →
          ∃ (A B : Opens (ComplexModel (m + 1))), e.val y ∈ A ∧
            A ≤ chartTarget e ∧ B ≤ chartTarget d ∧
            ((A : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d) ∧
            (∀ z ∈ B, d.val.symm z ∉ E) ∧ (∀ z ∈ B, s (d.val.symm z) ∈ e.val.source) ∧
            IsBiholomorphicPair A B (coordinateMap π e d) (coordinateMap s d e))
    (y : Y) (hy : π y ∉ E) :
    ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ O ⊆ π ⁻¹' Eᶜ ∧
      (globalMixedMeasure θ φ (fun i => (hφ i).1)).restrict O =
        (globalMixedMeasure (pullbackTuple hπ.1 θ') (fun i y => u' i (π y))
          (fun i => thetaPlurisubharmonic_comp hπ.1 (hu' i).1)).restrict O := by
  classical
  -- patches at `y` and at `π y`
  obtain ⟨P₀, hyP₀⟩ := exists_patch_containing (fun i => (hφ i).1) y
  obtain ⟨Q₀, hyQ₀⟩ := exists_patch_containing (fun i => (hu' i).1) (π y)
  set e := P₀.chart with he
  set d := Q₀.chart with hd
  have hye : y ∈ e.val.source := P₀.source_subset hyP₀
  have hyd : π y ∈ d.val.source := Q₀.source_subset hyQ₀
  obtain ⟨A, B, hyA, hAe, hBd, hAdom, hBE, hBs, hp⟩ := hpairs y hy e d hye hyd
  -- the common coordinate domain
  let D : Opens (ComplexModel (m + 1)) :=
    ⟨(A : Set (ComplexModel (m + 1))) ∩ P₀.domain ∩ coordinateMap π e d ⁻¹' Q₀.domain,
      (hp.holo.continuousOn.mono inter_subset_left).isOpen_inter_preimage
        (A.isOpen.inter P₀.domain.isOpen) Q₀.domain.isOpen⟩
  have hDA : D ≤ A := fun _ hz => hz.1.1
  have hDP : D ≤ P₀.domain := fun _ hz => hz.1.2
  have hDe : D ≤ chartTarget e := hDA.trans hAe
  have hDdom : (D : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d := fun _ hz =>
    hAdom (hDA hz)
  have hτy : coordinateMap π e d (e.val y) = d.val (π y) := by
    change d.val (π (e.val.symm (e.val y))) = d.val (π y)
    rw [e.val.left_inv hye]
  have hyD : e.val y ∈ D := ⟨⟨hyA, hyP₀.2⟩, by
    change coordinateMap π e d (e.val y) ∈ Q₀.domain
    rw [hτy]
    exact hyQ₀.2⟩
  have hpD := restrictPair hp hDA
  set B' : Opens (ComplexModel (m + 1)) :=
    ⟨(B : Set (ComplexModel (m + 1))) ∩ coordinateMap s d e ⁻¹' D,
      hp.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen D.isOpen⟩ with hB'
  have hB'Q : B' ≤ Q₀.domain := by
    intro w hw
    have h1 : coordinateMap π e d (coordinateMap s d e w) ∈ Q₀.domain := hw.2.2
    rwa [hp.right_inv w hw.1] at h1
  have hfib : ∀ y', π y' ∈ d.val.source → d.val (π y') ∈ B' →
      y' ∈ e.val.source ∧ e.val y' ∈ D := fun y' h1 h2 =>
    fibre_mem hleft hBE hBs h1 h2
  -- the pulled-back patch of `Q₀`
  set Pp := pullbackPatch hπ.1 Q₀ e with hPp
  have hDPp : D ≤ Pp.domain := fun z hz => ⟨hDdom hz, hz.2⟩
  have hPpcorr : ∀ i z, Pp.corrected i z =
      chartFunction (fun y => u' i (π y)) e z + (Q₀.potential i (coordinateMap π e d z) : EReal) := fun _ _ => rfl
  -- equality of `ddᶜ` of the corrected potentials on `D`, hence pluriharmonic differences
  have hlocal (i : Fin (m + 1)) : ∃ (U : Opens (ComplexModel (m + 1))) (_ : U ≤ D)
      (h : ComplexModel (m + 1) → ℝ), e.val y ∈ U ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      EqOn (P₀.corrected i) (fun z => Pp.corrected i z + (h z : EReal)) U ∧
      ∀ z ∈ U, ∀ w : ComplexModel (m + 1), leviForm h z w = 0 := by
    have hF : LocalQuasiPshPotentialOn (P₀.corrected i) D :=
      corrected_localQuasiPsh (hφ i) hDe ((P₀.plurisubharmonic i).mono hDP)
    have hG : LocalQuasiPshPotentialOn (Pp.corrected i) D :=
      corrected_localQuasiPsh (isThetaPshPotential_comp_of_isAnalyticModification hπ (θ' i) (hu' i))
        hDe ((Pp.plurisubharmonic i).mono hDPp)
    have hint (η : TestForm D (testDeg m)) :
        ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x * (P₀.corrected i x).toReal =
          ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x * (Pp.corrected i x).toReal := by
      have hk := integral_corrected_pushforward hπ.1 (θ i).val (hφ i) (θ' i).val (hu' i)
        (heq i) e d hpD hDP hB'Q hDdom hfib (P₀.potential i) (P₀.localPotential i)
        (Q₀.potential i) (Q₀.localPotential i) η
      refine hk.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
      by_cases hx : x ∈ D
      · have hxd : π (e.val.symm x) ∈ d.val.source := (hDdom hx).2
        change _ * (chartFunction (u' i) d (coordinateMap π e d x) + (Q₀.potential i (coordinateMap π e d x) : EReal)).toReal =
          _ * (chartFunction (fun y => u' i (π y)) e x + (Q₀.potential i (coordinateMap π e d x) : EReal)).toReal
        congr 3
        change u' i (d.val.symm (d.val (π (e.val.symm x)))) = u' i (π (e.val.symm x))
        rw [d.val.left_inv hxd]
      · have h0 : DDCOverlap.ddcAdjoint (pairFrame m) η x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h =>
            hx ((DDCOverlap.ddcAdjoint (pairFrame m) η).tsupport_subset h)
        simp only [h0, zero_mul]
    have hddc := ddC_eq_of_forall_integral_eq hF hG hint
    obtain ⟨U, hU, h, hyU, hh, -, hdiff, -, hlevi⟩ :=
      exists_smooth_original_difference_of_equal_native_ddc hF hG hddc (e.val y) hyD
    exact ⟨U, hU, h, hyU, hh, hdiff, hlevi⟩
  choose U hUD h hyU hh hdiff hlevi using hlocal
  -- the common smaller domain
  let W : Opens (ComplexModel (m + 1)) :=
    ⟨(D : Set (ComplexModel (m + 1))) ∩ ⋂ i, (U i : Set (ComplexModel (m + 1))),
      D.isOpen.inter (isOpen_iInter_of_finite fun i => (U i).isOpen)⟩
  have hWD : W ≤ D := fun _ hz => hz.1
  have hWU (i : Fin (m + 1)) : W ≤ U i := fun _ hz => mem_iInter.mp hz.2 i
  have hyW : e.val y ∈ W := ⟨hyD, mem_iInter.mpr hyU⟩
  let P' := P₀.restrict W (hWD.trans hDP)
  let Q' := Pp.restrict W (hWD.trans hDPp)
  have hPQ : patchMeasure P' = patchMeasure Q' := by
    refine patchMeasure_eq_of_corrected_eq_add P' Q' rfl rfl h
      (fun i => isSmoothPluriharmonicOn_of_levi (hh i) fun z hz => hlevi i z (hWU i hz))
      (fun i z hz => hdiff i (hWU i hz))
  refine ⟨P'.source, P'.source.isOpen, ⟨hye, hyW⟩, ?_, ?_⟩
  · intro x hx
    have hxD : e.val x ∈ D := hWD hx.2
    have hτx : coordinateMap π e d (e.val x) ∈ B := hp.mapsTo (hDA hxD)
    have hsymm : d.val.symm (coordinateMap π e d (e.val x)) = π x := by
      have hxd := (hDdom hxD).2
      change d.val.symm (d.val (π (e.val.symm (e.val x)))) = π x
      change π (e.val.symm (e.val x)) ∈ d.val.source at hxd
      rw [d.val.left_inv hxd, e.val.left_inv hx.1]
    have h := hBE _ hτx
    rwa [hsymm] at h
  · rw [globalMixedMeasure_restrict_patch _ P', hPQ]
    exact (globalMixedMeasure_restrict_patch _ Q').symm

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- **Agreement of the non-pluripolar measures over the isomorphism locus**: on `Y ∖ π⁻¹E`, the
global mixed non-pluripolar measure of `(θ, φ)` is that of `(π^*θ', u' ∘ π)`, where
`π_*(θ_i + ddᶜφ_i) = θ'_i + ddᶜu'_i`. -/
theorem globalMixedMeasure_restrict_eq_pullback {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) (φ : Fin (m + 1) → Y → EReal)
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (θ' : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) (u' : Fin (m + 1) → X → EReal)
    (hu' : ∀ i, IsThetaPshPotential (θ' i).val (u' i))
    (heq : ∀ i, currentPushforward hπ.1 (thetaPotentialCurrent (θ i).val (φ i) (hφ i)) =
      thetaPotentialCurrent (θ' i).val (u' i) (hu' i))
    {E : Set X} {s : X → Y} (hleft : ∀ y, π y ∉ E → s (π y) = y)
    (hpairs : ∀ (y : Y), π y ∉ E →
        ∀ (e : ComplexChart (m + 1) Y) (d : ComplexChart (m + 1) X),
          y ∈ e.val.source → π y ∈ d.val.source →
          ∃ (A B : Opens (ComplexModel (m + 1))), e.val y ∈ A ∧
            A ≤ chartTarget e ∧ B ≤ chartTarget d ∧
            ((A : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d) ∧
            (∀ z ∈ B, d.val.symm z ∉ E) ∧ (∀ z ∈ B, s (d.val.symm z) ∈ e.val.source) ∧
            IsBiholomorphicPair A B (coordinateMap π e d) (coordinateMap s d e)) :
    (globalMixedMeasure θ φ (fun i => (hφ i).1)).restrict (π ⁻¹' Eᶜ) =
      (globalMixedMeasure (pullbackTuple hπ.1 θ') (fun i y => u' i (π y))
        (fun i => thetaPlurisubharmonic_comp hπ.1 (hu' i).1)).restrict (π ⁻¹' Eᶜ) := by
  apply restrict_eq_of_locally_eq
  intro y hy
  exact exists_open_restrict_eq hπ θ φ hφ θ' u' hu' heq hleft hpairs y hy

/-- **Push-forward invariance of the total mixed non-pluripolar mass** (native form): if
`π_*(θ_i + ddᶜφ_i) = θ'_i + ddᶜu'_i` for a modification `π : Y → X`, then
`∫_X ⟨(θ'_1 + ddᶜu'_1) ∧ ⋯⟩ = ∫_Y ⟨(θ_1 + ddᶜφ_1) ∧ ⋯⟩`. -/
theorem globalMixedMeasure_univ_pushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) (φ : Fin (m + 1) → Y → EReal)
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (θ' : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) (u' : Fin (m + 1) → X → EReal)
    (hu' : ∀ i, IsThetaPshPotential (θ' i).val (u' i))
    (heq : ∀ i, currentPushforward hπ.1 (thetaPotentialCurrent (θ i).val (φ i) (hφ i)) =
      thetaPotentialCurrent (θ' i).val (u' i) (hu' i)) :
    globalMixedMeasure θ' u' (fun i => (hu' i).1) univ =
      globalMixedMeasure θ φ (fun i => (hφ i).1) univ := by
  obtain ⟨E, s, hEc, -, -, hpa, hpi, hleft, hpairs⟩ := exists_coordinatePairs hπ
  have hpol : ManifoldLocallyPluripolar (n := m + 1) (π ⁻¹' E) :=
    manifoldLocallyPluripolar_of_isComplexAnalyticSubset hpa hpi
  have hmeas : MeasurableSet (π ⁻¹' E) := (hEc.preimage hπ.1.continuous).measurableSet
  have hS0 := globalMixedMeasure_doesNotChargeManifoldPluripolar (fun i => (hφ i).1) _ hpol
  have hY0 := globalMixedMeasure_doesNotChargeManifoldPluripolar
    (θ := pullbackTuple hπ.1 θ') (u := fun i y => u' i (π y))
    (fun i => thetaPlurisubharmonic_comp hπ.1 (hu' i).1) _ hpol
  have hres := globalMixedMeasure_restrict_eq_pullback hπ θ φ hφ θ' u' hu' heq hleft hpairs
  have hcompl := congrArg (fun μ : Measure Y => μ univ) hres
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hcompl
  have hS : globalMixedMeasure θ φ (fun i => (hφ i).1) univ =
      globalMixedMeasure θ φ (fun i => (hφ i).1) (π ⁻¹' Eᶜ) := by
    rw [← measure_add_measure_compl hmeas, hS0, zero_add, preimage_compl]
  have hY : globalMixedMeasure (pullbackTuple hπ.1 θ') (fun i y => u' i (π y))
      (fun i => thetaPlurisubharmonic_comp hπ.1 (hu' i).1) univ =
      globalMixedMeasure (pullbackTuple hπ.1 θ') (fun i y => u' i (π y))
        (fun i => thetaPlurisubharmonic_comp hπ.1 (hu' i).1) (π ⁻¹' Eᶜ) := by
    rw [← measure_add_measure_compl hmeas, hY0, zero_add, preimage_compl]
  rw [hS, hcompl, ← hY]
  exact (AnalyticModificationMixedMass.globalMixedMeasure_univ_pullback_of_isAnalyticModification
    hπ (fun i => (hu' i).1)).symm

end Local

end MassPushforward

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

section Source

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace X]

/-- Source `prop:nppmassinv`, second identity, potential form: for a proper bimeromorphic
morphism `π : Y → X` (`Y` is then compact) and `θ_i + ddᶜφ_i` on `Y` with push-forwards
`π_*(θ_i + ddᶜφ_i) = θ'_i + ddᶜu'_i`, the total mixed non-pluripolar masses agree:
`∫_Y (θ_1 + ddᶜφ_1) ∧ ⋯ = ∫_X (θ'_1 + ddᶜu'_1) ∧ ⋯`. -/
theorem sourceMixedNonPluripolarMass_modification_pushforward [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) (φ : Fin (m + 1) → Y → EReal)
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (θ' : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) (u' : Fin (m + 1) → X → EReal)
    (hu' : ∀ i, IsThetaPshPotential (θ' i).val (u' i))
    (heq : ∀ i, currentPushforward hπ.1 (thetaPotentialCurrent (θ i).val (φ i) (hφ i)) =
      thetaPotentialCurrent (θ' i).val (u' i) (hu' i)) :
    sourceMixedNonPluripolarMass (fun i => nativeClosedFormToAtlas (θ' i)) u'
        (fun i => isThetaPSH_nativeClosedFormToAtlas (hu' i)) =
      sourceMixedNonPluripolarMass (fun i => nativeClosedFormToAtlas (θ i)) φ
        (fun i => isThetaPSH_nativeClosedFormToAtlas (hφ i)) := by
  simp only [sourceMixedNonPluripolarMass_eq_native, sourceNativeAtlasForm_roundTrip]
  exact MassPushforward.globalMixedMeasure_univ_pushforward hπ θ φ hφ θ' u' hu' heq

/-- Source `prop:nppmassinv`, second identity: for a proper bimeromorphic morphism
`π : Y → X` from a Kähler manifold `Y` onto the compact Kähler manifold `X` and closed positive
`(1,1)`-currents `S_1, …, S_n` on `Y`,
`∫_Y S_1 ∧ ⋯ ∧ S_n = ∫_X π_*S_1 ∧ ⋯ ∧ π_*S_n`
(`π_*S_i` is the push-forward of currents, again closed, of type `(1,1)` and positive). -/
theorem sourceCurrentNonPluripolarMass_modification_pushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (ωX : KahlerBackground (m + 1) X) (ωY : KahlerBackground (m + 1) Y)
    (S : Fin (m + 1) → GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (S i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (S i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (S i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    sourceCurrentNonPluripolarMass (fun i => currentPushforward hπ.1 (S i))
      (fun i => isClosed_currentPushforward hπ.1 (canonicalBasis (m + 1)) (hc i))
      (fun i => isTypeOneOne_currentPushforward hπ.1 (Nat.succ_pos m) (canonicalBasis (m + 1))
        (h11 i))
      (fun i => isFullPositive_currentPushforward hπ.1 (hp i)) =
      sourceCurrentNonPluripolarMass S hc h11 hp := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  obtain ⟨θ, φ, hφ, hread⟩ := exists_currentTupleRepresentation S hc h11 hp
  obtain ⟨θ', u', hu', hread'⟩ := exists_currentTupleRepresentation
    (fun i => currentPushforward hπ.1 (S i))
    (fun i => isClosed_currentPushforward hπ.1 (canonicalBasis (m + 1)) (hc i))
    (fun i => isTypeOneOne_currentPushforward hπ.1 (Nat.succ_pos m) (canonicalBasis (m + 1))
      (h11 i))
    (fun i => isFullPositive_currentPushforward hπ.1 (hp i))
  rw [sourceCurrentNonPluripolarMass_eq_representation ωX _ _ _ _ θ' u' hu' hread',
    sourceCurrentNonPluripolarMass_eq_representation ωY S hc h11 hp θ φ hφ hread]
  refine sourceMixedNonPluripolarMass_modification_pushforward hπ θ φ hφ θ' u' hu' fun i => ?_
  rw [← hread i]
  exact hread' i

end Source

section DimZero

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]
  [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace X]

/-- Source `prop:nppmassinv`, second identity, in dimension `0`: there are no `(1,1)`-currents,
both sides are the masses of the empty tuples, and the identity is the pull-back identity
(`sourceMixedNonPluripolarMass_modification_pullback`). -/
theorem sourceMixedNonPluripolarMass_modification_pushforward_dim_zero {π : Y → X}
    (hπ : IsAnalyticModification (n := 0) π)
    (θ : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 Y)) (φ : Fin 0 → Y → EReal)
    (hφ : ∀ i, (ofFixedModel 0 Y).IsThetaPSH (θ i) (φ i))
    (θ' : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 X)) (u' : Fin 0 → X → EReal)
    (hu' : ∀ i, (ofFixedModel 0 X).IsThetaPSH (θ' i) (u' i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    sourceMixedNonPluripolarMass θ' u' hu' = sourceMixedNonPluripolarMass θ φ hφ := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  have h := sourceMixedNonPluripolarMass_modification_pullback hπ θ' u' hu'
  obtain rfl : θ = fun i => nativeClosedFormToAtlas
      (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (θ' i))) :=
    funext fun i => i.elim0
  obtain rfl : φ = fun i => u' i ∘ π := funext fun i => i.elim0
  exact h.symm

end DimZero

end SGPT.NPP
