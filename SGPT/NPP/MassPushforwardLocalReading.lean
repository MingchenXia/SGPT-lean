import SGPT.NPP.MassPushforwardDdcCovariance
import SGPT.BDivisor.CurrentPushforward
import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
import SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility

/-!
# The push-forward of a current read over the isomorphism locus of a modification

Let `π : Y → X` be a holomorphic map from a compact manifold, `S` a current on `Y`, `e` a chart
of `Y` and `d` a chart of `X`, and let `τ = d ∘ π ∘ e⁻¹` be the coordinate expression of `π`.
Suppose `τ` maps an open `D ⊆ e(Y)` into an open `B ⊆ d(X)` and every point of `Y` lying over
`d⁻¹(B)` lies in `e⁻¹(D)` (the *fibre condition*; it holds over the isomorphism locus of a
modification). Then for test forms `η` on `D` and `ζ` on `B` with `η = τ^*ζ`,

`(π_* S)_d(ζ) = S_e(η)`  (`currentPushforward_inChart_eq`):

the pull-back of the zero extension of `ζ` is, chart by chart, the zero extension of `η`.

For a modification, coordinate biholomorphic pairs satisfying the fibre condition exist at
every point off the exceptional set (`exists_coordinatePairs`, after
`Pending.AnalyticModificationCoordinatePairs`, with the extra data needed here).

Combined with the chart readers of `θ + ddᶜφ` and the holomorphic covariance of `ddᶜ`
(`SGPT.NPP.MassPushforwardDdcCovariance`), this gives the key local identity of the
push-forward half of source `prop:nppmassinv`: if `π_*(θ + ddᶜφ) = θ' + ddᶜu'`, then over the
isomorphism locus the corrected local potentials `φ + ρ` (in `e`) and `(u' + κ) ∘ τ` have the same
`ddᶜ` (`integral_corrected_pushforward`, `ddC_eq_of_forall_integral_eq`), i.e. `θ + ddᶜφ = π^*θ' + ddᶜ(u' ∘ π)` there.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.NPP.MassPushforward

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DDCOverlap
  SGPT.Foundations.Analysis.Pending.BedfordTaylor
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension
  SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality
  SGPT.Foundations.Analysis.Pending.NaturalFullNativeSmoothDuality
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor

/-! ### Coordinate biholomorphic pairs off the exceptional set -/

section Pairs

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem coordinateMap_contDiffAt_of_contMDiffAt' {f : X → Y}
    (e : ComplexChart n X) (d : ComplexChart n Y) {z : ComplexModel n}
    (hz : z ∈ coordinateDomain f e d)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f (e.val.symm z)) :
    ContDiffAt ℂ ∞ (coordinateMap f e d) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas e.property)
    (IsManifold.subset_maximalAtlas d.property)
    (e.val.map_target hz.1) hz.2).mp hf
  simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, e.val.right_inv hz.1,
    contDiffWithinAt_univ] using h.2

/-- **Coordinate biholomorphic pairs of a modification.** A proper bimeromorphic morphism
`π : Y → X` is a biholomorphism off a closed analytic set `E ⊆ X` with empty interior (and
`π⁻¹ E` analytic with empty interior): with the holomorphic inverse `s` off `E`, at every point
`y` with `π y ∉ E` and for any charts `e ∋ y`, `d ∋ π y`, the coordinate expressions
`d ∘ π ∘ e⁻¹ : A → B` and `e ∘ s ∘ d⁻¹ : B → A` are inverse biholomorphisms, with
`d⁻¹(B) ∩ E = ∅` and `s(d⁻¹ B) ⊆ e(Y)`. -/
theorem exists_coordinatePairs {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    ∃ (E : Set X) (s : X → Y), IsClosed E ∧ IsComplexAnalyticSubset (n := n) E ∧
      interior E = ∅ ∧ IsComplexAnalyticSubset (n := n) (π ⁻¹' E) ∧
      interior (π ⁻¹' E) = ∅ ∧ (∀ y, π y ∉ E → s (π y) = y) ∧
      ∀ (y : Y), π y ∉ E →
        ∀ (e : ComplexChart n Y) (d : ComplexChart n X),
          y ∈ e.val.source → π y ∈ d.val.source →
          ∃ (A B : Opens (ComplexModel n)), e.val y ∈ A ∧
            A ≤ chartTarget e ∧ B ≤ chartTarget d ∧
            ((A : Set (ComplexModel n)) ⊆ coordinateDomain π e d) ∧
            (∀ z ∈ B, d.val.symm z ∉ E) ∧ (∀ z ∈ B, s (d.val.symm z) ∈ e.val.source) ∧
            IsBiholomorphicPair A B (coordinateMap π e d) (coordinateMap s d e) := by
  obtain ⟨D, E, s, _hDc, hDa, hDi, hEc, hEa, hEi, hpre, hs, hright, hleft⟩ := hπ.2.2
  have hne (y : Y) (hy : π y ∉ E) : y ∉ D := by
    intro hyD
    apply hy
    change y ∈ π ⁻¹' E
    rwa [hpre]
  refine ⟨E, s, hEc, hEa, hEi, ?_, ?_, fun y hy => hleft y (hne y hy), ?_⟩
  · rwa [hpre]
  · rwa [hpre]
  intro y hy e d hye hyd
  let V : Set X := d.val.source ∩ (Eᶜ ∩ s ⁻¹' e.val.source)
  have hV : IsOpen V := d.val.open_source.inter
    (hs.continuousOn.isOpen_inter_preimage hEc.isOpen_compl e.val.open_source)
  have hys : s (π y) = y := hleft y (hne y hy)
  have hyV : π y ∈ V := by
    refine ⟨hyd, hy, ?_⟩
    change s (π y) ∈ e.val.source
    rwa [hys]
  let A : Opens (ComplexModel n) := ⟨e.val.target ∩ e.val.symm ⁻¹' (π ⁻¹' V),
    e.val.isOpen_inter_preimage_symm (hV.preimage hπ.1.continuous)⟩
  let B : Opens (ComplexModel n) := ⟨d.val.target ∩ d.val.symm ⁻¹' V,
    d.val.isOpen_inter_preimage_symm hV⟩
  have hyA : e.val y ∈ A := ⟨e.val.map_source hye, by
    change π (e.val.symm (e.val y)) ∈ V
    rwa [e.val.left_inv hye]⟩
  have hAt : A ≤ chartTarget e := fun _ hz => hz.1
  have hBt : B ≤ chartTarget d := fun _ hz => hz.1
  have hAdom : (A : Set (ComplexModel n)) ⊆ coordinateDomain π e d :=
    fun _ hz => ⟨hz.1, hz.2.1⟩
  have hBoff : ∀ z ∈ B, d.val.symm z ∉ E := fun _ hz => hz.2.2.1
  have hBs : ∀ z ∈ B, s (d.val.symm z) ∈ e.val.source := fun _ hz => hz.2.2.2
  refine ⟨A, B, hyA, hAt, hBt, hAdom, hBoff, hBs, ?_⟩
  refine { holo := (coordinateMap_contDiffOn hπ.1 e d).mono hAdom
           holo_inv := ?_
           mapsTo := ?_
           mapsTo_inv := ?_
           left_inv := ?_
           right_inv := ?_ }
  · intro w hw
    have hdom : w ∈ coordinateDomain s d e := ⟨hw.1, hw.2.2.2⟩
    exact (coordinateMap_contDiffAt_of_contMDiffAt' d e hdom
      (hs.contMDiffAt (hEc.isOpen_compl.mem_nhds (hBoff w hw)))).contDiffWithinAt
  · intro z hz
    have hzdom := hAdom hz
    refine ⟨coordinateMap_mem_target hzdom, ?_⟩
    change d.val.symm (d.val (π (e.val.symm z))) ∈ V
    rw [d.val.left_inv hzdom.2]
    exact hz.2
  · intro w hw
    have hswe : s (d.val.symm w) ∈ e.val.source := hw.2.2.2
    refine ⟨e.val.map_source hswe, ?_⟩
    change π (e.val.symm (e.val (s (d.val.symm w)))) ∈ V
    rw [e.val.left_inv hswe, hright _ (hBoff w hw)]
    exact hw.2
  · intro z hz
    have hzdom := hAdom hz
    change e.val (s (d.val.symm (d.val (π (e.val.symm z))))) = z
    rw [d.val.left_inv hzdom.2, hleft _ (hne _ hz.2.2.1), e.val.right_inv hz.1]
  · intro w hw
    have hswe : s (d.val.symm w) ∈ e.val.source := hw.2.2.2
    change d.val (π (e.val.symm (e.val (s (d.val.symm w))))) = w
    rw [e.val.left_inv hswe, hright _ (hBoff w hw), d.val.right_inv hw.1]

/-- Restricting a biholomorphic pair `A → B` to an open `D ⊆ A` (target `B ∩ σ⁻¹ D = τ(D)`). -/
theorem restrictPair {A B D : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ) (hDA : D ≤ A) :
    IsBiholomorphicPair D ⟨(B : Set (ComplexModel n)) ∩ σ ⁻¹' D,
      h.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen D.isOpen⟩ τ σ where
  holo := h.holo.mono hDA
  holo_inv := h.holo_inv.mono fun _ hw => hw.1
  mapsTo := fun z hz => ⟨h.mapsTo (hDA hz), by
    change σ (τ z) ∈ D
    rw [h.left_inv z (hDA hz)]
    exact hz⟩
  mapsTo_inv := fun _ hw => hw.2
  left_inv := fun z hz => h.left_inv z (hDA hz)
  right_inv := fun w hw => h.right_inv w hw.1

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
/-- **The fibre condition** over a coordinate pair of a modification: every point of `Y` over
`d⁻¹(B ∩ σ⁻¹ D)` lies in `e⁻¹(D)`. -/
theorem fibre_mem {π : Y → X} {E : Set X} {s : X → Y} (hleft : ∀ y, π y ∉ E → s (π y) = y)
    {e : ComplexChart n Y} {d : ComplexChart n X} {B D : Opens (ComplexModel n)}
    (hBE : ∀ z ∈ B, d.val.symm z ∉ E) (hBs : ∀ z ∈ B, s (d.val.symm z) ∈ e.val.source)
    {y : Y} (hyd : π y ∈ d.val.source)
    (hyB : d.val (π y) ∈ (B : Set (ComplexModel n)) ∩ coordinateMap s d e ⁻¹' D) :
    y ∈ e.val.source ∧ e.val y ∈ D := by
  have hsymm : d.val.symm (d.val (π y)) = π y := d.val.left_inv hyd
  have hyE : π y ∉ E := by
    have h := hBE _ hyB.1
    rwa [hsymm] at h
  have hys : s (π y) = y := hleft y hyE
  have hye : y ∈ e.val.source := by
    have h := hBs _ hyB.1
    rwa [hsymm, hys] at h
  refine ⟨hye, ?_⟩
  have h := hyB.2
  change e.val (s (d.val.symm (d.val (π y)))) ∈ D at h
  rwa [hsymm, hys] at h

end Pairs

/-! ### The chart reading of the push-forward over the isomorphism locus -/

section Reading

variable {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

theorem testExtension_coeff_self {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {q : ℕ} (e : ComplexChart n M)
    (η : TestForm (chartTarget e) q) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (testExtension e η).coeff e z = η z :=
  extend_coeff_self e η η.contDiff η.hasCompactSupport η.tsupport_subset hz

theorem testExtension_coeff_eq_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {q : ℕ} (e f : ComplexChart n M)
    (η : TestForm (chartTarget e) q) {z : ComplexModel n} (hz : f.val.symm z ∉ e.val.source) :
    (testExtension e η).coeff f z = 0 :=
  extend_coeff_eq_zero e f η η.contDiff η.hasCompactSupport η.tsupport_subset hz

/-- The coefficient of the zero extension of a chart test form in another chart, at a point of
the source of the extended chart. -/
theorem testExtension_coeff_of_mem {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {q : ℕ} (e c : ComplexChart n M)
    (η : TestForm (chartTarget e) q) {z : ComplexModel n}
    (hz : z ∈ (chartTransition c e).source) (v : Fin q → ComplexModel n) :
    (testExtension e η).coeff c z v =
      η (chartTransition c e z) (fun i => chartTransitionDerivative c e z (v i)) := by
  have h := testExtension_coeff_self e η
    (show chartTransition c e z ∈ e.val.target from e.val.map_source hz.2)
  rw [(testExtension e η).compatible c e z hz v, h]

variable {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)

/-- **The push-forward read over the isomorphism locus.** If `τ = d ∘ π ∘ e⁻¹` maps `D` into
`B`, every point over `d⁻¹ B` lies in `e⁻¹ D`, and `η = τ^* ζ`, then
`(π_* S)_d(ζ) = S_e(η)`. -/
theorem currentPushforward_inChart_eq [CompactSpace Y] {k : CurrentDegree n}
    (S : GlobalCurrent n Y k) (e : ComplexChart n Y) (d : ComplexChart n X)
    {D B : Opens (ComplexModel n)} (hDe : D ≤ chartTarget e) (hBd : B ≤ chartTarget d)
    (hDdom : (D : Set (ComplexModel n)) ⊆ coordinateDomain π e d)
    (hmaps : MapsTo (coordinateMap π e d) D B)
    (hfib : ∀ y, π y ∈ d.val.source → d.val (π y) ∈ B → y ∈ e.val.source ∧ e.val y ∈ D)
    (η : TestForm D (Module.finrank ℝ (ComplexModel n) - k.val))
    (ζ : TestForm B (Module.finrank ℝ (ComplexModel n) - k.val))
    (hrel : ∀ z ∈ D, ∀ v : Fin (Module.finrank ℝ (ComplexModel n) - k.val) → ComplexModel n,
      η z v = ζ (coordinateMap π e d z) (fun i => fderiv ℝ (coordinateMap π e d) z (v i))) :
    (currentPushforward hπ S).inChart d (TestFunction.monoCLM ℝ ζ) =
      S.inChart e (TestFunction.monoCLM ℝ η) := by
  let ηe : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val) :=
    TestFunction.monoCLM ℝ η
  let ζd : TestForm (chartTarget d) (Module.finrank ℝ (ComplexModel n) - k.val) :=
    TestFunction.monoCLM ℝ ζ
  have hηe (x : ComplexModel n) : ηe x = η x := testForm_inclusion_apply hDe η x
  have hζd (x : ComplexModel n) : ζd x = ζ x := testForm_inclusion_apply hBd ζ x
  rw [currentPushforward_inChart, ← pairing_testExtension S e]
  apply pairing_eq_of_geometricallyEq
  intro c z hz
  set y := c.val.symm z with hy
  -- the right-hand side vanishes unless `y ∈ e⁻¹ D`
  have hRzero (hno : ¬ (y ∈ e.val.source ∧ e.val y ∈ D)) :
      (testExtension e ηe).coeff c z = 0 := by
    by_cases hye : y ∈ e.val.source
    · have hT : z ∈ (chartTransition c e).source := ⟨hz, hye⟩
      have hyD : e.val y ∉ D := fun h => hno ⟨hye, h⟩
      ext v
      rw [testExtension_coeff_of_mem e c ηe hT v]
      change ηe (e.val y) _ = 0
      rw [hηe, DDCOverlap.testForm_eq_zero_of_notMem η hyD]
      rfl
    · exact testExtension_coeff_eq_zero e c ηe hye
  by_cases h1 : π y ∈ d.val.source
  · have hzd : z ∈ coordinateDomain π c d := ⟨hz, h1⟩
    have hcm : coordinateMap π c d z = d.val (π y) := rfl
    rw [SmoothRealForm.pullback_coeff hπ _ c d hzd,
      testExtension_coeff_self d ζd (coordinateMap_mem_target hzd), hζd, hcm]
    by_cases h2 : d.val (π y) ∈ B
    · obtain ⟨hye, hyD⟩ := hfib y h1 h2
      have hT : z ∈ (chartTransition c e).source := ⟨hz, hye⟩
      have hTz : chartTransition c e z = e.val y := rfl
      have hτ : coordinateMap π e d (e.val y) = d.val (π y) := by
        change d.val (π (e.val.symm (e.val y))) = d.val (π y)
        rw [e.val.left_inv hye]
      have hder := coordinateMap_fderiv_change_source hπ c e d hT hzd
      ext v
      rw [testExtension_coeff_of_mem e c ηe hT v, hTz, hηe, hrel _ hyD, hτ,
        ContinuousAlternatingMap.compContinuousLinearMap_apply, hder, hTz]
      rfl
    · have h0 : ζ (d.val (π y)) = 0 := DDCOverlap.testForm_eq_zero_of_notMem ζ h2
      rw [h0, hRzero]
      · ext v
        rfl
      · rintro ⟨hye, hyD⟩
        apply h2
        have h := hmaps hyD
        have hτ : coordinateMap π e d (e.val y) = d.val (π y) := by
          change d.val (π (e.val.symm (e.val y))) = d.val (π y)
          rw [e.val.left_inv hye]
        rwa [hτ] at h
  · let d' := complexChartAt (n := n) (π y)
    have hzd' : z ∈ coordinateDomain π c d' := ⟨hz, mem_complexChartAt_source _⟩
    have hne : d'.val.symm (coordinateMap π c d' z) ∉ d.val.source := by
      change d'.val.symm (d'.val (π y)) ∉ d.val.source
      rwa [d'.val.left_inv (mem_complexChartAt_source _)]
    rw [SmoothRealForm.pullback_coeff hπ _ c d' hzd', testExtension_coeff_eq_zero d d' ζd hne,
      hRzero]
    · ext v
      rfl
    · rintro ⟨hye, hyD⟩
      apply h1
      have h := (hDdom hyD).2
      change π (e.val.symm (e.val y)) ∈ d.val.source at h
      rwa [e.val.left_inv hye] at h

end Reading

/-! ### Chart readers of `θ + ddᶜφ` and the key local identity -/

section Readers

variable {m : ℕ}

/-- The frame used to pair `(1,1)`-currents with test forms. -/
abbrev pairFrame (m : ℕ) :=
  currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))

/-- The degree of the test forms paired with `(1,1)`-currents. -/
abbrev testDeg (m : ℕ) : ℕ :=
  Module.finrank ℝ (ComplexModel (m + 1)) - (degreeTwo (Nat.succ_pos m)).val

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- **Chart reader of `θ + ddᶜu`**: on a domain `W` of the chart `e` carrying a local potential
`ρ` of `θ`, the current `θ + ddᶜu` is `ddᶜ` of the corrected potential `u + ρ`; on test forms,
`(θ + ddᶜu)_e(η) = ∫ (ddᶜ)^*η · (u + ρ)`. -/
theorem thetaPotentialCurrent_inChart_mono_eq_integral (θ : SmoothRealForm (m + 1) M 2)
    {u : M → EReal} (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (ρ : ComplexModel (m + 1) → ℝ)
    (hpot : IsSmoothLocalPotential θ e W ρ) (η : TestForm W (testDeg m)) :
    (thetaPotentialCurrent θ u hu).inChart e (TestFunction.monoCLM ℝ η) =
      ∫ x, ddcAdjoint (pairFrame m) η x * (chartFunction u e x + (ρ x : EReal)).toReal := by
  obtain ⟨-, -, hL, hcoef, -⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader θ hu e ρ hpot
  have hW : W ≤ chartTarget e := hpot.2.1
  have hfrom : fromLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
      ((thetaPotentialCurrent θ u hu).restrictChart e hW) =
      restrictForm ((thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e) hW := by
    ext v φ
    rw [GlobalCurrent.coefficients_restrictChart]
    rfl
  have hrestr : (thetaPotentialCurrent θ u hu).restrictChart e hW =
      toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
        (ddC (regularDistribution volume
          (fun z => (chartFunction u e z + (ρ z : EReal)).toReal) hL)) := by
    rw [← hcoef, ← hfrom, CurrentPairing.toLocalCurrent_fromLocalCurrent]
  change (thetaPotentialCurrent θ u hu).restrictChart e hW η = _
  rw [hrestr]
  change wedgePairing (pairFrame m) _ η = _
  rw [DDCOverlap.wedgePairing_ddC, regularDistribution_apply]

/-- Two local quasi-psh potentials whose pairings with all adjoint test functions agree have the
same `ddᶜ`. -/
theorem ddC_eq_of_forall_integral_eq {D : Opens (ComplexModel (m + 1))}
    {F G : ComplexModel (m + 1) → EReal}
    (hF : LocalQuasiPshPotentialOn F D) (hG : LocalQuasiPshPotentialOn G D)
    (h : ∀ η : TestForm D (testDeg m),
      ∫ x, ddcAdjoint (pairFrame m) η x * (F x).toReal =
        ∫ x, ddcAdjoint (pairFrame m) η x * (G x).toReal) :
    ddC (regularLocalQuasiPsh hF) = ddC (regularLocalQuasiPsh hG) := by
  have hT : toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
      (ddC (regularLocalQuasiPsh hF)) =
      toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
        (ddC (regularLocalQuasiPsh hG)) := by
    ext η
    change wedgePairing (pairFrame m) _ η = wedgePairing (pairFrame m) _ η
    rw [DDCOverlap.wedgePairing_ddC, DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh,
      regularLocalQuasiPsh, regularDistribution_apply, regularDistribution_apply]
    exact h η
  have h' := congrArg (fromLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) hT
  simpa only [CurrentPairing.fromLocalCurrent_toLocalCurrent] using h'

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- **The key local identity.** Let `π_*(θ + ddᶜφ) = θ' + ddᶜu'`, and let `τ = d ∘ π ∘ e⁻¹` be a
biholomorphism `D → B` satisfying the fibre condition, with local potentials `ρ` of `θ` on
`W ⊇ D` and `κ` of `θ'` on `W' ⊇ B`. Then the corrected potentials `φ + ρ` and `(u' + κ) ∘ τ`
pair identically with all adjoint test functions on `D`. -/
theorem integral_corrected_pushforward [CompactSpace Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (θ : SmoothRealForm (m + 1) Y 2) {φ : Y → EReal} (hφ : IsThetaPshPotential θ φ)
    (θ' : SmoothRealForm (m + 1) X 2) {u' : X → EReal} (hu' : IsThetaPshPotential θ' u')
    (heq : currentPushforward hπ (thetaPotentialCurrent θ φ hφ) =
      thetaPotentialCurrent θ' u' hu')
    (e : ComplexChart (m + 1) Y) (d : ComplexChart (m + 1) X)
    {D B W W' : Opens (ComplexModel (m + 1))} {σ : ComplexModel (m + 1) → ComplexModel (m + 1)}
    (hp : IsBiholomorphicPair D B (coordinateMap π e d) σ) (hDW : D ≤ W) (hBW' : B ≤ W')
    (hDdom : (D : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d)
    (hfib : ∀ y, π y ∈ d.val.source → d.val (π y) ∈ B → y ∈ e.val.source ∧ e.val y ∈ D)
    (ρ : ComplexModel (m + 1) → ℝ) (hρ : IsSmoothLocalPotential θ e W ρ)
    (κ : ComplexModel (m + 1) → ℝ) (hκ : IsSmoothLocalPotential θ' d W' κ)
    (η : TestForm D (testDeg m)) :
    ∫ x, ddcAdjoint (pairFrame m) η x * (chartFunction φ e x + (ρ x : EReal)).toReal =
      ∫ x, ddcAdjoint (pairFrame m) η x *
        (chartFunction u' d (coordinateMap π e d x) +
          (κ (coordinateMap π e d x) : EReal)).toReal := by
  have hDe : D ≤ chartTarget e := hDW.trans hρ.2.1
  have hBd : B ≤ chartTarget d := hBW'.trans hκ.2.1
  let ζ := pushTest hp η
  have hrel := pushTest_rel hp η
  have h1 : (thetaPotentialCurrent θ φ hφ).inChart e (TestFunction.monoCLM ℝ η) =
      ∫ x, ddcAdjoint (pairFrame m) η x * (chartFunction φ e x + (ρ x : EReal)).toReal := by
    have hmono : (TestFunction.monoCLM ℝ η : TestForm (chartTarget e) (testDeg m)) =
        TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm W (testDeg m)) := by
      apply TestFunction.ext
      intro x
      rw [testForm_inclusion_apply hDe, testForm_inclusion_apply hρ.2.1,
        testForm_inclusion_apply hDW]
    rw [hmono, thetaPotentialCurrent_inChart_mono_eq_integral θ hφ e ρ hρ]
    congr 1
    funext x
    rw [ddcAdjoint_monoCLM_apply hDW]
  have h2 : (thetaPotentialCurrent θ' u' hu').inChart d (TestFunction.monoCLM ℝ ζ) =
      ∫ y, ddcAdjoint (pairFrame m) ζ y * (chartFunction u' d y + (κ y : EReal)).toReal := by
    have hmono : (TestFunction.monoCLM ℝ ζ : TestForm (chartTarget d) (testDeg m)) =
        TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ ζ : TestForm W' (testDeg m)) := by
      apply TestFunction.ext
      intro x
      rw [testForm_inclusion_apply hBd, testForm_inclusion_apply hκ.2.1,
        testForm_inclusion_apply hBW']
    rw [hmono, thetaPotentialCurrent_inChart_mono_eq_integral θ' hu' d κ hκ]
    congr 1
    funext y
    rw [ddcAdjoint_monoCLM_apply hBW']
  have h3 := currentPushforward_inChart_eq hπ (thetaPotentialCurrent θ φ hφ) e d hDe hBd hDdom
    hp.mapsTo hfib η ζ hrel
  calc
    _ = (thetaPotentialCurrent θ φ hφ).inChart e (TestFunction.monoCLM ℝ η) := h1.symm
    _ = (currentPushforward hπ (thetaPotentialCurrent θ φ hφ)).inChart d
          (TestFunction.monoCLM ℝ ζ) := h3.symm
    _ = (thetaPotentialCurrent θ' u' hu').inChart d (TestFunction.monoCLM ℝ ζ) := by rw [heq]
    _ = _ := h2
    _ = _ := (integral_ddcAdjoint_mul_comp (pairFrame m) hp η ζ hrel
          (fun y => (chartFunction u' d y + (κ y : EReal)).toReal)).symm

end Readers

end SGPT.NPP.MassPushforward
