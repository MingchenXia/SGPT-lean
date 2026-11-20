import SGPT.NPP.MassPushforwardInvariance
import SGPT.Siu.SiuDecomposition
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
import SGPT.Foundations.Analysis.Pending.HolomorphicLocalInverse
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance

/-!
# Lelong numbers of push-forwards along modifications, and `lma:ndvpush`

Let `π : Y → X` be a proper bimeromorphic morphism of compact complex manifolds
(`IsAnalyticModification`), and let `Exc π` be its exceptional locus (the points where `dπ` is
not bijective).  Off `π(Exc π)` the map `π` is an isomorphism
(`AnalyticModificationExceptionalFibres.isIsomorphismOver_compl_image_exceptionalLocus`), and the
push-forward of a current is read, over this isomorphism locus, as the transport of the current
(`SGPT.NPP.MassPushforward.currentPushforward_inChart_eq`).  We deduce:

* `exists_inverse_off_image_exceptionalLocus`: the holomorphic inverse `s` of `π` over the
  complement of `π(Exc π)`;
* `exists_coordinatePairs_of_inverse`: coordinate biholomorphic pairs `τ = d ∘ π ∘ e⁻¹` over the
  complement of any closed set off which `π` has a holomorphic inverse (after
  `SGPT.NPP.MassPushforward.exists_coordinatePairs`, which uses the witness of the definition);
* `lelongNumber_eq_of_currentPushforward_eq`: if `π_*(θ + ddᶜφ) = θ' + ddᶜu'`, then
  `ν(φ, y) = ν(u', π y)` for every `y ∉ Exc π`;
* `currentLelong_currentPushforward`: **`ν(π_*T, π y) = ν(T, y)` for `y ∉ Exc π`**, for every
  closed positive `(1,1)`-current `T` on `Y`;
* `currentGenericLelong_currentPushforward`: for a prime divisor `D` of `X` and its strict
  transform `D'` (a prime divisor of `Y`, `strictTransformPrime`), `ν(π_*T, D) = ν(T, D')`;
* `isNonDivisorial_currentPushforward`: **source `lma:ndvpush`**: the push-forward of a
  non-divisorial current is non-divisorial.

The proof of `lma:ndvpush` is the book's: a prime divisor `D` of `X` is not contained in the
image of the exceptional locus (Zariski's main theorem; here
`AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one`),
its strict transform `D'` is a prime divisor of `Y`
(`AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader`), and by Siu's
semicontinuity theorem (closedness of the upper level sets of Lelong numbers,
`isClosed_currentLelong_superlevel`) the generic Lelong numbers along `D` and `D'` are computed
on the dense parts lying over the isomorphism locus, where they agree pointwise.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DDCOverlap
  SGPT.Foundations.Analysis.Pending.BedfordTaylor
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  SGPT.BDivisor SGPT.NPP.MassPushforward

/-! ### The inverse of a modification over the complement of the exceptional image -/

section Inverse

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
/-- A point lying over the complement of `π(Exc π)` is not exceptional. -/
theorem notMem_exceptionalLocus_of_notMem_image {π : Y → X} {y : Y}
    (hy : π y ∉ π '' exceptionalLocus n π) : y ∉ exceptionalLocus n π :=
  fun h => hy ⟨y, h, rfl⟩

/-- A non-exceptional point lies over the complement of `π(Exc π)`. -/
theorem notMem_image_of_notMem_exceptionalLocus {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) {y : Y} (hy : y ∉ exceptionalLocus n π) :
    π y ∉ π '' exceptionalLocus n π := by
  intro h
  apply hy
  rw [← AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hπ]
  exact h

/-- **The holomorphic inverse of a modification off the exceptional image.** Over the open
complement of `π(Exc π)` the modification `π` is bijective and unramified, and its inverse is
holomorphic. -/
theorem exists_inverse_off_image_exceptionalLocus {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) :
    ∃ s : X → Y, ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s
        (π '' exceptionalLocus n π)ᶜ ∧
      (∀ x ∉ π '' exceptionalLocus n π, π (s x) = x) ∧
      ∀ y, π y ∉ π '' exceptionalLocus n π → s (π y) = y := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x,
      fun y => isEmptyElim (π y)⟩
  have : Nonempty Y :=
    ⟨(AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ x₀).choose⟩
  set E := π '' exceptionalLocus n π with hE
  have hiso := AnalyticModificationExceptionalFibres.isIsomorphismOver_compl_image_exceptionalLocus
    hπ
  have hbij : BijOn π (π ⁻¹' Eᶜ) Eᶜ := hiso.1
  set s := Function.invFunOn π (π ⁻¹' Eᶜ) with hsdef
  have hright : ∀ x ∉ E, π (s x) = x := fun x hx => hbij.surjOn.rightInvOn_invFunOn hx
  have hmem : ∀ x ∉ E, s x ∈ π ⁻¹' Eᶜ := fun x hx => hbij.surjOn.mapsTo_invFunOn hx
  have hleft : ∀ y, π y ∉ E → s (π y) = y := fun y hy => hbij.injOn.leftInvOn_invFunOn hy
  refine ⟨s, ?_, hright, hleft⟩
  intro x hx
  have hsx : π (s x) = x := hright x hx
  have hy : s x ∉ exceptionalLocus n π := by
    apply notMem_exceptionalLocus_of_notMem_image
    rw [hsx]
    exact hx
  obtain ⟨V, t, hV, hxV, -, htinv, htsmooth, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse hπ.1 hy
  rw [hsx] at hxV
  have hEc : IsOpen Eᶜ :=
    (AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ).isOpen_compl
  have heq : t =ᶠ[𝓝 x] s := by
    filter_upwards [hV.mem_nhds hxV, hEc.mem_nhds hx] with x' hx'V hx'E
    have h1 : t x' ∈ π ⁻¹' Eᶜ := by
      change π (t x') ∈ Eᶜ
      rw [htinv x' hx'V]
      exact hx'E
    exact hbij.injOn h1 (hmem x' hx'E) ((htinv x' hx'V).trans (hright x' hx'E).symm)
  exact ((htsmooth x hxV).congr_of_eventuallyEq heq.symm).contMDiffWithinAt

end Inverse

/-! ### Coordinate biholomorphic pairs over an isomorphism locus -/

section Pairs

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

theorem coordinateMap_contDiffAt_of_contMDiffAt {f : X → Y}
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

/-- **Coordinate biholomorphic pairs over an isomorphism locus.** Let `π : Y → X` be holomorphic,
`E ⊆ X` closed, and `s : X → Y` holomorphic on `Eᶜ` with `π ∘ s = id` on `Eᶜ` and `s ∘ π = id`
on `π⁻¹(Eᶜ)`. At every `y` with `π y ∉ E` and for any charts `e ∋ y`, `d ∋ π y`, the coordinate
expressions `d ∘ π ∘ e⁻¹ : A → B` and `e ∘ s ∘ d⁻¹ : B → A` are inverse biholomorphisms, with
`d⁻¹(B) ∩ E = ∅` and `s(d⁻¹ B) ⊆ e(Y)`. -/
theorem exists_coordinatePairs_of_inverse {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {E : Set X} (hEc : IsClosed E) {s : X → Y}
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Eᶜ)
    (hright : ∀ x ∉ E, π (s x) = x) (hleft : ∀ y, π y ∉ E → s (π y) = y)
    (y : Y) (hy : π y ∉ E) (e : ComplexChart n Y) (d : ComplexChart n X)
    (hye : y ∈ e.val.source) (hyd : π y ∈ d.val.source) :
    ∃ (A B : Opens (ComplexModel n)), e.val y ∈ A ∧
      A ≤ chartTarget e ∧ B ≤ chartTarget d ∧
      ((A : Set (ComplexModel n)) ⊆ coordinateDomain π e d) ∧
      (∀ z ∈ B, d.val.symm z ∉ E) ∧ (∀ z ∈ B, s (d.val.symm z) ∈ e.val.source) ∧
      IsBiholomorphicPair A B (coordinateMap π e d) (coordinateMap s d e) := by
  let V : Set X := d.val.source ∩ (Eᶜ ∩ s ⁻¹' e.val.source)
  have hV : IsOpen V := d.val.open_source.inter
    (hs.continuousOn.isOpen_inter_preimage hEc.isOpen_compl e.val.open_source)
  have hys : s (π y) = y := hleft y hy
  have hyV : π y ∈ V := by
    refine ⟨hyd, hy, ?_⟩
    change s (π y) ∈ e.val.source
    rwa [hys]
  let A : Opens (ComplexModel n) := ⟨e.val.target ∩ e.val.symm ⁻¹' (π ⁻¹' V),
    e.val.isOpen_inter_preimage_symm (hV.preimage hπ.continuous)⟩
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
  refine { holo := (coordinateMap_contDiffOn hπ e d).mono hAdom
           holo_inv := ?_
           mapsTo := ?_
           mapsTo_inv := ?_
           left_inv := ?_
           right_inv := ?_ }
  · intro w hw
    have hdom : w ∈ coordinateDomain s d e := ⟨hw.1, hw.2.2.2⟩
    exact (coordinateMap_contDiffAt_of_contMDiffAt d e hdom
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
    rw [d.val.left_inv hzdom.2, hleft _ hz.2.2.1, e.val.right_inv hz.1]
  · intro w hw
    have hswe : s (d.val.symm w) ∈ e.val.source := hw.2.2.2
    change d.val (π (e.val.symm (e.val (s (d.val.symm w))))) = w
    rw [e.val.left_inv hswe, hright _ (hBoff w hw), d.val.right_inv hw.1]

end Pairs

/-! ### Lelong numbers of the push-forward over the isomorphism locus -/

section LocalLelong

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- **Lelong numbers of the potentials of a push-forward over the isomorphism locus.** If
`π_*(θ + ddᶜφ) = θ' + ddᶜu'` for a modification `π : Y → X` from a compact manifold, then
`ν(φ, y) = ν(u', π y)` at every point `y` where `dπ` is bijective. -/
theorem lelongNumber_eq_of_currentPushforward_eq [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : SmoothRealForm (m + 1) Y 2) {φ : Y → EReal} (hφ : IsThetaPshPotential θ φ)
    (θ' : ClosedRealOneOneForm (m + 1) X) {u' : X → EReal} (hu' : IsThetaPshPotential θ'.val u')
    (heq : currentPushforward hπ.1 (thetaPotentialCurrent θ φ hφ) =
      thetaPotentialCurrent θ'.val u' hu')
    {y : Y} (hy : y ∉ exceptionalLocus (m + 1) π) :
    lelongNumber (n := m + 1) φ y = lelongNumber (n := m + 1) u' (π y) := by
  classical
  obtain ⟨s, hs, hright, hleft⟩ := exists_inverse_off_image_exceptionalLocus hπ
  have hEc := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hπ
  have hxE := notMem_image_of_notMem_exceptionalLocus hπ hy
  let e := complexChartAt (n := m + 1) y
  let d := complexChartAt (n := m + 1) (π y)
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hyd : π y ∈ d.val.source := mem_complexChartAt_source (π y)
  obtain ⟨A, B, hyA, hAe, hBd, hAdom, hBE, hBs, hp⟩ :=
    exists_coordinatePairs_of_inverse hπ.1 hEc hs hright hleft y hxE e d hye hyd
  set τ := coordinateMap π e d with hτdef
  have hτy : τ (e.val y) = d.val (π y) := by
    change d.val (π (e.val.symm (e.val y))) = d.val (π y)
    rw [e.val.left_inv hye]
  -- local potentials of `θ` near `e y` and of `θ'` near `d (π y)`
  obtain ⟨W, ρ, hyW, hρ, hρpsh⟩ := hφ.1 e (e.val y) (e.val.map_source hye)
  obtain ⟨W', κ, hxW', hκ, hκpsh⟩ := hu'.1 d (d.val (π y)) (d.val.map_source hyd)
  let Wo : Opens (ComplexModel (m + 1)) := ⟨W, hρ.1⟩
  let W'o : Opens (ComplexModel (m + 1)) := ⟨W', hκ.1⟩
  -- the common coordinate domain
  let D : Opens (ComplexModel (m + 1)) :=
    ⟨(A : Set (ComplexModel (m + 1))) ∩ W ∩ τ ⁻¹' W',
      (hp.holo.continuousOn.mono inter_subset_left).isOpen_inter_preimage
        (A.isOpen.inter hρ.1) hκ.1⟩
  have hDA : D ≤ A := fun _ hz => hz.1.1
  have hDW : D ≤ Wo := fun _ hz => hz.1.2
  have hDe : D ≤ chartTarget e := hDA.trans hAe
  have hDdom : (D : Set (ComplexModel (m + 1))) ⊆ coordinateDomain π e d := fun _ hz =>
    hAdom (hDA hz)
  have hyD : e.val y ∈ D := ⟨⟨hyA, hyW⟩, by
    change τ (e.val y) ∈ W'
    rw [hτy]
    exact hxW'⟩
  have hpD := restrictPair hp hDA
  set B' : Opens (ComplexModel (m + 1)) :=
    ⟨(B : Set (ComplexModel (m + 1))) ∩ coordinateMap s d e ⁻¹' D,
      hp.holo_inv.continuousOn.isOpen_inter_preimage B.isOpen D.isOpen⟩ with hB'
  have hB'W' : B' ≤ W'o := by
    intro w hw
    have h1 : τ (coordinateMap s d e w) ∈ W' := hw.2.2
    rwa [hp.right_inv w hw.1] at h1
  have hfib : ∀ y', π y' ∈ d.val.source → d.val (π y') ∈ B' →
      y' ∈ e.val.source ∧ e.val y' ∈ D := fun y' h1 h2 =>
    fibre_mem hleft hBE hBs h1 h2
  -- the two corrected potentials on `D`
  have hcomp := isThetaPshPotential_comp_of_isAnalyticModification hπ θ' hu'
  set F : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction φ e z + (ρ z : EReal) with hFdef
  set G : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction (fun y => u' (π y)) e z + (κ (τ z) : EReal) with hGdef
  have hGeq : EqOn G (fun z => chartFunction u' d (τ z) + (κ (τ z) : EReal)) D := by
    intro z hz
    have hzd : π (e.val.symm z) ∈ d.val.source := (hDdom hz).2
    change u' (π (e.val.symm z)) + _ = u' (d.val.symm (d.val (π (e.val.symm z)))) + _
    rw [d.val.left_inv hzd]
  have hGpsh : PlurisubharmonicOn G D := by
    have h := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic D.isOpen
      ((hp.holo.mono hDA).differentiableOn (by simp)) (fun z hz => hz.2) hκpsh
    intro z hz
    refine (h z hz).congr ?_
    filter_upwards [D.isOpen.mem_nhds hz] with z' hz'
    exact (hGeq hz').symm
  have hF : LocalQuasiPshPotentialOn F D :=
    corrected_localQuasiPsh hφ hDe (hρpsh.mono hDW)
  have hG : LocalQuasiPshPotentialOn G D := corrected_localQuasiPsh hcomp hDe hGpsh
  have hint (η : TestForm D (testDeg m)) :
      ∫ x, ddcAdjoint (pairFrame m) η x * (F x).toReal =
        ∫ x, ddcAdjoint (pairFrame m) η x * (G x).toReal := by
    have hk := integral_corrected_pushforward hπ.1 θ hφ θ'.val hu' heq e d hpD hDW hB'W'
      hDdom hfib ρ hρ κ hκ η
    refine hk.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
    by_cases hx : x ∈ D
    · change _ * (chartFunction u' d (τ x) + (κ (τ x) : EReal)).toReal = _ * (G x).toReal
      rw [hGeq hx]
    · have h0 : ddcAdjoint (pairFrame m) η x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h =>
          hx ((ddcAdjoint (pairFrame m) η).tsupport_subset h)
      simp only [h0, zero_mul]
  have hddc := ddC_eq_of_forall_integral_eq hF hG hint
  obtain ⟨U, hUD, h, hyU, hh, -, hdiff, -, -⟩ :=
    exists_smooth_original_difference_of_equal_native_ddc hF hG hddc (e.val y) hyD
  -- Lelong numbers
  have hρc : ContinuousAt ρ (e.val y) :=
    ((hρ.2.2.1 _ hyW).contDiffAt (hρ.1.mem_nhds hyW)).continuousAt
  have hτc : ContinuousAt τ (e.val y) :=
    (hp.holo.contDiffAt (A.isOpen.mem_nhds hyA)).continuousAt
  have hκc : ContinuousAt (fun z => κ (τ z)) (e.val y) := by
    have h1 : ContinuousAt κ (τ (e.val y)) := by
      rw [hτy]
      exact ((hκ.2.2.1 _ hxW').contDiffAt (hκ.1.mem_nhds hxW')).continuousAt
    exact h1.comp hτc
  have hhc : ContinuousAt h (e.val y) := hh.continuous.continuousAt
  have hcongr : F =ᶠ[𝓝 (e.val y)] fun z => G z + (h z : EReal) :=
    Filter.eventually_of_mem (U.isOpen.mem_nhds hyU) fun z hz => hdiff hz
  have hstep1 : lelongNumber (n := m + 1) φ y = lelongNumber (n := m + 1) F (e.val y) := by
    rw [LelongChartReaderInvariance.lelongNumber_add_continuous_eq hρc,
      LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hye]
  have hstep2 : lelongNumber (n := m + 1) F (e.val y) =
      lelongNumber (n := m + 1) (fun y => u' (π y)) y := by
    rw [LelongNumberComparison.lelongNumber_congr hcongr,
      LelongChartReaderInvariance.lelongNumber_add_continuous_eq hhc,
      LelongChartReaderInvariance.lelongNumber_add_continuous_eq hκc,
      LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hye]
  have hle1 : lelongNumber (n := m + 1) u' (π y) ≤
      lelongNumber (n := m + 1) (fun y => u' (π y)) y :=
    LelongNumberComparison.lelongNumber_le_comp (hπ.1.mdifferentiableAt (by simp))
      fun hpos => eq_bot_of_lelongNumber_pos (Nat.succ_pos m) hu'.1 hpos
  have hle2 : lelongNumber (n := m + 1) (fun y => u' (π y)) y ≤
      lelongNumber (n := m + 1) u' (π y) :=
    HolomorphicLocalInverse.lelongNumber_comp_le hπ.1 hy
      fun hpos => eq_bot_of_lelongNumber_pos (Nat.succ_pos m) hcomp.1 hpos
  rw [hstep1, hstep2]
  exact le_antisymm hle2 hle1

end LocalLelong

/-! ### Lelong numbers of the push-forward of a closed positive current -/

section PushforwardCurrents

/-- **The push-forward of a closed positive `(1,1)`-current is a closed positive
`(1,1)`-current.** -/
theorem isClosedPositiveCurrent_currentPushforward {m : ℕ} {Z W : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z] [CompactSpace Z]
    [TopologicalSpace W] [ChartedSpace (ComplexModel (m + 1)) W] [IsComplexManifold (m + 1) W]
    {g : Z → W} (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    {T : GlobalCurrent (m + 1) Z (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T) :
    IsClosedPositiveCurrent (currentPushforward hg T) :=
  ⟨isClosed_currentPushforward hg _ hT.1,
    isTypeOneOne_currentPushforward hg (Nat.succ_pos m) _ hT.2.1,
    isFullPositive_currentPushforward hg hT.2.2⟩

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

/-- **Lelong numbers of the push-forward over the isomorphism locus**: for a closed positive
`(1,1)`-current `T` on `Y` and a point `y` where `dπ` is bijective, `ν(π_*T, π y) = ν(T, y)`. -/
theorem currentLelong_currentPushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    {T : GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    {y : Y} (hy : y ∉ exceptionalLocus (m + 1) π) :
    currentLelong (currentPushforward hπ.1 T)
        (isClosedPositiveCurrent_currentPushforward hπ.1 hT) (π y) =
      currentLelong T hT y := by
  obtain ⟨σ, φ, hφ, heqT⟩ := hT.exists_thetaPotential
  have hT' := isClosedPositiveCurrent_currentPushforward hπ.1 hT
  obtain ⟨σ', u', hu', heqT'⟩ := hT'.exists_thetaPotential
  have hpush : currentPushforward hπ.1 (thetaPotentialCurrent σ.val φ hφ) =
      thetaPotentialCurrent σ'.val u' hu' := by
    rw [← heqT]
    exact heqT'
  have hL := lelongNumber_eq_of_currentPushforward_eq hπ σ.val hφ σ' hu' hpush hy
  rw [currentLelong_eq_of_eq_thetaPotentialCurrent hT' heqT',
    currentLelong_eq_of_eq_thetaPotentialCurrent hT heqT]
  dsimp only
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
    ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  exact hL.symm

/-- **The strict transform of a prime divisor** `D` of `X` under a modification `π : Y → X`:
the prime divisor `D' = closure (π⁻¹ D ∖ Exc π)` of `Y` (a closed irreducible analytic
hypersurface, `AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader`). -/
def strictTransformPrime {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y :=
  ⟨strictTransform (m + 1) π D.val, by
    obtain ⟨V, hVc, hVdim⟩ := D.property
    obtain ⟨Vt, hst, hd, -, -⟩ :=
      AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hπ V hVdim
    exact ⟨Vt, by rw [hst, hVc], by rw [hd]; exact hVdim⟩⟩

omit [CompactSpace X] [CompactSpace Y] in
theorem strictTransformPrime_val {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    (strictTransformPrime hπ D).val = strictTransform (m + 1) π D.val := rfl

omit [CompactSpace X] [CompactSpace Y] in
/-- The strict transform of `D` maps onto `D`. -/
theorem image_strictTransformPrime {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    π '' (strictTransformPrime hπ D).val = D.val := by
  obtain ⟨V, hVc, hVdim⟩ := D.property
  obtain ⟨Vt, hst, -, himg, -⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hπ V hVdim
  rw [strictTransformPrime_val, ← hVc, ← hst, himg]

/-- **Generic Lelong numbers of the push-forward along strict transforms**: for a prime divisor
`D` of `X` with strict transform `D'`, `ν(π_*T, D) = ν(T, D')`. -/
theorem currentGenericLelong_currentPushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    {T : GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    currentGenericLelong (currentPushforward hπ.1 T)
        (isClosedPositiveCurrent_currentPushforward hπ.1 hT) D =
      currentGenericLelong T hT (strictTransformPrime hπ D) := by
  have hT' := isClosedPositiveCurrent_currentPushforward hπ.1 hT
  set S : Set Y := π ⁻¹' D.val \ exceptionalLocus (m + 1) π with hSdef
  have hD' : (strictTransformPrime hπ D).val = closure S := rfl
  have hread : ∀ y ∈ S, currentLelong (currentPushforward hπ.1 T) hT' (π y) =
      currentLelong T hT y := fun y hy => currentLelong_currentPushforward hπ hT hy.2
  apply le_antisymm
  · -- `ν(π_*T, D) ≤ ν(T, y)` on `S`, hence on its closure `D'`
    set a := currentGenericLelong (currentPushforward hπ.1 T) hT' D
    have hSsub : S ⊆ {y : Y | a ≤ currentLelong T hT y} := by
      intro y hy
      rw [mem_ofPred_eq, ← hread y hy]
      exact currentGenericLelong_le hT' D hy.1
    have hcl := closure_minimal hSsub (isClosed_currentLelong_superlevel hT a)
    refine le_iInf₂ fun y hy => ?_
    rw [hD'] at hy
    exact hcl hy
  · -- `ν(T, D') ≤ ν(π_*T, x)` on `π(S)`, hence on its closure, which contains `D = π(D')`
    set b := currentGenericLelong T hT (strictTransformPrime hπ D)
    have hSsub : π '' S ⊆ {x : X | b ≤ currentLelong (currentPushforward hπ.1 T) hT' x} := by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_ofPred_eq, hread y hy]
      exact currentGenericLelong_le hT _ (by rw [hD']; exact subset_closure hy)
    have hcl := closure_minimal hSsub (isClosed_currentLelong_superlevel hT' b)
    have hDsub : D.val ⊆ closure (π '' S) := by
      rw [← image_strictTransformPrime hπ D, hD']
      exact image_closure_subset_closure_image hπ.1.continuous
    exact le_iInf₂ fun x hx => hcl (hDsub hx)

/-- **Source `lma:ndvpush`: the push-forward of a non-divisorial current is non-divisorial.** For
a proper bimeromorphic morphism `π : Y → X` of compact complex manifolds and a non-divisorial
closed positive `(1,1)`-current `T` on `Y`, the closed positive current `π_*T` is
non-divisorial. -/
theorem isNonDivisorial_currentPushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    {T : GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (hnd : IsNonDivisorial T hT) :
    IsNonDivisorial (currentPushforward hπ.1 T)
      (isClosedPositiveCurrent_currentPushforward hπ.1 hT) := by
  rw [isNonDivisorial_iff] at hnd ⊢
  intro D
  rw [currentGenericLelong_currentPushforward hπ hT D]
  exact hnd _

end PushforwardCurrents

end SGPT.Siu
