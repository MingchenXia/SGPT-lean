import SGPT.NPP.DN8Transfer
import SGPT.NPP.DN2Modification
import SGPT.NPP.DN7Main
import SGPT.NPP.DNTBigReduction
import SGPT.NPP.DNTBigLowDim
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization

/-!
# `thm:DNT23_C11bar` for all big classes

Source: SGPT `thm:DNT23_C11bar` (`chapter_npp.tex`, Di Nezza–Trapani): if `{θ}` is
big and `f ∈ C^{1,1̄}(X)`, then `P_θ(f) ∈ C^{1,1̄}(X ∖ nK({θ}))`; in particular
`V_θ ∈ C^{1,1̄}(X ∖ nK({θ}))`.  The proof is FPT `thm:big-metric-laplacian-rooftop`
(`chapters/inputs/q10-big-envelope-regularity.tex`):

1. **Reduction to one obstacle with bounded complex Hessian** (`DNTBig.rooftopEnvelope_eq_of_bounded_obstacle`):
   `P_θ(f) = P_θ(g)` with `g = P_κ(f)` of bounded complex Hessian; adding a constant,
   `0 ≤ g + c ≤ B` (`rooftopEnvelope_add_const`).
2. **Passage to a modification** (lane DN7, `DN7.exists_modificationData`): a modification
   `π : Y → X` which is biholomorphic over `X ∖ nK` (holomorphic section `σ`), a Kähler form `ω_Y`
   and a divisorial Kähler current `π^*θ + ddᶜφ ≥ ω_Y` with poles `π⁻¹(nK)`.
3. **The estimate on the modification** (lane DN2, `DN2.hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing`):
   `P_θ(g) ∘ π ∈ C^{1,1̄}_{ω_Y}(Y ∖ π⁻¹(nK))`, from the joint smoothing of FPT
   `lem:chern-joint-smoothing` (`DN2.JointSmoothingStatement`, lanes DN3–DN6).
4. **Return to `X`** (`hasBoundedMetricLaplacianOn_of_holomorphic_section`, this lane): through
   `σ`, `P_θ(g) ∈ C^{1,1̄}_ω(X ∖ nK)`.

Here `nK` is the native non-Kähler locus (`nonKahlerLocus`, positive Lelong numbers of all Kähler
currents in the class), which is contained in the book's `nK({θ})` (`sourceNonKahlerLocus`,
`def:nKlocus`), so the statement on `X ∖ nK` is at least as strong as the book's.  In complex
dimension `0` the source statement is DNT-BIG's `…_of_dim_le_one`.

## Main results

* `rooftopEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing`: native form.
* `sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing`,
  `sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing`: the book's
  statement and its "in particular", for every big class, given `DN2.JointSmoothingStatement`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Manifold

namespace SGPT.NPP.DN8

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Envelopes.LapClass

/-! ### The class `C^{1,1̄}_ω(U)` -/

section Class

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

omit [BorelSpace Y] in
/-- `C^{1,1̄}_ω(U)` only depends on the values on `U`. -/
theorem HasBoundedMetricLaplacianOn.congr {w : KahlerBackground N Y} {U : Set Y} {F G : Y → ℝ}
    (hF : HasBoundedMetricLaplacianOn w U F) (hFG : EqOn F G U) :
    HasBoundedMetricLaplacianOn w U G := by
  refine ⟨hF.1.congr fun x hx => (hFG hx).symm, fun K hKU hKc => ?_⟩
  obtain ⟨M, hM⟩ := hF.2 K hKU hKc
  refine ⟨M, fun χ hχ hχ0 hχK => ?_⟩
  have heq : ∫ y, G y * laplacian w.form.val χ y ∂(kahlerVolume w) =
      ∫ y, F y * laplacian w.form.val χ y ∂(kahlerVolume w) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport χ
    · show G y * _ = F y * _
      rw [hFG (hKU (hχK hy))]
    · show G y * _ = F y * _
      rw [KahlerLaplacianStokes.laplacian_eq_zero_of_notMem_tsupport _ hy]
      simp
  rw [heq]
  exact hM χ hχ hχ0 hχK

omit [BorelSpace Y] in
/-- `C^{1,1̄}_ω(U)` passes to smaller sets. -/
theorem HasBoundedMetricLaplacianOn.mono {w : KahlerBackground N Y} {U U' : Set Y} (hUU' : U ⊆ U')
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacianOn w U' f) : HasBoundedMetricLaplacianOn w U f :=
  ⟨hf.1.mono hUU', fun K hK hKc => hf.2 K (hK.trans hUU') hKc⟩

/-- `C^{1,1̄}_ω(U)` is stable under subtracting constants (`∫ Δ_ω χ ω^N = 0`). -/
theorem HasBoundedMetricLaplacianOn.sub_const {w : KahlerBackground N Y} {U : Set Y}
    (hU : IsOpen U) {F : Y → ℝ} (hF : HasBoundedMetricLaplacianOn w U F) (c : ℝ) :
    HasBoundedMetricLaplacianOn w U (fun y => F y - c) := by
  refine ⟨hF.1.sub continuousOn_const, fun K hKU hKc => ?_⟩
  obtain ⟨M, hM⟩ := hF.2 K hKU hKc
  refine ⟨M, fun χ hχ hχ0 hχK => ?_⟩
  have hi := DNTBig.integrable_mul_laplacian_of_tsupport_subset w hU hF.1 hχ (hχK.trans hKU)
  have hl : Integrable (fun y => laplacian w.form.val χ y) (kahlerVolume w) :=
    integral_continuous (continuous_laplacian_of_chartSmooth w.isKahler.1 hχ) _
  have h0 := KahlerLaplacianStokes.integral_laplacian_eq_zero w (chartSmooth_two' hχ)
  have hsplit : ∫ y, (F y - c) * laplacian w.form.val χ y ∂(kahlerVolume w) =
      (∫ y, F y * laplacian w.form.val χ y ∂(kahlerVolume w)) -
        c * ∫ y, laplacian w.form.val χ y ∂(kahlerVolume w) := by
    rw [← integral_const_mul, ← integral_sub hi (hl.const_mul c)]
    congr 1; funext y; ring
  rw [hsplit, h0, mul_zero, sub_zero]
  exact hM χ hχ hχ0 hχK

end Class

theorem eq_coe_sub_of_add_eq {p : EReal} {a c : ℝ} (h : p + (c : EReal) = (a : EReal)) :
    p = ((a - c : ℝ) : EReal) := by
  induction p using EReal.rec with
  | bot => simp at h
  | coe b =>
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
      rw [EReal.coe_eq_coe_iff]
      linarith
  | top => simp at h

/-! ### The native theorem -/

universe u

section Native

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [ConnectedSpace X]

/-- **`thm:DNT23_C11bar` for every big class, native form** (given the joint smoothing of FPT
`lem:chern-joint-smoothing`).  If `{θ}` is big and `f ∈ C^{1,1̄}_ω(X)`, then `P_θ(f)` is
real-valued off the non-Kähler locus and has bounded `ω`-Laplacian on every compact subset of
`X ∖ nK({θ})`. -/
theorem rooftopEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing
    (hJ : DN2.JointSmoothingStatement.{u}) (w : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {f : X → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    (∀ x ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ),
      rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
        (((rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w (nonKahlerLocus (RealBottChern.ofRepresentative θ))ᶜ
      (fun x => (rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal) := by
  classical
  have hn : 0 < m + 1 := Nat.succ_pos m
  set nK := nonKahlerLocus (RealBottChern.ofRepresentative θ) with hnKdef
  -- 1. reduction to one obstacle with bounded complex Hessian, `0 ≤ g' ≤ B`
  obtain ⟨φ₀, hφ₀⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  obtain ⟨g, -, hgH, -, heq⟩ := DNTBig.rooftopEnvelope_eq_of_bounded_obstacle w θ hφ₀ hf
  obtain ⟨c₀, hc₀⟩ := isCompact_univ.exists_bound_of_continuousOn hgH.1.continuousOn
  set c := |c₀| with hcdef
  have hgc : ∀ x, |g x| ≤ c := fun x => by
    have := hc₀ x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  set g' : X → ℝ := fun x => g x + c with hg'def
  have hg'0 : ∀ x, 0 ≤ g' x := fun x => by
    have := abs_le.mp (hgc x)
    simp only [hg'def]
    linarith
  have hg'B : ∀ x, g' x ≤ 2 * c := fun x => by
    have := abs_le.mp (hgc x)
    simp only [hg'def]
    linarith
  have hB0 : 0 ≤ 2 * c := by positivity
  have hg'H : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := m + 1) g' :=
    ⟨hgH.1.add continuous_const, fun e =>
      hgH.exists_density_add e e.val.open_target subset_rfl contDiffOn_const⟩
  set P' := rooftopEnvelope θ.val (fun y => (g' y : EReal)) with hP'def
  have hshift : ∀ x, rooftopEnvelope θ.val (fun y => (g y : EReal)) x + (c : EReal) = P' x := by
    intro x
    have h := RooftopEnvelopeNormalization.rooftopEnvelope_add_const θ.val
      (fun y => (g y : EReal)) c
    have hfun : (fun y => (g y : EReal) + (c : EReal)) = fun y => (g' y : EReal) := by
      funext y
      simp only [hg'def, EReal.coe_add]
    rw [hfun] at h
    rw [hP'def, h]
  -- 2. the modification data
  obtain ⟨Y, tY, cY, mY, π, hπ, wY, φ, Cφ, hYc, -, -, ⟨σ, hσ, hπσ, -⟩, hφ1, hφ2, hφ0, hZ, hZi,
    hφZ, hφc, hCφ, hφs, hφL⟩ := DN7.exists_modificationData hn θ hbig
  let _ : MeasurableSpace Y := borel Y
  have _ : BorelSpace Y := ⟨rfl⟩
  -- 3. the estimate on the modification
  obtain ⟨r₀, Ψ, hJs⟩ := hJ (m + 1) Y wY
  have hYL := DN2.hasBoundedMetricLaplacianOn_envelope_comp_of_jointSmoothing hn w θ hbig hg'H
    hg'0 hB0 hg'B hπ hJs hφ1 hφ2 hφ0 hZ hZi hφZ hφc hCφ hφs hφL
  obtain ⟨hu, hudef, hule⟩ := DN2.envelope_pullback_data hn hπ θ hbig hg'H.1
  set u : Y → EReal := fun y => P' (π y) with hudef'
  have hφu : ∀ y, φ y ≤ u y := by
    have h := le_rooftopEnvelope hφ2 (quasiEverywhere_of_forall (n := m + 1) fun y =>
      (hφ0 y).trans (EReal.coe_nonneg.mpr (hg'0 (π y))))
    intro y
    rw [show u y = _ from congrFun hudef y]
    exact h y
  have hfin : ∀ y ∈ (π ⁻¹' nK)ᶜ, u y = ((u y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hule y))
      (ne_bot_of_le_ne_bot (hφZ y hy) (hφu y))).symm
  -- `nK` is closed: the image of the closed set `π⁻¹(nK)` under the proper surjection `π`
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  have hnKc : IsClosed nK := by
    have h : π '' (π ⁻¹' nK) = nK := image_preimage_eq nK hsurj
    rw [← h]
    exact hπ.2.1.isClosedMap _ hZ.isClosed
  have hσU : ∀ x ∈ nKᶜ, σ x ∈ (π ⁻¹' nK)ᶜ := fun x hx => by
    show π (σ x) ∉ nK
    rw [hπσ x hx]
    exact hx
  -- 4. return to `X` through the section `σ`
  have hX := hasBoundedMetricLaplacianOn_of_holomorphic_section w wY
    (ClosedRealOneOneForm.pullback hπ.1 θ).val hu.1 hZ.isClosed.isOpen_compl hfin hYL
    hnKc.isOpen_compl hσ hσU (f := fun x => (P' x).toReal) fun x hx => by
      simp only [hudef']
      rw [hπσ x hx]
  -- finiteness of `P'` and the identification with `P_θ(f)`
  have hP'fin : ∀ x ∈ nKᶜ, P' x = ((P' x).toReal : EReal) := fun x hx => by
    have h := hfin (σ x) (hσU x hx)
    simp only [hudef'] at h
    rwa [hπσ x hx] at h
  have hPf : ∀ x ∈ nKᶜ, rooftopEnvelope θ.val (fun y => (f y : EReal)) x =
      (((P' x).toReal - c : ℝ) : EReal) := fun x hx => by
    rw [heq]
    apply eq_coe_sub_of_add_eq
    rw [hshift x]
    exact hP'fin x hx
  refine ⟨fun x hx => by rw [hPf x hx, EReal.toReal_coe], ?_⟩
  refine HasBoundedMetricLaplacianOn.congr
    (HasBoundedMetricLaplacianOn.sub_const hnKc.isOpen_compl hX c) fun x hx => ?_
  show (P' x).toReal - c = (rooftopEnvelope θ.val (fun y => (f y : EReal)) x).toReal
  rw [hPf x hx, EReal.toReal_coe]

end Native

/-! ### The source statements -/

section Source

open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {N : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel N) X]
  [IsComplexManifold N X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Source `thm:DNT23_C11bar`** (book class `C^{1,1̄}`, bounded `ω`-Laplacian), for every big
class, given the joint smoothing (`DN2.JointSmoothingStatement`, FPT `lem:chern-joint-smoothing`):
if `{θ}` is big and `f ∈ C^{1,1̄}_ω(X)`, then `P_θ(f) = sourceRelativeEnvelope θ ⊤ f`
(`def:Pthetaf`) is real-valued on `X ∖ nK({θ})` and lies in `C^{1,1̄}_ω(X ∖ nK({θ}))`, with
`nK = sourceNonKahlerLocus` (`def:nKlocus`). -/
theorem sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing
    (hJ : DN2.JointSmoothingStatement.{u}) (w : KahlerBackground N X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {f : X → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    (∀ x ∉ sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
        (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) :
          EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  rcases N with _ | m
  · obtain ⟨h1, h2⟩ :=
      DNTBig.sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_dim_le_one
        (by omega) w θ hbig hf
    exact ⟨fun x _ => h1 x, h2⟩
  · rw [sourceObstacleEnvelope_eq_native]
    obtain ⟨h1, h2⟩ :=
      rooftopEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing hJ w _ hbig hf
    have hsub := nativeNonKahlerLocus_subset_source (Nat.succ_pos m)
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))
    exact ⟨fun x hx => h1 x fun h => hx (hsub h),
      HasBoundedMetricLaplacianOn.mono (compl_subset_compl.mpr hsub) h2⟩

/-- **The "in particular" of source `thm:DNT23_C11bar`**, for every big class, given the joint
smoothing: `V_θ` (`sourceMinimalEnvelope`, `eq:Vtheta`) is real-valued on `X ∖ nK({θ})` and lies in
`C^{1,1̄}_ω(X ∖ nK({θ}))`. -/
theorem sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing
    (hJ : DN2.JointSmoothingStatement.{u}) (w : KahlerBackground N X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    (∀ x ∉ sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) := by
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hV : sourceMinimalEnvelope θ =
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun _ => ((0 : ℝ) : EReal)) := by
    rw [sourceMinimalEnvelope_eq_native, sourceObstacleEnvelope_eq_native]
    exact SGPT.Envelopes.DNTReg.thetaPshSupremum_eq_rooftopEnvelope_zero w _ hφ
  rw [hV]
  exact sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_jointSmoothing hJ w θ
    hbig (f := fun _ => 0) (hasBoundedMetricLaplacian_of_chartSmooth w fun _ => contDiffOn_const)

end Source

end SGPT.NPP.DN8
