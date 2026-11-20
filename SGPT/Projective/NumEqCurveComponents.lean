import SGPT.Projective.NumEqCurves
import SGPT.Foundations.Analysis.Pending.OpensRestriction
import SGPT.Foundations.Analysis.Pending.FormPullbackCompMixed

/-! Numerical triviality on actual connected test curves also annihilates
actual compact disconnected curves, by gluing actual component potentials. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Foundations.Analysis.Pending.OpensRestriction
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

section LocalSmooth
variable {n : ℕ} {C : Type} [TopologicalSpace C]
  [ChartedSpace (ComplexModel n) C] [IsComplexManifold n C]

/-- Smooth functions on genuine open submanifolds glue locally as actual
chart-smooth real functions on the original manifold. -/
private theorem chartSmooth_of_local_opens (f : C → ℝ)
    (h : ∀ x, ∃ (U : Opens C) (_hx : x ∈ U) (F : U → ℝ),
      ChartSmooth (n := n) F ∧ ∀ y : U, f y = F y) : ChartSmooth (n := n) f := by
  intro c z hz
  let x := c.val.symm z
  obtain ⟨U, hx, F, hF, heq⟩ := h x
  let y : U := ⟨x, hx⟩
  let d := complexChartAt (n := n) y
  let e := complexChartAt (n := n) x
  let v := coordinateMap (id : C → C) c e
  have hdom : z ∈ coordinateDomain (id : C → C) c e :=
    ⟨hz, mem_complexChartAt_source x⟩
  have hv : v z = d.val y := rfl
  have hvd : v z ∈ d.val.target := hv ▸ d.val.map_source (mem_complexChartAt_source y)
  have hs := ((hF d).contDiffAt (d.val.open_target.mem_nhds hvd)).comp z
    (coordinateMap_contDiffAt_real contMDiff_id c e hdom)
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  have hvnhds := (coordinateMap_contDiffAt_real contMDiff_id c e hdom).continuousAt
    |>.preimage_mem_nhds (d.val.open_target.mem_nhds hvd)
  filter_upwards [(coordinateDomain_isOpen contMDiff_id c e).mem_nhds hdom, hvnhds] with w hw hwv
  have hsym : (d.val.symm (v w) : C) = c.val.symm w := by
    rw [val_complexChartAt_opens_symm y hwv]
    exact e.val.left_inv hw.2
  exact ((heq (d.val.symm (v w))).symm.trans (congrArg f hsym)).symm

/-- A compatible original form is determined by its actual preferred-chart
value at each point. Off-target coefficient extensions are irrelevant. -/
private theorem geometricallyEq_of_preferred {k : ℕ} (a b : SmoothRealForm n C k)
    (h : ∀ x, a.coeff (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val x) =
      b.coeff (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val x)) :
    a.GeometricallyEq b := by
  intro c z hz
  let x := c.val.symm z
  let e := complexChartAt (n := n) x
  have hdom : z ∈ (chartTransition c e).source := ⟨hz, mem_complexChartAt_source x⟩
  ext v
  rw [a.compatible c e z hdom v, b.compatible c e z hdom v]
  exact congrArg (fun T : (ComplexModel n) [⋀^Fin k]→L[ℝ] ℝ => T (fun i => chartTransitionDerivative c e z (v i))) (h x)

end LocalSmooth


section ComponentPotentials
variable {n : ℕ} {C : Type} [TopologicalSpace C] [LocallyConnectedSpace C]
  [ChartedSpace (ComplexModel n) C] [IsComplexManifold n C]

private theorem ofRepresentative_eq_zero_of_component_restrictions
    (alpha : ClosedRealOneOneForm n C)
    (h : ∀ p : C, RealBottChern.ofRepresentative
      (restrictForm (⟨connectedComponent p, isOpen_connectedComponent⟩ : Opens C) alpha) = 0) :
    RealBottChern.ofRepresentative alpha = 0 := by
  classical
  let anchor : ConnectedComponents C → C := Quotient.out
  have hanchor (c : ConnectedComponents C) : ConnectedComponents.mk (anchor c) = c :=
    Quotient.out_eq c
  let U (c : ConnectedComponents C) : Opens C :=
    ⟨connectedComponent (anchor c), isOpen_connectedComponent⟩
  have hx (x : C) : x ∈ U (ConnectedComponents.mk x) :=
    ConnectedComponents.coe_eq_coe'.mp (hanchor (ConnectedComponents.mk x)).symm
  have hpot : ∀ c, ∃ F : U c → ℝ, ChartSmooth (n := n) F ∧
      ∀ (d : ComplexChart n (U c)) (z : ComplexModel n), z ∈ d.val.target →
        (restrictForm (U c) alpha).val.coeff d z =
          smoothDDC (fun w => F (d.val.symm w)) z := by
    intro c
    have hrel : ClosedRealOneOneForm.BottChernRel 0 (restrictForm (U c) alpha) :=
      (RealBottChern.ofRepresentative_eq_iff _ _).mp (by
        rw [RealBottChern.ofRepresentative_zero]
        exact (h (anchor c)).symm)
    obtain ⟨F, hF, hcoef⟩ := hrel
    exact ⟨F, hF, fun d z hz => by simpa only [ClosedRealOneOneForm.coeff_zero, zero_add] using hcoef d z hz⟩
  choose F hF hcoef using hpot
  let ext : ConnectedComponents C → C → ℝ := fun c x =>
    if hx : x ∈ U c then F c ⟨x, hx⟩ else 0
  let f : C → ℝ := fun x => ext (ConnectedComponents.mk x) x
  have hglue (c : ConnectedComponents C) (y : U c) : f y = F c y := by
    have he : ConnectedComponents.mk (y : C) = c :=
      (ConnectedComponents.coe_eq_coe'.mpr y.property).trans (hanchor c)
    change ext (ConnectedComponents.mk (y : C)) y = F c y
    rw [he]
    exact dif_pos y.property
  have hf : ChartSmooth (n := n) f := chartSmooth_of_local_opens f (fun x =>
    ⟨U (ConnectedComponents.mk x), hx x, F (ConnectedComponents.mk x),
      hF (ConnectedComponents.mk x), hglue (ConnectedComponents.mk x)⟩)
  let beta := ManifoldTubePositivity.ddcClosedForm f hf
  have hgeo : alpha.val.GeometricallyEq beta.val := by
    apply geometricallyEq_of_preferred
    intro x
    let c := ConnectedComponents.mk x
    let y : U c := ⟨x, hx x⟩
    let d := complexChartAt (n := n) y
    let e := complexChartAt (n := n) x
    let z := e.val x
    have hzd : z ∈ d.val.target := d.val.map_source (mem_complexChartAt_source y)
    have hevent : (fun w => f (e.val.symm w)) =ᶠ[𝓝 z]
        fun w => F c (d.val.symm w) := by
      filter_upwards [d.val.open_target.mem_nhds hzd] with w hw
      rw [← val_complexChartAt_opens_symm y hw]
      exact hglue c (d.val.symm w)
    have hc := hcoef c d z hzd
    rw [restrictForm_coeff_chartAt alpha y hzd] at hc
    change alpha.val.coeff e z = beta.val.coeff e z
    rw [ManifoldTubePositivity.ddcClosedForm_coeff, smoothDDC_congr hevent]
    exact hc
  have hrel : ClosedRealOneOneForm.BottChernRel 0 alpha := by
    refine ⟨f, hf, fun e z hz => ?_⟩
    rw [ClosedRealOneOneForm.coeff_zero, zero_add, ← ManifoldTubePositivity.ddcClosedForm_coeff f hf]
    exact hgeo e hz
  have heq := (RealBottChern.ofRepresentative_eq_iff _ _).mpr hrel
  rw [RealBottChern.ofRepresentative_zero] at heq
  exact heq.symm

end ComponentPotentials


section CompactCurve
variable {n : ℕ} {X C : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C]
  [CompactSpace C]

/-- Every actual compact curve pulls an original numerically trivial form
back to the zero ORIGINAL Bott--Chern class, including disconnected curves.
Actual potentials are produced on its components and genuinely glued. -/
theorem ofRepresentative_pullback_eq_zero_of_isNumericallyTrivial_compactCurve
    (theta : ClosedRealOneOneForm n X) (hnum : IsNumericallyTrivial theta)
    (κ : KahlerBackground 1 C) {g : C → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g) :
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg theta) = 0 := by
  let : LocallyConnectedSpace C := ChartedSpace.locallyConnectedSpace (ComplexModel 1) C
  apply ofRepresentative_eq_zero_of_component_restrictions
  intro p
  let U : Opens C := ⟨connectedComponent p, isOpen_connectedComponent⟩
  let : CompactSpace U := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let κU := restrictKahler U κ
  have hdeg := hnum U κU (g ∘ Subtype.val) (hg.comp (contMDiff_val U))
  change slotIntegral κU (fun _ => ClosedRealOneOneForm.pullback
    (hg.comp (contMDiff_val U)) theta) = 0 at hdeg
  have hgeo := FormPullbackCompMixed.pullback_comp_geometricallyEq hg (contMDiff_val U) theta.val
  have hrel : ClosedRealOneOneForm.BottChernRel
      (ClosedRealOneOneForm.pullback (hg.comp (contMDiff_val U)) theta)
      (restrictForm U (ClosedRealOneOneForm.pullback hg theta)) :=
    ClosedRealOneOneForm.bottChernRel_of_geometricallyEq hgeo
  exact ofRepresentative_eq_zero_of_slotIntegral_eq_zero_dim_one κU _
    ((slotIntegral_eq_of_bottChernRel κU _ _ (fun _ => hrel)).symm.trans hdeg)

/-- Numerical triviality, as originally defined using connected test
curves, annihilates the degree of every actual compact Kähler curve.
No component-degree splitting or curve-intersection certificate is an input. -/
theorem degreeAlong_eq_zero_of_isNumericallyTrivial_compactCurve
    (theta : ClosedRealOneOneForm n X) (hnum : IsNumericallyTrivial theta)
    (κ : KahlerBackground 1 C) {g : C → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g) :
    degreeAlong κ hg theta = 0 := by
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  have h0 := ofRepresentative_pullback_eq_zero_of_isNumericallyTrivial_compactCurve theta hnum κ hg
  have hrel : ClosedRealOneOneForm.BottChernRel (ClosedRealOneOneForm.pullback hg theta) 0 :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mp (by
      rw [RealBottChern.ofRepresentative_zero]
      exact h0)
  change slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg theta) = 0
  exact (slotIntegral_eq_of_bottChernRel κ _ _ (fun _ => hrel)).trans (by
    rw [fun_eq_update_dim_one κ 0, slotIntegral_update_zero])

end CompactCurve

end SGPT.Projective.NumEq
