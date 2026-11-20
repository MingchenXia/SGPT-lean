import SGPT.PSH.SourceTestCurveSemipositiveProjection
import SGPT.PSH.SourceTestCurveEnergy
import SGPT.Envelopes.SourceRepresentativeChange
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-! # Original test-curve representative independence

Existing smooth compensation and actual mixed-measure invariance produce
positive ordinary model slices in an arbitrary equal Bott--Chern class.
One uniform compact gauge bound identifies the genuine spatial USC limits.
Canonical whole-curve equivalences restrict to the original based, bounded
and finite-energy sets and obey the literal cocycle law.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem tcRepresentative_shift_type (u : M → EReal) (g : M → ℝ)
    (B : ℝ) (hB : ∀ x, |g x| ≤ B) :
    SGPT.PSH.SingularityEquiv u (fun x ↦ u x - (g x : EReal)) := by
  refine ⟨⟨B, fun x _ ↦ ?_⟩, ⟨B, fun x _ ↦ ?_⟩⟩
  · have h := add_le_add (le_refl (u x - (g x : EReal)))
      (EReal.coe_le_coe_iff.mpr (abs_le.mp (hB x)).2)
    simpa only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      neg_add_cancel, EReal.coe_zero, add_zero] using h
  · change u x + -(g x : EReal) ≤ u x + (B : EReal)
    apply add_le_add le_rfl
    rw [← EReal.coe_neg]
    exact EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hB x)).1])

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem tcRepresentative_envelope_shift (u : M → EReal) (g : M → ℝ)
    (B : ℝ) (hB : ∀ x, |g x| ≤ B) :
    sourceSingularityEnvelope η u =
      sourceSingularityEnvelope η (fun x ↦ u x - (g x : EReal)) := by
  have ht := tcRepresentative_shift_type u g B hB
  exact le_antisymm (sourceOrdinaryEnvelope_mono ht.1) (sourceOrdinaryEnvelope_mono ht.2)

private theorem tcRepresentative_model (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {u : M → EReal} (hu : SourceModelPotential θ u) :
    ∃ hP : SourceModelPotential η (sourceSingularityEnvelope η u),
      SGPT.PSH.SingularityEquiv u (sourceSingularityEnvelope η u) ∧
      sourcePotentialNonPluripolarMeasure η (sourceSingularityEnvelope η u)
        hP.thetaPSH univ = sourcePotentialNonPluripolarMeasure θ u hu.thetaPSH univ := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hc
  have hs := sourceThetaPSH_sub_smooth
    ((sourceSmoothBackgroundChange_iff_native θ η g).mpr ⟨hg, hθη⟩) hu.thetaPSH
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hb : ∀ x, |g x| ≤ B := fun x ↦ by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  have he := tcRepresentative_envelope_shift (η := η) u g B hb
  have hm : sourcePotentialNonPluripolarMeasure η (fun x ↦ u x - (g x : EReal)) hs univ =
      sourcePotentialNonPluripolarMeasure θ u hu.thetaPSH univ := by
    have hh := congrArg (fun μ : Measure M ↦ μ univ)
      (GlobalMeasureInvariance.globalMixedMeasure_changeRepresentative
        (θ := fun _ : Fin n ↦ atlasClosedFormToNative θ)
        (η := fun _ : Fin n ↦ atlasClosedFormToNative η)
        (u := fun _ ↦ u) (f := fun _ ↦ g)
        (fun _ ↦ hg) (fun _ ↦ hθη)
        (fun _ ↦ ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.thetaPSH).1))
    exact hh
  have hp := sourceOrdinaryEnvelope_model ω hs (hm ▸ hu.choose_spec.2)
  have ht := (sourceOrdinaryEnvelope_changeRepresentative hg hθη hu.thetaPSH).2
  rw [hu.choose_spec.1.symm] at ht
  refine ⟨he.symm ▸ hp, he.symm ▸ ht, ?_⟩
  simpa only [he] using (sourceOrdinaryEnvelope_diagonalMass_eq ω hs).trans hm

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem tcRepresentative_uniform
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    ∃ C : ℝ, ∀ u : M → EReal,
      sourceSingularityEnvelope θ u ≤ (fun x ↦ sourceSingularityEnvelope η u x + (C : EReal)) ∧
      sourceSingularityEnvelope η u ≤ (fun x ↦ sourceSingularityEnvelope θ u x + (C : EReal)) := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hb : ∀ x, |g x| ≤ B := fun x ↦ by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  have hneg : ChartSmooth (n := n) (fun x ↦ -g x) := fun e ↦ (hg e).neg
  have hηθ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (atlasClosedFormToNative θ).val.coeff e z =
        (atlasClosedFormToNative η).val.coeff e z + smoothDDC (fun y ↦ -g (e.val.symm y)) z := by
    intro e z hz
    rw [smoothDDC_neg e.val.open_target (hg e) hz, hθη e z hz, add_neg_cancel_right]
  refine ⟨2 * B, fun u ↦ ?_⟩
  have he := tcRepresentative_envelope_shift (η := η) u g B hb
  have hf := sourceOrdinaryEnvelope_changeRepresentative_le hg hθη B hb u
  rw [← he] at hf
  have hr := sourceOrdinaryEnvelope_changeRepresentative_le hneg hηθ B
    (fun x ↦ by simpa only [abs_neg] using hb x) (fun x ↦ u x - (g x : EReal))
  have hcancel : (fun x ↦ u x - (g x : EReal) - ((-g x : ℝ) : EReal)) = u := by
    funext x
    simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      neg_neg, neg_add_cancel, EReal.coe_zero, add_zero]
  rw [hcancel, ← he] at hr
  exact ⟨hf, hr⟩

omit [BorelSpace M] in
private theorem tcRepresentative_concave
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace Γ.max
      (fun r ↦ sourceSingularityEnvelope η (Γ.potential r)) x) := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hc
  have hs r := sourceThetaPSH_sub_smooth
    ((sourceSmoothBackgroundChange_iff_native θ η g).mpr ⟨hg, hθη⟩) (Γ.thetaPSH r)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hb : ∀ y, |g y| ≤ B := fun y ↦ by
    simpa only [Real.norm_eq_abs] using hB y (mem_univ y)
  have he r := tcRepresentative_envelope_shift (η := η) (Γ.potential r) g B hb
  apply sourceTestCurveNegativeTrace_convex_of_chords
  intro a b t ht0 ht1 y
  simp only [he]
  apply (sourceOrdinaryEnvelope_convexComb_le (hs a) (hs b) ht0 ht1 y).trans
  apply sourceOrdinaryEnvelope_mono
  apply MoreSingularOn.of_le
  intro z _
  have hcoeff : t * (-g z) + (1 - t) * (-g z) = -g z := by ring
  have hh := congrFun (POrderAffineRooftop.convexComb_add_const ht0 ht1
    (Γ.potential a) (Γ.potential b) (-g z) (-g z)) z
  rw [hcoeff] at hh
  have hshift : convexComb t (fun w ↦ Γ.potential a w - (g w : EReal))
      (fun w ↦ Γ.potential b w - (g w : EReal)) z =
      convexComb t (Γ.potential a) (Γ.potential b) z - (g z : EReal) := by
    simpa only [sub_eq_add_neg, EReal.coe_neg, convexComb] using hh
  rw [hshift]
  exact EReal.sub_le_sub (Γ.toSourceTestCurvePredata.convexComb_le a b ht0 ht1 z) le_rfl

/-- Canonical compensated transport uses the original cutoff and actual
ordinary envelopes of the original slices. No gauge occurs in its data. -/
def SourceTestCurve.changeRepresentativePredata (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) : SourceTestCurvePredata η where
  max := Γ.max
  potential r := sourceSingularityEnvelope η (Γ.potential r)
  thetaPSH r := (tcRepresentative_model ω hc (Γ.slice_model ω r)).choose.thetaPSH
  antitone x _a _b hab := sourceOrdinaryEnvelope_mono
    (MoreSingularOn.of_le fun y _ ↦ Γ.antitone y hab) x
  concave := tcRepresentative_concave hc Γ
  fixedPoint r := (tcRepresentative_model ω hc (Γ.slice_model ω r)).choose.choose_spec.1.symm

/-- Actual original positive output is manufactured from the existing
increasing-supremum mass producer, before any based-limit assertion. -/
def SourceTestCurve.changeRepresentative (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) : SourceTestCurve η where
  toSourceTestCurvePredata := Γ.changeRepresentativePredata ω hc
  positiveLimitMass := by
    have : Nonempty (Iio Γ.max) :=
      ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
    have hp := sourceIncreasingOrdinary_sup_positive ω
      (fun r : Iio Γ.max ↦ (tcRepresentative_model ω hc (Γ.slice_model ω r)).choose.thetaPSH)
      (fun r ↦ (tcRepresentative_model ω hc (Γ.slice_model ω r)).choose.choose_spec.2)
      (C := 0) (fun r y ↦ by
        simpa only [EReal.coe_zero, Pi.zero_apply] using sourceSingularityEnvelope_le_zero η _ y)
    have hU : (⨆ r : Iio Γ.max, sourceSingularityEnvelope η (Γ.potential r)) =
        fun y ↦ ⨆ r : Iio Γ.max, sourceSingularityEnvelope η (Γ.potential r) y := by
      funext y
      exact iSup_apply
    change 0 < sourcePotentialNonPluripolarMeasure η
      (uscRegularization (fun y ↦ ⨆ r : Iio Γ.max, sourceSingularityEnvelope η (Γ.potential r) y)) _ univ
    simpa only [hU] using hp

/-- The same literal cutoff is retained. -/
theorem SourceTestCurve.changeRepresentative_max (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    (Γ.changeRepresentative ω hc).max = Γ.max := rfl

/-- The data are ordinary envelopes of the SAME original strict slices. -/
theorem SourceTestCurve.changeRepresentative_potential (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    (Γ.changeRepresentative ω hc).potential r =
      sourceSingularityEnvelope η (Γ.potential r) := rfl

private theorem tcRepresentative_envelope_comp (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {u : M → EReal} (hu : SourceModelPotential θ u) :
    sourceSingularityEnvelope ζ (sourceSingularityEnvelope η u) = sourceSingularityEnvelope ζ u := by
  have ht := (tcRepresentative_model ω hc hu).choose_spec.1
  exact le_antisymm (sourceOrdinaryEnvelope_mono (θ := ζ) ht.2)
    (sourceOrdinaryEnvelope_mono (θ := ζ) ht.1)

/-- Actual same-type slices give exact composition, for arbitrary triples
of backgrounds with equal original Bott--Chern classes. -/
theorem SourceTestCurve.changeRepresentative_comp (ω : KahlerBackground n M)
    (hθη : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hηζ : RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative ζ)) (Γ : SourceTestCurve θ) :
    (Γ.changeRepresentative ω hθη).changeRepresentative ω hηζ =
      Γ.changeRepresentative ω (hθη.trans hηζ) := by
  apply SourceTestCurve.ext_of_max_potential _ _
  · exact ((Γ.changeRepresentative ω hθη).changeRepresentative_max ω hηζ).trans
      ((Γ.changeRepresentative_max ω hθη).trans
        (Γ.changeRepresentative_max ω (hθη.trans hηζ)).symm)
  · intro r hr hr'
    have hr0 : r < Γ.max := hr
    calc
      _ = sourceSingularityEnvelope ζ
          ((Γ.changeRepresentative ω hθη).potential ⟨r, hr⟩) :=
        (Γ.changeRepresentative ω hθη).changeRepresentative_potential ω hηζ _
      _ = sourceSingularityEnvelope ζ (sourceSingularityEnvelope η (Γ.potential ⟨r, hr0⟩)) :=
        congrArg (sourceSingularityEnvelope ζ) (Γ.changeRepresentative_potential ω hθη _)
      _ = sourceSingularityEnvelope ζ (Γ.potential ⟨r, hr0⟩) :=
        tcRepresentative_envelope_comp ω hθη (Γ.slice_model ω ⟨r, hr0⟩)
      _ = _ := (Γ.changeRepresentative_potential ω (hθη.trans hηζ) _).symm

/-- The unchanged background gives the same entire original curve. -/
theorem SourceTestCurve.changeRepresentative_self (ω : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : Γ.changeRepresentative ω rfl = Γ := by
  apply SourceTestCurve.ext_of_max_potential _ _
  · rfl
  · intro r hr hr'
    exact Γ.fixedPoint ⟨r, hr⟩

/-- Exact actual whole-curve equivalence, with reverse transport as its
proved inverse. This is an equivalence of the original curve objects. -/
def sourceTestCurveRepresentativeEquiv (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    SourceTestCurve θ ≃ SourceTestCurve η where
  toFun Γ := Γ.changeRepresentative ω hc
  invFun Δ := Δ.changeRepresentative ω hc.symm
  left_inv Γ := (Γ.changeRepresentative_comp ω hc hc.symm).trans (Γ.changeRepresentative_self ω)
  right_inv Δ := (Δ.changeRepresentative_comp ω hc.symm hc).trans (Δ.changeRepresentative_self ω)

/-- Exact cocycle as equality of the actual canonical equivalences. -/
theorem sourceTestCurveRepresentativeEquiv_trans (ω : KahlerBackground n M)
    (hθη : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hηζ : RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative ζ)) :
    (sourceTestCurveRepresentativeEquiv ω hθη).trans (sourceTestCurveRepresentativeEquiv ω hηζ) =
      sourceTestCurveRepresentativeEquiv ω (hθη.trans hηζ) := by
  apply Equiv.ext
  intro Γ
  exact Γ.changeRepresentative_comp ω hθη hηζ

/-- The original spatial USC limit is retained. Uniform compact gauge
bounds compare BOTH actual limits before model fixedness identifies them. -/
theorem SourceTestCurve.changeRepresentative_limit (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    sourceTestCurveLimit (Γ.changeRepresentative ω hc).toSourceTestCurvePredata =
      sourceSingularityEnvelope η (sourceTestCurveLimit Γ.toSourceTestCurvePredata) := by
  obtain ⟨C, hC⟩ := tcRepresentative_uniform hc
  let A : M → EReal := fun x ↦ ⨆ r : Iio Γ.max, Γ.potential r x
  let B : M → EReal := fun x ↦ ⨆ r : Iio Γ.max, sourceSingularityEnvelope η (Γ.potential r) x
  have hAB : A ≤ fun x ↦ B x + (C : EReal) := by
    intro x
    apply iSup_le
    intro r
    have hh := (hC (Γ.potential r)).1 x
    rw [Γ.fixedPoint r] at hh
    exact hh.trans (add_le_add (le_iSup (fun s : Iio Γ.max ↦
      sourceSingularityEnvelope η (Γ.potential s) x) r) le_rfl)
  have hBA : B ≤ fun x ↦ A x + (C : EReal) := by
    intro x
    apply iSup_le
    intro r
    have hh := (hC (Γ.potential r)).2 x
    rw [Γ.fixedPoint r] at hh
    exact hh.trans (add_le_add (le_iSup (fun s : Iio Γ.max ↦ Γ.potential s x) r) le_rfl)
  have hregAB := uscRegularization_mono hAB
  have hregBA := uscRegularization_mono hBA
  rw [uscRegularization_add_coe_const] at hregAB hregBA
  have ht : SGPT.PSH.SingularityEquiv (uscRegularization A) (uscRegularization B) :=
    ⟨⟨C, fun x _ ↦ hregAB x⟩, ⟨C, fun x _ ↦ hregBA x⟩⟩
  have he : sourceSingularityEnvelope η (uscRegularization A) =
      sourceSingularityEnvelope η (uscRegularization B) :=
    le_antisymm (sourceOrdinaryEnvelope_mono ht.1) (sourceOrdinaryEnvelope_mono ht.2)
  have hfix := (Γ.changeRepresentative ω hc).limit_model ω
  exact hfix.choose_spec.1.trans he.symm

/-- Every possible smooth gauge gives the exact printed slice formula;
the canonical data contain no chosen gauge. -/
theorem SourceTestCurve.changeRepresentative_potential_sub_smooth (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {g : M → ℝ} (hg : SourceSmoothBackgroundChange θ η g)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    (Γ.changeRepresentative ω hc).potential r =
      sourceSingularityEnvelope η (fun x ↦ Γ.potential r x - (g x : EReal)) := by
  have hs := ((sourceSmoothBackgroundChange_iff_native θ η g).mp hg).1
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hs).continuousOn
  exact tcRepresentative_envelope_shift (Γ.potential r) g B (fun x ↦ by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x))

/-- Each actual transported strict-slice mass equals its original mass;
no real readback or assumed integrability is used. -/
theorem SourceTestCurve.changeRepresentative_mass (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    sourcePotentialNonPluripolarMeasure η ((Γ.changeRepresentative ω hc).potential r)
      ((Γ.changeRepresentative ω hc).thetaPSH r) univ =
      sourcePotentialNonPluripolarMeasure θ (Γ.potential r) (Γ.thetaPSH r) univ :=
  (tcRepresentative_model ω hc (Γ.slice_model ω r)).choose_spec.2

/-- The genuine original real mass function is unchanged at ALL original
parameters, including the auxiliary zero branch outside the domain. -/
theorem SourceTestCurve.changeRepresentative_realMass (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    sourceTestCurveRealMassAt ω (Γ.changeRepresentative ω hc) = sourceTestCurveRealMassAt ω Γ := by
  funext r
  by_cases hr : r < Γ.max
  · exact (sourceTestCurveRealMassAt_of_lt ω (Γ.changeRepresentative ω hc) hr).trans
      ((congrArg ENNReal.toReal (Γ.changeRepresentative_mass ω hc ⟨r, hr⟩)).trans
        (sourceTestCurveRealMassAt_of_lt ω Γ hr).symm)
  · have hr' : ¬ r < (Γ.changeRepresentative ω hc).max := hr
    simp [sourceTestCurveRealMassAt, hr', hr]

section BasedClasses
variable {φ φ' : M → EReal}
  (hφ : SourceModelPotential θ φ) (hφ' : SourceModelPotential η φ')
  (hφφ' : SGPT.PSH.SingularityEquiv φ φ')

include hφ' hφφ'

omit [BorelSpace M] [ConnectedSpace M] in
private theorem tcRepresentative_base_envelope : sourceSingularityEnvelope η φ = φ' := by
  exact (le_antisymm (sourceOrdinaryEnvelope_mono hφφ'.1)
    (sourceOrdinaryEnvelope_mono hφφ'.2)).trans hφ'.choose_spec.1.symm

/-- Literal equality of the original based limit is preserved. -/
theorem SourceTestCurve.changeRepresentative_based (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (hb : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    Γ.changeRepresentative ω hc ∈ SourceTestCurvesBased η φ' hφ' := by
  change sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ at hb
  change sourceTestCurveLimit (Γ.changeRepresentative ω hc).toSourceTestCurvePredata = φ'
  exact (Γ.changeRepresentative_limit ω hc).trans
    ((congrArg (sourceSingularityEnvelope η) hb).trans (tcRepresentative_base_envelope hφ' hφφ'))

/-- The inverse whole-curve transport reflects the actual based class. -/
theorem SourceTestCurve.changeRepresentative_based_iff (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    Γ.changeRepresentative ω hc ∈ SourceTestCurvesBased η φ' hφ' ↔
      Γ ∈ SourceTestCurvesBased θ φ hφ := by
  constructor
  · intro hb
    have hh := (Γ.changeRepresentative ω hc).changeRepresentative_based hφ' hφ
      (SGPT.PSH.singularityEquiv_symm hφφ') ω hc.symm hb
    have hi := (sourceTestCurveRepresentativeEquiv ω hc).symm_apply_apply Γ
    exact hi ▸ hh
  · exact Γ.changeRepresentative_based hφ hφ' hφφ' ω hc

/-- Base mass equality is produced from the actual model transport and
literal uniqueness in the original target singularity type. -/
theorem sourceTestCurveRepresentative_base_mass (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    sourcePotentialNonPluripolarMeasure η φ' hφ'.thetaPSH univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ := by
  have he := tcRepresentative_base_envelope hφ' hφφ'
  simpa only [he] using (tcRepresentative_model ω hc hφ).choose_spec.2

/-- The entire extended energy is exactly preserved, including bottom;
every actual mass, cutoff and integral input is identified first. -/
theorem SourceTestCurve.changeRepresentative_energy (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (hb : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceTestCurveEnergy ω hφ' (Γ.changeRepresentative ω hc)
        (Γ.changeRepresentative_based hφ hφ' hφφ' ω hc hb) =
      sourceTestCurveEnergy ω hφ Γ hb := by
  unfold sourceTestCurveEnergy
  rw [sourceTestCurveRepresentative_base_mass hφ hφ' hφφ' ω hc,
    Γ.changeRepresentative_realMass ω hc]
  rfl

/-- Equality of the full extended energies preserves and reflects exactly
the original finite-energy class; basedness is produced in both directions. -/
theorem SourceTestCurve.changeRepresentative_finiteEnergy_iff (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    Γ.changeRepresentative ω hc ∈ SourceFiniteEnergyTestCurves ω η φ' hφ' ↔
      Γ ∈ SourceFiniteEnergyTestCurves ω θ φ hφ := by
  constructor
  · rintro ⟨hb, he⟩
    have hbo := (Γ.changeRepresentative_based_iff hφ hφ' hφφ' ω hc).mp hb
    refine ⟨hbo, ?_⟩
    exact (Γ.changeRepresentative_energy hφ hφ' hφφ' ω hc hbo) ▸ he
  · rintro ⟨hb, he⟩
    refine ⟨Γ.changeRepresentative_based hφ hφ' hφφ' ω hc hb, ?_⟩
    exact (Γ.changeRepresentative_energy hφ hφ' hφφ' ω hc hb).symm ▸ he

/-- Literal eventual equality of all original strict slices is preserved;
the function-valued base is identified by its ordinary fixedpoint. -/
theorem SourceTestCurve.changeRepresentative_bounded (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (hb : SourceTestCurveIsBounded φ Γ) :
    SourceTestCurveIsBounded φ' (Γ.changeRepresentative ω hc) := by
  filter_upwards [hb] with r hr
  exact (Γ.changeRepresentative_potential ω hc r).trans
    ((congrArg (sourceSingularityEnvelope η) hr).trans (tcRepresentative_base_envelope hφ' hφφ'))

include hφ in
/-- Reverse canonical transport reflects original eventual literal boundedness. -/
theorem SourceTestCurve.changeRepresentative_bounded_iff (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    SourceTestCurveIsBounded φ' (Γ.changeRepresentative ω hc) ↔ SourceTestCurveIsBounded φ Γ := by
  constructor
  · intro hb
    have hh := (Γ.changeRepresentative ω hc).changeRepresentative_bounded hφ
      (SGPT.PSH.singularityEquiv_symm hφφ') ω hc.symm hb
    exact (sourceTestCurveRepresentativeEquiv ω hc).symm_apply_apply Γ ▸ hh
  · exact Γ.changeRepresentative_bounded hφ' hφφ' ω hc

/-- The actual bounded collection retains the literal original based clause. -/
theorem SourceTestCurve.changeRepresentative_mem_bounded_iff (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    Γ.changeRepresentative ω hc ∈ SourceBoundedTestCurves η φ' hφ' ↔
      Γ ∈ SourceBoundedTestCurves θ φ hφ := by
  exact and_congr (Γ.changeRepresentative_based_iff hφ hφ' hφφ' ω hc)
    (Γ.changeRepresentative_bounded_iff hφ hφ' hφφ' ω hc)

/-- WHOLE original prop:testcurveindeptheta: the canonical bijection on
actual based curves, both original restricted classes, and its cocycle. -/
theorem source_test_curve_representative_independence_whole (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    BijOn (sourceTestCurveRepresentativeEquiv ω hc)
        (SourceTestCurvesBased θ φ hφ) (SourceTestCurvesBased η φ' hφ') ∧
      BijOn (sourceTestCurveRepresentativeEquiv ω hc)
        (SourceFiniteEnergyTestCurves ω θ φ hφ) (SourceFiniteEnergyTestCurves ω η φ' hφ') ∧
      BijOn (sourceTestCurveRepresentativeEquiv ω hc)
        (SourceBoundedTestCurves θ φ hφ) (SourceBoundedTestCurves η φ' hφ') ∧
      (∀ (ξ : AtlasClosedRealOneOneForm (ofFixedModel n M))
        (hηξ : RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
          RealBottChern.ofRepresentative (atlasClosedFormToNative ξ)),
        (sourceTestCurveRepresentativeEquiv ω hc).trans (sourceTestCurveRepresentativeEquiv ω hηξ) =
          sourceTestCurveRepresentativeEquiv ω (hc.trans hηξ)) := by
  refine ⟨(sourceTestCurveRepresentativeEquiv ω hc).bijOn (fun Γ ↦ ?_),
    (sourceTestCurveRepresentativeEquiv ω hc).bijOn (fun Γ ↦ ?_),
    (sourceTestCurveRepresentativeEquiv ω hc).bijOn (fun Γ ↦ ?_), ?_⟩
  · exact Γ.changeRepresentative_based_iff hφ hφ' hφφ' ω hc
  · exact Γ.changeRepresentative_finiteEnergy_iff hφ hφ' hφφ' ω hc
  · exact Γ.changeRepresentative_mem_bounded_iff hφ hφ' hφφ' ω hc
  · intro ξ hηξ
    exact sourceTestCurveRepresentativeEquiv_trans ω hc hηξ

end BasedClasses


end SGPT.PSH.VariableComplexAtlas
