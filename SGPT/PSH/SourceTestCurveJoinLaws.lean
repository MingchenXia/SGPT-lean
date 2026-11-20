import SGPT.PSH.SourceTestCurveJoinIGood
import SGPT.PSH.SourceTestCurveIntrinsicOrder

/-! # The original binary-join least upper bound, limit and algebra

Whole original cor:testcurvlorprop on the actual constructed join and intrinsic
order. Convex majorants and genuine ordinary-envelope/USC mothers manufacture
all conclusions; no desired output or limit certificate is supplied.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] in
/-- Genuine convexity of the whole negative trace gives the raw majorant law. -/
theorem sourceTestCurveRawConcaveMaximum_le_whole
    (Γ Δ Ξ : SourceTestCurvePredata θ)
    (hΓ : ∀ r, sourceTestCurveAt Γ r ≤ sourceTestCurveAt Ξ r)
    (hΔ : ∀ r, sourceTestCurveAt Δ r ≤ sourceTestCurveAt Ξ r)
    (τ : ℝ) : sourceTestCurveRawConcaveMaximum Γ Δ τ ≤ sourceTestCurveAt Ξ τ := by
  intro x
  have h : -sourceTestCurveAt Ξ τ x ≤ sourceTestCurveJoinConvexEnvelope Γ Δ x τ :=
    SGPT.Convex.le_lowerConvexEnvelope (Ξ.closedNegativeTrace_convex x)
      (fun r => EReal.neg_le_neg_iff.mpr (max_le (hΓ r x) (hΔ r x))) τ
  simpa only [sourceTestCurveRawConcaveMaximum, neg_neg] using
    EReal.neg_le_neg_iff.mpr h

/-- Original intrinsic lower comparison for the first input. -/
theorem SourceTestCurve.order_join_left (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) : SourceTestCurvePOrder Γ (Γ.join omega Δ) := by
  apply (sourceTestCurvePOrder_iff omega Γ (Γ.join omega Δ)).mpr
  exact ⟨le_max_left Γ.max Δ.max, fun _ hr => Γ.le_join_left omega Δ hr⟩

/-- Original intrinsic lower comparison for the second input. -/
theorem SourceTestCurve.order_join_right (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) : SourceTestCurvePOrder Δ (Γ.join omega Δ) := by
  apply (sourceTestCurvePOrder_iff omega Δ (Γ.join omega Δ)).mpr
  exact ⟨le_max_right Γ.max Δ.max, fun _ hr => Γ.le_join_right omega Δ hr⟩

/-- The actual original join lies below every genuine common upper test curve. -/
theorem SourceTestCurve.join_le (omega : KahlerBackground n M)
    (Γ Δ Ξ : SourceTestCurve θ)
    (hΓ : SourceTestCurvePOrder Γ Ξ) (hΔ : SourceTestCurvePOrder Δ Ξ) :
    SourceTestCurvePOrder (Γ.join omega Δ) Ξ := by
  have hc : max Γ.max Δ.max ≤ Ξ.max := max_le hΓ.cutoff_le hΔ.cutoff_le
  have hraw := sourceTestCurveRawConcaveMaximum_le_whole
    Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata Ξ.toSourceTestCurvePredata
    ((sourceTestCurvePOrder_iff_extension omega Γ Ξ).mp hΓ)
    ((sourceTestCurvePOrder_iff_extension omega Δ Ξ).mp hΔ)
  apply (sourceTestCurvePOrder_iff omega (Γ.join omega Δ) Ξ).mpr
  refine ⟨hc, fun τ hr => ?_⟩
  rw [SourceTestCurve.join_potential, ← Ξ.fixedPoint ⟨τ, hr.trans_le hc⟩]
  apply sourceOrdinaryEnvelope_mono
  apply MoreSingularOn.of_le
  intro x _
  simpa only [sourceTestCurveAt_of_lt Ξ.toSourceTestCurvePredata (hr.trans_le hc)] using
    hraw τ x

/-- Exact least-upper-bound reader, with the original intrinsic relation. -/
theorem SourceTestCurve.join_le_iff (omega : KahlerBackground n M)
    (Γ Δ Ξ : SourceTestCurve θ) :
    SourceTestCurvePOrder (Γ.join omega Δ) Ξ ↔
      SourceTestCurvePOrder Γ Ξ ∧ SourceTestCurvePOrder Δ Ξ := by
  constructor
  · intro h
    exact ⟨(Γ.order_join_left omega Δ).trans omega h,
      (Γ.order_join_right omega Δ).trans omega h⟩
  · rintro ⟨hΓ, hΔ⟩
    exact Γ.join_le omega Δ Ξ hΓ hΔ

/-- Literal equality of entire original curves, not only their singularity classes. -/
theorem SourceTestCurve.join_comm (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) : Γ.join omega Δ = Δ.join omega Γ := by
  apply SourceTestCurvePOrder.antisymm omega
  · exact Γ.join_le omega Δ _ (Δ.order_join_right omega Γ) (Δ.order_join_left omega Γ)
  · exact Δ.join_le omega Γ _ (Γ.order_join_right omega Δ) (Γ.order_join_left omega Δ)

/-- Associativity follows from the actual LUB and intrinsic transitivity. -/
theorem SourceTestCurve.join_assoc (omega : KahlerBackground n M)
    (Γ Δ Ξ : SourceTestCurve θ) :
    (Γ.join omega Δ).join omega Ξ = Γ.join omega (Δ.join omega Ξ) := by
  apply SourceTestCurvePOrder.antisymm omega
  · apply SourceTestCurve.join_le omega
    · apply SourceTestCurve.join_le omega
      · exact Γ.order_join_left omega _
      · exact (Δ.order_join_left omega Ξ).trans omega (Γ.order_join_right omega _)
    · exact (Δ.order_join_right omega Ξ).trans omega (Γ.order_join_right omega _)
  · apply SourceTestCurve.join_le omega
    · exact (Γ.order_join_left omega Δ).trans omega ((Γ.join omega Δ).order_join_left omega Ξ)
    · apply SourceTestCurve.join_le omega
      · exact (Γ.order_join_right omega Δ).trans omega ((Γ.join omega Δ).order_join_left omega Ξ)
      · exact (Γ.join omega Δ).order_join_right omega Ξ

/-- The same actual LUB gives literal idempotence. -/
theorem SourceTestCurve.join_self (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : Γ.join omega Γ = Γ := by
  exact SourceTestCurvePOrder.antisymm omega
    (Γ.join_le omega Γ Γ (.refl omega Γ) (.refl omega Γ))
    (Γ.order_join_left omega Γ)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- A constant EReal concave majorant retains both infinite values. -/
theorem sourceTestCurveRawConcaveMaximum_le_constant
    (Γ Δ : SourceTestCurvePredata θ) (u : M → EReal)
    (hΓ : ∀ r, sourceTestCurveAt Γ r ≤ u)
    (hΔ : ∀ r, sourceTestCurveAt Δ r ≤ u) (τ : ℝ) :
    sourceTestCurveRawConcaveMaximum Γ Δ τ ≤ u := by
  intro x
  have hg : SGPT.Convex.IsConvex (fun _ : ℝ => -u x) := by
    generalize -u x = c
    cases c using EReal.rec with
    | bot => exact SGPT.Convex.isConvex_bot
    | top => exact SGPT.Convex.isConvex_top
    | coe c => exact SGPT.Convex.isConvex_const c
  have h : -u x ≤ sourceTestCurveJoinConvexEnvelope Γ Δ x τ :=
    SGPT.Convex.le_lowerConvexEnvelope hg
      (fun r => EReal.neg_le_neg_iff.mpr (max_le (hΓ r x) (hΔ r x))) τ
  simpa only [sourceTestCurveRawConcaveMaximum, neg_neg] using
    EReal.neg_le_neg_iff.mpr h

/-- Intrinsic comparison orders the actual spatial USC-supremum limits. -/
theorem SourceTestCurvePOrder.limit_le (omega : KahlerBackground n M)
    {Γ Δ : SourceTestCurve θ} (h : SourceTestCurvePOrder Γ Δ) :
    sourceTestCurveLimit Γ.toSourceTestCurvePredata ≤
      sourceTestCurveLimit Δ.toSourceTestCurvePredata := by
  have hs := ((sourceTestCurvePOrder_iff omega Γ Δ).mp h).2
  apply uscRegularization_le
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp Δ.limit_thetaPSH).1.quasiPlurisubharmonic.upperSemicontinuous
  intro x
  apply iSup_le
  intro r
  exact (hs r.1 r.2 x).trans
    ((le_iSup (fun q => Δ.potential q x) ⟨r.1, r.2.trans_le h.cutoff_le⟩).trans
      (le_uscRegularization (fun y => ⨆ q, Δ.potential q y) x))

/-- The exact original negative-infinity limit of the actual binary join. -/
theorem SourceTestCurve.join_limit (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    sourceTestCurveLimit (Γ.join omega Δ).toSourceTestCurvePredata =
      sourceSingularityEnvelope θ (fun x => max
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata x)
        (sourceTestCurveLimit Δ.toSourceTestCurvePredata x)) := by
  let S := Γ.join omega Δ
  let U : M → EReal := fun x => max
    (sourceTestCurveLimit Γ.toSourceTestCurvePredata x)
    (sourceTestCurveLimit Δ.toSourceTestCurvePredata x)
  have hU : (ofFixedModel n M).IsThetaPSH θ U := Γ.limit_thetaPSH.max Δ.limit_thetaPSH
  have hP := sourceOrdinaryEnvelope_genuine hU
  have hraw : ∀ τ, sourceTestCurveRawConcaveMaximum
      Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ ≤ U :=
    sourceTestCurveRawConcaveMaximum_le_constant _ _ U
      (fun r x => (Γ.toSourceTestCurvePredata.at_le_limit r x).trans (le_max_left _ _))
      (fun r x => (Δ.toSourceTestCurvePredata.at_le_limit r x).trans (le_max_right _ _))
  have hupper : sourceTestCurveLimit S.toSourceTestCurvePredata ≤ sourceSingularityEnvelope θ U := by
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hP).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro r
    exact sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun y _ => hraw r.1 y) x
  have hUL : U ≤ sourceTestCurveLimit S.toSourceTestCurvePredata := by
    intro x
    exact max_le ((Γ.order_join_left omega Δ).limit_le omega x)
      ((Γ.order_join_right omega Δ).limit_le omega x)
  exact le_antisymm hupper ((sourceOrdinaryEnvelope_mono
    (MoreSingularOn.of_le fun x _ => hUL x)).trans_eq
      (S.limit_model omega).choose_spec.1.symm)

/-- WHOLE original cor:testcurvlorprop, including actual original union classes. -/
theorem source_test_curve_join_properties_whole (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    Γ.join omega Δ ∈ SourceTestCurvesPositive θ ∧
    sourceTestCurveLimit (Γ.join omega Δ).toSourceTestCurvePredata =
      sourceSingularityEnvelope θ (fun x => max
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata x)
        (sourceTestCurveLimit Δ.toSourceTestCurvePredata x)) ∧
    (Γ ∈ SourceIModelTestCurvesPositive θ → Δ ∈ SourceIModelTestCurvesPositive θ →
      Γ.join omega Δ ∈ SourceIModelTestCurvesPositive θ) ∧
    (∀ Ξ : SourceTestCurve θ, SourceTestCurvePOrder Γ Ξ → SourceTestCurvePOrder Δ Ξ →
      SourceTestCurvePOrder (Γ.join omega Δ) Ξ) ∧
    Γ.join omega Δ = Δ.join omega Γ ∧
    (∀ Ξ : SourceTestCurve θ, (Γ.join omega Δ).join omega Ξ = Γ.join omega (Δ.join omega Ξ)) := by
  exact ⟨Γ.join_mem_positive omega Δ, Γ.join_limit omega Δ,
    Γ.join_mem_iModelPositive omega Δ, Γ.join_le omega Δ,
    Γ.join_comm omega Δ, Γ.join_assoc omega Δ⟩

end SGPT.PSH.VariableComplexAtlas
