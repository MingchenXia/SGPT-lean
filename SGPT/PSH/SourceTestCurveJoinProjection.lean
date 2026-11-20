import SGPT.PSH.SourceTestCurveJoinIGood
import SGPT.PSH.SourceTestCurveSemipositiveProjection
import SGPT.PSH.SourceNAPositiveScaling
import SGPT.PSH.SourceGlobalOrderAddition
import SGPT.PSH.SourceGlobalOrderSupremum

/-! # Original binary-join compatibility with positive background projection

A stronger arbitrary-semipositive theorem is proved first using actual global
mixture indices, existing P-type operation mothers and genuinely positive target
masses. The exact original positive-background construction is recovered as
an equality of entire original curves. No output compatibility is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open ThetaPshConvexCombination
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual global mixture index is unchanged by original projection. -/
def sourceTestCurveJoinMixtureIndex_projectionEquiv
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ Δ : SourceTestCurve θ) (τ : ℝ) :
    SourceTestCurveJoinMixtureIndex Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ ≃
      SourceTestCurveJoinMixtureIndex
        (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata
        (Δ.semipositiveProjection omega η hη).toSourceTestCurvePredata τ where
  toFun j := ⟨j.left, j.right, j.weight, j.barycenter⟩
  invFun j := ⟨j.left, j.right, j.weight, j.barycenter⟩
  left_inv j := by cases j; rfl
  right_inv j := by cases j; rfl

/-- A genuine original strict slice has the global P-type of its actual projection. -/
theorem sourceTestCurveStrictSlice_semipositive_sourcePEquivalent
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    GlobalPComparison.sourcePEquivalent (n := n) (Γ.potential r)
      ((Γ.semipositiveProjection omega η hη).potential r) := by
  change GlobalPComparison.sourcePEquivalent (n := n) (Γ.potential r)
    (sourceSingularityEnvelope (θ.add η) (Γ.potential r))
  simpa only [sourceSingularityEnvelope_eq_native] using
    SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
      (atlasClosedFormToNative (θ.add η))
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp
        (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r)))

/-- Actual endpoint-safe mixtures preserve the original global P-type. -/
theorem sourceTestCurveJoinMixture_semipositive_sourcePEquivalent
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ Δ : SourceTestCurve θ) (τ : ℝ)
    (j : SourceTestCurveJoinMixtureIndex Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ) :
    GlobalPComparison.sourcePEquivalent (n := n)
      (sourceTestCurveJoinMixture Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ j)
      (sourceTestCurveJoinMixture
        (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata
        (Δ.semipositiveProjection omega η hη).toSourceTestCurvePredata τ
        (sourceTestCurveJoinMixtureIndex_projectionEquiv omega η hη Γ Δ τ j)) := by
  let G := Γ.semipositiveProjection omega η hη
  let D := Δ.semipositiveProjection omega η hη
  have hG := sourceTestCurveStrictSlice_semipositive_sourcePEquivalent omega η hη Γ j.left
  have hD := sourceTestCurveStrictSlice_semipositive_sourcePEquivalent omega η hη Δ j.right
  change GlobalPComparison.sourcePEquivalent (n := n)
    (if j.weight.1 = 0 then Δ.potential j.right else
      if j.weight.1 = 1 then Γ.potential j.left else
        convexComb j.weight.1 (Γ.potential j.left) (Δ.potential j.right))
    (if j.weight.1 = 0 then D.potential j.right else
      if j.weight.1 = 1 then G.potential j.left else
        convexComb j.weight.1 (G.potential j.left) (D.potential j.right))
  split_ifs with hw0 hw1
  · exact hD
  · exact hG
  · have ht : 0 < j.weight.1 := lt_of_le_of_ne j.weight.2.1 (Ne.symm hw0)
    have ht1 : 0 < 1-j.weight.1 := sub_pos.mpr (lt_of_le_of_ne j.weight.2.2 hw1)
    have hGc : GlobalPComparison.sourcePEquivalent (n := n)
        (fun x => (j.weight.1 : EReal)*Γ.potential j.left x)
        (fun x => (j.weight.1 : EReal)*G.potential j.left x) :=
      ⟨sourcePOrder_positiveScaling hG.1 ht, sourcePOrder_positiveScaling hG.2 ht⟩
    have hDc : GlobalPComparison.sourcePEquivalent (n := n)
        (fun x => ((1-j.weight.1 : ℝ) : EReal)*Δ.potential j.right x)
        (fun x => ((1-j.weight.1 : ℝ) : EReal)*D.potential j.right x) :=
      ⟨sourcePOrder_positiveScaling hD.1 ht1, sourcePOrder_positiveScaling hD.2 ht1⟩
    exact SGPT.PSH.GlobalOrderAddition.sourcePEquivalent_add omega
      ⟨_, sourcePositiveScaling_thetaPSH (Γ.thetaPSH j.left) ht⟩
      ⟨_, sourcePositiveScaling_thetaPSH (Δ.thetaPSH j.right) ht1⟩
      ⟨_, sourcePositiveScaling_thetaPSH (G.thetaPSH j.left) ht⟩
      ⟨_, sourcePositiveScaling_thetaPSH (D.thetaPSH j.right) ht1⟩ hGc hDc

/-- The same literal raw envelope retains global P-type after projection. -/
theorem sourceTestCurveRawConcaveMaximum_semipositive_sourcePEquivalent
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    GlobalPComparison.sourcePEquivalent (n := n)
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)
      (sourceTestCurveRawConcaveMaximum
        (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata
        (Δ.semipositiveProjection omega η hη).toSourceTestCurvePredata τ) := by
  let G := Γ.semipositiveProjection omega η hη
  let D := Δ.semipositiveProjection omega η hη
  let J := SourceTestCurveJoinMixtureIndex Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ
  have : Nonempty J := sourceTestCurveJoinMixtureIndex_nonempty _ _ hτ
  let e := sourceTestCurveJoinMixtureIndex_projectionEquiv omega η hη Γ Δ τ
  let u : J → M → EReal :=
    sourceTestCurveJoinMixture Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ
  let v : J → M → EReal := fun j =>
    sourceTestCurveJoinMixture G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ (e j)
  have hu (j : J) : (ofFixedModel n M).IsThetaPSH (θ.add η) (u j) :=
    sourceThetaPSH_add_semipositive η hη (sourceTestCurveJoinMixture_thetaPSH _ _ τ j)
  have hv (j : J) : (ofFixedModel n M).IsThetaPSH (θ.add η) (v j) :=
    sourceTestCurveJoinMixture_thetaPSH G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ (e j)
  have hp (j : J) : GlobalPComparison.sourcePEquivalent (n := n) (u j) (v j) :=
    sourceTestCurveJoinMixture_semipositive_sourcePEquivalent omega η hη Γ Δ τ j
  have huBound : ∃ C : ℝ, ∀ j x, u j x ≤ (C : EReal) :=
    ⟨0, fun j x => sourceTestCurveJoinMixture_le_zero _ _ τ j x⟩
  have hvBound : ∃ C : ℝ, ∀ j x, v j x ≤ (C : EReal) :=
    ⟨0, fun j x => sourceTestCurveJoinMixture_le_zero _ _ τ (e j) x⟩
  have hforward := sourcePOrder_uscSup omega hu hv huBound hvBound (fun j => (hp j).1)
  have hreverse := sourcePOrder_uscSup omega hv hu hvBound huBound (fun j => (hp j).2)
  have hrawu : sourceTestCurveRawConcaveMaximum
      Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ = uscSup u := by
    rw [sourceTestCurveRawConcaveMaximum_eq_mixtureUSC omega
      Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ]
    apply congrArg uscRegularization
    funext x
    exact iSup_apply
  have hrawv : sourceTestCurveRawConcaveMaximum
      G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ = uscSup v := by
    rw [sourceTestCurveRawConcaveMaximum_eq_mixtureUSC omega
      G.toSourceTestCurvePredata D.toSourceTestCurvePredata hτ]
    apply congrArg uscRegularization
    funext x
    rw [iSup_apply]
    apply le_antisymm
    · apply iSup_le
      intro j'
      obtain ⟨j, rfl⟩ := e.surjective j'
      exact le_iSup (fun j => v j x) j
    · apply iSup_le
      intro j
      exact le_iSup (fun j' => sourceTestCurveJoinMixture
        G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ j' x) (e j)
  rw [← hrawu, ← hrawv] at hforward hreverse
  exact ⟨hforward, hreverse⟩

/-- A strict target-envelope equality, without reducing constructed curve proof fields. -/
theorem sourceTestCurveJoinProjection_envelope_eq
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    sourceSingularityEnvelope (θ.add η) (sourceSingularityEnvelope θ
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) =
    sourceSingularityEnvelope (θ.add η) (sourceTestCurveRawConcaveMaximum
      (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata
      (Δ.semipositiveProjection omega η hη).toSourceTestCurvePredata τ) := by
  let G := Γ.semipositiveProjection omega η hη
  let D := Δ.semipositiveProjection omega η hη
  let T := θ.add η
  let u := sourceSingularityEnvelope θ
    (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)
  have hm : SourceModelPotential θ u := sourceTestCurveJoinSlice_model omega Γ Δ hτ
  have hu : (ofFixedModel n M).IsThetaPSH T u :=
    sourceThetaPSH_add_semipositive η hη hm.thetaPSH
  have hup : 0 < sourcePotentialNonPluripolarMeasure T u hu univ :=
    hm.choose_spec.2.trans_le (sourcePotentialMass_le_add_semipositive η hη hm.thetaPSH)
  have hv : (ofFixedModel n M).IsThetaPSH T
      (sourceTestCurveRawConcaveMaximum G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ) :=
    sourceTestCurveRawConcaveMaximum_thetaPSH omega
      G.toSourceTestCurvePredata D.toSourceTestCurvePredata hτ.le
  have hvp := sourceTestCurveRawConcaveMaximum_mass_positive omega G D hτ
  have hraw₀ := sourceTestCurveRawConcaveMaximum_thetaPSH omega
    Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ.le
  have henvelope := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
    (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ _).mp hraw₀)
  have hsraw : GlobalPComparison.sourcePEquivalent (n := n) u
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ) := by
    change GlobalPComparison.sourcePEquivalent (n := n)
      (sourceSingularityEnvelope θ
        (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) _
    rw [sourceSingularityEnvelope_eq_native]
    exact ⟨henvelope.2, henvelope.1⟩
  have hraw := sourceTestCurveRawConcaveMaximum_semipositive_sourcePEquivalent
    omega η hη Γ Δ hτ
  have hequiv : GlobalPComparison.sourcePEquivalent (n := n) u
      (sourceTestCurveRawConcaveMaximum G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ) :=
    ⟨GlobalPComparison.sourcePOrder_trans omega hsraw.1 hraw.1,
      GlobalPComparison.sourcePOrder_trans omega hraw.2 hsraw.2⟩
  have hfixed := (SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith omega
    (atlasClosedFormToNative T)
    ((isThetaPSH_iff_nativeThetaPotential T _).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential T _).mp hv) hup hvp).mp hequiv
  change sourceSingularityEnvelope T u = sourceSingularityEnvelope T
    (sourceTestCurveRawConcaveMaximum G.toSourceTestCurvePredata D.toSourceTestCurvePredata τ)
  rw [sourceSingularityEnvelope_eq_native, sourceSingularityEnvelope_eq_native]
  exact FirstPass.POrder.pEquivalentWith_iff_envelope_eq.mp hfixed

/-- WHOLE original lma:testcurlorPthetapomega, including every weak-positive added form. -/
theorem source_test_curve_join_semipositive_projection_compatible
    (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ Δ : SourceTestCurve θ) :
    (Γ.join omega Δ).semipositiveProjection omega η hη =
      (Γ.semipositiveProjection omega η hη).join omega
        (Δ.semipositiveProjection omega η hη) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.semipositiveProjection_max, SourceTestCurve.join_max]
  · intro r hr hs
    change sourceSingularityEnvelope (θ.add η) (sourceSingularityEnvelope θ
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r)) =
      sourceSingularityEnvelope (θ.add η) (sourceTestCurveRawConcaveMaximum
        (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata
        (Δ.semipositiveProjection omega η hη).toSourceTestCurvePredata r)
    exact sourceTestCurveJoinProjection_envelope_eq omega η hη Γ Δ hr

/-- The genuine semipositive special case is the SAME original positive projection. -/
theorem SourceTestCurve.semipositiveProjection_kahler_eq_backgroundProjection
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    (hω : (atlasClosedFormToNative (nativeClosedFormToAtlas omega.form)).val.IsSemipositive) :
    Γ.semipositiveProjection omega (nativeClosedFormToAtlas omega.form) hω =
      Γ.backgroundProjection omega := by
  apply SourceTestCurve.ext_of_max_potential
  · rfl
  · intro r hr hs
    rfl

/-- Exact original backgroundProjection compatibility in the Kahler specialization. -/
theorem source_test_curve_join_background_projection_compatible
    (omega : KahlerBackground n M) (Γ Δ : SourceTestCurve θ) :
    (Γ.join omega Δ).backgroundProjection omega =
      (Γ.backgroundProjection omega).join omega (Δ.backgroundProjection omega) := by
  have hω : (atlasClosedFormToNative (nativeClosedFormToAtlas omega.form)).val.IsSemipositive := by
    simpa only [sourceNativeAtlasForm_roundTrip] using omega.isSemipositive
  have h := source_test_curve_join_semipositive_projection_compatible omega
    (nativeClosedFormToAtlas omega.form) hω Γ Δ
  change @Eq (SourceTestCurve (θ.add (nativeClosedFormToAtlas omega.form))) _ _
  simpa only [SourceTestCurve.semipositiveProjection_kahler_eq_backgroundProjection,
    sourceTestCurveEnlargedBackground] using h

end SGPT.PSH.VariableComplexAtlas
