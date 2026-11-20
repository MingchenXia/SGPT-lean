import SGPT.PSH.GlobalPComparison
import SGPT.PSH.SourceIEnvelope
import SGPT.Foundations.Analysis.Pending.PositiveGlobalPEnvelopeSuprema
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation

/-! Whole original `prop:Ppartialsup`: actual arbitrary nonempty uniformly
bounded families, genuine common-background PSH, and both global P and
all-positive-level multiplier order of their literal USC suprema. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section GlobalP
variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Entire original global-P clause; output PSH and positive backgrounds are internal. -/
theorem sourcePOrder_uscSup (omega : KahlerBackground n M)
    {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : I → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i))
    (huBound : ∃ C : ℝ, ∀ i x, u i x ≤ (C : EReal))
    (hvBound : ∃ D : ℝ, ∀ i x, v i x ≤ (D : EReal))
    (huv : ∀ i, GlobalPComparison.sourcePOrder (n := n) (u i) (v i)) :
    GlobalPComparison.sourcePOrder (n := n) (uscSup u) (uscSup v) := by
  obtain ⟨C, hC⟩ := huBound
  obtain ⟨D, hD⟩ := hvBound
  let U := uscSup u
  let V := uscSup v
  let T := atlasClosedFormToNative θ
  have hU : (ofFixedModel n M).IsThetaPSH θ U :=
    isThetaPSH_uscSup_of_majorant hu upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top C) hC
  have hV : (ofFixedModel n M).IsThetaPSH θ V :=
    isThetaPSH_uscSup_of_majorant hv upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top D) hD
  have hun (i : I) : IsThetaPshPotential T.val (u i) :=
    (isThetaPSH_iff_nativeThetaPotential θ (u i)).mp (hu i)
  have hvn (i : I) : IsThetaPshPotential T.val (v i) :=
    (isThetaPSH_iff_nativeThetaPotential θ (v i)).mp (hv i)
  have hUn : IsThetaPshPotential T.val U := (isThetaPSH_iff_nativeThetaPotential θ U).mp hU
  have hVn : IsThetaPshPotential T.val V := (isThetaPSH_iff_nativeThetaPotential θ V).mp hV
  have hvV (i : I) : v i ≤ V := fun x =>
    (le_iSup (fun j => v j x) i).trans (le_uscRegularization (fun y => ⨆ j, v j y) x)
  let Θ := T + (1 : ℝ) • omega.form
  have hsemi := KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one
  have hVΘ : IsThetaPshPotential Θ.val V :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hVn hsemi
  have hVpos : DiagonalMass.HasPositivePotentialMass Θ V hVΘ :=
    SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
      omega hVn zero_lt_one
  let E := singularityEnvelope Θ.val V
  have hE : IsThetaPshPotential Θ.val E :=
    Pending.singularityEnvelope_isThetaPshPotential Θ.val Θ.property.1 Θ.property.2
      hVΘ.1.hasSmoothLocalPotentials V hVΘ
  have hmajor (i : I) : u i ≤ fun x => E x + (C : EReal) := by
    have hai : IsThetaPshPotential Θ.val (fun x => u i x + ((-C : ℝ) : EReal)) :=
      (LocalPotentials.isThetaPshPotential_add_of_semipositive (hun i) hsemi).add_const (-C)
    have hai0 : (fun x => u i x + ((-C : ℝ) : EReal)) ≤ 0 := by
      intro x
      change u i x + ((-C : ℝ) : EReal) ≤ (0 : EReal)
      have h := add_le_add (hC i x) (le_refl ((-C : ℝ) : EReal))
      simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
    have haiu := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega Θ T hai (hun i)
      ⟨-C, fun _ _ => le_rfl⟩
    have hiV := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega T T (hvn i) hVn
      (MoreSingularOn.of_le fun x _ => hvV i x)
    have haiV := (haiu.trans omega (huv i)).trans omega hiV
    have hle := PositiveGlobalPEnvelopeSuprema.le_singularityEnvelope_of_sourcePOrder_of_nonpositive
      omega Θ hVΘ hVpos hai hai0 haiV
    intro x
    have h := add_le_add (hle x) (le_refl (C : EReal))
    simpa only [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] using h
  have hUE : U ≤ fun x => E x + (C : EReal) :=
    uscRegularization_le
      (upperSemicontinuous_add_coe_const (upperSemicontinuous_uscRegularization _) C)
      (fun x => iSup_le fun i => hmajor i x)
  have horder := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega T Θ hUn hE
    ⟨C, fun x _ => hUE x⟩
  exact horder.trans omega
    (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega Θ hVΘ).2

end GlobalP

section IdealOrder
variable [CompactSpace M] [Nonempty M]

/-- Entire original I-order clause, including both manufactured genuine QPSH domains. -/
theorem sourceIOrder_uscSup {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : I → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i))
    (huBound : ∃ C : ℝ, ∀ i x, u i x ≤ (C : EReal))
    (hvBound : ∃ D : ℝ, ∀ i x, v i x ≤ (D : EReal))
    (huv : ∀ i, sourceIOrder (ofFixedModel n M) (u i) (v i)) :
    sourceIOrder (ofFixedModel n M) (uscSup u) (uscSup v) := by
  obtain ⟨C, hC⟩ := huBound
  obtain ⟨D, hD⟩ := hvBound
  let U := uscSup u
  let V := uscSup v
  let T := atlasClosedFormToNative θ
  have hU : (ofFixedModel n M).IsThetaPSH θ U :=
    isThetaPSH_uscSup_of_majorant hu upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top C) hC
  have hV : (ofFixedModel n M).IsThetaPSH θ V :=
    isThetaPSH_uscSup_of_majorant hv upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top D) hD
  have hun (i : I) : IsThetaPshPotential T.val (u i) :=
    (isThetaPSH_iff_nativeThetaPotential θ (u i)).mp (hu i)
  have hVn : IsThetaPshPotential T.val V := (isThetaPSH_iff_nativeThetaPotential θ V).mp hV
  have hvV (i : I) : v i ≤ V := fun x =>
    (le_iSup (fun j => v j x) i).trans (le_uscRegularization (fun y => ⨆ j, v j y) x)
  let B := IEnvelope.iSingularityEnvelope T.val V
  have hB : IsThetaPshPotential T.val B :=
    iSingularityEnvelope_isThetaPshPotential T.val T.property.1 T.property.2
      hVn.1.hasSmoothLocalPotentials V hVn
  have hmajor (i : I) : u i ≤ fun x => B x + (C : EReal) := by
    have hiV : IEnvelope.IOrderOnManifold (n := n) (u i) V :=
      ((sourceIOrder_iff_native ⟨θ, hu i⟩ ⟨θ, hv i⟩).mp (huv i)).trans
        (iOrderOnManifold_of_le hVn.1.quasiPlurisubharmonic (hvV i))
    have henv := ActualIEnvelopeOrderInfimum.iSingularityEnvelope_le_of_iOrderOnManifold
      T hVn hiV
    have hai : IsThetaPshPotential T.val (fun x => u i x + ((-C : ℝ) : EReal)) :=
      (hun i).add_const (-C)
    have hai0 : (fun x => u i x + ((-C : ℝ) : EReal)) ≤ 0 := by
      intro x
      change u i x + ((-C : ℝ) : EReal) ≤ (0 : EReal)
      have h := add_le_add (hC i x) (le_refl ((-C : ℝ) : EReal))
      simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
    have haiI : IEnvelope.IEquivalentOnManifold (n := n)
        (fun x => u i x + ((-C : ℝ) : EReal)) (u i) := by
      simpa only [sub_eq_add_neg, EReal.coe_neg] using iEquivalentOnManifold_sub_const (u i) C
    have hle := (IEnvelope.le_iSingularityEnvelope hai hai0 haiI).trans henv
    intro x
    have h := add_le_add (hle x) (le_refl (C : EReal))
    simpa only [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] using h
  have hUB : U ≤ fun x => B x + (C : EReal) :=
    uscRegularization_le
      (upperSemicontinuous_add_coe_const (upperSemicontinuous_uscRegularization _) C)
      (fun x => iSup_le fun i => hmajor i x)
  have hUIB := iOrderOnManifold_of_le_add hB.1.quasiPlurisubharmonic hUB
  have hVB := iEquivalent_iSingularityEnvelope T.val T.property.1 T.property.2
    hVn.1.hasSmoothLocalPotentials V hVn
  exact (sourceIOrder_iff_native ⟨θ, hU⟩ ⟨θ, hV⟩).mpr (hUIB.trans hVB.2)

end IdealOrder
end SGPT.PSH.VariableComplexAtlas
