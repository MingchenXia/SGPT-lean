import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.PSH.SourceIEnvelope
import SGPT.Foundations.Analysis.Pending.DirectedIncreasingIEnvelope

/-! Whole original `prop:incnetmodelPI`: arbitrary nonempty directed nets,
literal original regularized suprema, genuine domains manufactured internally.
Source: author/chapter_envelopes.tex:2417--2442. No countable cofinality or
target-envelope equality is an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Whole original `prop:incnetmodelPI`, first assertion: the actual source
I-envelope commutes with the regularized supremum of an arbitrary increasing
positive-mass net. Genuine limit membership and bigness are internal outputs. -/
theorem sourceIEnvelope_uscSup_of_monotone_positive
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hv : ∀ i, IsThetaPSH θ (v i)) (hmono : Monotone v)
    (hbound : ∃ C : ℝ, ∀ i x, v i x ≤ (C : EReal))
    (hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure θ (v i) (hv i) univ) :
    ∃ _hu : IsThetaPSH θ (uscSup v),
      uscSup (fun i => sourceIEnvelope θ (v i)) = sourceIEnvelope θ (uscSup v) := by
  classical
  obtain ⟨C, hC⟩ := hbound
  have hu : IsThetaPSH θ (uscSup v) :=
    isThetaPSH_uscSup_of_majorant hv upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top C) hC
  let i0 : I := Classical.arbitrary I
  let Θ := atlasClosedFormToNative θ
  have hbig : IsBigClass (RealBottChern.ofRepresentative Θ) :=
    sourcePositiveMass_isBig omega (hv i0) (hpos i0)
  have hvn (i : I) : IsThetaPshPotential Θ.val (v i) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mp (hv i)
  have hun : IsThetaPshPotential Θ.val (uscSup v) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mp hu
  have hvu : v i0 ≤ uscSup v := fun x =>
    (le_iSup (fun i => v i x) i0).trans
      (le_uscRegularization (fun y => ⨆ i, v i y) x)
  have hupos : HasPositivePotentialMass Θ (uscSup v) hun :=
    (hpos i0).trans_le (diagonalPotentialMass_mono_of_kahler omega (hvn i0) hun
      (MoreSingularOn.of_le fun x _ => hvu x))
  have hsup (a : I → M → EReal) : uscSup a = uscRegularization (⨆ i, a i) := by
    unfold uscSup
    apply congrArg uscRegularization
    funext x
    simp only [iSup_apply]
  have hn := DirectedIncreasingIEnvelope.iSingularityEnvelope_directed_regularized_iSup_eq
    omega Θ hbig hvn hmono hun (hsup v).symm hupos
  refine ⟨hu, ?_⟩
  have hread : (fun i => sourceIEnvelope θ (v i)) =
      fun i => IEnvelope.iSingularityEnvelope Θ.val (v i) :=
    funext fun i => sourceIEnvelope_eq_native θ _ (hv i)
  rw [hsup, hread, sourceIEnvelope_eq_native θ _ hu]
  exact hn

/-- Whole original `prop:incnetmodelPI`, final assertion: an increasing
positive-mass net of genuine original I-model potentials has an I-model
regularized supremum. Its uniform upper bound is manufactured as zero. -/
theorem sourceIModel_uscSup_of_monotone_positive
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hmodel : ∀ i, sourceIModel θ (v i)) (hmono : Monotone v)
    (hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure θ (v i) (hmodel i).1 univ) :
    sourceIModel θ (uscSup v) := by
  have hzero : ∀ i x, v i x ≤ (0 : EReal) := by
    intro i x
    rw [(hmodel i).2]
    exact sourceIEnvelope_le_zero θ (v i) x
  obtain ⟨hu, heq⟩ := sourceIEnvelope_uscSup_of_monotone_positive omega
    (fun i => (hmodel i).1) hmono ⟨0, by simpa only [EReal.coe_zero] using hzero⟩ hpos
  refine ⟨hu, ?_⟩
  have hread : v = fun i => sourceIEnvelope θ (v i) := funext fun i => (hmodel i).2
  exact (congrArg uscSup hread).trans heq

end SGPT.PSH.VariableComplexAtlas
