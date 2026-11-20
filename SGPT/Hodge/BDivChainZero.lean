import SGPT.NPP.DimensionZero
import SGPT.Envelopes.SourceClassVolume
import SGPT.PSH.SourceIModelGood

/-!
# Actual source potential and class volumes in dimension zero

These producers support, but do not themselves provide, dimension-zero
b-divisors: the current and b-divisor APIs used by `BDivChainReal` require
positive dimension. In particular this module does not replace those objects
by a proxy and does not assert the dimension-zero form of `thm:DT`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Hodge.BDivChain

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Every actual closed real `(1,1)`-form is zero in complex dimension zero. -/
theorem closedRealOneOneForm_eq_zero_of_dim_zero (θ : ClosedRealOneOneForm 0 M) : θ = 0 := by
  apply ClosedRealOneOneForm.ext
  intro e z
  apply ContinuousAlternatingMap.ext
  intro v
  change (θ.val.coeff e z) v = 0
  exact (θ.val.coeff e z).map_coord_zero (0 : Fin 2) (Subsingleton.elim (v 0) 0)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The actual real Bott--Chern class group is trivial in dimension zero. -/
theorem realBottChern_eq_zero_of_dim_zero (α : RealBottChern 0 M) : α = 0 := by
  induction α using Quotient.inductionOn with
  | h θ =>
    rw [closedRealOneOneForm_eq_zero_of_dim_zero θ]
    rfl

/-- In dimension zero the actual source I-volume is one. -/
theorem sourceIVolume_eq_one_of_dim_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : M → EReal)
    (hu : (ofFixedModel 0 M).IsThetaPSH θ u) : sourceIVolume θ u hu = 1 := by
  unfold sourceIVolume
  exact SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ _
    (isThetaPSH_sourceIEnvelope hu)

/-- The I-envelope of every actual theta-PSH potential is I-good in dimension zero. -/
theorem sourceIEnvelope_iGood_of_dim_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : M → EReal)
    (hu : (ofFixedModel 0 M).IsThetaPSH θ u) :
    sourceIGoodWith θ (sourceIEnvelope θ u) (isThetaPSH_sourceIEnvelope hu) := by
  apply (sourceIModel_positive_iGood θ (sourceIEnvelope θ u) (sourceIEnvelope_isIModel hu) ?_).1
  exact SGPT.NPP.sourcePositiveMass_of_dim_zero θ _ (isThetaPSH_sourceIEnvelope hu)

/-- In dimension zero the actual source volume of every Bott--Chern class is
one; no additional Kähler background is needed for this normalization. -/
theorem sourceClassVolume_eq_one_of_dim_zero (α : RealBottChern 0 M) :
    sourceClassVolume α = 1 := by
  classical
  have hα := realBottChern_eq_zero_of_dim_zero α
  let θa := nativeClosedFormToAtlas (0 : ClosedRealOneOneForm 0 M)
  have hu : (ofFixedModel 0 M).IsThetaPSH θa (fun _ => (0 : EReal)) :=
    SGPT.NPP.isThetaPSH_const_of_dim_zero θa 0
  have hex : ∃ θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M),
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) = α ∧
        ∃ φ : M → EReal, SourceMinimalSingularities θ φ := by
    refine ⟨θa, ?_, sourceMinimalEnvelope θa, sourceMinimalEnvelope_minimalSingularities hu⟩
    simpa only [θa, sourceNativeAtlasForm_roundTrip, RealBottChern.ofRepresentative_zero] using hα.symm
  unfold sourceClassVolume
  rw [dif_pos hex]
  exact sourceIVolume_eq_one_of_dim_zero _ _ _

end SGPT.Hodge.BDivChain
