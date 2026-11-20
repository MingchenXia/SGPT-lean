import SGPT.Hodge.BDivChainPresentationUniformDraft
import SGPT.Hodge.BDivChainZeroSiuDraft
import SGPT.Hodge.BDivChainZeroNefDraft
import SGPT.Hodge.BDivChainZeroSourceVolumeDraft
import SGPT.PSH.SourceSingularityDistance

/-!
# Source-facing zero-dimensional b-divisor endpoints

These declarations use the proposed actual chart
current, current b-divisor and dimension-uniform family predicates from the
companion modules. They assemble genuine source quantifiers and the
actual source `dS`, I-envelope and I-volume. The zero-dimensional statements
do not by themselves establish the corresponding all-dimensional source results.
-/

set_option autoImplicit false
noncomputable section
universe u

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [ConnectedSpace X]

/-- The current of the SAME original source theta-psh potential in dimension
zero. Its chart coefficients are the actual `θ + ddᶜ u` distribution; the
presentation equality below derives that fact. -/
def sourcePotentialCurrentZero (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X))
    (_u : SourceThetaPotentialL1 θ) : ClosedPositive (n := 0) (X := X) :=
  closedPositiveZeroDim

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The chosen original source potential really presents the constructed
current, with the same native θ and the same potential. -/
theorem sourcePotentialCurrentZero_isPresentation
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X)) (u : SourceThetaPotentialL1 θ) :
    IsPresentationAny (sourcePotentialCurrentZero θ u) (atlasClosedFormToNative θ) u.val := by
  apply (isPresentationAny_iff_zero _ _ _).mpr
  exact isPresentationZero_of_isThetaPshPotential _ _
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property)

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- Source `thm:DT` nef clause in zero dimension, for every actual closed
positive chart current and every actual model system. -/
theorem currentBDivisorAnyOn_isNef_zero (S : ModelSystem 0 X)
    (T : ClosedPositive (n := 0) (X := X)) : IsNefAny (currentBDivisorAnyOn S T) :=
  isNefAny_zero _

/-- Source `thm:DT` volume identity in zero dimension, for EVERY actual
source theta-PSH presentation of the same current. The left side is the proposed
conditional model infimum; the actual book-model limit is separately proved
in `tendsto_bookModelVolume_zero`. -/
theorem currentBDivisorAnyOn_vol_eq_sourceIVolume_zero (S : ModelSystem 0 X)
    (T : ClosedPositive (n := 0) (X := X))
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X)) (u : X → EReal)
    (hpres : IsPresentationAny T (atlasClosedFormToNative θ) u) :
    volumeAny (currentBDivisorAnyOn S T) =
      sourceIVolume θ u ((isThetaPSH_iff_nativeThetaPotential θ u).mpr hpres.choose) := by
  rw [volumeAny_currentBDivisorAnyOn_zero,
    sourceIVolume_eq_one_of_dim_zero]

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- At every actual model all zero-dimensional class traces coincide;
therefore the original modelwise Euclidean convergence holds for any filter,
without a convergence premise. -/
theorem currentBDivisorAnyOn_converges_zero (S : ModelSystem 0 X) {I : Type*} (F : Filter I)
    (w : I → ClosedPositive (n := 0) (X := X)) (v : ClosedPositive (n := 0) (X := X)) :
    ConvergesAny F (fun i => currentBDivisorAnyOn S (w i)) (currentBDivisorAnyOn S v) := by
  intro π
  have hfun : (fun i => (currentBDivisorAnyOn S (w i)).val π) =
      (fun _ => (currentBDivisorAnyOn S v).val π) := by
    funext i
    exact (modelClass_eq_zero S _ π).trans (modelClass_eq_zero S _ π).symm
  rw [hfun]
  let : TopologicalSpace (RealBottChern 0 π.1.carrier) := euclideanTopology _
  exact tendsto_const_nhds

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Every original zero-dimensional background class is big in the
existing actual Kähler-current definition: the zero form is a Kähler form
and the constant zero function is theta-psh. -/
theorem isBigClass_sourceBackground_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X)) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) := by
  let β := atlasClosedFormToNative θ
  let κ : KahlerBackground 0 X := kahlerBackgroundZero
  refine ⟨⟨β, rfl, (fun _ => (0 : EReal)), κ, ?_⟩⟩
  exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (β - κ.form))
    (fun _ => EReal.coe_ne_top 0) (fun _ => EReal.coe_ne_bot 0)

/-- Source `prop:dscontbdiv` in dimension zero with the original source dS
hypothesis retained, over the actual book model system. -/
theorem currentBDivisorAnyOn_converges_of_dS_zero (ω : KahlerBackground 0 X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (_hlim : Tendsto w F (@nhds _ (sourceSingularityTopology ω θ hbig) v)) :
    ConvergesAny F
      (fun i => currentBDivisorAnyOn (ModelSystem.blowup 0 X) (sourcePotentialCurrentZero θ (w i)))
      (currentBDivisorAnyOn (ModelSystem.blowup 0 X) (sourcePotentialCurrentZero θ v)) :=
  currentBDivisorAnyOn_converges_zero _ F _ _

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- The root of every actual zero-dimensional family is the class of the
same selected actual source theta-psh current. -/
theorem sourcePotentialCurrentZero_class_eq_root (S : ModelSystem 0 X)
    (D : WeilFamilyAny S) (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X))
    (u : SourceThetaPotentialL1 θ) :
    currentClassAny (sourcePotentialCurrentZero θ u) = D.val ModelSystem.Model.root := by
  exact (realBottChern_eq_zero_of_dim_zero _).trans (realBottChern_eq_zero_of_dim_zero _).symm

/-- Source `thm:bigandnefreal` zero-dimensional candidate: in fact every
actual family is represented, and the chosen SAME theta-psh potential is
I-good. This is stronger than assuming big and nef because all native zero
model classes vanish. -/
theorem exists_iGood_currentBDivisorAnyOn_eq_zero (S : ModelSystem 0 X)
    (D : WeilFamilyAny S) :
    ∃ (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 X)) (u : SourceThetaPotentialL1 θ),
      currentClassAny (sourcePotentialCurrentZero θ u) = D.val ModelSystem.Model.root ∧
      currentBDivisorAnyOn S (sourcePotentialCurrentZero θ u) = D ∧
      sourceIGoodWith θ u.val u.property := by
  let θ := nativeClosedFormToAtlas (0 : ClosedRealOneOneForm 0 X)
  have h0 : (ofFixedModel 0 X).IsThetaPSH θ (fun _ => (0 : EReal)) :=
    SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0
  let u : SourceThetaPotentialL1 θ :=
    ⟨sourceIEnvelope θ (fun _ => (0 : EReal)), isThetaPSH_sourceIEnvelope h0⟩
  have hgood : sourceIGoodWith θ u.val u.property :=
    sourceIEnvelope_iGood_of_dim_zero θ (fun _ => (0 : EReal)) h0
  refine ⟨θ, u, sourcePotentialCurrentZero_class_eq_root S D θ u, ?_, hgood⟩
  exact (weilFamily_eq_zero_of_dim_zero _).trans (weilFamily_eq_zero_of_dim_zero D).symm

end SGPT.Hodge.BDivChain.NativeDraft
