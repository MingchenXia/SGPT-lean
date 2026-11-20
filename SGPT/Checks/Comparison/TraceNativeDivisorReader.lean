import SGPT.NAPotential.BJPrepDivisorialTransform
import SGPT.NAPotential.DecreasingInfimum

/-! The UNCHANGED actual NA transform on the ORIGINAL direct geometric
quotient, with positive REAL weights and the actual trivial reader.
Blueprint: trace-native-divisor-readers.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison
open Set Filter
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ENNReal

variable {k : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [CompactSpace V] [ConnectedSpace V]

/-- Actual original direct prime classes, positive REAL weights, and
the trivial point. Dimension zero has no strict prime presentation. -/
def NativeDivisorialPoint (k : ℕ) (V : Type u) [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [CompactSpace V] [ConnectedSpace V] : Type (u+1) :=
  Option ({c : ℝ // 0 < c} × DirectPrimeOver k V)

variable [MeasurableSpace V] [BorelSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k V)}

/-- The literal original Legendre reader, using the actual direct
common-resolution quotient reader of every SAME original component slice. -/
def directNAPrimeValue (Γ : SourceNAPotential θ) (κ : SourceKahlerForm k V)
    (p : DirectPrimeOver k V) (c : ℝ) : EReal :=
  ⨆ s : Iio (Γ.component κ).val.max, ((s.val : ℝ) : EReal) - (c : EReal) *
    (directReader ((Γ.component κ).val.potential s)
      (((Γ.component κ).val.native_thetaPSH s).1.quasiPlurisubharmonic) p : EReal)

/-- Readback on EVERY actual original representative, literally to the
UNCHANGED original native transform. -/
theorem directNAPrimeValue_mk (Γ : SourceNAPotential θ) (κ : SourceKahlerForm k V)
    (p : PrimePresentation k V) (c : ℝ) :
    directNAPrimeValue Γ κ (Quot.mk commonResolutionRelation p) c =
      BJPrep.naDivisorialTransform Γ κ p c := by
  unfold directNAPrimeValue BJPrep.naDivisorialTransform BJPrep.curveDivisorialTransform
  rw [iSup_subtype]
  rfl

/-- The actual native divisorial function, including the unchanged
actual maximum at the native trivial point. -/
def nativeDivisorialFunction (Γ : SourceNAPotential θ) (κ : SourceKahlerForm k V) :
    NativeDivisorialPoint k V → EReal
  | none => (((Γ.component κ).val.max : ℝ) : EReal)
  | some cp => directNAPrimeValue Γ κ cp.2 cp.1.val

theorem nativeDivisorialFunction_trivial (Γ : SourceNAPotential θ) (κ : SourceKahlerForm k V) :
    nativeDivisorialFunction Γ κ none = (((Γ.component κ).val.max : ℝ) : EReal) := rfl

theorem nativeDivisorialFunction_prime_mk (Γ : SourceNAPotential θ) (κ : SourceKahlerForm k V)
    (p : PrimePresentation k V) (c : ℝ) (hc : 0 < c) :
    nativeDivisorialFunction Γ κ (some (⟨c,hc⟩,Quot.mk commonResolutionRelation p)) =
      BJPrep.naDivisorialTransform Γ κ p c :=
  directNAPrimeValue_mk Γ κ p c

/-- The SAME canonical function is independent of its Kähler index,
internally, at every actual direct prime class and the trivial point. -/
theorem nativeDivisorialFunction_independent (Γ : SourceNAPotential θ)
    (κ η : SourceKahlerForm k V) : nativeDivisorialFunction Γ κ = nativeDivisorialFunction Γ η := by
  funext v
  cases v with
  | none =>
    simp only [nativeDivisorialFunction]
    congr 1
    exact (sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative κ) Γ κ).symm.trans
      (sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative κ) Γ η)
  | some cp =>
    rcases cp with ⟨c,p⟩
    change directNAPrimeValue Γ κ p c.val = directNAPrimeValue Γ η p c.val
    refine Quot.inductionOn p fun p => ?_
    exact (directNAPrimeValue_mk Γ κ p c.val).trans
      ((BJPrep.naDivisorialTransform_independent Γ κ η p c.val).trans
        (directNAPrimeValue_mk Γ η p c.val).symm)

end SGPT.NAPotential.TraceComparison
