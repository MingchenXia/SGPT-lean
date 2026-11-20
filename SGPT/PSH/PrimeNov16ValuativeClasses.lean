import SGPT.PSH.PrimeNov16PrimeOver
import SGPT.PSH.ValMultClass
import SGPT.PSH.ValMultFinite
import SGPT.PSH.RIsoAValuativeDimZero

/-! The original whole-fibre stalk order, Jacobian discrepancy and valuative
criterion on actual SINGLE-common-resolution prime classes over arbitrary manifolds.
The existing exact finite polar-component test is retained, not reconstructed.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16ValuativeClasses
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  AnalyticModificationLocalDiscrepancy CompactPrimeOver CompactPrimeLogDiscrepancy
  RIsoAGermOrder ActualGermValuative HironakaSmoothCentreRealDomainActualSheafStalk
  VariableComplexAtlas SquaredLogLelongSourceNormalization

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The original `A_X(E)` descends along each genuine common-resolution witness. -/
def logDiscrepancy : PrimeNov16PrimeOver.PrimeOver n X → ℕ :=
  Quot.lift presentationLogDiscrepancy (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationLogDiscrepancy_eq_of_commonResolution h)

theorem logDiscrepancy_mk (p : PrimePresentation n X) :
    logDiscrepancy (Quot.mk commonResolutionRelation p) = presentationLogDiscrepancy p := rfl

section Positive
variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m+1)) X]
  [IsComplexManifold (m+1) X]

/-- The book's actual minimum over the WHOLE fibre intersection, on prime classes. -/
def stalkOrder (x : X) (g : actualComplexStructureStalk (n := m+1) x) :
    PrimeNov16PrimeOver.PrimeOver (m+1) X → ℕ∞ :=
  Quot.lift (fun p => stalkOrdE p x g) (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact ValMultClass.stalkOrdE_eq_of_commonResolution h x g)

theorem stalkOrder_mk (x : X) (g : actualComplexStructureStalk (n := m+1) x)
    (p : PrimePresentation (m+1) X) :
    stalkOrder x g (Quot.mk commonResolutionRelation p) = stalkOrdE p x g := rfl

/-- One epsilon before EVERY original prime class, with all original readers. -/
def PrimeBound (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := m+1) φ)
    (x : X) (g : actualComplexStructureStalk (n := m+1) x) (ε : ℝ) : Prop :=
  ∀ E : PrimeNov16PrimeOver.PrimeOver (m+1) X, x ∈ PrimeNov16PrimeOver.center E →
    ENNReal.ofReal (1+ε) * PrimeNov16PrimeOver.reader φ hφ E ≤
      extendedOrderValue (stalkOrder x g E) + (logDiscrepancy E : ℝ≥0∞)

theorem primeBound_iff (φ : X → EReal)
    (hφ : ManifoldQuasiPlurisubharmonic (n := m+1) φ) (x : X)
    (g : actualComplexStructureStalk (n := m+1) x) (ε : ℝ) :
    PrimeBound φ hφ x g ε ↔ BookPrimeBound φ x g ε := by
  constructor
  · intro hb p hp
    exact hb (Quot.mk commonResolutionRelation p) hp
  · intro hb E
    induction E using Quot.ind with
    | mk p => exact hb p

/-- The original positive-dimensional valuative criterion, now on genuine
prime CLASSES over arbitrary noncompact, possibly disconnected, smooth bases. -/
theorem mem_multiplierIdeal_iff_primeBound {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m+1) φ) (x : X)
    (g : actualComplexStructureStalk (n := m+1) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m+1) 1 φ) x ↔
      ∃ ε : ℝ, 0 < ε ∧ PrimeBound φ hφ x g ε := by
  simp only [primeBound_iff]
  exact RIsoAGermOrder.mem_multiplierIdeal_iff_bookPrimeBound hφ x g

/-- Source `φ ∈ PSH(X)` input, the actual original stalk and the original readers. -/
theorem sourcePSH_mem_multiplierIdeal_iff_primeBound {φ : X → EReal}
    (hφ : (ofFixedModel (m+1) X).IsPSH φ) (x : X)
    (g : actualComplexStructureStalk (n := m+1) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m+1) 1 φ) x ↔
      ∃ ε : ℝ, 0 < ε ∧
        ∀ E : PrimeNov16PrimeOver.PrimeOver (m+1) X, x ∈ PrimeNov16PrimeOver.center E →
          ENNReal.ofReal (1+ε) * PrimeNov16PrimeOver.sourcePSHReader φ hφ E ≤
            extendedOrderValue (stalkOrder x g E) + (logDiscrepancy E : ℝ≥0∞) := by
  have hnative : ManifoldPSH (n := m+1) φ := (ofFixedModel_isPSH_iff (m+1) X φ).mp hφ
  have hqpsh : ManifoldQuasiPlurisubharmonic (n := m+1) φ := by
    intro e z hz
    exact (hnative.chartPlurisubharmonic e z hz).quasiPlurisubharmonicAt
  exact mem_multiplierIdeal_iff_primeBound hqpsh x g

/-- The classwise condition is the EXACT held finite test on ALL polar
components meeting the whole fibre, with the same original min-order convention. -/
theorem primeBound_iff_finiteTest {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m+1) φ)
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m+1)) Y]
    [IsComplexManifold (m+1) Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := m+1) π)
    {D : EffectiveGeometricQDivisor (m+1) Y} (hD : D.IsSNC)
    (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π)) (x : X)
    (g : actualComplexStructureStalk (n := m+1) x) :
    (∃ ε : ℝ, 0 < ε ∧ PrimeBound φ hφ x g ε) ↔
      ValMultFinite.FiniteLogResolutionTest φ hπ hD x g :=
  (mem_multiplierIdeal_iff_primeBound hφ x g).symm.trans
    (ValMultFinite.mem_multiplierIdeal_iff_finiteLogResolutionTest hφ hπ hD hlog x g)

end Positive

section Zero
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X]

/-- The exact zero-dimensional source clause, on the SAME genuine prime quotient:
all original stalk germs belong, and there is no prime class to test. -/
theorem sourcePSH_mem_multiplierIdeal_dim_zero {φ : X → EReal}
    (hφ : (ofFixedModel 0 X).IsPSH φ) (x : X)
    (g : actualComplexStructureStalk (n := 0) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := 0) 1 φ) x ∧
      IsEmpty (PrimeNov16PrimeOver.PrimeOver 0 X) := by
  have hnative : ManifoldPSH (n := 0) φ := (ofFixedModel_isPSH_iff 0 X φ).mp hφ
  have h := RIsoAValuativeDimZero.valuativemulti_dim_zero hnative x g
  exact ⟨h.1, ⟨fun E => Quot.inductionOn E (fun p => h.2.false p)⟩⟩

end Zero
end SGPT.PSH.PrimeNov16ValuativeClasses
