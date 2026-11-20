import SGPT.PSH.OriginalVariableBetaLocalization
import SGPT.PSH.SourceComplexPositiveCurrentReality

/-! LITERAL global source beta positivity equals actual all-local testing,
by genuine arbitrary smooth beta globalization on each compact test support. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentBridge
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.ComplexCurrentDraft SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] (A : VariableComplexAtlas X) (p : ℕ)

/-- LITERAL GLOBAL beta source positivity gives the ACTUAL all-local-beta
criterion. Arbitrary local smooth beta fields are internally globalized on the
actual compact test support, never inserted as extra source hypotheses. -/
theorem source_global_positive_implies_local (T : OriginalComplexCurrent A (2*p))
    (hT : OriginalSourceComplexPositive A p T) : OriginalComplexWeakPositive A p T := by
  intro i beta hbeta phi hphi alpha halpha
  let K : Compacts (ComplexModel (A.dimension i)) := ⟨tsupport phi,phi.hasCompactSupport⟩
  obtain ⟨B,hB⟩ := global_beta_family_variable_on_compact A i K phi.tsupport_subset p beta hbeta
  have htest : variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
      (fun j => (B j).smooth i) phi=alpha := by
    apply TestFunction.ext
    intro z
    change phi z • betaProduct (fun j => (B j).coeff i z)=alpha z
    rw [halpha z]
    by_cases hz : z∈(K : Set _)
    · have he : (fun j => (B j).coeff i z)=(fun j => beta j z) := funext (fun j => hB j z hz)
      rw [he]
    · have hzero : phi z=0 := image_eq_zero_of_notMem_tsupport hz
      rw [hzero,zero_smul,zero_smul]
  have h := hT B i phi hphi
  change (T.val i (testOfRealCLM (originalCurrentTarget A i)
      (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
        (fun j => (B j).smooth i) phi))).im=0 ∧
    0≤(T.val i (testOfRealCLM (originalCurrentTarget A i)
      (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
        (fun j => (B j).smooth i) phi))).re at h
  rw [htest] at h
  exact h

omit [T2Space X] in
/-- Genuine global fields restrict to the ACTUAL local smooth fields, so
all-local testing yields the literal global source positivity without any
local-to-global or supplied output assumption. -/
theorem source_local_positive_implies_global (T : OriginalComplexCurrent A (2*p))
    (hT : OriginalComplexWeakPositive A p T) : OriginalSourceComplexPositive A p T := by
  intro B i phi hphi
  exact hT i (fun j => (B j).coeff i) (fun j => (B j).smooth i) phi hphi
    (variableBetaTestCLM (originalCurrentTarget A i) (fun j => (B j).coeff i)
      (fun j => (B j).smooth i) phi) (fun _ => rfl)

/-- PROVED equality of literal GLOBAL source positivity and actual established
all-chart LOCAL testing, every dimension/degree and arbitrary original atlas. -/
theorem source_global_positive_iff_local (T : OriginalComplexCurrent A (2*p)) :
    OriginalSourceComplexPositive A p T ↔ OriginalComplexWeakPositive A p T :=
  ⟨source_global_positive_implies_local A p T,source_local_positive_implies_global A p T⟩

end SGPT.PSH.ComplexCurrentBridge
