import SGPT.Okounkov.FlagBiholomorphicLifting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

/-- Equality transport with the SAME original carrier/topology retained
definitionally. Only genuine equal dimensions and their finite indices are
cast; no new geometry or source-body presentation is assigned. -/
def changeFlagDimension {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n) :
    OriginalFlagGeometry.{u} m where
  carrier := F.carrier
  topology := F.topology
  charts := by cases h; exact F.charts
  complex := by cases h; exact F.complex
  compact := F.compact
  connected := F.connected
  omega := by cases h; exact F.omega
  flag i := F.flag (Fin.cast (congrArg (fun a => a + 1) h.symm) i)
  smooth := by cases h; exact F.smooth

theorem changeFlagDimension_refl {n : ℕ} (F : OriginalFlagGeometry.{u} n) :
    changeFlagDimension rfl F = F := rfl

/-- Exact original actual-point carrier, before any body comparison. -/
theorem changeFlagDimension_carrier {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n) :
    (changeFlagDimension h F).carrier = F.carrier := rfl

/-- Literal original finite flag-index readback at EVERY level. -/
theorem changeFlagDimension_flag {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n)
    (i : Fin (m + 1)) :
    (changeFlagDimension h F).flag i = F.flag (Fin.cast (congrArg (fun a => a + 1) h.symm) i) := rfl

/-- The SAME original closed tensor, transported only through equal native
model dimensions on the SAME actual original carrier. -/
def changeFlagDimensionForm {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n)
    (θ : ClosedRealOneOneForm n F.carrier) : ClosedRealOneOneForm m (changeFlagDimension h F).carrier := by
  cases h
  exact θ

/-- The literal identity on actual original points is holomorphic between
the equal native model dimensions. -/
theorem contMDiff_changeFlagDimension_id {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n) :
    letI : ChartedSpace (ComplexModel n) (changeFlagDimension h F).carrier := F.charts
    letI := (changeFlagDimension h F).charts
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (id : (changeFlagDimension h F).carrier → F.carrier) := by
  cases h
  exact contMDiff_id

/-- Strong source PSH is unchanged on the SAME function and SAME tensor. -/
theorem thetaPsh_changeFlagDimension {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    IsThetaPshPotential (changeFlagDimensionForm h F θ).val φ := by
  cases h
  exact hφ

/-- Genuine original source bodies transport by the LITERAL coordinate
cast under equal dimensions, including the actual0-dimensional construction. -/
theorem sourceGeneralBody_changeFlagDimension {n m : ℕ} (h : n = m) (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    SourceTestCurveAllDimensions.generalBody (changeFlagDimension h F) (changeFlagDimensionForm h F θ)
      ⟨φ, thetaPsh_changeFlagDimension h F hφ⟩ =
      (fun x : Fin n → ℝ => fun j : Fin m => x (Fin.cast h.symm j)) ''
        SourceTestCurveAllDimensions.generalBody F θ ⟨φ, hφ⟩ := by
  cases h
  exact (Set.image_id _).symm

end SGPT.Okounkov.ToricTransport
