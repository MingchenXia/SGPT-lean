import SGPT.NAPotential.BJSectionValuation
import Mathlib.Data.EReal.Basic

/-! Genuine negative section valuations and generic-trivial calibration,
using the actual native section injectivity of an integral scheme. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.Berkovich.BJSections
open AlgebraicGeometry CategoryTheory Topology Opposite SGPT.Foundations.Schemes
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f]

/-- Actual tensor power atlas, made from the genuine constructed power frames. -/
def powerAtlas {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ) :
    LineBundleAtlas (bundleTensorPower L n) where
  I := a.I
  opens := a.opens
  covers := a.covers
  frame := fun i => (a.frame i).tensorPower n

/-- A nonzero native global section has zero value at the ACTUAL trivial
point, not only at a divisorial proxy or a singleton scheme. -/
theorem localPowerValue_trivial [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L)
    {U : X.Opens} (e : LocalBundleFrame L U)
    (hc : (BerkovichPoint.trivial f).center ∈ U) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (hs : s≠0) :
    localPowerValue (BerkovichPoint.trivial f) e hc n s=0 := by
  let : Nonempty U := ⟨⟨_,hc⟩⟩
  let r : Γ(X,U) := (e.tensorPower n).coefficients (𝟙 U)
    ((bundleTensorPower L n).val.map (homOfLE le_top).op s)
  have hgeneric : X.germToFunctionField U r≠0 := by
    have hinj := globalSectionToFunctionField_injective (powerAtlas a n) (e.tensorPower n)
    intro hzero
    apply hs
    apply hinj
    rw [map_zero]
    change X.germToFunctionField U r=0
    exact hzero
  have hresinj : Function.Injective (X.residue (genericPoint X)).hom :=
    (X.residue (genericPoint X)).hom.injective
  have hev : X.evaluation U (genericPoint X) (genericPoint_mem_nonempty_open U) r≠0 := by
    change (X.residue (genericPoint X)).hom (X.germToFunctionField U r)≠0
    exact fun h => hgeneric (hresinj (by simpa only [map_zero] using h))
  change (BerkovichPoint.trivial f).valAt
    (X.evaluation U (genericPoint X) _ r)=0
  exact BerkovichPoint.trivial_valAt_of_ne_zero hev

theorem powerSectionValue_trivial [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n) (hs : s≠0) :
    powerSectionValue a n s (BerkovichPoint.trivial f)=0 :=
  localPowerValue_trivial a _ _ n s hs

/-- Literal -v(s): +infinite vanishing value becomes negative infinity. -/
def negativeValue : WithTop ℝ → EReal
  | ⊤ => ⊥
  | (r:ℝ) => ((-r:ℝ):EReal)

@[simp] theorem negativeValue_top : negativeValue ⊤=⊥ := rfl
@[simp] theorem negativeValue_coe (r:ℝ) : negativeValue (r:WithTop ℝ)=((-r:ℝ):EReal) := rfl
@[simp] theorem negativeValue_zero : negativeValue 0=0 := by simp [negativeValue]

theorem negativeValue_ne_top (a:WithTop ℝ) : negativeValue a≠⊤ := by
  cases a with
  | top => exact bot_ne_top
  | coe r => exact EReal.coe_ne_top _

theorem negativeValue_nonpos {a:WithTop ℝ} (ha:0≤a) : negativeValue a≤0 := by
  cases a with
  | top => exact bot_le
  | coe r =>
    have hr:0≤r := by exact_mod_cast ha
    exact EReal.coe_nonpos.mpr (neg_nonpos.mpr hr)

/-- The genuine non-Archimedean logarithmic norm of a native global section. -/
def sectionLogNorm {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) : EReal :=
  negativeValue (powerSectionValue a n s v)

theorem sectionLogNorm_atlas_independent {L : X.Modules} (a b : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) :
    sectionLogNorm a n s v=sectionLogNorm b n s v :=
  congrArg negativeValue (powerSectionValue_atlas_independent a b n s v)

theorem sectionLogNorm_nonpos {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) : sectionLogNorm a n s v≤0 :=
  negativeValue_nonpos (powerSectionValue_nonneg a n s v)

theorem sectionLogNorm_trivial [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s : bundlePowerGlobalSections L n) (hs:s≠0) :
    sectionLogNorm a n s (BerkovichPoint.trivial f)=0 := by
  rw [sectionLogNorm,powerSectionValue_trivial a n s hs,negativeValue_zero]

end SGPT.NAPotential.Berkovich.BJSections
