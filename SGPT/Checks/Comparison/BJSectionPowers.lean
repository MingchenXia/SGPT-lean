import SGPT.Checks.Comparison.BJGFCommonPowers

/-! Genuine homogeneous tensor powers of actual sections, preserving values
at ALL original Berkovich points and internally producing nonvanishing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.Berkovich.BJSections
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
variable {X : Scheme.{0}} {L : X.Modules}

/-- Transport along a genuine equality of the original homogeneous degree. -/
def castPowerSection {m n : ℕ} (h : m=n) (s : bundlePowerGlobalSections L m) :
    bundlePowerGlobalSections L n := h▸s

theorem castPowerSection_coefficients (a : LineBundleAtlas L) {m n : ℕ} (h : m=n)
    (s : bundlePowerGlobalSections L m) (i : a.I) :
    atlasPowerGlobalCoefficients a n i (castPowerSection h s)=
      atlasPowerGlobalCoefficients a m i s := by
  cases h
  rfl

/-- Actual repeated glued section multiplication, with original degree nk. -/
def tensorPowerSection (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) : (k : ℕ) → bundlePowerGlobalSections L (n*k)
  | 0 => castPowerSection (Nat.mul_zero n).symm (bundlePowerGlobalOne L)
  | k+1 => castPowerSection (Nat.mul_succ n k).symm
      (atlasPowerGlobalMul a (n*k) n (tensorPowerSection a n s k) s)

theorem tensorPowerSection_coefficients (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (k : ℕ) (i : a.I) :
    atlasPowerGlobalCoefficients a (n*k) i (tensorPowerSection a n s k)=
      (atlasPowerGlobalCoefficients a n i s)^k := by
  induction k with
  | zero => rw [tensorPowerSection,castPowerSection_coefficients,atlasPowerGlobalCoefficients_one,pow_zero]
  | succ k ih =>
    rw [tensorPowerSection,castPowerSection_coefficients,atlasPowerGlobalMul_coefficients,ih,pow_succ]

variable {p : X ⟶ Spec (.of ℂ)} [IsProper p]

theorem castPowerSection_value (a : LineBundleAtlas L) {m n : ℕ} (h : m=n)
    (s : bundlePowerGlobalSections L m) (v : BerkovichPoint p) :
    powerSectionValue a n (castPowerSection h s) v=powerSectionValue a m s v := by
  cases h
  rfl

theorem powerSectionValue_one (a : LineBundleAtlas L) (v : BerkovichPoint p) :
    powerSectionValue a 0 (bundlePowerGlobalOne L) v=0 := by
  change v.sectionVal _ _ (atlasPowerGlobalCoefficients a 0 (centerIndex a v)
    (bundlePowerGlobalOne L))=0
  rw [atlasPowerGlobalCoefficients_one]
  simp only [BerkovichPoint.sectionVal,map_one,BerkovichPoint.valAt_one]

/-- Full original-point value identity, including zero/polar arithmetic. -/
theorem tensorPowerSection_value (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (k : ℕ) (v : BerkovichPoint p) :
    powerSectionValue a (n*k) (tensorPowerSection a n s k) v=k•powerSectionValue a n s v := by
  induction k with
  | zero => rw [tensorPowerSection,castPowerSection_value,powerSectionValue_one,zero_nsmul]
  | succ k ih =>
    rw [tensorPowerSection,castPowerSection_value,powerSectionValue_mul,ih,succ_nsmul]

include p in
/-- No actual nonvanishing premise for the output section: the genuine
trivial original point internally proves every original tensor power nonzero. -/
theorem tensorPowerSection_ne_zero [IsIntegral X] (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (hs : s≠0) (k : ℕ) :
    tensorPowerSection a n s k≠0 := by
  intro hz
  have hv := tensorPowerSection_value a n s k (BerkovichPoint.trivial p)
  rw [hz,powerSectionValue_zero,powerSectionValue_trivial a n s hs,nsmul_zero] at hv
  simp at hv

end SGPT.NAPotential.Berkovich.BJSections
