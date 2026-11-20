import SGPT.NAPotential.BerkovichIdealValue
import SGPT.LineBundle.SectionRing

/-! Actual all-point values of native global line-bundle sections. No
rational metric or numerical-class convergence is supplied as a certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.Berkovich.BJSections
open AlgebraicGeometry CategoryTheory Topology Opposite SGPT.Foundations.Schemes
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f]

/-- Native center-germ valuation agrees with native support-section valuation. -/
theorem centerVal_germ_eq_sectionVal (v : BerkovichPoint f) (U : X.Opens)
    (hc : v.center ∈ U) (r : Γ(X,U)) :
    v.centerVal ((X.presheaf.germ U v.center hc).hom r)=
      v.sectionVal U (v.support_specializes_center.mem_open U.isOpen hc) r := by
  unfold BerkovichPoint.centerVal BerkovichPoint.sectionVal BerkovichPoint.specializationMap
  change v.valAt (((X.presheaf.germ U v.center hc ≫
    X.presheaf.stalkSpecializes v.support_specializes_center) ≫ X.residue v.support).hom r)=_
  rw [X.presheaf.germ_stalkSpecializes]
  rfl

/-- Actual regular units on a center-containing open have valuation zero. -/
theorem sectionVal_unit (v : BerkovichPoint f) (U : X.Opens)
    (hc : v.center ∈ U) (u : (Γ(X,U))ˣ) :
    v.sectionVal U (v.support_specializes_center.mem_open U.isOpen hc) (u:Γ(X,U))=0 := by
  rw [← centerVal_germ_eq_sectionVal v U hc]
  exact (v.centerVal_eq_zero_iff _).mpr (u.isUnit.map (X.presheaf.germ U v.center hc).hom)

/-- The literal global coefficient in a chosen actual power frame. -/
def localPowerValue {L : X.Modules} (v : BerkovichPoint f) {U : X.Opens}
    (e : LocalBundleFrame L U) (hc : v.center ∈ U) (n : ℕ)
    (s : bundlePowerGlobalSections L n) : WithTop ℝ :=
  v.sectionVal U (v.support_specializes_center.mem_open U.isOpen hc)
    ((e.tensorPower n).coefficients (𝟙 U)
      ((bundleTensorPower L n).val.map (homOfLE le_top).op s))

/-- Genuine frame invariance on every Berkovich support, including sections
vanishing identically on that support. -/
theorem localPowerValue_frame_independent {L : X.Modules} (v : BerkovichPoint f)
    {U V : X.Opens} (e : LocalBundleFrame L U) (e' : LocalBundleFrame L V)
    (hc : v.center ∈ U) (hc' : v.center ∈ V) (n : ℕ)
    (s : bundlePowerGlobalSections L n) :
    localPowerValue v e hc n s=localPowerValue v e' hc' n s := by
  let W := U⊓V
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ V := homOfLE inf_le_right
  have hcW : v.center ∈ W := ⟨hc,hc'⟩
  have hsW : v.support ∈ W := v.support_specializes_center.mem_open W.isOpen hcW
  let u : (Γ(X,W))ˣ := localBundleFrameTransition e e' i j
  have hu : v.sectionVal W hsW ((u:Γ(X,W))^n)=0 := by
    exact sectionVal_unit v W hcW (u^n)
  have hcoeff := LocalBundleFrame.global_coefficients_transition e e' i j n s
  have hval := congrArg (v.sectionVal W hsW) hcoeff
  rw [BerkovichPoint.sectionVal_mul,hu,zero_add] at hval
  let rU : Γ(X,U) := (e.tensorPower n).coefficients (𝟙 U)
    ((bundleTensorPower L n).val.map (homOfLE le_top).op s)
  let rV : Γ(X,V) := (e'.tensorPower n).coefficients (𝟙 V)
    ((bundleTensorPower L n).val.map (homOfLE le_top).op s)
  change v.sectionVal W hsW (X.presheaf.map (homOfLE inf_le_right).op rV)=
    v.sectionVal W hsW (X.presheaf.map (homOfLE inf_le_left).op rU) at hval
  rw [BerkovichPoint.sectionVal_restrict,BerkovichPoint.sectionVal_restrict] at hval
  exact hval.symm

/-- The actual atlas chooses a frame containing the actual proper center. -/
def centerIndex {L : X.Modules} (a : LineBundleAtlas L) (v : BerkovichPoint f) : a.I :=
  (a.covers v.center).choose

theorem center_mem_open {L : X.Modules} (a : LineBundleAtlas L) (v : BerkovichPoint f) :
    v.center ∈ a.opens (centerIndex a v) := (a.covers v.center).choose_spec

/-- Intrinsic section valuation is constructed from genuine center frames. -/
def powerSectionValue {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) : WithTop ℝ :=
  localPowerValue v (a.frame (centerIndex a v)) (center_mem_open a v) n s

theorem powerSectionValue_eq_local {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) {U : X.Opens}
    (e : LocalBundleFrame L U) (hc : v.center ∈ U) :
    powerSectionValue a n s v=localPowerValue v e hc n s :=
  localPowerValue_frame_independent v _ _ _ _ n s

/-- No chosen atlas survives in the actual value. -/
theorem powerSectionValue_atlas_independent {L : X.Modules} (a b : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) :
    powerSectionValue a n s v=powerSectionValue b n s v :=
  powerSectionValue_eq_local a n s v (b.frame (centerIndex b v)) (center_mem_open b v)

theorem powerSectionValue_nonneg {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (s : bundlePowerGlobalSections L n) (v : BerkovichPoint f) : 0≤powerSectionValue a n s v := by
  unfold powerSectionValue localPowerValue
  rw [← centerVal_germ_eq_sectionVal v _ (center_mem_open a v)]
  exact v.centerVal_nonneg _

@[simp] theorem powerSectionValue_zero {L : X.Modules} (a : LineBundleAtlas L) (n : ℕ)
    (v : BerkovichPoint f) : powerSectionValue a n 0 v=⊤ := by
  unfold powerSectionValue localPowerValue BerkovichPoint.sectionVal
  simp only [map_zero,BerkovichPoint.valAt_zero]

/-- Native genuine sheafified tensor products add the intrinsic valuations. -/
theorem powerSectionValue_mul {L : X.Modules} (a : LineBundleAtlas L) (m n : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n)
    (v : BerkovichPoint f) :
    powerSectionValue a (m+n) (atlasPowerGlobalMul a m n s t) v=
      powerSectionValue a m s v+powerSectionValue a n t v := by
  unfold powerSectionValue localPowerValue
  change v.sectionVal _ _ (atlasPowerGlobalCoefficients a (m+n) _ (atlasPowerGlobalMul a m n s t))=_
  rw [atlasPowerGlobalMul_coefficients,BerkovichPoint.sectionVal_mul]
  rfl

end SGPT.NAPotential.Berkovich.BJSections
