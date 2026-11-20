import SGPT.Checks.Comparison.BJNativeGFBridge

/-! Every given genuine native nonzero rational weighted section datum
internally produces actual source GF data, with true classes and ALL values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.NativeGF
open AlgebraicGeometry CategoryTheory Opposite SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
open SGPT.Foundations.Envelope.SchemeModuleIsoGlobalSections
open SGPT.Foundations.Envelope.SchemeGlobalSectionModelNormIsometries
open SGPT.Foundations.Envelope.SchemeGlobalSectionNormDetection
open scoped Classical NNReal ENNReal
variable {X : Scheme.{0}}

def nonzeroTerms (D : FSData X) : Finset (Γ(D.line,⊤)×ℝ) := D.terms.filter (fun q => q.1≠0)

theorem nonzeroTerms_nonempty (D : FSData X) (hD : D.Nonzero) : (nonzeroTerms D).Nonempty := by
  obtain ⟨q,hq,hq0⟩ := hD
  exact ⟨q,Finset.mem_filter.mpr ⟨hq,hq0⟩⟩

/-- Genuine original first tensor power, with its canonical actual unit iso. -/
def powerOneIso (M : X.Modules) : bundleTensorPower M 1≅M := bundleTensorLeftUnitIso M

def liftToPowerOne (M : X.Modules) (s : Γ(M,⊤)) : bundlePowerGlobalSections M 1 :=
  (moduleIsoTopEquiv (powerOneIso M)).symm s

theorem liftToPowerOne_ne_zero (M : X.Modules) {s : Γ(M,⊤)} (hs : s≠0) :
    liftToPowerOne M s≠0 := (moduleIsoTopEquiv (powerOneIso M)).symm.map_ne_zero_iff.mpr hs

/-- Actual original sheaf, internally produced atlas, nonzero actual sections
and actual rational weights. No requested output package is supplied. -/
def ofNativeRational (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational) :
    Printed.RationalGFPackage X where
  line := D.line
  atlas := atlasOfInvertible D.invertible
  n := 1
  m := D.m
  data := {
    I := nonzeroTerms D
    fintype := inferInstance
    nonempty := by
      obtain ⟨q,hq,hq0⟩ := hD
      exact ⟨⟨q,Finset.mem_filter.mpr ⟨hq,hq0⟩⟩⟩
    sections := fun q => liftToPowerOne D.line q.val.1
    sections_ne_zero := fun q => liftToPowerOne_ne_zero D.line (Finset.mem_filter.mp q.property).2
    weight := fun q => (hR q.val (Finset.mem_filter.mp q.property).1).choose
    power_pos := by omega
    denominator_pos := D.m_pos }

theorem ofNativeRational_weight (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (q : nonzeroTerms D) :
    (((ofNativeRational D hD hR).data.weight q:ℚ):ℝ)=q.val.2 :=
  (hR q.val (Finset.mem_filter.mp q.property).1).choose_spec.symm

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

theorem ofNativeRational_numericalClass (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational) :
    (ofNativeRational D hD hR).numericalClass p=D.numericalClass p := by
  change NativePicard.numericalClass p ((1/(D.m:ℚ))•
      rationalPicardClass (atlasOfInvertible D.invertible))=
    (D.m:ℝ)⁻¹•NativeRealNumericalClasses.lineClass p D.line D.invertible
  rw [NativePicard.numericalClass_rat_smul,NativePicard.numericalClass_line]
  rw [← Rat.cast_smul_eq_qsmul ℝ (1/(D.m:ℚ))]
  simp only [one_div,Rat.cast_inv,Rat.cast_natCast]

/-- Actual tensor-unit isometry, composed with the original/native log norm
producer, retains the whole original section value on EVERY point. -/
theorem sectionLogNorm_liftToPowerOne (D : FSData X) (s : Γ(D.line,⊤)) (v : BerkovichPoint p) :
    sectionLogNorm (atlasOfInvertible D.invertible) 1 (liftToPowerOne D.line s) v=
      ENNReal.log (globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v)
        D.line D.invertible s : ℝ≥0∞) := by
  rw [← nativeGlobalSectionLogNorm_eq_source]
  have hn := globalSectionNorm_moduleIso Valuation.one_apply_le_one (pointEquiv p v)
    (isInvertible_of_atlas (powerAtlas (atlasOfInvertible D.invertible) 1)) D.invertible
    (powerOneIso D.line) (liftToPowerOne D.line s)
  have he : moduleIsoTopEquiv (powerOneIso D.line) (liftToPowerOne D.line s)=s :=
    (moduleIsoTopEquiv (powerOneIso D.line)).apply_symm_apply s
  rw [he] at hn
  exact congrArg (fun z : ℝ≥0 => ENNReal.log (z:ℝ≥0∞)) hn

/-- Zero sections contribute only negative infinity, including common-zero
poles, so they may be removed from the ACTUAL finite maximum. -/
theorem native_sup_nonzeroTerms (D : FSData X) (v : BerkovichPoint p) :
    (nonzeroTerms D).sup (fun q => ENNReal.log (globalSectionNorm Valuation.one_apply_le_one
      (pointEquiv p v) D.line D.invertible q.1 : ℝ≥0∞)+(q.2:EReal))=
    D.terms.sup (fun q => ENNReal.log (globalSectionNorm Valuation.one_apply_le_one
      (pointEquiv p v) D.line D.invertible q.1 : ℝ≥0∞)+(q.2:EReal)) := by
  apply le_antisymm
  · exact Finset.sup_mono (Finset.filter_subset _ _)
  · apply Finset.sup_le
    intro q hq
    by_cases hq0 : q.1=0
    · rw [hq0,globalSectionNorm_zero,ENNReal.coe_zero,ENNReal.log_zero]
      simp only [EReal.bot_add]
      exact bot_le
    · exact Finset.le_sup (f:=fun q : Γ(D.line,⊤)×ℝ =>
        ENNReal.log (globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v)
          D.line D.invertible q.1 : ℝ≥0∞)+(q.2:EReal))
        (show q∈nonzeroTerms D from Finset.mem_filter.mpr ⟨hq,hq0⟩)

/-- Every given native rational datum now yields a literal source GF
function with EXACTLY the native value on the full original point space. -/
theorem ofNativeRational_eval (D : FSData X) (hD : D.Nonzero) (hR : D.IsRational)
    (v : BerkovichPoint p) :
    (ofNativeRational D hD hR).eval p v=D.eval p (pointEquiv p v) := by
  let F : (Γ(D.line,⊤)×ℝ) → EReal := fun q =>
    ENNReal.log (globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v)
      D.line D.invertible q.1 : ℝ≥0∞)+(q.2:EReal)
  have hterms : (⨆ q : nonzeroTerms D,
      sectionLogNorm (atlasOfInvertible D.invertible) 1 (liftToPowerOne D.line q.val.1) v+
        ((((ofNativeRational D hD hR).data.weight q:ℚ):ℝ):EReal))=
      (nonzeroTerms D).sup F := by
    have he : (⨆ q : nonzeroTerms D,F q.val)=(nonzeroTerms D).sup F := by
      apply le_antisymm
      · exact iSup_le fun q => Finset.le_sup q.property
      · exact Finset.sup_le fun q hq => le_iSup_of_le ⟨q,hq⟩ le_rfl
    rw [← he]
    apply iSup_congr
    intro q
    rw [sectionLogNorm_liftToPowerOne,ofNativeRational_weight]
  change (((1/(D.m:ℝ)):ℝ):EReal)*(⨆ q : nonzeroTerms D,
      sectionLogNorm (atlasOfInvertible D.invertible) 1 (liftToPowerOne D.line q.val.1) v+
        ((((ofNativeRational D hD hR).data.weight q:ℚ):ℝ):EReal))=
    (((D.m:ℝ)⁻¹:ℝ):EReal)*D.terms.sup F
  rw [hterms,native_sup_nonzeroTerms,one_div]

end SGPT.NAPotential.BJ.NativeGF
