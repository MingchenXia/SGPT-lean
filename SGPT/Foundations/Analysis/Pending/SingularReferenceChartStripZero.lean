import SGPT.Foundations.Analysis.Pending.SingularReferenceStripNonpluripolarZero
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation

set_option autoImplicit false

/-! # Any actual local-potential chart supplies the singular reference strip NP equation -/

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.SingularReferenceChartStripZero

open FirstPass BedfordTaylorStripCovariance SingularReferenceStripNonpluripolarZero

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Any actual smooth local potential internally supplies corrected base PSH and its genuine singular strip pullback. -/
theorem plurisubharmonicOn_corrected_reference_strip
    {θ : SmoothRealForm n M 2} {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) {S : Set ℂ} (hS : IsOpen S) :
    PlurisubharmonicOn
      (fun q => chartFunction φ e (stripFst n q) + (ρ (stripFst n q) : EReal))
      (stripLift (⟨W, hρ.1⟩ : Opens (ComplexModel n)) S hS) :=
  plurisubharmonicOn_comp_stripFst hS
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hφ e hρ)

/-- The actual theta-PSH reference, corrected by any genuine local potential, has zero actual canonical diagonal mixed strip NP measure. -/
theorem mixedTruncationLimitMeasure_corrected_reference_strip_eq_zero
    {θ : SmoothRealForm n M 2} {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) {S : Set ℂ} (hS : IsOpen S) :
    MixedNonPluripolar.mixedTruncationLimitMeasure
      (stripLift (⟨W, hρ.1⟩ : Opens (ComplexModel n)) S hS)
      (fun _ q => chartFunction φ e (stripFst n q) + (ρ (stripFst n q) : EReal))
      (fun _ => plurisubharmonicOn_corrected_reference_strip hφ e hρ hS) = 0 :=
  mixedTruncationLimitMeasure_diagonal_comp_stripFst_eq_zero hS
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hφ e hρ)

/-- The corresponding genuine scalar NP strip equation is internally produced with no corrected-PSH or rank-zero input. -/
theorem truncationLimitMeasure_corrected_reference_strip_eq_zero
    {θ : SmoothRealForm n M 2} {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) {S : Set ℂ} (hS : IsOpen S) :
    MongeAmpere.truncationLimitMeasure
      (stripLift (⟨W, hρ.1⟩ : Opens (ComplexModel n)) S hS)
      (fun q => chartFunction φ e (stripFst n q) + (ρ (stripFst n q) : EReal))
      (plurisubharmonicOn_corrected_reference_strip hφ e hρ hS) = 0 :=
  truncationLimitMeasure_comp_stripFst_eq_zero hS
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hφ e hρ)

end

end SGPT.Foundations.Analysis.Pending.SingularReferenceChartStripZero
