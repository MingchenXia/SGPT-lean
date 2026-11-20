import SGPT.Checks.Comparison.BJModel2BerkovichMap
import SGPT.Checks.Comparison.BJNativePicard
import SGPT.Foundations.Schemes.NativeLinePullbackFrames
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import SGPT.Foundations.Envelope.AlgGeom.InvertibleBaseIdealPullback
import SGPT.Support.Principalization.Scheme.IdealSheaf.StalkLe

/-! The actual original section/ideal and semi-valuation restriction square for
`thm:comp_traceop`, `eq:varphiAncordF`. Blueprint: `trace-na-compatibility.tex`.
The whole actual section ideal and actual adjunction-unit pullback are retained,
including zero sections, nonflat maps and semi-valuations on their zero loci. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace SGPT.Foundations.Schemes
open Scheme.Modules
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ
open SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.InvertibleSheafBaseIdeal
open scoped ENNReal

local instance (X : Scheme.{0}) : ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

variable {X Y : Scheme.{0}} {fX : X ⟶ Spec (.of ℂ)} {fY : Y ⟶ Spec (.of ℂ)}

/-- The genuine image semi-valuation under the actual original complex scheme morphism. -/
def schemeAnMap (i : Y ⟶ X) (hi : i ≫ fX = fY) (w : BerkovichPoint fY) :
    BerkovichPoint fX :=
  letI := residueComplexAlgebra fY w.support
  fieldBerkovichPoint (L := Y.residueField w.support) fX
    (Y.fromSpecResidueField w.support ≫ i)
    (by rw [Category.assoc, hi]; exact (spec_map_residueComplexHom fY w.support).symm) w.val

/-- Values of the WHOLE actual inverse-image ideal at the SAME actual original point. -/
theorem idealVal_comap_schemeAnMap [IsProper fX] [IsProper fY]
    (i : Y ⟶ X) (hi : i ≫ fX = fY) (w : BerkovichPoint fY) (J : X.IdealSheafData) :
    w.idealVal (J.comap i) = (schemeAnMap i hi w).idealVal J := by
  let _ := residueComplexAlgebra fY w.support
  have hg : (Spec.map (𝟙 (Y.residueField w.support)) ≫
      Y.fromSpecResidueField w.support) ≫ fY =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Y.residueField w.support))) := by
    rw [Spec.map_id, Category.id_comp]
    exact (spec_map_residueComplexHom fY w.support).symm
  rw [← idealVal_fieldBerkovichPoint_fromSpecResidueField
    (L := Y.residueField w.support) w (𝟙 (Y.residueField w.support)) w.val hg
      (fun a => rfl) (J.comap i), idealVal_comap_fieldBerkovichPoint i hi]
  have he : (Spec.map (𝟙 (Y.residueField w.support)) ≫
      Y.fromSpecResidueField w.support) ≫ i = Y.fromSpecResidueField w.support ≫ i := by
    rw [Spec.map_id, Category.id_comp]
  unfold schemeAnMap
  exact congrArg (fun v : BerkovichPoint fX => v.idealVal J)
    (fieldBerkovichPoint_congr (L := Y.residueField w.support) he _ _ w.val)

/-- The native coefficient ideal and canonical evaluation-image ideal are the
SAME entire original section ideal, with no ideal-comparison premise. -/
theorem sectionZeroIdealSheaf_eq_sectionIdeal {M : X.Modules} (a : LineBundleAtlas M)
    (s : Γ(M, ⊤)) :
    sectionZeroIdealSheaf a s = sectionIdeal (isInvertible_of_atlas a) s := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro x
  obtain ⟨j, hj⟩ := a.covers x
  obtain ⟨W, hW, hxW, hWa⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := a.opens j) (x := x) hj
  let U : X.affineOpens := ⟨W, hW⟩
  let e : LocalBundleFrame M W :=
    SGPT.Support.ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M
      (a.opens j) (a.frame j) (Over.mk (homOfLE hWa))
  change stalkIdeal (sectionZeroIdealSheaf a s) x =
    stalkIdeal (sectionIdeal (isInvertible_of_atlas a) s) x
  rw [stalkIdeal_eq_map (sectionZeroIdealSheaf a s) U hxW,
    stalkIdeal_eq_map (sectionIdeal (isInvertible_of_atlas a) s) U hxW]
  congr 1
  change sectionZeroIdeal M s W = _
  rw [sectionZeroIdeal_eq_span_frame s e (𝟙 W),
    InvertibleBaseIdealFrameCoefficients.sectionIdeal_ideal_of_frame
      (isInvertible_of_atlas a) U e s]
  congr 2
  change e.coefficients (𝟙 W) (M.presheaf.map (homOfLE le_top).op s) =
    e.coefficients (𝟙 W) ((1 : Γ(X, W)) • M.presheaf.map (homOfLE le_top).op s)
  rw [one_smul]

/-- The actual original adjunction-unit pullback has precisely the WHOLE
original inverse-image section ideal, even for zero sections/nonflat morphisms. -/
theorem sectionZeroIdealSheaf_comap (i : Y ⟶ X) {M : X.Modules} (a : LineBundleAtlas M)
    (s : Γ(M, ⊤)) :
    (sectionZeroIdealSheaf a s).comap i =
      sectionZeroIdealSheaf (a.nativePullback i) (affinePullbackUnitTop i M s) := by
  rw [sectionZeroIdealSheaf_eq_sectionIdeal, sectionZeroIdealSheaf_eq_sectionIdeal]
  exact InvertibleBaseIdealPullback.sectionIdeal_comap i (isInvertible_of_atlas a) s

/-- Every original semi-valuation reads exactly the same actual section ideal
after genuine restriction. No incoming norm/evaluation/ideal certificate. -/
theorem idealVal_actual_section_pullback [IsProper fX] [IsProper fY]
    (i : Y ⟶ X) (hi : i ≫ fX = fY) {M : X.Modules} (a : LineBundleAtlas M)
    (s : Γ(M, ⊤)) (w : BerkovichPoint fY) :
    w.idealVal (sectionZeroIdealSheaf (a.nativePullback i) (affinePullbackUnitTop i M s)) =
      (schemeAnMap i hi w).idealVal (sectionZeroIdealSheaf a s) := by
  rw [← sectionZeroIdealSheaf_comap]
  exact idealVal_comap_schemeAnMap i hi w _

/-- Actual inverse image preserves the ENTIRE ideal generated by the original
section family. No section is silently discarded when it restricts to zero. -/
theorem sectionFamilyIdeal_comap (i : Y ⟶ X) {M : X.Modules} (a : LineBundleAtlas M)
    {J : Type} (s : J → Γ(M, ⊤)) :
    (⨆ j, sectionZeroIdealSheaf a (s j)).comap i =
      ⨆ j, sectionZeroIdealSheaf (a.nativePullback i) (affinePullbackUnitTop i M (s j)) := by
  rw [(Scheme.IdealSheafData.map_gc i).l_iSup]
  exact iSup_congr fun j => sectionZeroIdealSheaf_comap i a (s j)

/-- Every actual original semi-valuation reads the SAME entire original
generated section ideal under the genuine restriction map. -/
theorem idealVal_actual_sectionFamily_pullback [IsProper fX] [IsProper fY]
    (i : Y ⟶ X) (hi : i ≫ fX = fY) {M : X.Modules} (a : LineBundleAtlas M)
    {J : Type} (s : J → Γ(M, ⊤)) (w : BerkovichPoint fY) :
    w.idealVal (⨆ j, sectionZeroIdealSheaf (a.nativePullback i)
        (affinePullbackUnitTop i M (s j))) =
      (schemeAnMap i hi w).idealVal (⨆ j, sectionZeroIdealSheaf a (s j)) := by
  rw [← sectionFamilyIdeal_comap]
  exact idealVal_comap_schemeAnMap i hi w _

/-- The literal original -K⁻¹ minimum-of-section-values formula commutes
with actual restriction, including its original infinite/common-zero values. -/
theorem normalized_actual_sectionFamily_pullback [IsProper fX] [IsProper fY]
    (i : Y ⟶ X) (hi : i ≫ fX = fY) {M : X.Modules} (a : LineBundleAtlas M)
    {J : Type} (s : J → Γ(M, ⊤)) (K : ℕ) (w : BerkovichPoint fY) :
    -((w.idealVal (⨆ j, sectionZeroIdealSheaf (a.nativePullback i)
        (affinePullbackUnitTop i M (s j))) / K : ℝ≥0∞) : EReal) =
      -(((schemeAnMap i hi w).idealVal (⨆ j, sectionZeroIdealSheaf a (s j)) / K : ℝ≥0∞) : EReal) := by
  rw [idealVal_actual_sectionFamily_pullback i hi a s w]

end SGPT.NAPotential.TraceComparison
