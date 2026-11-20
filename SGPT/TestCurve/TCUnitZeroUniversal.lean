import SGPT.TestCurve.TCCoordinateRegularity
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme

/-! Entire zero schemes of actual functions, with their genuine universal property.
Blueprint: tc-unit-zero-universal.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable (Y : Scheme.{0}) (r : Γ(Y, ⊤))

abbrev unitFunctionSection : Γ((trivialIntrinsicLineBundle Y).sheaf, ⊤) := r

abbrev unitZeroScheme : Scheme.{0} :=
  sectionZeroSubscheme (trivialIntrinsicLineBundle Y).atlas (unitFunctionSection Y r)

abbrev unitZeroInclusion : unitZeroScheme Y r ⟶ Y :=
  sectionZeroι (trivialIntrinsicLineBundle Y).atlas (unitFunctionSection Y r)

/-- The actual trivial-line evaluation ideal is the genuine principal ideal sheaf. -/
theorem unitZeroIdeal_eq :
    sectionZeroIdealSheaf (trivialIntrinsicLineBundle Y).atlas (unitFunctionSection Y r) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {r}) := by
  apply Scheme.IdealSheafData.ext
  funext U
  change sectionZeroIdeal (SheafOfModules.unit Y.ringCatSheaf) r U.val = _
  let e : LocalBundleFrame (SheafOfModules.unit Y.ringCatSheaf) ⊤ := Iso.refl _
  rw [sectionZeroIdeal_eq_span_frame (L := SheafOfModules.unit Y.ringCatSheaf) (show Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) from r) e U.val.leTop]
  change Ideal.span {Y.presheaf.map U.val.leTop.op r} = _
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
  rfl

/-- Actual global restriction to the ENTIRE zero scheme annihilates the function. -/
theorem unitZero_coordinate_zero : (unitZeroInclusion Y r).appTop r = 0 := by
  let j := unitZeroInclusion Y r
  apply TopCat.Presheaf.IsSheaf.section_ext (unitZeroScheme Y r).sheaf.property
  intro z hz
  obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show j z ∈ (⊤ : Y.Opens) from trivial)
  let A : Y.affineOpens := ⟨U,hU⟩
  have hm : Y.presheaf.map U.leTop.op r ∈ j.ker.ideal A := by
    rw [show j.ker = sectionZeroIdealSheaf (trivialIntrinsicLineBundle Y).atlas
      (unitFunctionSection Y r) from Scheme.IdealSheafData.ker_subschemeι _]
    rw [unitZeroIdeal_eq]
    change Y.presheaf.map U.leTop.op r ∈ (Ideal.span {r}).map (Y.presheaf.map U.leTop.op).hom
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton r))
  have hzero : j.app U (Y.presheaf.map U.leTop.op r) = 0 :=
    j.ideal_ker_le A hm
  have hn := congrArg (fun q => q r) (j.naturality U.leTop.op)
  change j.app U (Y.presheaf.map U.leTop.op r) =
    (unitZeroScheme Y r).presheaf.map (j ⁻¹ᵁ U).leTop.op (j.appTop r) at hn
  refine ⟨j ⁻¹ᵁ U, le_top, hzU, ?_⟩
  change (unitZeroScheme Y r).presheaf.map (j ⁻¹ᵁ U).leTop.op (j.appTop r) =
    (unitZeroScheme Y r).presheaf.map (j ⁻¹ᵁ U).leTop.op 0
  rw [← hn,hzero,map_zero]

variable {Z : Scheme.{0}} (g : Z ⟶ Y)

/-- Annihilation of the original function gives the actual closed-subscheme factorization criterion. -/
theorem unitZero_ker_le (h : g.appTop r = 0) :
    (unitZeroInclusion Y r).ker ≤ g.ker := by
  rw [show (unitZeroInclusion Y r).ker =
    sectionZeroIdealSheaf (trivialIntrinsicLineBundle Y).atlas (unitFunctionSection Y r)
    from Scheme.IdealSheafData.ker_subschemeι _, unitZeroIdeal_eq]
  apply Scheme.IdealSheafData.le_ofIdeals_iff.mpr
  intro U
  change (Ideal.span {r}).map (Y.presheaf.map U.val.leTop.op).hom ≤ RingHom.ker (g.app U.val).hom
  rw [Ideal.map_span,Set.image_singleton]
  apply Ideal.span_le.mpr
  intro s hs
  obtain rfl := Set.mem_singleton_iff.mp hs
  change g.app U.val (Y.presheaf.map U.val.leTop.op r) = 0
  have hn := congrArg (fun q => q r) (g.naturality U.val.leTop.op)
  change g.app U.val (Y.presheaf.map U.val.leTop.op r) =
    Z.presheaf.map (g ⁻¹ᵁ U.val).leTop.op (g.appTop r) at hn
  rw [hn,h,map_zero]

/-- Genuine factorization through the same entire zero subscheme. -/
def unitZeroLift (h : g.appTop r = 0) : Z ⟶ unitZeroScheme Y r :=
  IsClosedImmersion.lift (unitZeroInclusion Y r) g (unitZero_ker_le Y r g h)

theorem unitZeroLift_fac (h : g.appTop r = 0) :
    unitZeroLift Y r g h ≫ unitZeroInclusion Y r = g :=
  IsClosedImmersion.lift_fac _ _ _

/-- The actual zero subscheme represents annihilation, including all nilpotents. -/
theorem unitZero_factorization (h : g.appTop r = 0) :
    ∃! k : Z ⟶ unitZeroScheme Y r, k ≫ unitZeroInclusion Y r = g := by
  refine ⟨unitZeroLift Y r g h, unitZeroLift_fac Y r g h, ?_⟩
  intro k hk
  apply (cancel_mono (unitZeroInclusion Y r)).mp
  exact hk.trans (unitZeroLift_fac Y r g h).symm

end SGPT.TestCurve.CentralFiber
