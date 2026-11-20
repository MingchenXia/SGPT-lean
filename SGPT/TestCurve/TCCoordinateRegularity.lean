import SGPT.TestCurve.TCActualCentralRestriction

/-! Actual original coordinate regularity on all opens and global power sections.
Blueprint: tc-coordinate-regularity.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCOko

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- The actual nonempty original off-central fibre rules out the zero coordinate. -/
theorem totalCoordinate_ne_zero [Nonempty X] : tFun T.toLine ≠ 0 := by
  intro h
  let x : (offCentral T.toLine).toScheme := Classical.arbitrary _
  have hx := x.property
  change x.val ∈ T.space.basicOpen (tFun T.toLine) at hx
  simp [h] at hx

variable [IsIntegral X] (E : ClosedProjectiveEmbedding f)

include E in
/-- Literal original coordinate restriction is a nonzerodivisor on EVERY open. -/
theorem totalCoordinate_regular_on_open (V : T.space.Opens) :
    T.space.presheaf.map V.leTop.op (tFun T.toLine) ∈ nonZeroDivisors Γ(T.space,V) := by
  let : IsIntegral T.space := T.isIntegral_space_of_embedding E
  apply mem_nonZeroDivisors_iff_left.mpr
  intro r hr
  apply TopCat.Presheaf.IsSheaf.section_ext T.space.sheaf.property
  intro x hx
  let : Nonempty V := ⟨⟨x,hx⟩⟩
  have hcoord : T.space.presheaf.map V.leTop.op (tFun T.toLine) ≠ 0 := by
    intro h
    apply totalCoordinate_ne_zero T
    apply map_injective_of_isIntegral (X := T.space) V.leTop
    simpa only [map_zero] using h
  have hr0 : r=0 := (mul_eq_zero.mp hr).resolve_left hcoord
  refine ⟨V,le_rfl,hx,?_⟩
  simp only [hr0,map_zero]

include E in
/-- The original SAME multiplication-by-t map is injective in EVERY degree. -/
theorem tMul_injective (m : ℕ) : Function.Injective (tMul T m) := by
  let : IsIntegral T.space := T.isIntegral_space_of_embedding E
  intro s u h
  apply T.eq_of_epsCoeff_eq
  intro j
  have hc := congrArg (fun q => T.epsCoeff m j q) h
  rw [epsCoeff_tMul,epsCoeff_tMul] at hc
  have hi := congrArg (fun q => (T.tUnit j)⁻¹.val*q) hc
  simpa only [← mul_assoc,← Units.val_mul,inv_mul_cancel,Units.val_one,one_mul] using hi

end SGPT.TestCurve.CentralFiber
