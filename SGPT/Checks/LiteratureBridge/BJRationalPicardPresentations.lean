import SGPT.Checks.LiteratureBridge.BJNativePicard
import Mathlib.Data.Rat.Cast.Defs

/-! Actual positive-denominator line representatives of the SAME scheme
rational Picard group. All line and atlas outputs are produced internally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.NativePicard
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules SGPT.Foundations.Schemes
open scoped TensorProduct
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {X : Scheme.{0}}

/-- Actual tensor induction produces one positive common denominator and
one actual native Picard element for every rational Picard element. -/
theorem exists_positive_denominator (z : RationalPicardSpace X) :
    ∃ m : ℕ,0<m ∧ ∃ a : Additive X.Pic,
      z=(1/(m:ℚ))•rationalizePicard X a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1,by omega,0,by rw [map_zero,smul_zero]⟩
  | tmul r a =>
    refine ⟨r.den,r.den_pos,r.num•a,?_⟩
    rw [map_zsmul,← Int.cast_smul_eq_zsmul ℚ r.num,smul_smul]
    have ht : r⊗ₜ[ℤ] a=r•rationalizePicard X a := by
      change r⊗ₜ[ℤ] a=r•((1:ℚ)⊗ₜ[ℤ] a)
      rw [TensorProduct.smul_tmul']
      simp only [smul_eq_mul,mul_one]
    rw [ht]
    congr 1
    rw [one_div,mul_comm,← div_eq_mul_inv,r.num_div_den]
  | add z w hz hw =>
    obtain ⟨m,hm,a,rfl⟩ := hz
    obtain ⟨n,hn,b,rfl⟩ := hw
    refine ⟨m*n,Nat.mul_pos hm hn,n•a+m•b,?_⟩
    rw [map_add,map_nsmul,map_nsmul,smul_add,
      ← Nat.cast_smul_eq_nsmul ℚ n,← Nat.cast_smul_eq_nsmul ℚ m,smul_smul,smul_smul]
    have hmQ : (m:ℚ)≠0 := by exact_mod_cast hm.ne'
    have hnQ : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
    have hc0 : (1/((m*n:ℕ):ℚ))*(n:ℚ)=1/(m:ℚ) := by
      push_cast
      field_simp [hmQ,hnQ]
    have hc1 : (1/((m*n:ℕ):ℚ))*(m:ℚ)=1/(n:ℚ) := by
      push_cast
      field_simp [hmQ,hnQ]
    rw [hc0,hc1]

/-- The same actual skeleton quotient supplies its native sheaf representative. -/
def picardRepresentative (a : X.Pic) : X.Modules := a.val.out

theorem picardRepresentative_isInvertible (a : X.Pic) :
    IsInvertible (picardRepresentative a) := by
  apply isInvertible_of_isUnit_toSkeleton
  change IsUnit (toSkeleton a.val.out)
  rw [show toSkeleton a.val.out=a.val from Quotient.out_eq a.val]
  exact a.isUnit

/-- Actual native open-cover invertibility internally gives a rank-one atlas
of the same original sheaf, via genuine restriction/over-site equivalences. -/
def atlasOfInvertible {L : X.Modules} (hL : IsInvertible L) : LineBundleAtlas L := by
  classical
  let I : Type := hL.choose
  let U : I→X.Opens := hL.choose_spec.choose
  have hU : iSup U=⊤ ∧ ∀ i,Nonempty ((pullback (U i).ι).obj L≅unitObj (U i).toScheme) :=
    hL.choose_spec.choose_spec
  exact {
    I:=I
    opens:=U
    covers:=fun x => TopologicalSpace.Opens.mem_iSup.mp (by rw [hU.1];trivial)
    frame:=fun i => overTrivializationOfRestrictIso L (U i)
      (restrictIsoOfPullbackIso L (U i) (hU.2 i).some) }

theorem linePicardClass_representative (a : X.Pic) :
    linePicardClass (atlasOfInvertible (picardRepresentative_isInvertible a))=a := by
  apply Units.ext
  rw [linePicardClass_val]
  exact Quotient.out_eq a.val

/-- EVERY actual rational Picard class has a genuine native sheaf/atlas
presentation with positive denominator, with no supplied realization field. -/
theorem exists_actual_line_presentation (z : RationalPicardSpace X) :
    ∃ (L : X.Modules) (a : LineBundleAtlas L) (m : ℕ),0<m ∧
      z=(1/(m:ℚ))•rationalPicardClass a := by
  obtain ⟨m,hm,c,hc⟩ := exists_positive_denominator z
  refine ⟨picardRepresentative c.toMul,
    atlasOfInvertible (picardRepresentative_isInvertible c.toMul),m,hm,?_⟩
  rw [rationalPicardClass,linePicardClass_representative]
  exact hc

end SGPT.NAPotential.BJ.NativePicard
