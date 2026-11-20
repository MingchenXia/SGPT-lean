import SGPT.Unibranch.ComplexSpaceRamifiedDiskLift
import SGPT.Unibranch.ComplexPowerDiscCriterion
import SGPT.Unibranch.ComplexDiscPowerSubharmonic
import SGPT.Unibranch.ComplexSpacePSHProperDescent

/-! Genuine original proper descent passes actual disk germs. All lift and
source raw-PSH data are produced from original objects, not supplied certificates.
Blueprint: complex-space-proper-disc-descent.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry Metric
open scoped Topology
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.SourceReducedComplexSpace

private theorem modelPullback_at_point {Z : SourceReducedComplexSpace} {n : ℕ}
    {U : Opens (FirstPass.ComplexModel n)}
    (F : (Pending.HironakaReducedComplexAnalyticSpaces.modelOver U (univ : Set U)).left ⟶ Z.obj.left)
    (ψ : Z.obj.left → EReal) (c : (univ : Set U)) :
    modelPullback F ψ c.val.val = ψ (F.base c) := by
  unfold modelPullback
  split_ifs with hc
  · rfl
  · exact False.elim (hc c.val.property)

/-- The SAME original USC descent has a genuine disc-PSH germ at zero for
EVERY actual disk; finite lifting and all source reader data are internal. -/
theorem discPullback_pshAt_zero_of_proper {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    {ψ : Y.obj.left → EReal} (hψ : ∀ y,Y.IsLocallyAmbientPSHAt ψ y)
    {φ : X.obj.left → EReal} (hφ : UpperSemicontinuous φ)
    (hcoh : ∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) (f : unitDisc ⟶ X) :
    PlurisubharmonicAt (discPullback f φ) (0 : ℂ) := by
  obtain ⟨r,hr,hr1,k,hk,gLift,hlift⟩ := SGPT.Unibranch.exists_ramified_disk_lift π hπ f
  have hraw := discPshOn_modelPullback hψ gLift.hom.left (Over.w gLift.hom)
  have hscalar := hraw.comp_affine discCoordinate 0
  have hdomain : (fun z : ℂ => 0+discCoordinate z) ⁻¹'
      (smallDiskOpens r : Set (FirstPass.ComplexModel 1)) = ball 0 r := by
    ext z
    simp [smallDiskOpens,norm_discCoordinate]
  rw [hdomain] at hscalar
  have heq : EqOn (fun z : ℂ => modelPullback gLift.hom.left ψ (0+discCoordinate z))
      (fun z : ℂ => discPullback f φ (z^k)) (ball 0 r) := by
    intro z hz
    have hzD : discCoordinate z ∈ smallDiskOpens r := by
      simpa [smallDiskOpens,norm_discCoordinate,mem_ball_zero_iff] using hz
    let q : (univ : Set (smallDiskOpens r)) := ⟨⟨discCoordinate z,hzD⟩,trivial⟩
    have hzUnit : z ∈ ball (0 : ℂ) 1 := ball_subset_ball hr1 hz
    have hzPow : z^k ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff,norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hzUnit) (Nat.ne_of_gt hk)
    have hzPowD := discCoordinate_mem_unitDiscOpens hzPow
    have hpoint : (smallDiskInclusion r hr1 ≫ discPowerMorphism k hk).hom.left.base q =
        (⟨⟨discCoordinate (z^k),hzPowD⟩,trivial⟩ : (univ : Set unitDiscOpens)) := by
      apply Subtype.ext
      apply Subtype.ext
      change ((discPowerMorphism k hk).hom.left.base ((smallDiskInclusion r hr1).hom.left.base q)).val.val = _
      rw [discPowerMorphism_apply]
      change discCoordinate ((discCoordinate z 0)^k) = discCoordinate (z^k)
      rw [discCoordinate_apply_zero]
    have hsource : modelPullback gLift.hom.left ψ (0+discCoordinate z) =
        ψ (gLift.hom.left.base q) := by
      erw [zero_add]
      exact modelPullback_at_point gLift.hom.left ψ q
    have htarget : discPullback f φ (z^k) =
        φ (f.hom.left.base (⟨⟨discCoordinate (z^k),hzPowD⟩,trivial⟩ : (univ : Set unitDiscOpens))) :=
      modelPullback_at_point f.hom.left φ ⟨⟨discCoordinate (z^k),hzPowD⟩,trivial⟩
    have hcoherent : ψ (gLift.hom.left.base q) =
        φ (f.hom.left.base ((smallDiskInclusion r hr1 ≫ discPowerMorphism k hk).hom.left.base q)) :=
      (hcoh _).symm.trans (congrArg φ (hlift q))
    exact hsource.trans (hcoherent.trans
      ((congrArg (fun t : (univ : Set unitDiscOpens) => φ (f.hom.left.base t)) hpoint).trans htarget.symm))
  have hrawPow := hscalar.congr heq
  have hRk : r^k ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hr.le hr1 k
  have htarget := RamifiedPower.discPshOn_of_comp_pow k hk hr
    ((discPullback_upperSemicontinuousOn f hφ).mono (ball_subset_ball hRk)) hrawPow
  exact ⟨ball 0 (r^k),isOpen_ball,mem_ball_self (pow_pos hr k),htarget⟩

/-- ORIGINAL hπ+hX and actual upstairs local PSH internally produce the
unique USC descent and genuine zero-germ test for EVERY actual original disk. -/
theorem exists_unique_usc_descent_with_disc_germs {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {ψ : Y.obj.left → EReal} (hψ : ∀ y,Y.IsLocallyAmbientPSHAt ψ y) :
    ∃! φ : X.obj.left → EReal,UpperSemicontinuous φ ∧
      (∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y) ∧
      ∀ f : unitDisc ⟶ X,PlurisubharmonicAt (discPullback f φ) (0 : ℂ) := by
  obtain ⟨φ,⟨hφ,hcoh⟩,hunique⟩ := exists_unique_usc_descent_of_connected_proper_fibers
    π hπ.1 (hπ.isConnected_fiber_of_isUnibranch hX) hψ
  refine ⟨φ,⟨hφ,hcoh,fun f => discPullback_pshAt_zero_of_proper π hπ hψ hφ hcoh f⟩,?_⟩
  intro χ hχ
  exact hunique χ ⟨hχ.1,hχ.2.1⟩

end SGPT.Unibranch.SourceReducedComplexSpace
