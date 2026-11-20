import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import SGPT.Unibranch.ComplexSpaceFornaessNarasimhan
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The actual original power cover of the actual original disk.
Blueprint: complex-disc-power.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set CategoryTheory AlgebraicGeometry Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SourceReducedComplexSpace

private theorem power_maps_unitDisc (k : ℕ) (hk : 0 < k)
    {z : ComplexModel 1} (hz : z ∈ unitDiscOpens) :
    discCoordinate ((z 0)^k) ∈ unitDiscOpens := by
  change discCoordinate ((z 0)^k) ∈ ball 0 1
  rw [mem_ball_zero_iff]
  rw [norm_discCoordinate,norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (norm_le_of_mem_unitDiscOpens hz) (Nat.ne_of_gt hk)

/-- The actual original holomorphic disk power morphism, including its
actual analytic structure-sheaf map over the original complex point. -/
def discPowerMorphism (k : ℕ) (hk : 0 < k) : unitDisc ⟶ unitDisc :=
  analyticModelMorphism isComplexAnalyticSubset_univ isComplexAnalyticSubset_univ
    (fun z => discCoordinate ((z 0)^k))
    ((discCoordinate.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff.pow k)).contDiffOn)
    (fun _ hz => power_maps_unitDisc k hk hz) (fun _ => trivial)

/-- The actual original point map has the SAME literal complex power. -/
@[simp] theorem discPowerMorphism_apply (k : ℕ) (hk : 0 < k)
    (c : (univ : Set unitDiscOpens)) :
    ((discPowerMorphism k hk).hom.left.base c).val.val = discCoordinate ((c.val.val 0)^k) := rfl

private theorem norm_lt_one_of_pow {z w : ℂ} {k : ℕ}
    (hpow : z^k = w) (hw : ‖w‖ < 1) : ‖z‖ < 1 := by
  by_contra hz
  have hp : 1 ≤ ‖z‖^k := one_le_pow₀ (le_of_not_gt hz)
  rw [← norm_pow,hpow] at hp
  exact (not_lt_of_ge hp) hw

/-- Every point of the SAME actual original disk has an actual finite
power root in that disk. -/
theorem discPowerMorphism_surjective (k : ℕ) (hk : 0 < k) :
    Function.Surjective (discPowerMorphism k hk).hom.left.base := by
  intro c
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (c.val.val 0) hk
  have hzn : ‖z‖ < 1 := norm_lt_one_of_pow hz (norm_le_of_mem_unitDiscOpens c.val.property)
  let d : (univ : Set unitDiscOpens) :=
    ⟨⟨discCoordinate z,by simpa [unitDiscOpens,norm_discCoordinate] using hzn⟩,trivial⟩
  refine ⟨d,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [discPowerMorphism_apply]
  change discCoordinate ((discCoordinate z 0)^k) = c.val.val
  rw [discCoordinate_apply_zero,hz]
  ext i
  fin_cases i
  simp [discCoordinate]

/-- Literal original pullback under the SAME original composed disk. -/
theorem discPullback_comp_power {X : SourceReducedComplexSpace}
    (f : unitDisc ⟶ X) (φ : X.obj.left → EReal) (k : ℕ) (hk : 0 < k)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    discPullback (discPowerMorphism k hk ≫ f) φ t = discPullback f φ (t^k) := by
  have htD := discCoordinate_mem_unitDiscOpens ht
  have htp : t^k ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp ht) (Nat.ne_of_gt hk)
  have htpD := discCoordinate_mem_unitDiscOpens htp
  unfold discPullback modelPullback
  rw [dif_pos htD,dif_pos htpD]
  change φ (f.hom.left.base ((discPowerMorphism k hk).hom.left.base
      ⟨⟨discCoordinate t,htD⟩,trivial⟩)) =
    φ (f.hom.left.base ⟨⟨discCoordinate (t^k),htpD⟩,trivial⟩)
  apply congrArg φ
  apply congrArg f.hom.left.base
  apply Subtype.ext
  apply Subtype.ext
  rw [discPowerMorphism_apply]
  simp only [discCoordinate_apply_zero]

/-- Actual original nontriviality is equivalent before and after the
finite power; the root witness and unit-disk condition are produced. -/
theorem discPullback_comp_power_nontrivial_iff {X : SourceReducedComplexSpace}
    (f : unitDisc ⟶ X) (φ : X.obj.left → EReal) (k : ℕ) (hk : 0 < k) :
    (∃ t ∈ ball (0 : ℂ) 1,discPullback (discPowerMorphism k hk ≫ f) φ t ≠ ⊥) ↔
      ∃ t ∈ ball (0 : ℂ) 1,discPullback f φ t ≠ ⊥ := by
  constructor
  · rintro ⟨t,ht,hfin⟩
    have htp : t^k ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff,norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp ht) (Nat.ne_of_gt hk)
    exact ⟨t^k,htp,(discPullback_comp_power f φ k hk ht) ▸ hfin⟩
  · rintro ⟨t,ht,hfin⟩
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq t hk
    have hzn : z ∈ ball (0 : ℂ) 1 := by
      exact mem_ball_zero_iff.mpr (norm_lt_one_of_pow hz (mem_ball_zero_iff.mp ht))
    refine ⟨z,hzn,?_⟩
    rw [discPullback_comp_power f φ k hk hzn,hz]
    exact hfin

end SGPT.Unibranch.SourceReducedComplexSpace
