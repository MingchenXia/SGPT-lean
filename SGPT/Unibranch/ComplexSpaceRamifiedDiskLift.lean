import SGPT.Unibranch.ComplexSpaceSmoothDiskScalarChart
import SGPT.Unibranch.ComplexAnalyticPowerNormalForm
import SGPT.Unibranch.ComplexDiscPower

/-! ACTUAL original finite ramified disk lifting. No lifting, normalization,
curve, smooth source, unit root or inverse certificate is an input.
Blueprint: complex-space-ramified-disk-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch
open SourceReducedComplexSpace

/-- The SAME original smaller disk model. -/
def smallDiskOpens (r : ℝ) : Opens (ComplexModel 1) := ⟨ball 0 r,isOpen_ball⟩

/-- Actual original holomorphic disk inclusion, including its real sheaf map. -/
def smallDiskInclusion (r : ℝ) (hr1 : r ≤ 1) : domainSpace (smallDiskOpens r) ⟶ unitDisc :=
  analyticModelMorphism isComplexAnalyticSubset_univ isComplexAnalyticSubset_univ
    (fun z : ComplexModel 1 => z) contDiffOn_id (fun _ hz => ball_subset_ball hr1 hz)
    (fun _ => trivial)

private theorem coordinate_mem_smallDisk {r : ℝ} {z : ComplexModel 1}
    (hz : z ∈ smallDiskOpens r) : z 0 ∈ ball (0 : ℂ) r := by
  have hn : ‖z‖ = ‖z 0‖ := by
    rw [EuclideanSpace.norm_eq,Fin.sum_univ_one,Real.sqrt_sq (norm_nonneg _)]
  change z ∈ ball 0 r at hz
  rw [mem_ball_zero_iff,hn] at hz
  exact mem_ball_zero_iff.mpr hz

/-- Actual finite-power disk lift, produced ONLY from original proper
bimeromorphic π and actual f, preserving all actual sheaf morphisms/point maps. -/
theorem exists_ramified_disk_lift {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (f : unitDisc ⟶ X) :
    ∃ (r : ℝ) (_hr : 0 < r) (hr1 : r ≤ 1) (k : ℕ) (hk : 0 < k)
      (gLift : domainSpace (smallDiskOpens r) ⟶ Y),
      ∀ z : (univ : Set (smallDiskOpens r)),π.hom.left.base (gLift.hom.left.base z) =
        f.hom.left.base ((smallDiskInclusion r hr1 ≫ discPowerMorphism k hk).hom.left.base z) := by
  obtain ⟨T,a,b,t,_hT,_hat,hsquare,C,v,k,u,hk,hu,hu0,hcurve⟩ :=
    exists_regular_disk_germ π hπ f
  obtain ⟨ψ,hψ,hψ0,hψpower⟩ := RamifiedPower.exists_analytic_power_normalizer hu hu0 k hk
  have htψ : Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h := hψ.continuousAt.tendsto
    rwa [hψ0] at h
  have hcurve' : ∀ᶠ s in 𝓝 (0 : ℂ),C.point.val.val+ψ s • v ∈ C.window ∧
      C.scalar (C.point.val.val+ψ s • v) = s^k := by
    filter_upwards [htψ.eventually hcurve,hψpower] with s hs hp
    exact ⟨hs.1,hs.2.trans hp⟩
  obtain ⟨r₀,hr₀,hball⟩ := Metric.eventually_nhds_iff_ball.mp hcurve'
  obtain ⟨rψ,hrψ,hψball⟩ := hψ.exists_ball_analyticOnNhd
  let r : ℝ := min r₀ (min rψ 1)
  have hr : 0 < r := lt_min hr₀ (lt_min hrψ zero_lt_one)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrrψ : r ≤ rψ := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let γ : ComplexModel 1 → ComplexModel C.dim := fun z => C.point.val.val+ψ (z 0) • v
  have hγwindow : ∀ z ∈ smallDiskOpens r,γ z ∈ C.window ∧ C.scalar (γ z) = (z 0)^k := by
    intro z hz
    exact hball (z 0) (ball_subset_ball hrr₀ (coordinate_mem_smallDisk hz))
  have hψOn : ContDiffOn ℂ ∞ ψ (ball (0 : ℂ) rψ) := hψball.contDiffOn_of_completeSpace
  have hparam : ContDiffOn ℂ ∞ (fun z : ComplexModel 1 => ψ (z 0)) (smallDiskOpens r) :=
    hψOn.comp (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff.contDiffOn
      (fun _ hz => ball_subset_ball hrrψ (coordinate_mem_smallDisk hz))
  have hγ : ContDiffOn ℂ ∞ γ (smallDiskOpens r) :=
    contDiffOn_const.add (hparam.smul contDiffOn_const)
  have hmaps : MapsTo γ (smallDiskOpens r) C.ambient :=
    fun z hz => C.window_subset (hγwindow z hz).1
  let L : domainSpace (smallDiskOpens r) ⟶ domainSpace C.ambient :=
    analyticModelMorphism isComplexAnalyticSubset_univ isComplexAnalyticSubset_univ γ hγ hmaps
      (fun _ => trivial)
  let J : domainSpace C.ambient ⟶ T := domainMorphism C.map C.overPoint
  let gLift : domainSpace (smallDiskOpens r) ⟶ Y := L ≫ J ≫ b
  refine ⟨r,hr,hr1,k,hk,gLift,?_⟩
  intro z
  have hzcurve := hγwindow z.val.val z.val.property
  have hread : (a.hom.left.base (J.hom.left.base (L.hom.left.base z))).val.val 0 =
      (z.val.val 0)^k :=
    (C.readback (L.hom.left.base z) hzcurve.1).symm.trans hzcurve.2
  have hpow : ((smallDiskInclusion r hr1 ≫ discPowerMorphism k hk).hom.left.base z).val.val 0 =
      (z.val.val 0)^k := by
    change ((discPowerMorphism k hk).hom.left.base ((smallDiskInclusion r hr1).hom.left.base z)).val.val 0 = _
    rw [discPowerMorphism_apply,discCoordinate_apply_zero]
    rfl
  have hpoint : a.hom.left.base (J.hom.left.base (L.hom.left.base z)) =
      (smallDiskInclusion r hr1 ≫ discPowerMorphism k hk).hom.left.base z := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    fin_cases i
    exact hread.trans hpow.symm
  change π.hom.left.base (b.hom.left.base (J.hom.left.base (L.hom.left.base z))) = _
  exact (hsquare _).trans (congrArg f.hom.left.base hpoint)

end SGPT.Unibranch
