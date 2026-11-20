import SGPT.Toric.SourcePointBlowupOkounkov
import SGPT.Projective.Maps
import SGPT.Toric.PointBlowupHyperplane
import Lean.Elab.Command

section ExceptionalCanonicalFragment001
/- BEGIN OriginalExceptionalCurveDraft; original source SHA256 66079898222ed3df5450dec04370d6e301fcf29ccde6a246c0835188d87475b0 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Toric.BlowdownDraft
open scoped Topology Manifold ContDiff

/-- Actual literal incidence fibre point; membership is manufactured. -/
def exceptionalIncidencePoint (u : SGPT.Projective.ComplexProjectiveSpace 1) : blowupIncidenceSet :=
  ⟨(blowdownOrigin, u), by
    have h1 : blowdownOrigin.rep 1 = 0 :=
      (projective_rep_mk_eq_zero_iff _ _ 1).mpr rfl
    have h2 : blowdownOrigin.rep 2 = 0 :=
      (projective_rep_mk_eq_zero_iff _ _ 2).mpr rfl
    change blowdownOrigin.rep 1 * u.rep 1 = blowdownOrigin.rep 2 * u.rep 0
    rw [h1, h2, zero_mul, zero_mul]⟩

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Actual original exceptional curve, manufactured on the SAME source surface. -/
def originalExceptionalCurve (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    PolytopeToricVariety blowupGenerator hs :=
  (originalBlowupIncidenceHomeomorph hs).symm (exceptionalIncidencePoint u)

theorem originalExceptionalCurve_blowdown (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    originalBlowdown hs (originalExceptionalCurve hs u) = blowdownOrigin := by
  change ((originalBlowupIncidenceHomeomorph hs)
    ((originalBlowupIncidenceHomeomorph hs).symm (exceptionalIncidencePoint u))).val.1 = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem originalExceptionalCurve_direction (u : SGPT.Projective.ComplexProjectiveSpace 1) :
    originalBlowupDirection hs (originalExceptionalCurve hs u) = u := by
  change ((originalBlowupIncidenceHomeomorph hs)
    ((originalBlowupIncidenceHomeomorph hs).symm (exceptionalIncidencePoint u))).val.2 = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem originalExceptionalCurve_injective : Function.Injective (originalExceptionalCurve hs) := by
  intro u v h
  have h' := congrArg (originalBlowupDirection hs) h
  simpa only [originalExceptionalCurve_direction] using h'

theorem originalExceptionalCurve_range :
    range (originalExceptionalCurve hs) = toricPrimeDivisor (blowupExceptionalRay hs) := by
  rw [← originalBlowdown_fibre_origin hs]
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact originalExceptionalCurve_blowdown hs u
  · intro hp
    refine ⟨originalBlowupDirection hs p, ?_⟩
    apply originalBlowup_pair_injective hs
    · exact (originalExceptionalCurve_blowdown hs _).trans hp.symm
    · exact originalExceptionalCurve_direction hs _

def exceptionalChartIndex (i : Fin 2) : Fin 4 := if i = 0 then 0 else 3

def exceptionalOrderedAffine (i : Fin 2) (z : ComplexModel 1) : Fin 2 → ℂ :=
  if i = 0 then ![0, z 0] else ![z 0, 0]

/-- Literal formula on BOTH complete standard affine direction charts. -/
theorem originalExceptionalCurve_affine (i : Fin 2) (z : ComplexModel 1) :
    originalExceptionalCurve hs (SGPT.Projective.ComplexProjectiveSpace.affinePoint i z) =
      blowupOriginalChartPoint hs (exceptionalChartIndex i) (exceptionalOrderedAffine i z) := by
  apply originalBlowup_pair_injective hs
  · rw [originalExceptionalCurve_blowdown, originalBlowdown_chart]
    fin_cases i <;> simp [exceptionalChartIndex, exceptionalOrderedAffine, blowdownChartVector,
      blowdownOrigin]
  · rw [originalExceptionalCurve_direction, originalBlowupDirection_chart]
    fin_cases i <;> simp [exceptionalChartIndex, exceptionalOrderedAffine, blowupDirectionChartVector,
      SGPT.Projective.ComplexProjectiveSpace.affinePoint, SGPT.Projective.ComplexProjectiveSpace.affineLift]
    all_goals
      apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
      refine ⟨1, ?_⟩
      rw [one_smul]
      ext j
      fin_cases j <;> rfl

theorem contDiff_exceptionalNativeAffine (i : Fin 2) :
    ContDiff ℂ ∞ (fun z : ComplexModel 1 =>
      blowupOriginalCoordinates hs (exceptionalChartIndex i) (exceptionalOrderedAffine i z)) := by
  have hcoords (k : Fin 2) :
      ContDiff ℂ ∞ (fun z : ComplexModel 1 => exceptionalOrderedAffine i z k) := by
    fin_cases i <;> fin_cases k
    · exact contDiff_const
    · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff
    · exact contDiff_const
  apply (contDiff_piLp 2).mpr
  intro j
  exact hcoords (blowupOriginalPermutation hs (exceptionalChartIndex i) j)

theorem contMDiff_originalExceptionalCurve_local (i : Fin 2) :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞
      (fun z : ComplexModel 1 =>
        blowupOriginalChartPoint hs (exceptionalChartIndex i) (exceptionalOrderedAffine i z)) := by
  let c : OpenPartialHomeomorph (PolytopeToricVariety blowupGenerator hs) (ComplexModel 2) :=
    originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex (exceptionalChartIndex i))
  have hc : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ c.symm := by
    intro z
    exact (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := PolytopeToricVariety blowupGenerator hs)
        (show c ∈ atlas (ComplexModel 2) (PolytopeToricVariety blowupGenerator hs) from
          ⟨blowupVertex (exceptionalChartIndex i), rfl⟩))).contMDiffAt
        (by change c.target ∈ 𝓝 z
            rw [show c.target = univ from originalPolytopeNativeModelChart_target _ _ _]
            exact Filter.univ_mem)
  exact hc.comp (contDiff_exceptionalNativeAffine hs i).contMDiff

/-- Genuine global holomorphy in the actual existing P1 and original X atlases. -/
theorem contMDiff_originalExceptionalCurve :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞ (originalExceptionalCurve hs) := by
  intro u
  let i := SGPT.Projective.ComplexProjectiveSpace.chartIndex u
  let c := SGPT.Projective.ComplexProjectiveSpace.affineChart i
  have hu : u ∈ c.source := SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex u
  have hc := SGPT.Projective.ComplexProjectiveSpace.contMDiffAt_affineChart i hu
  apply ((contMDiff_originalExceptionalCurve_local hs i).contMDiffAt.comp u hc).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hu] with v hv
  calc
    originalExceptionalCurve hs v = originalExceptionalCurve hs (c.symm (c v)) :=
      congrArg (originalExceptionalCurve hs) (c.left_inv hv).symm
    _ = _ := originalExceptionalCurve_affine hs i (c v)

theorem isClosedEmbedding_originalExceptionalCurve : IsClosedEmbedding (originalExceptionalCurve hs) :=
  (contMDiff_originalExceptionalCurve hs).continuous.isClosedEmbedding
    (originalExceptionalCurve_injective hs)

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END OriginalExceptionalCurveDraft -/
end ExceptionalCanonicalFragment001

section ExceptionalCanonicalFragment002
/- BEGIN NativeHolomorphicPullbackLiftDraft; original source SHA256 08e7a0f15416943573d18332857bfe9e161599c0cd0ad5117675244dae1ba45e -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology Manifold ContDiff

/-- The canonical lift of the ACTUAL native pullback total space is holomorphic,
with the genuinely independent native pullback topology and atlas. -/
theorem contMDiff_nativePullbackLift {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (T : HermitianHolomorphicLineBundle n M)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) N M ∞) :
    ContMDiff ((𝓘(ℂ, ComplexModel m)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (@Bundle.Pullback.lift M ℂ T.Fiber N f) := by
  intro x
  let e := trivializationAt ℂ T.Fiber (f x.proj)
  let e' := e.pullback f
  let : MemTrivializationAtlas e' := ⟨e, inferInstance, rfl⟩
  have hx : x ∈ e'.source := by
    apply e'.mem_source.mpr
    exact mem_baseSet_trivializationAt ℂ T.Fiber (f x.proj)
  have he : Bundle.Pullback.lift f x ∈ e.source := hx
  apply (e.contMDiffAt_iff he).mpr
  refine ⟨f.contMDiff.contMDiffAt.comp x (contMDiffAt_proj (f *ᵖ T.Fiber)), ?_⟩
  exact ((e'.contMDiffOn (IB := 𝓘(ℂ, ComplexModel m)) (n := ∞)).contMDiffAt
    (e'.open_source.mem_nhds hx)).snd

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END NativeHolomorphicPullbackLiftDraft -/
end ExceptionalCanonicalFragment002

section ExceptionalCanonicalFragment003
/- BEGIN NativeHolomorphicPullbackMkDraft; original source SHA256 00316d0b7a7e0769925c7d2f873f658868371418c9333ff9fecfd42ef447d05c -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.ExceptionalRestrictionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology Manifold ContDiff

/-- The ACTUAL native pullback chart criterion: holomorphic base and original
physical total-space maps give a holomorphic map to the actual pullback bundle. -/
theorem contMDiff_nativePullbackMk {n m : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (T : HermitianHolomorphicLineBundle n M)
    (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) N M ∞)
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℂ EQ] [TopologicalSpace HQ]
    (IQ : ModelWithCorners ℂ EQ HQ) [TopologicalSpace Q] [ChartedSpace HQ Q]
    (a : Q → N) (b : ∀ q, T.Fiber (f (a q)))
    (ha : ContMDiff IQ 𝓘(ℂ, ComplexModel m) ∞ a)
    (hb : ContMDiff IQ ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun q => (⟨f (a q), b q⟩ : TotalSpace ℂ T.Fiber))) :
    ContMDiff IQ ((𝓘(ℂ, ComplexModel m)).prod (𝓘(ℂ, ℂ))) ∞
      (fun q => (⟨a q, b q⟩ : TotalSpace ℂ (f *ᵖ T.Fiber))) := by
  intro x
  let e := trivializationAt ℂ T.Fiber (f (a x))
  let e' := e.pullback f
  let : MemTrivializationAtlas e' := ⟨e, inferInstance, rfl⟩
  have hx : (⟨a x, b x⟩ : TotalSpace ℂ (f *ᵖ T.Fiber)) ∈ e'.source := by
    apply e'.mem_source.mpr
    exact mem_baseSet_trivializationAt ℂ T.Fiber (f (a x))
  have he : (⟨f (a x), b x⟩ : TotalSpace ℂ T.Fiber) ∈ e.source := by
    apply e.mem_source.mpr
    exact mem_baseSet_trivializationAt ℂ T.Fiber (f (a x))
  exact (e'.contMDiffAt_iff
    (f := fun q => (⟨a q, b q⟩ : TotalSpace ℂ (f *ᵖ T.Fiber))) (x₀ := x) hx).mpr
      ⟨ha x, ((e.contMDiffAt_iff
        (f := fun q => (⟨f (a q), b q⟩ : TotalSpace ℂ T.Fiber)) (x₀ := x) he).mp (hb x)).2⟩

end SGPT.Toric.ExceptionalRestrictionDraft

end
/- END NativeHolomorphicPullbackMkDraft -/
end ExceptionalCanonicalFragment003


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalExceptionalCurveDraft, `NativeHolomorphicPullbackLiftDraft, `NativeHolomorphicPullbackMkDraft, `ExceptionalHyperplaneRestrictionDraft, `ExceptionalRestrictionFullSectionsDraft, `PhysicalPowerExceptionalValuesDraft, `OriginalFullSectionProjectiveMapDraft, `PhysicalHyperplaneNonseparationDraft, `SourceExceptionalRestrictionDraft, `ExceptionalFlatHermitianMetricDraft, `ExceptionalCurveDegreeDraft, `OriginalHyperplaneDivisorPullbackDraft, `ActualHyperplaneCartierEquationsDraft, `SourceP2BlowupExampleDraft, `OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private source or geometry provider in proper exceptional module: {m}"
