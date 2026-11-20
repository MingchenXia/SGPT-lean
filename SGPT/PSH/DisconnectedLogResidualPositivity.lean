import SGPT.PSH.ActualGeometricLogMetric
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable

/-! Genuine residual nef/Kähler positivity on arbitrary compact native
manifolds, with support-interior emptiness from ORIGINAL nondegeneracy. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open ResidualNefReduction ThetaPshCodimTwoExtension PshAnalyticSetExtension
open ManifoldTubePositivity
open scoped Topology Manifold ContDiff
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ORIGINAL local nondegeneracy forbids any nonempty open subset in the
SAME actual logarithmic divisor support, even on disconnected manifolds. -/
theorem actual_log_support_interior_empty
    {θ : ClosedRealOneOneForm n M} {E : MeteredEffectiveQDivisor n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (L : HasLogSingularitiesAlong E u) :
    interior E.support=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y,hy,hyfin⟩ := hu.2 x (interior E.support) isOpen_interior hx
  exact L.notMem_support_of_ne_bot hyfin (interior_subset hy)

/-- Actual bounded logarithmic residual plus ORIGINAL theta-PSH gives nef
on the whole compact native manifold, without connectedness or nonempty
premises. Existing genuine removability/smoothing provide all approximation. -/
theorem actual_residual_nef [CompactSpace M] (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {E : MeteredEffectiveQDivisor n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (L : HasLogSingularitiesAlong E u) :
    NefWithRespectTo omega (θ-E.curvature) := by
  let A := E.support
  let b : M → EReal := fun x => (L.residual x : EReal)
  have hoff : ThetaPshOff (θ-E.curvature).val A b := thetaPshOff_residual hu.1 L
  have hbound : LocallyBoundedAboveOff A b := L.locallyBoundedAboveOff
  have hA : IsComplexAnalyticSubset (n := n) A := ResidualNef.isComplexAnalyticSubset_support E
  have hpot : HasSmoothLocalPotentials (θ-E.curvature).val :=
    ResidualNef.hasSmoothLocalPotentials_sub hu.1.hasSmoothLocalPotentials
      (ResidualNef.hasSmoothLocalPotentials_curvature E)
  have hext : ThetaPlurisubharmonic (θ-E.curvature).val (extensionAcross A b) :=
    thetaPlurisubharmonic_extensionAcross_of_localClosure hA.isClosed hoff
      (PshAnalyticRemovable.thetaPshLocalClosure_of_isComplexAnalyticSubset hpot hA hoff hbound)
  have hAi : interior A=∅ := actual_log_support_interior_empty hu L
  have hupp : ∀ x,extensionAcross A b x≤(L.bound : EReal) :=
    ResidualNef.extensionAcross_le_of_forall_le
      (fun y => EReal.coe_le_coe_iff.mpr (L.le_bound y))
  have hlow : ∀ x,((-L.bound : ℝ) : EReal)≤extensionAcross A b x :=
    ResidualNef.le_extensionAcross_of_interior_eq_empty hAi
      (fun y => EReal.coe_le_coe_iff.mpr (L.neg_bound_le y))
  intro ε hε
  obtain ⟨h,hh,hpos,_hvalue,_hupper⟩ :=
    BoundedPotentialSmoothing.demailly1992_exists_chartSmooth_of_bounded_thetaPsh
      omega (θ-E.curvature) hext hlow hupp hε
  exact ⟨h,hh,hpos⟩

/-- The ACTUAL Kahler-current lower background and produced bounded log
residual give a smooth Kahler representative, without a connectedness flag. -/
theorem actual_residual_kahler [CompactSpace M]
    {θ : ClosedRealOneOneForm n M} {E : MeteredEffectiveQDivisor n M} {u : M → EReal}
    (hu : IsKahlerCurrentPotential θ u) (L : HasLogSingularitiesAlong E u) :
    ∃ (h : M → ℝ) (hh : ChartSmooth (n := n) h),
      ((θ-E.curvature)+ddcClosedForm h hh).val.IsKahler := by
  obtain ⟨omega,hpot⟩ := hu
  obtain ⟨h,hh,hpos⟩ := actual_residual_nef omega (θ := θ-omega.form)
    (E := E) (u := u) (by simpa using hpot) L (1/2) (by norm_num)
  refine ⟨h,hh,⟨fun e z hz => ⟨?_,?_⟩,((θ-E.curvature)+ddcClosedForm h hh).2.1⟩⟩
  · exact ((θ-E.curvature)+ddcClosedForm h hh).2.2 e z hz
  · intro v hv
    have hkey := hpos e z hz v
    have hstrict := (omega.isKahler.1 e z hz).2 v hv
    rw [BlowupBigPullback.coeff_sub,BlowupBigPullback.coeff_sub] at hkey
    have hcoeff : ((θ-E.curvature)+ddcClosedForm h hh).val.coeff e z=
        (θ.val.coeff e z-E.curvature.val.coeff e z)+smoothDDC (fun y => h (e.val.symm y)) z := by
      rw [ClosedRealOneOneForm.coeff_add,BlowupBigPullback.coeff_sub,ddcClosedForm_coeff]
    rw [hcoeff]
    simp only [ContinuousAlternatingMap.sub_apply,ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hkey ⊢
    linarith

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
