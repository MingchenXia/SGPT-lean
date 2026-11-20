import SGPT.Trace.OptimalNativeNormalBackground
import SGPT.Trace.OTMarginPole
import SGPT.Foundations.Analysis.Pending.LocalGiraudTransform

/-!
# Actual flattening data with literal last coordinate equal to the original normal

The SAME-W inverse construction retains the normal equation, not merely its
zero set. It feeds original physical-volume critical-error vanishing.
Blueprint: work/sgpt-resume-20261114/bert-e2-exact-normal/blueprint/bert-e2-exact-normal.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniExactNormalCoordinates
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Trace.OTMargin SGPT.Trace.BertiniPencilNormal SGPT.Trace.OptimalNativeNormalBackground

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual same-W flattening: literal last=f, original source point and
original recentering retained. No normal-coordinate certificate supplied. -/
theorem exists_exact_normal_flatData {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {x : X}
    (hsub : Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x)) (hfx : f x = 0) :
    ∃ (hn : 0 < n) (F : FlatData n (n - 1) X {y | f y = 0}),
      x ∈ F.ambSource ∧ fcoord F x = 0 ∧
      ∀ y ∈ F.ambSource, (fcoord F y) ⟨n - 1, Nat.sub_lt hn one_pos⟩ = f y := by
  have hhol : ∀ y, HolomorphicAt n f y := fun _ =>
    Eventually.of_forall fun y => hf.contMDiffAt.mdifferentiableAt (by simp)
  obtain ⟨v, hv⟩ := hsub (1 : ℂ)
  change ComplexModel n at v
  rw [mfderiv_scalar_eq_chart (hf.contMDiffAt.mdifferentiableAt (by simp))] at hv
  have hd : chartDeriv (complexChartAt (n := n) x) v f x ≠ 0 := by
    change fderiv ℂ (f ∘ (complexChartAt (n := n) x).val.symm)
      ((complexChartAt (n := n) x).val x) v ≠ 0
    intro hzero
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (hv.symm.trans hzero)
  obtain ⟨hn, W, hWs, hWinj, hWu⟩ := LocalGiraudTransform.exists_hypersurface_coords
    (hhol x) (mem_complexChartAt_source x) hd
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := BlowupSNCTransform.exists_recentred_coords
    (chartAt (ComplexModel n) x).open_source
    (fun y hy => hWs y hy (hhol y)) (mem_chart_source _ x) hWinj
  have hplane : ∀ y, W y ∈ complexCoordinatePlane n (n - 1) ↔ f y = 0 := fun y => by
    rw [LocalGiraudTransform.mem_plane_pred_iff hn, hWu]
  let F : FlatData n (n - 1) X {y | f y = 0} := {
    amb := complexChartAt (n := n) x
    flat := Θ.toOpenPartialHomeomorph
    differentiableOn_flat := Θ.toFun_holomorphic
    differentiableOn_flat_symm := Θ.invFun_holomorphic
    flat_source_subset := hΘt
    mem_iff := fun y hy hyΘ => by
      change f y = 0 ↔ Θ.toFun ((complexChartAt (n := n) x).val y) ∈ complexCoordinatePlane n (n - 1)
      rw [(hΘ hy hyΘ).2, BlowupStrictSubmanifold.sub_mem_plane_iff ((hplane x).mpr hfx)]
      exact (hplane y).symm
    base := x
    base_mem := hfx }
  refine ⟨hn, F, ⟨mem_complexChartAt_source x, Θ.center_mem_source⟩, hΘ0, ?_⟩
  intro y hy
  have hval : fcoord F y = W y - W x := (hΘ hy.1 hy.2).2
  rw [hval, PiLp.sub_apply, hWu, hWu, hfx, sub_zero]

/-- The SAME original inverse reads the true normal, not just its zeros. -/
theorem exact_normal_inverse {f : X → ℂ} {F : FlatData n (n - 1) X {y | f y = 0}}
    {j : Fin n} (hF : ∀ y ∈ F.ambSource, (fcoord F y) j = f y)
    {z : ComplexModel n} (hz : z ∈ F.flat.target) : f (finv F z) = z j := by
  have h := hF (finv F z) (finv_mem F hz)
  rw [fcoord_finv F hz] at h
  exact h.symm

/-- Actual normalized native pencil instantiation supplies holomorphy and
surjective original differential from its proved original geometry. -/
theorem exists_exact_pencil_normal_flatData {N : ℕ}
    (p : X → SGPT.Projective.ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1))
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, SGPT.Trace.Bertini.IsSmoothHypersurfaceMember n p
      (SGPT.Trace.BertiniPencilFamily.pencilParameter i a v t.val))
    {ρ : ℝ} (hρ : 0 < ρ) :
    letI := SGPT.Trace.BertiniPencilFamily.familyChartedSpace p i a v U hp hsm
    haveI := SGPT.Trace.BertiniPencilFamily.isComplexManifold_family p i a v U hp hsm
    ∀ (q : SGPT.Trace.BertiniPencilFamily.familyIncidence p i a v U),
      normalizedPencilNormal p i a v U ρ q = 0 →
      ∃ (hn : 0 < n) (F : FlatData n (n - 1)
        (SGPT.Trace.BertiniPencilFamily.familyIncidence p i a v U)
        {y | normalizedPencilNormal p i a v U ρ y = 0}),
        q ∈ F.ambSource ∧ fcoord F q = 0 ∧
        ∀ y ∈ F.ambSource, (fcoord F y) ⟨n - 1, Nat.sub_lt hn one_pos⟩ =
          normalizedPencilNormal p i a v U ρ y := by
  let := SGPT.Trace.BertiniPencilFamily.familyChartedSpace p i a v U hp hsm
  have := SGPT.Trace.BertiniPencilFamily.isComplexManifold_family p i a v U hp hsm
  intro q hq
  exact exists_exact_normal_flatData (contMDiff_normalizedPencilNormal p i a v U hp hsm ρ)
    (surjective_mfderiv_normalizedPencilNormal p i a v U hp hsm hρ q) hq

end SGPT.Trace.BertiniExactNormalCoordinates
