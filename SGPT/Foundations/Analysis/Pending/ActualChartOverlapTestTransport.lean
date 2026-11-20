import SGPT.Foundations.Analysis.Pending.ActualOriginalLocalPotentialCurrentOverlap
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-! Genuine internally constructed constant-form test transport on actual chart overlaps. -/

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.ActualChartOverlapTestTransport
open FirstPass FirstPass.HolomorphicMaps
open _root_.SGPT.Foundations.Analysis.LocalCurrents

private def normalizedAlternation {n q : ℕ} :
    (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) →L[ℝ]
      (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :=
  (q.factorial : ℝ)⁻¹ • LinearMap.mkContinuous
    ({ toFun := ContinuousMultilinearMap.alternatization
       map_add' := fun a b => ContinuousMultilinearMap.alternatization.map_add a b
       map_smul' := by
         intro c a
         ext w
         simp only [ContinuousMultilinearMap.alternatization_apply_apply,
           smul_apply, ContinuousAlternatingMap.smul_apply,
           smul_eq_mul]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro σ _
         rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h] } :
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) →ₗ[ℝ]
        (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ))
    q.factorial (fun a => by
      change ‖∑ σ : Equiv.Perm (Fin q), Equiv.Perm.sign σ • a.domDomCongr σ‖ ≤ _
      refine (norm_sum_le _ _).trans_eq ?_
      have hterm (σ : Equiv.Perm (Fin q)) :
          ‖Equiv.Perm.sign σ • a.domDomCongr σ‖ = ‖a‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul])

private theorem normalizedAlternation_eq {n q : ℕ}
    (γ : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    normalizedAlternation γ.toContinuousMultilinearMap = γ := by
  have h : ContinuousMultilinearMap.alternatization γ.toContinuousMultilinearMap =
      q.factorial • γ := by
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    simpa using AlternatingMap.coe_alternatization γ.toAlternatingMap
  ext w
  simp [normalizedAlternation, h, nsmul_eq_mul, Nat.factorial_ne_zero]

private theorem contDiff_fixed_pullback {n q : ℕ}
    (γ : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ)
    {D : ComplexModel n → (ComplexModel n →L[ℝ] ComplexModel n)}
    {U : Set (ComplexModel n)} (hD : ContDiffOn ℝ ∞ D U) :
    ContDiffOn ℝ ∞ (fun x => γ.compContinuousLinearMap (D x)) U := by
  let A := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : Fin q => ComplexModel n) (fun _ => ComplexModel n) ℝ
  have hA : ContDiffOn ℝ ∞
      (fun x => A (fun _ => D x) γ.toContinuousMultilinearMap) U :=
    (A.contDiff.contDiffOn.comp (contDiffOn_pi.mpr fun _ => hD) (fun _ _ => mem_univ _)).clm_apply
      contDiffOn_const
  have hN := (normalizedAlternation (n := n) (q := q)).contDiff.contDiffOn.comp hA
    (fun _ _ => mem_univ _)
  convert hN using 1
  funext x
  change γ.compContinuousLinearMap (D x) =
    normalizedAlternation (γ.compContinuousLinearMap (D x)).toContinuousMultilinearMap
  exact (normalizedAlternation_eq _).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

open Classical in
/-- An original scalar compact test produces the entire tensor counterpart on
an actual holomorphic chart overlap. No counterpart or transport certificate
is provided by the caller. -/
theorem exists_constant_form_counterpart
    (e f : ComplexChart n M) (Ω P : Opens (ComplexModel n)) (q : ℕ) :
    let F := chartTransition e f
    let U : Opens (ComplexModel n) :=
      ⟨Ω ∩ (F.source ∩ F ⁻¹' P), Ω.isOpen.inter (F.isOpen_inter_preimage P.isOpen)⟩
    ∀ (φ : 𝓓(U, ℝ)) (γ : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ),
      ∃ ζ : TestForm (P ⊓ overlapTarget e f) q,
        tsupport ζ ⊆ F '' tsupport φ ∧
        (∀ y, ζ y = if y ∈ F.target then
          φ (F.symm y) • γ.compContinuousLinearMap (fderiv ℝ F.symm y) else 0) ∧
        ∀ x ∈ F.source, ∀ w : Fin q → ComplexModel n,
          φ x * γ w = ζ (F x) (fun i => chartTransitionDerivative e f x (w i)) := by
  classical
  intro F U φ γ
  let g : ComplexModel n → (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) := fun y =>
    if y ∈ F.target then
      φ (F.symm y) • γ.compContinuousLinearMap (fderiv ℝ F.symm y) else 0
  have hs : tsupport φ ⊆ F.source := fun x hx => (φ.tsupport_subset hx).2.1
  have hK : IsCompact (F '' tsupport φ) :=
    φ.hasCompactSupport.isCompact.image_of_continuousOn (F.continuousOn.mono hs)
  have hKt : F '' tsupport φ ⊆ F.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact F.map_source (hs hx)
  have hKP : F '' tsupport φ ⊆ (P ⊓ overlapTarget e f : Opens _) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(φ.tsupport_subset hx).2.2, F.map_source (hs hx)⟩
  have hinv : ContDiffOn ℝ ∞ F.symm F.target :=
    fun y hy => (DDCOverlap.contDiffAt_chartTransition_symm e f hy).contDiffWithinAt
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F.symm) F.target :=
    hinv.fderiv_of_isOpen F.open_target (by simp)
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ F.target
    · have hev : g =ᶠ[𝓝 y] fun z =>
          φ (F.symm z) • γ.compContinuousLinearMap (fderiv ℝ F.symm z) := by
        filter_upwards [F.open_target.mem_nhds hy] with z hz
        simp only [g, hz, ↓reduceIte]
      have hsm : ContDiffOn ℝ ∞ (fun z =>
          φ (F.symm z) • γ.compContinuousLinearMap (fderiv ℝ F.symm z)) F.target :=
        (φ.contDiff.contDiffOn.comp hinv (fun _ _ => mem_univ _)).smul
          (contDiff_fixed_pullback γ hD)
      exact (hsm.contDiffAt (F.open_target.mem_nhds hy)).congr_of_eventuallyEq hev
    · have hyK : y ∉ F '' tsupport φ := fun h => hy (hKt h)
      have hev : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with z hz
        by_cases hzt : z ∈ F.target
        · have hz' : F.symm z ∉ tsupport φ := fun h =>
            hz ⟨F.symm z, h, F.right_inv hzt⟩
          simp [g, hzt, image_eq_zero_of_notMem_tsupport hz']
        · simp [g, hzt]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hgK : tsupport g ⊆ F '' tsupport φ := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hnot
    have hz : g y = 0 := by
      by_cases hyt : y ∈ F.target
      · have hn : F.symm y ∉ tsupport φ := fun h =>
          hnot ⟨F.symm y, h, F.right_inv hyt⟩
        simp [g, hyt, image_eq_zero_of_notMem_tsupport hn]
      · simp [g, hyt]
    exact hy hz
  let ζ : TestForm (P ⊓ overlapTarget e f) q :=
    ⟨g, hg, hK.of_isClosed_subset (isClosed_tsupport g) hgK, hgK.trans hKP⟩
  refine ⟨ζ, hgK, (fun _ => rfl), ?_⟩
  intro x hx w
  have hF : HasFDerivAt F (chartTransitionDerivative e f x) x :=
    ((chartTransition_contDiffAt_real e f hx).differentiableAt (by simp)).hasFDerivAt
  have hFs : HasFDerivAt F.symm (fderiv ℝ F.symm (F x)) (F x) :=
    ((DDCOverlap.contDiffAt_chartTransition_symm e f (F.map_source hx)).differentiableAt
      (by simp)).hasFDerivAt
  have hev : (fun z => F.symm (F z)) =ᶠ[𝓝 x] id := by
    filter_upwards [F.open_source.mem_nhds hx] with z hz
    exact F.left_inv hz
  have hcomp : (fderiv ℝ F.symm (F x)).comp (chartTransitionDerivative e f x) =
      ContinuousLinearMap.id ℝ (ComplexModel n) :=
    ((hFs.comp x hF).congr_of_eventuallyEq hev.symm).unique (hasFDerivAt_id x)
  have hv (v : ComplexModel n) :
      fderiv ℝ F.symm (F x) (chartTransitionDerivative e f x v) = v :=
    DFunLike.congr_fun hcomp v
  change φ x * γ w = g (F x) (fun i => chartTransitionDerivative e f x (w i))
  simp [g, F.map_source hx, F.left_inv hx,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hv]

end SGPT.Foundations.Analysis.Pending.ActualChartOverlapTestTransport
