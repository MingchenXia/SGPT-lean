import SGPT.Foundations.Analysis.FirstPass.CurrentPairing
import Mathlib.GroupTheory.Perm.Finite

/-!
# Inverse identities for the oriented current pairing

The forward and reverse maps, continuity of coefficient extraction and
insertion, normalized volume, and forward determinant covariance are
constructed in the checked core.  This file proves that the two maps are
inverse.

No measure is involved in these algebraic inverse statements. Compatibility
with regular densities requires a measure normalized to the chosen volume;
chart changes, the current differential, and full positivity are separate
global obligations, not consequences of these signatures.
-/

noncomputable section

open TopologicalSpace
open SGPT.Foundations.Analysis.LocalCurrents

namespace SGPT.Foundations.Analysis.Pending.CurrentPairing

private lemma modSumCongr_crosses_relative
    {k q : ℕ} (σ : Equiv.Perm (Fin k ⊕ Fin q))
    (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q))
    (hs : s ≠ QuotientGroup.mk σ) :
    ∃ j i, s.out (Sum.inr j) = σ (Sum.inl i) := by
  by_contra h
  push Not at h
  let δ : Equiv.Perm (Fin k ⊕ Fin q) := σ⁻¹ * s.out
  have hr : Set.MapsTo δ (Set.range (@Sum.inr (Fin k) (Fin q)))
      (Set.range (@Sum.inr (Fin k) (Fin q))) := by
    rintro _ ⟨j, rfl⟩
    rcases heq : δ (Sum.inr j) with i | j'
    · have : s.out (Sum.inr j) = σ (Sum.inl i) := by
        have := congrArg σ heq
        simpa [δ] using this
      exact (h j i this).elim
    · exact ⟨j', rfl⟩
  have hl : Set.MapsTo δ (Set.range (@Sum.inl (Fin k) (Fin q)))
      (Set.range (@Sum.inl (Fin k) (Fin q))) :=
    (Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr δ).2 hr
  have hδ : δ ∈
      (Equiv.Perm.sumCongrHom (Fin k) (Fin q)).range :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl
  have hm : QuotientGroup.mk σ = QuotientGroup.mk s.out :=
    Quotient.sound' (by
      rw [QuotientGroup.leftRel_apply]
      exact hδ)
  exact hs (hm.trans (Quotient.out_eq' s)).symm

private lemma modSumCongr_crosses_left_relative
    {k q : ℕ} (σ : Equiv.Perm (Fin k ⊕ Fin q))
    (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q))
    (hs : s ≠ QuotientGroup.mk σ) :
    ∃ i j, s.out (Sum.inl i) = σ (Sum.inr j) := by
  by_contra h
  push Not at h
  let δ : Equiv.Perm (Fin k ⊕ Fin q) := σ⁻¹ * s.out
  have hl : Set.MapsTo δ (Set.range (@Sum.inl (Fin k) (Fin q)))
      (Set.range (@Sum.inl (Fin k) (Fin q))) := by
    rintro _ ⟨i, rfl⟩
    rcases heq : δ (Sum.inl i) with i' | j
    · exact ⟨i', rfl⟩
    · have : s.out (Sum.inl i) = σ (Sum.inr j) := by
        have := congrArg σ heq
        simpa [δ] using this
      exact (h i j this).elim
  have hδ : δ ∈
      (Equiv.Perm.sumCongrHom (Fin k) (Fin q)).range :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl
  have hm : QuotientGroup.mk σ = QuotientGroup.mk s.out :=
    Quotient.sound' (by
      rw [QuotientGroup.leftRel_apply]
      exact hδ)
  exact hs (hm.trans (Quotient.out_eq' s)).symm

private lemma wedgeTerm_eq_summand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} {k q : ℕ} (v : Fin k ⊕ Fin q → E)
    (A : DistributionForm Ω k) (η : TestForm Ω q)
    (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q)) :
    Equiv.Perm.sign s.out •
        A (fun i => v (s.out (Sum.inl i)))
          (testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η) =
      distributionTestPairing
        (AlternatingMap.domCoprod.summand A (testFormAlternating η) s v) := by
  conv_rhs =>
    rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  change Equiv.Perm.sign s.out •
      A (fun i => v (s.out (Sum.inl i)))
        (testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η) =
    distributionTestPairing (Equiv.Perm.sign s.out •
      (A (fun i => v (s.out (Sum.inl i))) ⊗ₜ[ℝ]
        testCoefficientCLM (fun j => v (s.out (Sum.inr j))) η))
  simp [Units.smul_def]

private lemma scalarWedgeTerm_eq_summand
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {k q : ℕ} (v : Fin k ⊕ Fin q → E)
    (a : E [⋀^Fin k]→ₗ[ℝ] ℝ) (c : E [⋀^Fin q]→ₗ[ℝ] ℝ)
    (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q)) :
    Equiv.Perm.sign s.out •
        (a (fun i => v (s.out (Sum.inl i))) *
          c (fun j => v (s.out (Sum.inr j)))) =
      (TensorProduct.lid ℝ ℝ)
        (AlternatingMap.domCoprod.summand a c s v) := by
  conv_rhs =>
    rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  change Equiv.Perm.sign s.out •
      (a (fun i => v (s.out (Sum.inl i))) *
        c (fun j => v (s.out (Sum.inr j)))) =
    (TensorProduct.lid ℝ ℝ) (Equiv.Perm.sign s.out •
      (a (fun i => v (s.out (Sum.inl i))) ⊗ₜ[ℝ]
        c (fun j => v (s.out (Sum.inr j)))))
  change (Equiv.Perm.sign s.out : ℤ) •
      (a (fun i => v (s.out (Sum.inl i))) *
        c (fun j => v (s.out (Sum.inr j)))) =
    (TensorProduct.lid ℝ ℝ) ((Equiv.Perm.sign s.out : ℤ) •
      (a (fun i => v (s.out (Sum.inl i))) ⊗ₜ[ℝ]
        c (fun j => v (s.out (Sum.inr j)))))
  rw [map_zsmul, TensorProduct.lid_tmul, smul_eq_mul]

private def rightVolumeContraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k q : ℕ} (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ) (w : Fin q → E) :
    E [⋀^Fin k]→ₗ[ℝ] ℝ :=
  (formEvaluationCLM w).toLinearMap.compAlternatingMap (volumeContraction vol)

@[simp] private theorem rightVolumeContraction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k q : ℕ} (vol : E [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ)
    (w : Fin q → E) (v : Fin k → E) :
    rightVolumeContraction vol w v = contractVolume vol v w := rfl

private theorem testForm_shuffle_reconstruction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} {k q : ℕ}
    (e : Module.Basis (Fin k ⊕ Fin q) ℝ E)
    (η : TestForm Ω q) :
    (∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q),
      Equiv.Perm.sign s.out • constantTestFormCLM
        (contractVolume (basisVolume e)
          (fun i => e (s.out (Sum.inl i))))
        (testCoefficientCLM (fun j => e (s.out (Sum.inr j))) η)) = η := by
  classical
  apply TestFunction.ext
  intro x
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating e
  intro a ha
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (@Sum.inr (Fin k) (Fin q)) a Sum.inr_injective ha
  let s₀ : Equiv.Perm.ModSumCongr (Fin k) (Fin q) := QuotientGroup.mk σ
  simp only [sum_apply]
  change formEvaluationCLM (fun j => e (a j))
      (∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q),
        (Equiv.Perm.sign s.out • constantTestFormCLM
          (contractVolume (basisVolume e)
            (fun i => e (s.out (Sum.inl i))))
          (testCoefficientCLM (fun j => e (s.out (Sum.inr j))) η)) x) =
    (η x).toAlternatingMap (fun j => e (a j))
  rw [map_sum]
  rw [Finset.sum_eq_single s₀]
  · change Equiv.Perm.sign s₀.out •
        ((η x).toAlternatingMap (fun j => e (s₀.out (Sum.inr j))) *
          rightVolumeContraction (basisVolume e) (fun j => e (a j))
            (fun i => e (s₀.out (Sum.inl i)))) =
      (η x).toAlternatingMap (fun j => e (a j))
    rw [mul_comm, scalarWedgeTerm_eq_summand]
    dsimp only [s₀]
    rw [AlternatingMap.domCoprod.summand_mk'']
    simp only [smul_apply, MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply]
    rw [Units.smul_def, map_zsmul, TensorProduct.lid_tmul, smul_eq_mul]
    change Equiv.Perm.sign σ •
        (contractVolume (basisVolume e) (fun i => e (σ (Sum.inl i)))
          (fun j => e (a j)) *
        η x (fun j => e (σ (Sum.inr j)))) =
      η x (fun j => e (a j))
    have hvol : contractVolume (basisVolume e)
        (fun i => e (σ (Sum.inl i))) (fun j => e (a j)) =
        Equiv.Perm.sign σ • (1 : ℝ) := by
      change basisVolume e (Sum.elim (fun i => e (σ (Sum.inl i)))
        (fun j => e (a j))) = _
      have hfamily : Sum.elim (fun i => e (σ (Sum.inl i)))
          (fun j => e (a j)) = e ∘ σ := by
        funext z
        rcases z with i | j
        · rfl
        · exact congrArg e (hσ j).symm
      rw [hfamily]
      change (basisVolume e).toAlternatingMap (e ∘ σ) = _
      calc
        (basisVolume e).toAlternatingMap (e ∘ σ) =
            Equiv.Perm.sign σ • (basisVolume e).toAlternatingMap e :=
          (basisVolume e).toAlternatingMap.map_perm e σ
        _ = Equiv.Perm.sign σ • 1 := by
          rw [show (basisVolume e).toAlternatingMap e = 1 from basisVolume_self e]
    rw [hvol]
    simp only [hσ]
    simp [smul_smul]
  · intro s _ hs
    obtain ⟨i, j, hcross⟩ := modSumCongr_crosses_left_relative σ s hs
    have hvol : contractVolume (basisVolume e)
        (fun i => e (s.out (Sum.inl i))) (fun j => e (a j)) = 0 := by
      change basisVolume e (Sum.elim (fun i => e (s.out (Sum.inl i)))
        (fun j => e (a j))) = 0
      apply (basisVolume e).map_eq_zero_of_eq _
        (i := Sum.inl i) (j := Sum.inr j)
      · change e (s.out (Sum.inl i)) = e (a j)
        rw [hcross, hσ]
      · exact Sum.inl_ne_inr
    change Equiv.Perm.sign s.out •
        ((η x).toAlternatingMap (fun j => e (s.out (Sum.inr j))) *
          rightVolumeContraction (basisVolume e) (fun j => e (a j))
            (fun i => e (s.out (Sum.inl i)))) = 0
    rw [rightVolumeContraction_apply, hvol]
    simp
  · simp

/-- Contraction by the normalized basis volume recovers each
distribution coefficient of the shuffle pairing. The complementary signs
occur twice and multiply to one, with no factorial. -/
theorem fromLocalCurrent_toLocalCurrent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (A : DistributionForm Ω k.val) :
    fromLocalCurrent b k (toLocalCurrent b k A) = A := by
  classical
  let e := currentPairingBasis b k
  apply Module.Basis.ext_alternating e
  intro a ha
  ext φ
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (@Sum.inl (Fin k.val) (Fin (Module.finrank ℝ E - k.val))) a
    Sum.inl_injective ha
  let s₀ : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ E - k.val)) := QuotientGroup.mk σ
  rw [fromLocalCurrent_apply]
  change wedgePairing e A
      (constantTestFormCLM
        (contractVolume (basisVolume e) (fun i => e (a i))) φ) =
    A (fun i => e (a i)) φ
  rw [wedgePairing_apply]
  rw [Finset.sum_eq_single s₀]
  · rw [wedgeTerm_eq_summand]
    dsimp only [s₀]
    rw [AlternatingMap.domCoprod.summand_mk'']
    change Equiv.Perm.sign σ •
        A (fun i => e (σ (Sum.inl i)))
          (testCoefficientCLM (fun j => e (σ (Sum.inr j)))
            (constantTestFormCLM
              (contractVolume (basisVolume e) (fun i => e (a i))) φ)) =
      A (fun i => e (a i)) φ
    rw [testCoefficient_constantTestForm]
    have hvol : contractVolume (basisVolume e) (fun i => e (a i))
        (fun j => e (σ (Sum.inr j))) = Equiv.Perm.sign σ • (1 : ℝ) := by
      change basisVolume e (Sum.elim (fun i => e (a i))
        (fun j => e (σ (Sum.inr j)))) = _
      have hfamily : Sum.elim (fun i => e (a i))
          (fun j => e (σ (Sum.inr j))) = e ∘ σ := by
        funext x
        rcases x with i | j
        · exact congrArg e (hσ i).symm
        · rfl
      rw [hfamily]
      change (basisVolume e).toAlternatingMap (e ∘ σ) = _
      calc
        (basisVolume e).toAlternatingMap (e ∘ σ) =
            Equiv.Perm.sign σ • (basisVolume e).toAlternatingMap e :=
          (basisVolume e).toAlternatingMap.map_perm e σ
        _ = Equiv.Perm.sign σ • 1 := by
          rw [show (basisVolume e).toAlternatingMap e = 1 from basisVolume_self e]
    rw [hvol]
    simp only [hσ, map_smul]
    simp [smul_smul]
  · intro s _ hs
    obtain ⟨j, i, hcross⟩ := modSumCongr_crosses_relative σ s hs
    have hvol : contractVolume (basisVolume e) (fun i => e (a i))
        (fun j => e (s.out (Sum.inr j))) = 0 := by
      change basisVolume e (Sum.elim (fun i => e (a i))
        (fun j => e (s.out (Sum.inr j)))) = 0
      apply (basisVolume e).map_eq_zero_of_eq _
        (i := Sum.inl i) (j := Sum.inr j)
      · change e (a i) = e (s.out (Sum.inr j))
        rw [← hσ i, hcross]
      · exact Sum.inl_ne_inr
    rw [testCoefficient_constantTestForm, hvol, zero_smul]
    simp
  · simp

/-- Expand an actual test form in complementary dual-basis wedges.
Every coefficient is a genuine scalar test and every reconstructed summand is
a genuine test form, so linearity of the current gives reconstruction. -/
theorem toLocalCurrent_fromLocalCurrent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (T : LocalCurrent Ω k) :
    toLocalCurrent b k (fromLocalCurrent b k T) = T := by
  classical
  let e := currentPairingBasis b k
  ext η
  change wedgePairing e (currentCoefficients (basisVolume e) T) η = T η
  rw [wedgePairing_apply]
  simp only [currentCoefficients_apply]
  calc
    _ = T (∑ s : Equiv.Perm.ModSumCongr (Fin k.val)
          (Fin (Module.finrank ℝ E - k.val)),
        Equiv.Perm.sign s.out • constantTestFormCLM
          (contractVolume (basisVolume e)
            (fun i => e (s.out (Sum.inl i))))
          (testCoefficientCLM (fun j => e (s.out (Sum.inr j))) η)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Units.smul_def, map_zsmul]
    _ = T η := by
      rw [testForm_shuffle_reconstruction e η]

end SGPT.Foundations.Analysis.Pending.CurrentPairing
