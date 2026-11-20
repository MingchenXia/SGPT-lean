import SGPT.Foundations.Analysis.FirstPass.CurrentPairing

/-! # The actual signed volume contraction identity

All three complete mathematical statements and ENTIRE proofs precede this
source. No coefficient/current differential comparison is an input.
-/

noncomputable section

open Function

namespace SGPT.Foundations.Analysis.Pending.NaturalVolumeContractionStokes

open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original block basis volume is the same actual ordered full basis volume. -/
theorem pairingBasisVolume_apply [FiniteDimensional ℝ E]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (v : Fin k.val → E)
    (w : Fin (Module.finrank ℝ E - k.val) → E) :
    basisVolume (currentPairingBasis b k) (Sum.elim v w) =
      basisVolume b (Fin.append (m := k.val) (n := Module.finrank ℝ E - k.val) v w ∘ Fin.cast (by omega)) := by
  classical
  rw [basisVolume_apply, currentPairingBasis, Module.Basis.det_reindex, basisVolume_apply]
  congr 1
  funext z
  let e : (Fin k.val ⊕ Fin (Module.finrank ℝ E - k.val)) ≃
      Fin (Module.finrank ℝ E) := finSumFinEquiv.trans (finCongr (by omega))
  obtain ⟨x, rfl⟩ := e.surjective z
  rcases x with i | j <;> simp [e]

/-- A genuine basis internally forces every one-higher-degree alternating form to vanish. -/
theorem alternating_succ_eq_zero_of_basis {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    (A : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) : A = 0 := by
  apply Module.Basis.ext_alternating b
  intro v hv
  have hc := Fintype.card_le_of_injective v hv
  simp only [Fintype.card_fin] at hc
  omega

/-- The entire covector-volume alternating sum is zero in one higher degree. -/
theorem topVolume_oneWedge_sum_eq_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    (L : E →L[ℝ] ℝ) (ν : E [⋀^Fin d]→L[ℝ] ℝ) (z : Fin (d + 1) → E) :
    ∑ i : Fin (d + 1), (-1 : ℤ) ^ (i : ℕ) • (L (z i) * ν (i.removeNth z)) = 0 := by
  have h := alternating_succ_eq_zero_of_basis b
    (AlternatingMap.alternatizeUncurryFin (L.toLinearMap.smulRight ν.toAlternatingMap))
  have hz := congrArg (fun A => A z) h
  simpa [AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.smulRight_apply, AlternatingMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_coe, AlternatingMap.zero_apply] using hz

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem removeNth_append_left {r s : ℕ} (v : Fin (r + 1) → E)
    (w : Fin (s + 1) → E) (i : Fin (r + 1)) :
    Fin.removeNth (n := (r + 1) + s) (i.castAdd (s + 1)) (Fin.append (m := r + 1) (n := s + 1) v w) =
      Fin.append (m := r) (n := s + 1) (i.removeNth v) w ∘ Fin.cast (show (r + 1) + s = r + (s + 1) by omega) := by
  funext t
  simp only [Fin.removeNth_apply, comp_apply]
  by_cases ht : t.val < r
  · let j : Fin r := ⟨t.val, ht⟩
    have hcast : Fin.cast (show (r + 1) + s = r + (s + 1) by omega) t = j.castAdd (s + 1) := by
      apply Fin.ext
      rfl
    rw [hcast, Fin.append_left, Fin.removeNth_apply]
    have hindex : (i.castAdd (s + 1)).succAbove t = (i.succAbove j).castAdd (s + 1) := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, j]
      split_ifs <;> simp_all
    rw [hindex, Fin.append_left]
  · let j : Fin (s + 1) := ⟨t.val - r, by omega⟩
    have hcast : Fin.cast (show (r + 1) + s = r + (s + 1) by omega) t = j.natAdd r := by
      apply Fin.ext
      simp [j]
      omega
    rw [hcast, Fin.append_right]
    have hindex : (i.castAdd (s + 1)).succAbove t = j.natAdd (r + 1) := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, j]
      split_ifs <;> simp_all
      all_goals omega
    rw [hindex, Fin.append_right]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem removeNth_append_right {r s : ℕ} (v : Fin r → E)
    (w : Fin (s + 1) → E) (j : Fin (s + 1)) :
    Fin.removeNth (n := r + s) (j.natAdd r) (Fin.append (m := r) (n := s + 1) v w) = Fin.append (m := r) (n := s) v (j.removeNth w) := by
  funext t
  simp only [Fin.removeNth_apply]
  by_cases ht : t.val < r
  · let i : Fin r := ⟨t.val, ht⟩
    have hcast : t = i.castAdd s := by
      apply Fin.ext
      rfl
    rw [hcast, Fin.append_left]
    have hindex : (j.natAdd r).succAbove (i.castAdd s) = i.castAdd (s + 1) := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, i]
      split_ifs <;> simp_all
      all_goals omega
    rw [hindex, Fin.append_left]
  · let i : Fin s := ⟨t.val - r, by omega⟩
    have hcast : t = i.natAdd r := by
      apply Fin.ext
      simp [i]
      omega
    rw [hcast, Fin.append_right, Fin.removeNth_apply]
    have hindex : (j.natAdd r).succAbove (i.natAdd r) = (j.succAbove i).natAdd r := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, i]
      split_ifs <;> simp_all
      all_goals omega
    rw [hindex, Fin.append_right]

/-- The literal full signed contraction identity in the two adjacent original degree blocks. -/
theorem signed_block_contraction_identity [FiniteDimensional ℝ E] (r s : ℕ)
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ E) (L : E →L[ℝ] ℝ)
    (v : Fin (r + 1) → E) (w : Fin (s + 1) → E) :
    (-1 : ℤ) ^ (r + 1) •
        (∑ j : Fin (s + 1), (-1 : ℤ) ^ (j : ℕ) •
          (L (w j) * basisVolume b (Fin.append (m := r + 1) (n := s) v (j.removeNth w)))) =
      -(∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
        (L (v i) * basisVolume b
          (Fin.append (m := r) (n := s + 1) (i.removeNth v) w ∘ Fin.cast (by omega)))) := by
  have hzero := topVolume_oneWedge_sum_eq_zero b L (basisVolume b) (Fin.append (m := r + 1) (n := s + 1) v w)
  have hsplit := Fin.sum_univ_add (a := r + 1) (b := s + 1)
    (fun i : Fin ((r + 1) + (s + 1)) => (-1 : ℤ) ^ (i : ℕ) •
      (L (Fin.append (m := r + 1) (n := s + 1) v w i) *
        basisVolume b (Fin.removeNth (n := (r + 1) + s) i
          (Fin.append (m := r + 1) (n := s + 1) v w))))
  have hzero := hsplit.symm.trans hzero
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd,
    removeNth_append_left, removeNth_append_right] at hzero
  have hfactor : (∑ j : Fin (s + 1), (-1 : ℤ) ^ (r + 1 + (j : ℕ)) •
      (L (w j) * basisVolume b (Fin.append (m := r + 1) (n := s) v (j.removeNth w)))) =
      (-1 : ℤ) ^ (r + 1) • (∑ j : Fin (s + 1), (-1 : ℤ) ^ (j : ℕ) •
        (L (w j) * basisVolume b (Fin.append (m := r + 1) (n := s) v (j.removeNth w)))) := by
    simp only [pow_add, mul_smul, Finset.smul_sum]
  rw [hfactor] at hzero
  exact eq_neg_of_add_eq_zero_right hzero

end SGPT.Foundations.Analysis.Pending.NaturalVolumeContractionStokes
