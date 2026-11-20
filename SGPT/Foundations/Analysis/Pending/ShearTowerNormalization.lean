import SGPT.Foundations.Analysis.Pending.WeierstrassPreparationDense
import SGPT.Foundations.Analysis.Pending.GermNoetherNormalization

set_option autoImplicit false

/-!
# Noether normalization by a shear tower: one direction for a finite family, near the identity

`Pending.GermNoetherNormalization.exists_isNoetherNormalization` puts ONE prime of `𝒪_n` in
Noether position after SOME linear change of coordinates `L`, about which nothing is
asserted.  Demailly's local parametrization theorem (CADG II.4.19) is consumed by
`Pending.AdaptedProjectionGerm.exists_adaptedProjection` in a stronger form, and the two
differences are exactly what this module supplies.

* ONE `L` must serve a FINITE FAMILY of primes at once, because the germ of a subvariety at
  a point is reducible and one projection has to be finite on every component.
* `L` must be PRESCRIBED up to `δ`, because a sheet bound whose direction is only
  existentially quantified is empty (see the docstring of
  `Pending.IrreducibleGermSheetBound`).

Both are obtained by re-running the induction of `exists_isNoetherNormalization_succ` with
the Weierstrass direction chosen by
`Pending.WeierstrassPreparationDense.exists_shear_prodWeierstrassGerm`: the directions in
which a nonzero germ is regular are open and dense
(`Pending.RegularDirectionDense`), so a single shear direction serves the whole family and
may be taken as close to `0` as we like.

## What is proved

`noetherShearProperty n` is the resulting statement at level `n`: a finite family
`P : Fin r → Ideal (HolGerm (ComplexModel n))` of primes and an `ε > 0` produce one
`L : ℂⁿ ≃L ℂⁿ` with every `P i` in Noether position with respect to `𝒪_{d i}`, and

  `‖L⁻¹ - id‖ ≤ ε`.

The bound is on `L⁻¹` rather than on the transported projection
`coordinateProjection n d ∘ L⁻¹` on purpose: the tower produces its own dimension `d i`, one
per member, so a bound on a projection to `ℂᵈ` cannot even be stated inside the induction,
while `‖coordinateProjection n d ∘ (L⁻¹ - id)‖ ≤ ‖L⁻¹ - id‖` holds for every `d` at once.
Prescribing a general `B₀` is then a separate, purely linear-algebraic step: conjugating the
tower by a `K` with `coordinateProjection n d ∘ K⁻¹ = B₀` moves the identity to `B₀`.

## The shear tower

Each step is `shearStep L a = σ ∘ (L × 1) ∘ shear a ∘ σ⁻¹`, where `σ = euclideanSnocCLE n`
splits off the last coordinate and `shear a : (x,t) ↦ (x + t·a, t)`.  Its inverse is
`y ↦ σ⁻¹(L⁻¹(y₁ - y₂·a), y₂)`, so it moves a point only inside the first `n` coordinates,
and `‖(shearStep L a)⁻¹ - id‖ ≤ ε + (ε+1)‖a‖` whenever `‖L⁻¹ - id‖ ≤ ε`.  Both `ε` and `‖a‖`
are free, so the tower converges: this is what makes the whole change of coordinates, and
not merely each of its steps, close to the identity.

Degenerate cases.  `r = 0`: the conclusion is the norm bound alone, satisfied by the
identity.  `P i = ⊥` (the germ is all of `ℂⁿ` near `0`): no nonzero element exists to
prepare, and the member is handled separately with `d i = n`; this is why the dimension is a
FAMILY `d : Fin r → ℕ` and not a single number.  `n = 0`: every prime of `𝒪₀ = ℂ` is `⊥`.
-/

open Filter Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ShearTowerNormalization

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open HolGerm

noncomputable section

/-! ### The splitting off the last coordinate is Pythagorean -/

theorem norm_sq_eq_sum {m : ℕ} (z : ComplexModel m) : ‖z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem norm_sq_euclideanSnocCLE (n : ℕ) (x : ComplexModel (n + 1)) :
    ‖x‖ ^ 2 = ‖(euclideanSnocCLE n x).1‖ ^ 2 + ‖(euclideanSnocCLE n x).2‖ ^ 2 := by
  rw [norm_sq_eq_sum, norm_sq_eq_sum, Fin.sum_univ_castSucc]
  simp [euclideanSnocCLE]

theorem norm_fst_euclideanSnocCLE_le (n : ℕ) (x : ComplexModel (n + 1)) :
    ‖(euclideanSnocCLE n x).1‖ ≤ ‖x‖ := by
  have h := norm_sq_euclideanSnocCLE n x
  nlinarith [norm_nonneg x, norm_nonneg (euclideanSnocCLE n x).1,
    norm_nonneg (euclideanSnocCLE n x).2, sq_nonneg ‖(euclideanSnocCLE n x).2‖]

theorem norm_snd_euclideanSnocCLE_le (n : ℕ) (x : ComplexModel (n + 1)) :
    ‖(euclideanSnocCLE n x).2‖ ≤ ‖x‖ := by
  have h := norm_sq_euclideanSnocCLE n x
  nlinarith [norm_nonneg x, norm_nonneg (euclideanSnocCLE n x).1,
    norm_nonneg (euclideanSnocCLE n x).2, sq_nonneg ‖(euclideanSnocCLE n x).1‖]

/-- The splitting is isometric on the first factor: adjoining a zero last coordinate does
not change the norm. -/
theorem norm_euclideanSnocCLE_symm_inl (n : ℕ) (u : ComplexModel n) :
    ‖(euclideanSnocCLE n).symm (u, (0 : ℂ))‖ = ‖u‖ := by
  have h := norm_sq_euclideanSnocCLE n ((euclideanSnocCLE n).symm (u, (0 : ℂ)))
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [norm_zero] at h
  nlinarith [norm_nonneg u, norm_nonneg ((euclideanSnocCLE n).symm (u, (0 : ℂ)))]

/-! ### One step of the shear tower -/

/-- One step of the Noether induction, as a change of coordinates of `ℂⁿ⁺¹`: split off the
last coordinate, apply a shear in the direction `a`, then a linear automorphism of the first
`n` coordinates. -/
def shearStep {n : ℕ} (L : ComplexModel n ≃L[ℂ] ComplexModel n) (a : ComplexModel n) :
    ComplexModel (n + 1) ≃L[ℂ] ComplexModel (n + 1) :=
  (euclideanSnocCLE n).trans
    ((L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)).trans
      ((HolGerm.shear a).trans (euclideanSnocCLE n).symm))

theorem shearStep_symm_apply {n : ℕ} (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (a : ComplexModel n) (y : ComplexModel (n + 1)) :
    (shearStep L a).symm y =
      (euclideanSnocCLE n).symm
        (L.symm ((euclideanSnocCLE n y).1 - (euclideanSnocCLE n y).2 • a),
          (euclideanSnocCLE n y).2) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  simp [shearStep]

/-- The step moves a point by the amount the shear and the inner automorphism move the
first `n` coordinates, and by nothing at all in the last one. -/
theorem shearStep_symm_sub {n : ℕ} (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (a : ComplexModel n) (y : ComplexModel (n + 1)) :
    (shearStep L a).symm y - y =
      (euclideanSnocCLE n).symm
        (L.symm ((euclideanSnocCLE n y).1 - (euclideanSnocCLE n y).2 • a) -
          (euclideanSnocCLE n y).1, (0 : ℂ)) := by
  obtain ⟨q, rfl⟩ : ∃ q, (euclideanSnocCLE n).symm q = y :=
    ⟨euclideanSnocCLE n y, by simp⟩
  rw [shearStep_symm_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [← map_sub]
  congr 1
  exact Prod.ext rfl (by simp)

/-- **The shear tower stays near the identity.**  If the inner automorphism moves `ℂⁿ` by at
most `ε` and the shear direction has norm `‖a‖`, the step moves `ℂⁿ⁺¹` by at most
`ε + (ε + 1) ‖a‖`. -/
theorem norm_shearStep_symm_sub_id_le {n : ℕ} (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (a : ComplexModel n) {ε : ℝ}
    (hL : ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
      ContinuousLinearMap.id ℂ (ComplexModel n)‖ ≤ ε) :
    ‖((shearStep L a).symm : ComplexModel (n + 1) →L[ℂ] ComplexModel (n + 1)) -
        ContinuousLinearMap.id ℂ (ComplexModel (n + 1))‖ ≤ ε + (ε + 1) * ‖a‖ := by
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) hL
  have hop : ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ ≤ ε + 1 := by
    have hid : ‖ContinuousLinearMap.id ℂ (ComplexModel n)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have hdec : (L.symm : ComplexModel n →L[ℂ] ComplexModel n) =
        ((L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
          ContinuousLinearMap.id ℂ (ComplexModel n)) +
          ContinuousLinearMap.id ℂ (ComplexModel n) := by abel
    calc ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖
        ≤ ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
              ContinuousLinearMap.id ℂ (ComplexModel n)‖ +
            ‖ContinuousLinearMap.id ℂ (ComplexModel n)‖ := by
          conv_lhs => rw [hdec]
          exact norm_add_le _ _
      _ ≤ ε + 1 := add_le_add hL hid
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  set y₁ := (euclideanSnocCLE n y).1 with hy₁
  set y₂ := (euclideanSnocCLE n y).2 with hy₂
  have hval : ((shearStep L a).symm : ComplexModel (n + 1) →L[ℂ] ComplexModel (n + 1)) y - y
      = (euclideanSnocCLE n).symm (L.symm (y₁ - y₂ • a) - y₁, (0 : ℂ)) :=
    shearStep_symm_sub L a y
  have hnorm : ‖(((shearStep L a).symm : ComplexModel (n + 1) →L[ℂ] ComplexModel (n + 1)) -
      ContinuousLinearMap.id ℂ (ComplexModel (n + 1))) y‖ = ‖L.symm (y₁ - y₂ • a) - y₁‖ := by
    rw [sub_apply, ContinuousLinearMap.id_apply, hval,
      norm_euclideanSnocCLE_symm_inl]
  rw [hnorm]
  have hsplit : L.symm (y₁ - y₂ • a) - y₁ =
      ((L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
        ContinuousLinearMap.id ℂ (ComplexModel n)) y₁ -
        (L.symm : ComplexModel n →L[ℂ] ComplexModel n) (y₂ • a) := by
    simp [sub_apply, map_sub, sub_right_comm]
  have h1 : ‖((L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
      ContinuousLinearMap.id ℂ (ComplexModel n)) y₁‖ ≤ ε * ‖y₁‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have h2 : ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n) (y₂ • a)‖ ≤ (ε + 1) * (‖y₂‖ * ‖a‖) := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    have : ‖y₂ • a‖ = ‖y₂‖ * ‖a‖ := by rw [norm_smul]
    rw [this]
    exact mul_le_mul_of_nonneg_right hop (by positivity)
  have hy1le : ‖y₁‖ ≤ ‖y‖ := norm_fst_euclideanSnocCLE_le n y
  have hy2le : ‖y₂‖ ≤ ‖y‖ := norm_snd_euclideanSnocCLE_le n y
  have := norm_sub_le ((( L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
    ContinuousLinearMap.id ℂ (ComplexModel n)) y₁)
    ((L.symm : ComplexModel n →L[ℂ] ComplexModel n) (y₂ • a))
  rw [hsplit]
  calc ‖((L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
        ContinuousLinearMap.id ℂ (ComplexModel n)) y₁ -
        (L.symm : ComplexModel n →L[ℂ] ComplexModel n) (y₂ • a)‖
      ≤ ε * ‖y₁‖ + (ε + 1) * (‖y₂‖ * ‖a‖) := le_trans this (add_le_add h1 h2)
    _ ≤ ε * ‖y‖ + (ε + 1) * (‖y‖ * ‖a‖) := by
        gcongr
    _ = (ε + (ε + 1) * ‖a‖) * ‖y‖ := by ring

/-! ### Approximate Noether normalization for a finite family -/

/-- **The approximate simultaneous Noether normalization property at level `n`.**  Every
finite family of primes of `𝒪_n` is put in Noether position — each with respect to its own
`d i` — by ONE linear change of coordinates, and that change may be taken as close to the
identity as we like. -/
def NoetherShearProperty (n : ℕ) : Prop :=
  ∀ {r : ℕ} (P : Fin r → Ideal (HolGerm (ComplexModel n))), (∀ i, (P i).IsPrime) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ (L : ComplexModel n ≃L[ℂ] ComplexModel n) (d : Fin r → ℕ),
        (∀ i, IsNoetherNormalization ((P i).map (comapEquiv L)) (d i)) ∧
        ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n) -
          ContinuousLinearMap.id ℂ (ComplexModel n)‖ ≤ ε

theorem noetherShearProperty_zero : NoetherShearProperty 0 := by
  intro r P hP ε hε
  refine ⟨ContinuousLinearEquiv.refl ℂ _, fun _ => 0, fun i => ?_, ?_⟩
  · have := hP i
    rw [map_comapEquiv_refl, eq_bot_of_isPrime_zero (P i)]
    exact isNoetherNormalization_bot 0
  · simpa using hε.le

/-- **Induction step.**  The step of `Pending.GermNoetherNormalization
.exists_isNoetherNormalization_succ`, performed once for a whole finite family and with the
shear direction taken small: the Weierstrass direction is chosen by
`Pending.WeierstrassPreparationDense.exists_shear_prodWeierstrassGerm`, which serves every
member of the family at once and may be prescribed near `0`. -/
theorem noetherShearProperty_succ {n : ℕ} (ih : NoetherShearProperty n) :
    NoetherShearProperty (n + 1) := by
  classical
  intro r P hP δ hδ
  set σ := euclideanSnocCLE n with hσ
  set P₁ : Fin r → Ideal (HolGerm (ComplexModel n × ℂ)) :=
    fun i => (P i).map (comapEquiv σ.symm) with hP₁def
  have hP₁ : ∀ i, (P₁ i).IsPrime := by
    intro i; have := hP i; exact Ideal.map_isPrime_of_equiv _
  have hbot : ∀ i, P₁ i = ⊥ ↔ P i = ⊥ := fun i =>
    Ideal.map_eq_bot_iff_of_injective (comapEquiv σ.symm).injective
  have hex : ∀ i, ∃ h : HolGerm (ComplexModel n × ℂ), h ≠ 0 ∧ (P i ≠ ⊥ → h ∈ P₁ i) := by
    intro i
    by_cases hi : P i = ⊥
    · exact ⟨1, one_ne_zero, fun hh => absurd hi hh⟩
    · obtain ⟨h, hmem, hne⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (fun hh => hi ((hbot i).1 hh))
      exact ⟨h, hne, fun _ => hmem⟩
  choose g hg0 hgmem using hex
  set ε : ℝ := min 1 (δ / 2) with hεdef
  have hε : 0 < ε := lt_min one_pos (by linarith)
  have hδa : (0 : ℝ) < δ / 8 := by linarith
  obtain ⟨a, ha, hWe⟩ := exists_shear_prodWeierstrassGerm hg0 (0 : ComplexModel n) hδa
  rw [sub_zero] at ha
  choose q s W hqu hWvan hWeq using hWe
  set A := HolGerm.shear a with hA
  set P₂ : Fin r → Ideal (HolGerm (ComplexModel n × ℂ)) :=
    fun i => (P₁ i).map (comapEquiv A) with hP₂def
  have hP₂ : ∀ i, (P₂ i).IsPrime := by
    intro i; have := hP₁ i; exact Ideal.map_isPrime_of_equiv _
  have hW₂ : ∀ i, P i ≠ ⊥ → prodWeierstrassGerm (s i) (W i) ∈ P₂ i := by
    intro i hi
    have hmem : comapEquiv A (g i) ∈ P₂ i := Ideal.mem_map_of_mem _ (hgmem i hi)
    have := (P₂ i).mul_mem_left (q i) hmem
    rwa [hWeq i] at this
  obtain ⟨L', d', hN, hL'⟩ :=
    ih (fun i => (P₂ i).comap ofFst)
      (fun i => by have := hP₂ i; exact Ideal.comap_isPrime ofFst (P₂ i)) hε
  set M := L'.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ) with hM
  set P₃ : Fin r → Ideal (HolGerm (ComplexModel n × ℂ)) :=
    fun i => (P₂ i).map (comapEquiv M) with hP₃def
  refine ⟨shearStep L' a, fun i => if P i = ⊥ then n + 1 else d' i, fun i => ?_, ?_⟩
  · by_cases hi : P i = ⊥
    · simp only [if_pos hi]
      rw [hi, Ideal.map_bot]
      exact isNoetherNormalization_bot (n + 1)
    · simp only [if_neg hi]
      have hQ : (P i).map (comapEquiv (shearStep L' a)) = (P₃ i).map (comapEquiv σ) := by
        show (P i).map (comapEquiv (σ.trans (M.trans (A.trans σ.symm)))) = _
        rw [map_comapEquiv_trans, map_comapEquiv_trans, map_comapEquiv_trans]
      rw [hQ]
      have key : ∀ x, projGerm (n + 1) n x ∈ (P₃ i).map (comapEquiv σ) ↔
          x ∈ ((P₂ i).comap ofFst).map (comapEquiv L') := by
        intro x
        rw [← comap_ofFst_map_comapEquiv_prodCongr L' (P₂ i), Ideal.mem_comap,
          ← comapEquiv_euclideanSnocCLE_ofFst]
        exact mem_map_ringEquiv_apply_iff _ _ _
      refine ⟨(hN i).le.trans n.le_succ, fun c hc => ?_, fun k hk hdk => ?_⟩
      · rw [← projGerm_projGerm (hN i).le, key] at hc
        exact (hN i).eq_zero_of_mem c hc
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | rfl
        · obtain ⟨s', A', hA', hw⟩ := (hN i).weierstrass k hkn hdk
          refine ⟨s', A', hA', ?_⟩
          have hmem := (key _).2 hw
          rwa [projGerm_weierstrassGerm hkn n.le_succ] at hmem
        · refine ⟨s i, fun j => comapEquiv L' (W i j), fun j hj => by
            simp [hWvan i j hj], ?_⟩
          rw [← comapEquiv_euclideanSnocCLE_prodWeierstrassGerm,
            ← comapEquiv_prodCongr_prodWeierstrassGerm]
          exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hW₂ i hi))
  · refine le_trans (norm_shearStep_symm_sub_id_le L' a hL') ?_
    have h1 : ε ≤ δ / 2 := min_le_right _ _
    have h2 : ε ≤ 1 := min_le_left _ _
    nlinarith [norm_nonneg a]

/-- **Noether normalization for a finite family of primes, by a change of coordinates
arbitrarily close to the identity.** -/
theorem noetherShearProperty (n : ℕ) : NoetherShearProperty n := by
  induction n with
  | zero => exact noetherShearProperty_zero
  | succ n ih => exact noetherShearProperty_succ ih

end

end SGPT.Foundations.Analysis.Pending.ShearTowerNormalization
