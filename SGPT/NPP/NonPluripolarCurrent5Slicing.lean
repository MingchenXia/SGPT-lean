import SGPT.NPP.NonPluripolarCurrent5Measurable

/-!
# Bedford–Taylor slicing over a base `ℂᵐ`

Source: `chapter_npp.tex`, `lma:boundedfibrefubini`.

Let `Ω ⊆ ℂⁿ⁺ᵐ = ℂⁿ × ℂᵐ` be open and let `u` be a tuple of `n + m` locally bounded psh
functions on `Ω` (in the sense of `BedfordTaylor.IsBTLimit`), whose last `m` slots are the
functions `|z_k|²` of the base coordinates (`baseNormSq`), so that the Bedford–Taylor limit `ν`
of `u` is `dd^c u₁ ∧ ⋯ ∧ dd^c uₙ ∧ dd^c|z₁|² ∧ ⋯ ∧ dd^c|z_m|²`.  Let `μ_z` be the Bedford–Taylor
limits of the fibre tuples `x ↦ (u₁(x, z), …, uₙ(x, z))`.  Then for every continuous `χ ≥ 0` with
compact support in `Ω` and every bounded Borel `F` (`integral_mul_isBTLimit_eq_fibreIntegral`):

`∫ χ F dν = π^{-m} ∫_{ℂᵐ} (∫ χ(x, z) F(x, z) dμ_z(x)) dz`,

the inner integrals being integrable in `z`.

The proof is an induction on `m`.  The step `m → m + 1` slices off the last base coordinate with
TN's one-dimensional slicing for bounded Borel weights
(`BedfordTaylorBorelFibreSlicing.integral_mul_borel_isBTLimit_eq_fibre`, on
`ℂⁿ⁺ᵐ⁺¹ = ℂⁿ⁺ᵐ × ℂ`), applies the induction hypothesis on every fibre `ℂⁿ⁺ᵐ × {τ}` (whose fibres
over `z ∈ ℂᵐ` are the fibres of `ℂⁿ⁺ᵐ⁺¹` over `(z, τ)`, `fibreMapM_succ`), and recombines the
iterated integral over `ℂᵐ × ℂ = ℂᵐ⁺¹` by Fubini.  The joint measurability needed for Fubini is
`aestronglyMeasurable_fibreIntegral_mul` (the source's monotone class argument); integrability
follows from the unweighted case and Tonelli.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff

namespace SGPT.NPP.FibreSlicing

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing
open SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

variable {n : ℕ}

/-- The base slot `|z_k|²` on `ℂⁿ⁺ᵐ`: the squared modulus of the coordinate `n + k`. -/
def baseNormSq (n m : ℕ) (k : Fin m) : ComplexModel (n + m) → ℝ :=
  fun q => ‖q (Fin.natAdd n k)‖ ^ 2

/-! ### The zero-dimensional base -/

theorem volume_univ_complexModel_zero : (volume : Measure (ComplexModel 0)) univ = 1 := by
  have h := (stdOrthonormalBasis ℝ (ComplexModel 0)).volume_parallelepiped
  have e : parallelepiped (stdOrthonormalBasis ℝ (ComplexModel 0)) = univ := by
    ext x
    simp only [mem_univ, iff_true]
    rw [Subsingleton.elim x 0, mem_parallelepiped_iff]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  rwa [e] at h

instance : IsProbabilityMeasure (volume : Measure (ComplexModel 0)) :=
  ⟨volume_univ_complexModel_zero⟩

theorem fibreMapM_zero (z : ComplexModel 0) (x : ComplexModel n) : fibreMapM n 0 z x = x := by
  ext i
  exact fibreMapM_castAdd z x i

/-! ### The induction -/

/-- The slicing statement over a base `ℂᵐ`. -/
def SlicingClaim (n m : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel (n + m))) (u : Fin (n + m) → ComplexModel (n + m) → ℝ),
    (∀ k : Fin m, u (Fin.natAdd n k) = baseNormSq n m k) →
    ∀ ν : Measure (ComplexModel (n + m)), IsBTLimit Ω u ν →
    ∀ μ : ComplexModel m → Measure (ComplexModel n),
      (∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z)) →
    ∀ χ : ComplexModel (n + m) → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      (∀ q, 0 ≤ χ q) →
    ∀ F : ComplexModel (n + m) → ℝ, Measurable F → ∀ C : ℝ, (∀ q, ‖F q‖ ≤ C) →
      Integrable (fibreIntegral μ fun q => χ q * F q) ∧
        ∫ q, χ q * F q ∂ν = (∫ z, fibreIntegral μ (fun q => χ q * F q) z) / Real.pi ^ m

theorem slicingClaim_zero : SlicingClaim n 0 := by
  intro Ω u _ ν hν μ hμ χ _ _ _ _ F _ C _
  have hO (z : ComplexModel 0) : fibreOpensM Ω z = Ω := by
    ext x
    simp [fibreMapM_zero]
  have hT (z : ComplexModel 0) : fibreTupleM u z = u := by
    funext i x
    simp only [fibreTupleM, fibreRestrictM, fibreMapM_zero]
    rfl
  have hμν (z : ComplexModel 0) : μ z = ν := by
    have h := hμ z
    rw [hO, hT] at h
    exact h.unique hν
  have hG : (fibreIntegral μ fun q => χ q * F q) = fun _ => ∫ q, χ q * F q ∂ν := by
    funext z
    simp only [fibreIntegral, fibreMapM_zero, hμν z]
    rfl
  rw [hG]
  refine ⟨integrable_const _, ?_⟩
  rw [integral_const, pow_zero, div_one]
  simp [measureReal_def]

/-- Index bookkeeping: the last slot of `ℂⁿ⁺ᵐ⁺¹` is the last base coordinate. -/
theorem natAdd_last_eq (m : ℕ) : (Fin.natAdd n (Fin.last m) : Fin (n + (m + 1))) =
    Fin.last (n + m) := Fin.ext rfl

theorem castSucc_natAdd {m : ℕ} (k : Fin m) :
    ((Fin.natAdd n k).castSucc : Fin (n + m + 1)) = Fin.natAdd n k.castSucc := Fin.ext rfl

theorem castSucc_castAdd {m : ℕ} (i : Fin n) :
    ((Fin.castAdd m i).castSucc : Fin (n + m + 1)) = Fin.castAdd (m + 1) i := Fin.ext rfl

theorem fibreOpensM_succ {m : ℕ} (Ω : Opens (ComplexModel (n + (m + 1)))) (z : ComplexModel m)
    (τ : ℂ) : fibreOpensM Ω ((stripModelEquiv m).symm (z, τ)) =
      fibreOpensM (fibreOpens (n := n + m) Ω τ) z := by
  ext x
  simp only [mem_fibreOpensM, SetLike.mem_coe, mem_fibreOpens]
  rw [fibreMapM_succ]

theorem fibreTupleM_succ {m : ℕ} (u : Fin (n + (m + 1)) → ComplexModel (n + (m + 1)) → ℝ)
    (z : ComplexModel m) (τ : ℂ) : fibreTupleM u ((stripModelEquiv m).symm (z, τ)) =
      fibreTupleM (fibreTuple (n := n + m) u τ) z := by
  funext i x
  simp only [fibreTupleM, fibreRestrictM, fibreTuple, fibreRestrict]
  rw [fibreMapM_succ, castSucc_castAdd]

theorem fibreIntegral_succ {m : ℕ} (μ : ComplexModel (m + 1) → Measure (ComplexModel n))
    (g : ComplexModel (n + (m + 1)) → ℝ) (z : ComplexModel m) (τ : ℂ) :
    fibreIntegral (fun z' => μ ((stripModelEquiv m).symm (z', τ)))
      (fibreRestrict (n := n + m) g τ) z =
      fibreIntegral μ g ((stripModelEquiv m).symm (z, τ)) := by
  simp only [fibreIntegral, fibreRestrict]
  congr 1
  funext x
  rw [fibreMapM_succ]

theorem slicingClaim_succ {m : ℕ} (ih : SlicingClaim n m) : SlicingClaim n (m + 1) := by
  intro Ω u hbase ν hν μ hμ χ hχ hχc hχΩ hχ0 F hFm C hFb
  -- the last base slot is TN's `|τ|²`
  have hlast : u (Fin.last (n + m)) = lastNormSq (n + m) := by
    rw [← natAdd_last_eq m, hbase]
    funext q
    simp only [baseNormSq, lastNormSq]
    rw [natAdd_last_eq m]
  -- Bedford–Taylor limits on the fibres of `ℂⁿ⁺ᵐ⁺¹ = ℂⁿ⁺ᵐ × ℂ`
  have hex (τ : ℂ) := exists_isBTLimit_fibre (n := n + m) hν τ
  choose μ' hμ' using hex
  -- the induction hypothesis on every fibre
  have hbaseτ (τ : ℂ) : ∀ k : Fin m, fibreTuple (n := n + m) u τ (Fin.natAdd n k) =
      baseNormSq n m k := by
    intro k
    funext y
    simp only [fibreTuple, fibreRestrict, baseNormSq]
    rw [castSucc_natAdd, hbase k.castSucc]
    simp only [baseNormSq]
    rw [← castSucc_natAdd, fibreMap, stripModelEquiv_symm_apply_castSucc]
  have hμτ (τ : ℂ) (z : ComplexModel m) :
      IsBTLimit (fibreOpensM (fibreOpens (n := n + m) Ω τ) z)
        (fibreTupleM (fibreTuple (n := n + m) u τ) z) (μ ((stripModelEquiv m).symm (z, τ))) := by
    have h := hμ ((stripModelEquiv m).symm (z, τ))
    rwa [fibreOpensM_succ, fibreTupleM_succ] at h
  have hχτ (τ : ℂ) : Continuous (fibreRestrict (n := n + m) χ τ) :=
    hχ.comp (continuous_fibreMap τ)
  have hχτc (τ : ℂ) : HasCompactSupport (fibreRestrict (n := n + m) χ τ) :=
    (isCompact_preimage_fibreMap hχc τ).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_fibreRestrict_subset χ τ)
  have hχτΩ (τ : ℂ) : tsupport (fibreRestrict (n := n + m) χ τ) ⊆ fibreOpens (n := n + m) Ω τ :=
    fun y hy => hχΩ (tsupport_fibreRestrict_subset χ τ hy)
  have hFτm (τ : ℂ) : Measurable (fibreRestrict (n := n + m) F τ) :=
    hFm.comp (continuous_fibreMap τ).measurable
  have IH (τ : ℂ) (H : ComplexModel (n + (m + 1)) → ℝ) (hHm : Measurable H) (D : ℝ)
      (hHb : ∀ q, ‖H q‖ ≤ D) :
      Integrable (fun z => fibreIntegral μ (fun q => χ q * H q) ((stripModelEquiv m).symm (z, τ)))
        ∧ ∫ y, fibreRestrict (n := n + m) χ τ y * fibreRestrict (n := n + m) H τ y ∂(μ' τ) =
          (∫ z, fibreIntegral μ (fun q => χ q * H q) ((stripModelEquiv m).symm (z, τ))) /
            Real.pi ^ m := by
    have h := ih (fibreOpens (n := n + m) Ω τ) (fibreTuple (n := n + m) u τ) (hbaseτ τ) (μ' τ)
      (hμ' τ) (fun z => μ ((stripModelEquiv m).symm (z, τ))) (hμτ τ)
      (fibreRestrict (n := n + m) χ τ) (hχτ τ) (hχτc τ) (hχτΩ τ) (fun y => hχ0 _)
      (fibreRestrict (n := n + m) H τ) (hHm.comp (continuous_fibreMap τ).measurable) D
      (fun y => hHb _)
    have e : (fibreIntegral (fun z => μ ((stripModelEquiv m).symm (z, τ)))
        fun y => fibreRestrict (n := n + m) χ τ y * fibreRestrict (n := n + m) H τ y) =
        fun z => fibreIntegral μ (fun q => χ q * H q) ((stripModelEquiv m).symm (z, τ)) := by
      funext z
      rw [← fibreIntegral_succ]
      rfl
    rw [e] at h
    exact h
  -- one-dimensional slicing of the last base coordinate (TN)
  have hTN := BedfordTaylorBorelFibreSlicing.integral_mul_borel_isBTLimit_eq_fibre
    (n := n + m) hlast hν hμ' hχ hχc hχΩ hχ0 hFm hFb
  have hTN1 := BedfordTaylorBorelFibreSlicing.integral_mul_borel_isBTLimit_eq_fibre
    (n := n + m) hlast hν hμ' hχ hχc hχΩ hχ0 (F := fun _ : ComplexModel (n + (m + 1)) => (1 : ℝ))
    measurable_const
    (C := 1) (fun _ => by simp)
  -- the joint fibre integrals on `ℂᵐ⁺¹`
  set G : ComplexModel (m + 1) → ℝ := fibreIntegral μ fun q => χ q * F q with hGdef
  set G1 : ComplexModel (m + 1) → ℝ := fibreIntegral μ fun q => χ q * (fun _ => (1 : ℝ)) q
    with hG1def
  set j : ComplexModel m × ℂ → ComplexModel (m + 1) := ⇑(stripModelEquiv m).symm with hjdef
  have hmp : MeasurePreserving j (volume.prod volume) volume :=
    measurePreserving_stripModelEquiv_symm (n := m)
  have hemb : MeasurableEmbedding j := (stripModelEquiv m).symm.toHomeomorph.measurableEmbedding
  have hGm : AEStronglyMeasurable G volume :=
    aestronglyMeasurable_fibreIntegral_mul hν hμ hχ hχc hχΩ hFm hFb
  have hG1m : AEStronglyMeasurable G1 volume :=
    aestronglyMeasurable_fibreIntegral_mul hν hμ hχ hχc hχΩ measurable_const
      (C := 1) (fun _ => by simp)
  have hG10 (w : ComplexModel (m + 1)) : 0 ≤ G1 w :=
    integral_nonneg fun x => by simp only [mul_one]; exact hχ0 _
  have hGle (w : ComplexModel (m + 1)) : ‖G w‖ ≤ C * G1 w := by
    have hint := integrable_fibre_test hμ hχ hχc hχΩ w
    have hb : ‖∫ x, χ (fibreMapM n (m + 1) w x) * F (fibreMapM n (m + 1) w x) ∂(μ w)‖ ≤
        ∫ x, C * fibreRestrictM χ w x ∂(μ w) :=
      norm_integral_le_of_norm_le (hint.const_mul C) (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hFb _) (hχ0 _))
    rw [integral_const_mul] at hb
    simpa only [hGdef, hG1def, fibreIntegral, fibreRestrictM, mul_one] using hb
  -- integrability of `G1 ∘ j`, then of `G ∘ j`, by Tonelli
  have hG1j : Integrable (G1 ∘ j) (volume.prod volume) := by
    refine (integrable_prod_iff' (hG1m.comp_measurePreserving hmp)).2 ⟨?_, ?_⟩
    · exact Eventually.of_forall fun τ => (IH τ (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by simp)).1
    · have hint : Integrable (fun τ : ℂ => Real.pi ^ m * ∫ y,
          fibreRestrict (n := n + m) χ τ y * fibreRestrict (n := n + m) (fun _ => (1 : ℝ)) τ y
            ∂(μ' τ)) := hTN1.2.2.1.const_mul _
      refine hint.congr (Eventually.of_forall fun τ => ?_)
      have h := (IH τ (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by simp)).2
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hG10 _)]
      have hpi : Real.pi ^ m ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
      calc _ = Real.pi ^ m * ((∫ z, G1 (j (z, τ))) / Real.pi ^ m) :=
            congrArg (fun t => Real.pi ^ m * t) h
        _ = _ := by field_simp
  have hGj : Integrable (G ∘ j) (volume.prod volume) :=
    (hG1j.const_mul C).mono' (hGm.comp_measurePreserving hmp)
      (Eventually.of_forall fun p => hGle (j p))
  have hGint : Integrable G volume := (hmp.integrable_comp_emb hemb).1 hGj
  refine ⟨hGint, ?_⟩
  -- the identity
  have hfub : ∫ w, G w = ∫ τ : ℂ, ∫ z, G (j (z, τ)) := by
    rw [← hmp.integral_comp hemb G]
    exact integral_prod_symm (fun p => G (j p)) hGj
  refine hTN.2.2.2.trans ?_
  rw [hfub]
  have hinner : (fun τ : ℂ => ∫ y, fibreRestrict (n := n + m) χ τ y *
      fibreRestrict (n := n + m) F τ y ∂(μ' τ)) =
      fun τ => (∫ z, G (j (z, τ))) / Real.pi ^ m := by
    funext τ
    exact (IH τ F hFm C hFb).2
  rw [hinner, integral_div, pow_succ, div_div]

/-- **Bedford–Taylor slicing over a base `ℂᵐ`.** -/
theorem slicingClaim (n m : ℕ) : SlicingClaim n m := by
  induction m with
  | zero => exact slicingClaim_zero
  | succ m ih => exact slicingClaim_succ ih

/-- **Bedford–Taylor slicing over a base `ℂᵐ`**, with bounded Borel weights:
`∫ χ F dν = π^{-m} ∫_{ℂᵐ} ∫ χ(x, z) F(x, z) dμ_z(x) dz` for `ν` the Bedford–Taylor limit of
`(u₁, …, uₙ, |z₁|², …, |z_m|²)` and `μ_z` those of the fibre tuples. -/
theorem integral_mul_isBTLimit_eq_fibreIntegral {m : ℕ} {Ω : Opens (ComplexModel (n + m))}
    {u : Fin (n + m) → ComplexModel (n + m) → ℝ}
    (hbase : ∀ k : Fin m, u (Fin.natAdd n k) = baseNormSq n m k)
    {ν : Measure (ComplexModel (n + m))} (hν : IsBTLimit Ω u ν)
    {μ : ComplexModel m → Measure (ComplexModel n)}
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    {χ : ComplexModel (n + m) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hχ0 : ∀ q, 0 ≤ χ q)
    {F : ComplexModel (n + m) → ℝ} (hFm : Measurable F) {C : ℝ} (hFb : ∀ q, ‖F q‖ ≤ C) :
    Integrable (fibreIntegral μ fun q => χ q * F q) ∧
      ∫ q, χ q * F q ∂ν = (∫ z, fibreIntegral μ (fun q => χ q * F q) z) / Real.pi ^ m :=
  slicingClaim n m Ω u hbase ν hν μ hμ χ hχ hχc hχΩ hχ0 F hFm C hFb

end SGPT.NPP.FibreSlicing
