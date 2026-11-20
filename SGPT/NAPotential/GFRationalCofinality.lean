import SGPT.NAPotential.GFRationalVertexSectionFamily

/-! # Rational parameter cofinality for the ORIGINAL finite concave hull
Blueprint: `gf-rational-hull-cofinality.tex`. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open SGPT.Convex.CutSimplex
open scoped BigOperators Classical

/-- The literal ORIGINAL cut-vertex expression on a finite family of extended-real values. -/
def cutVertexMaximum {ι : Type*} [Fintype ι] (τ : ι → ℝ) (s : ℝ) (A : ι → EReal) : EReal :=
  ⨆ v : VertexIndex τ s, ∑ i, ((vertexVector τ s v i : ℝ) : EReal) * A i

theorem coe_finite_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ((∑ i ∈ s, a i : ℝ) : EReal) = ∑ i ∈ s, (a i : EReal) := by
  let c : ℝ →+ EReal := ⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩
  exact map_sum c a s

theorem weighted_constant_sum {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) (a : EReal) :
    ∑ i, (w i : EReal) * a = a := by
  have h (s : Finset ι) : ∑ i ∈ s, (w i : EReal) * a = ((∑ i ∈ s, w i : ℝ) : EReal) * a := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]
      exact (EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr (hw i))
        (EReal.coe_nonneg.mpr (Finset.sum_nonneg (fun i _ => hw i)))).symm
  rw [h, hmass]
  simp

theorem weighted_shift_sum {ι : Type*} [Fintype ι] (w τ : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (A : ι → EReal) :
    (∑ i, (w i : EReal) * A i) + ((∑ i, w i * τ i : ℝ) : EReal) =
      ∑ i, (w i : EReal) * (A i + (τ i : EReal)) := by
  rw [coe_finite_sum]
  simp_rw [EReal.coe_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (hw i))
    (EReal.coe_ne_top (w i)) _ _).symm

/-- Every actual ORIGINAL feasible cut weight obeys the finite Legendre bound. -/
theorem cut_weighted_add_le_nodeMaximum {ι : Type*} [Fintype ι]
    (τ : ι → ℝ) (A : ι → EReal) (s : ℝ) (w : ι → ℝ) (hw : w ∈ cut τ s) :
    (∑ i, (w i : EReal) * A i) + (s : EReal) ≤ ⨆ i, A i + (τ i : EReal) := by
  obtain ⟨hnonneg, hmass, htime⟩ := (mem_cut_iff τ s w).mp hw
  calc
    _ ≤ (∑ i, (w i : EReal) * A i) + ((∑ i, w i * τ i : ℝ) : EReal) :=
      add_le_add le_rfl (EReal.coe_le_coe_iff.mpr htime)
    _ = ∑ i, (w i : EReal) * (A i + (τ i : EReal)) := weighted_shift_sum w τ hnonneg A
    _ ≤ ∑ i, (w i : EReal) * (⨆ j, A j + (τ j : EReal)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (le_iSup (fun j => A j + (τ j : EReal)) i)
        (EReal.coe_nonneg.mpr (hnonneg i))
    _ = _ := weighted_constant_sum w hnonneg hmass _

/-- Every actual ORIGINAL rational (or irrational) cut-vertex maximum obeys the same bound. -/
theorem cutVertexMaximum_add_le_nodeMaximum {ι : Type*} [Fintype ι]
    (τ : ι → ℝ) (A : ι → EReal) (s : ℝ) (i₀ : ι) (hs : s ≤ τ i₀) :
    cutVertexMaximum τ s A + (s : EReal) ≤ ⨆ i, A i + (τ i : EReal) := by
  let : Nonempty (VertexIndex τ s) := ⟨Sum.inl ⟨i₀, hs⟩⟩
  obtain ⟨v, hv⟩ := exists_eq_ciSup_of_finite
    (f := fun v : VertexIndex τ s => ∑ i, ((vertexVector τ s v i : ℝ) : EReal) * A i)
  rw [cutVertexMaximum, ← hv]
  exact cut_weighted_add_le_nodeMaximum τ A s _ (vertexVector_isExtreme τ s v).1

/-- Every original admissible node is actually one of the ORIGINAL vertices. -/
theorem node_le_cutVertexMaximum {ι : Type*} [Fintype ι] (τ : ι → ℝ) (A : ι → EReal)
    (s : ℝ) (i : ι) (hs : s ≤ τ i) : A i ≤ cutVertexMaximum τ s A := by
  have hb : (∑ j, ((vertexVector τ s (Sum.inl ⟨i, hs⟩) j : ℝ) : EReal) * A j) = A i := by
    simp only [vertexVector, basis]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [← hb]
  exact le_iSup (fun v : VertexIndex τ s => ∑ j,
    ((vertexVector τ s v j : ℝ) : EReal) * A j) (Sum.inl ⟨i, hs⟩)

/-- Rational parameters approach EVERY real parameter from below, also for polar values. -/
theorem add_real_le_rational_iSup (a : EReal) (t : ℝ) :
    a + (t : EReal) ≤ ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < t), a + ((q : ℝ) : EReal) := by
  cases a with
  | bot => simp
  | top =>
    obtain ⟨q, hq⟩ := exists_rat_lt t
    calc
      _ = (⊤ : EReal) := by simp
      _ = (⊤ : EReal) + ((q : ℝ) : EReal) := by simp
      _ ≤ _ := le_iSup_of_le q (le_iSup_of_le hq (by simp))
  | coe a =>
    rw [← EReal.coe_add]
    apply le_of_forall_lt_imp_le_of_dense
    intro z hz
    obtain ⟨r, hzr, hrt⟩ := EReal.lt_iff_exists_real_btwn.mp hz
    have hr : r - a < t := by
      have h := EReal.coe_lt_coe_iff.mp hrt
      linarith
    obtain ⟨q, hrq, hqt⟩ := exists_rat_btwn hr
    calc
      z ≤ (r : EReal) := hzr.le
      _ ≤ ((a + (q : ℝ) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
      _ = (a : EReal) + ((q : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ _ := le_iSup_of_le q (le_iSup_of_le hqt (by rfl))

/-- The ORIGINAL finite Legendre maximum equals the supremum of ORIGINAL rational cut-vertex values. -/
theorem nodeMaximum_eq_rational_cutVertexSup {ι : Type*} [Fintype ι]
    (τ : ι → ℝ) (A : ι → EReal) (i₀ : ι) (htop : ∀ i, τ i ≤ τ i₀) :
    (⨆ i, A i + (τ i : EReal)) =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < τ i₀), cutVertexMaximum τ (q : ℝ) A + ((q : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply (add_real_le_rational_iSup (A i) (τ i)).trans
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le q (le_iSup_of_le (hq.trans_le (htop i))
      (add_le_add (node_le_cutVertexMaximum τ A (q : ℝ) i hq.le) le_rfl))
  · exact iSup_le fun q => iSup_le fun hq =>
      cutVertexMaximum_add_le_nodeMaximum τ A (q : ℝ) i₀ hq.le

/-- Antitonicity alone extends the rational formula to ALL original real parameters. -/
theorem antitone_real_parameterSup_eq_rational (F : ℝ → EReal) (hF : Antitone F) (T : ℝ) :
    (⨆ s : ℝ, ⨆ (_ : s ≤ T), F s + (s : EReal)) =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < T), F q + ((q : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    apply (add_real_le_rational_iSup (F s) s).trans
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le q (le_iSup_of_le (hq.trans_le hs)
      (add_le_add (hF hq.le) le_rfl))
  · exact iSup_le fun q => iSup_le fun hq =>
      le_iSup_of_le (q : ℝ) (le_iSup_of_le hq.le le_rfl)

end SGPT.NAPotential.BJ.GfIm.RationalHull
