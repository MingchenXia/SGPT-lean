import SGPT.PSH.SourceTestCurvePrefixEnergy

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine closed-trace concavity forces strict domination of every earlier
summand. All actual slice values are proved finite before their real readback. -/
theorem SourceTestCurvePredata.prefixWinning_earlier_summand
    (Γ : SourceTestCurvePredata θ) {d : ℝ} (hd : 0 < d) (t : ℝ)
    (j : ℤ) (x : M)
    (hwin : sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) <
      sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
        ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal))
    (k : ℤ) (hkj : k < j) :
    sourceTestCurveAt Γ ((k : ℝ) * d) x + ((t * (k : ℝ) * d : ℝ) : EReal) <
      sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) := by
  let u : ℤ → EReal := fun i => sourceTestCurveAt Γ ((i : ℝ) * d) x
  have htop (i : ℤ) : u i ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (0 : EReal) ≠ ⊤) (Γ.at_le_zero _ x)
  have hnew : u (j + 1) ≠ ⊥ := by
    intro h
    change u j + _ < u (j + 1) + _ at hwin
    rw [h, EReal.bot_add] at hwin
    exact not_lt_bot hwin
  have hfinite (i : ℤ) (hi : i ≤ j + 1) : u i ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot hnew
    apply Γ.at_antitone x
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hd.le
  have hkbot := hfinite k (by omega)
  have hjbot := hfinite j (by omega)
  let r : ℤ → ℝ := fun i => (u i).toReal
  have hkval : u k = ((r k : ℝ) : EReal) := (EReal.coe_toReal (htop k) hkbot).symm
  have hjval : u j = ((r j : ℝ) : EReal) := (EReal.coe_toReal (htop j) hjbot).symm
  have hnval : u (j + 1) = ((r (j + 1) : ℝ) : EReal) :=
    (EReal.coe_toReal (htop _) hnew).symm
  let D : ℝ := (j : ℝ) + 1 - (k : ℝ)
  have hkjR : (k : ℝ) < (j : ℝ) := by exact_mod_cast hkj
  have hD : 0 < D := by dsimp [D]; linarith
  have hDne : D ≠ 0 := ne_of_gt hD
  let a : ℝ := 1 / D
  let b : ℝ := ((j : ℝ) - (k : ℝ)) / D
  have ha : 0 < a := one_div_pos.mpr hD
  have hb : 0 < b := div_pos (sub_pos.mpr hkjR) hD
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div]
    apply (div_eq_one_iff_eq hDne).mpr
    dsimp [D]
    ring
  have hparam : a * ((k : ℝ) * d) + b * (((j + 1 : ℤ) : ℝ) * d) =
      (j : ℝ) * d := by
    push_cast
    dsimp [a, b]
    field_simp [hDne]
    dsimp [D]
    ring
  have hp : (((k : ℝ) * d), -(r k)) ∈ SGPT.Convex.epigraph
      (sourceTestCurveClosedNegativeTrace Γ x) := by
    change -(u k) ≤ ((-(r k) : ℝ) : EReal)
    rw [hkval, EReal.coe_neg]
  have hq : ((((j + 1 : ℤ) : ℝ) * d), -(r (j + 1))) ∈ SGPT.Convex.epigraph
      (sourceTestCurveClosedNegativeTrace Γ x) := by
    change -(u (j + 1)) ≤ ((-(r (j + 1)) : ℝ) : EReal)
    rw [hnval, EReal.coe_neg]
  have hc := Γ.closedNegativeTrace_convex x hp hq ha.le hb.le hab
  change -sourceTestCurveAt Γ
    (a * ((k : ℝ) * d) + b * (((j + 1 : ℤ) : ℝ) * d)) x ≤
      ((a * (-(r k)) + b * (-(r (j + 1))) : ℝ) : EReal) at hc
  rw [hparam] at hc
  change -(u j) ≤ _ at hc
  rw [hjval, ← EReal.coe_neg] at hc
  have hcR : -(r j) ≤ a * (-(r k)) + b * (-(r (j + 1))) := by exact_mod_cast hc
  change u j + _ < u (j + 1) + _ at hwin
  rw [hjval, hnval, ← EReal.coe_add, ← EReal.coe_add] at hwin
  have hwR : r j + t * (j : ℝ) * d <
      r (j + 1) + t * ((j + 1 : ℤ) : ℝ) * d := by exact_mod_cast hwin
  have hlin : a * (t * (k : ℝ) * d) + b * (t * ((j + 1 : ℤ) : ℝ) * d) =
      t * (j : ℝ) * d := by nlinarith [congrArg (fun z : ℝ => t * z) hparam]
  have hstrict : r k + t * (k : ℝ) * d < r j + t * (j : ℝ) * d := by
    by_contra hn
    have hnR := le_of_not_gt hn
    have hp1 := mul_nonneg ha.le (sub_nonneg.mpr hnR)
    have hp2 := mul_pos hb (sub_pos.mpr hwR)
    have he := congrArg (fun z : ℝ => z * (r j + t * (j : ℝ) * d)) hab
    nlinarith
  change u k + _ < u j + _
  rw [hkval, hjval, ← EReal.coe_add, ← EReal.coe_add]
  exact_mod_cast hstrict

/-- The literal old prefix equals its last term whenever the next term wins. -/
theorem SourceTestCurvePredata.prefixWinning_old_branch
    (Γ : SourceTestCurvePredata θ) {d : ℝ} (hd : 0 < d) (t : ℝ)
    (j : ℤ) (x : M)
    (hwin : sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) <
      sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
        ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal)) :
    sourceTestCurveIntegerPrefix Γ d t j x =
      sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases he : k.1 = j
    · rw [he]
    · exact (Γ.prefixWinning_earlier_summand hd t j x hwin k.1
        (lt_of_le_of_ne k.2 he)).le
  · exact le_iSup (fun k : Iic j => sourceTestCurveAt Γ ((k.1 : ℝ) * d) x +
      ((t * (k.1 : ℝ) * d : ℝ) : EReal)) ⟨j, by change j ≤ j; exact le_rfl⟩

/-- Exact equality of the strict winning sets of actual consecutive prefixes
and actual consecutive summands, without regularizing either prefix. -/
theorem SourceTestCurvePredata.prefixWinning_iff
    (Γ : SourceTestCurvePredata θ) {d : ℝ} (hd : 0 < d) (t : ℝ)
    (j : ℤ) (x : M) :
    sourceTestCurveIntegerPrefix Γ d t j x < sourceTestCurveIntegerPrefix Γ d t (j + 1) x ↔
      sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) <
      sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
        ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal) := by
  rw [Γ.integerPrefix_succ]
  change _ < Max.max _ _ ↔ _
  constructor
  · intro h
    have hn := (lt_max_iff.mp h).resolve_left (lt_irrefl _)
    exact lt_of_le_of_lt (le_iSup (fun k : Iic j =>
      sourceTestCurveAt Γ ((k.1 : ℝ) * d) x + ((t * (k.1 : ℝ) * d : ℝ) : EReal))
      ⟨j, by change j ≤ j; exact le_rfl⟩) hn
  · intro h
    rw [Γ.prefixWinning_old_branch hd t j x h]
    exact lt_max_of_lt_right h

/-- Literal equality of the two strict winning regions. -/
theorem SourceTestCurvePredata.prefixWinning_set
    (Γ : SourceTestCurvePredata θ) {d : ℝ} (hd : 0 < d) (t : ℝ) (j : ℤ) :
    {x | sourceTestCurveIntegerPrefix Γ d t j x < sourceTestCurveIntegerPrefix Γ d t (j + 1) x} =
    {x | sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) <
      sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
        ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal)} := by
  ext x
  exact Γ.prefixWinning_iff hd t j x

/-- Both literal prefix branch identities on their actual strict winning set. -/
theorem SourceTestCurvePredata.prefixWinning_branches
    (Γ : SourceTestCurvePredata θ) {d : ℝ} (hd : 0 < d) (t : ℝ)
    (j : ℤ) (x : M)
    (hwin : sourceTestCurveIntegerPrefix Γ d t j x <
      sourceTestCurveIntegerPrefix Γ d t (j + 1) x) :
    sourceTestCurveIntegerPrefix Γ d t j x =
      sourceTestCurveAt Γ ((j : ℝ) * d) x + ((t * (j : ℝ) * d : ℝ) : EReal) ∧
    sourceTestCurveIntegerPrefix Γ d t (j + 1) x =
      sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
        ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal) := by
  have hw := (Γ.prefixWinning_iff hd t j x).mp hwin
  have ho := Γ.prefixWinning_old_branch hd t j x hw
  refine ⟨ho, ?_⟩
  rw [Γ.integerPrefix_succ]
  change Max.max _ _ = _
  rw [ho, max_eq_right hw.le]

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
/-- Strictness for the previous prefix uses the internally produced FINITE
collapse of the actual bounded test curve, never an infinite strict supremum. -/
theorem SourceTestCurve.prefixWinning_strict_previous
    {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ) (x : M)
    (hwin : sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x <
      sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x) :
    sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j - 1) x <
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((j : ℝ) * d) x +
        ((t * (j : ℝ) * d : ℝ) : EReal) := by
  classical
  have hw := (Γ.toSourceTestCurvePredata.prefixWinning_iff hd t j x).mp hwin
  obtain ⟨L, hL, _, heq⟩ := Γ.integerPrefix_finite hΓ hd ht (j - 1)
  rw [heq]
  let I := {k : ℤ // k ∈ Finset.Icc L (j - 1)}
  have : Nonempty I := ⟨⟨L, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩⟩⟩
  have hall (k : I) :
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((k.1 : ℝ) * d) x +
        ((t * (k.1 : ℝ) * d : ℝ) : EReal) <
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((j : ℝ) * d) x +
        ((t * (j : ℝ) * d : ℝ) : EReal) := by
    apply Γ.toSourceTestCurvePredata.prefixWinning_earlier_summand hd t j x hw k.1
    have := (Finset.mem_Icc.mp k.2).2
    omega
  dsimp only
  rw [iSup_subtype]
  dsimp only
  apply (Set.Nonempty.ciSup_lt_iff
    (show (↑(Finset.Icc L (j - 1)) : Set ℤ).Nonempty from
      ⟨L, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩⟩) (Finset.Icc L (j - 1)).finite_toSet).mpr
  intro k hk
  exact hall ⟨k, hk⟩

end SGPT.PSH.VariableComplexAtlas
