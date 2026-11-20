import SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  HironakaHolomorphicJetRankLoci BlowupFlatCoordinates

universe u

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {E : Set Y} {y : Y}

omit [IsComplexManifold (m + 1) Y] in
/-- The literal SAME flattening proves regularity; no regularity certificate is supplied. -/
theorem regularAtDim_of_divisorFlattening (Φ : DivisorFlattening (m := m) E y) :
    RegularAtDim (n := m + 1) E y m := by
  have hyE : y ∈ E := (Φ.mem_iff y (mem_complexChartAt_source y) Φ.chart_mem_source).mpr
    (by simp only [Φ.map_center, PiLp.zero_apply])
  refine ⟨Nat.le_succ m, hyE, Φ.Φ, Φ.source_subset, Φ.map_center, ?_⟩
  intro z hz hzΦ
  refine (Φ.mem_iff z hz hzΦ).trans ?_
  change Φ.Φ.toFun ((complexChartAt (n := m + 1) y).val z) (Fin.last m) = 0 ↔
    ∀ i : Fin (m + 1), m ≤ i.val → Φ.Φ.toFun ((complexChartAt (n := m + 1) y).val z) i = 0
  constructor
  · intro h i hi
    have hlt := i.isLt
    have heq : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    simpa only [heq] using h
  · intro h
    exact h (Fin.last m) (by simp)

private theorem flat_equation_holomorphic (Φ : DivisorFlattening (m := m) E y) :
    HolomorphicAt (m + 1) (flatCoord Φ.Φ (Fin.last m)) y :=
  holomorphicAt_flatCoord Φ.Φ (Fin.last m) (mem_flatDomain_self Φ.Φ)

/-- Genuine codimension-one Hadamard division gives the whole original stalk generator. -/
theorem vanishingIdeal_mem_iff_flat_equation (Φ : DivisorFlattening (m := m) E y)
    (f : Y → ℂ) :
    (vanishingIdeal (n := m + 1) E).mem y f ↔
      IsInSpanAt (n := m + 1) (· = flatCoord Φ.Φ (Fin.last m)) y f := by
  exact MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ.Φ
    (fun {z} hz hzΦ => Φ.mem_iff z hz hzΦ) (mem_flatDomain_self Φ.Φ) f

/-- Actual ideal powers, including k=0, have the literal original equation power as generator. -/
theorem idealPow_mem_iff_flat_equation (Φ : DivisorFlattening (m := m) E y)
    (k : ℕ) (f : Y → ℂ) :
    (IdealWeightPowers.idealPow (vanishingIdeal (n := m + 1) E) k).mem y f ↔
      IsInSpanAt (n := m + 1) (· = fun z => flatCoord Φ.Φ (Fin.last m) z ^ k) y f := by
  exact HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator
    (flat_equation_holomorphic Φ) (fun g => vanishingIdeal_mem_iff_flat_equation Φ g) k f

/-- The actual preferred chart right-inverse identifies the entire literal equation power germ. -/
theorem chartTranslatedGerm_flat_equation_pow (Φ : DivisorFlattening (m := m) E y) (k : ℕ) :
    chartTranslatedGerm y y (mem_chart_source _ y)
      (fun z => flatCoord Φ.Φ (Fin.last m) z ^ k)
      (CompanionReduction.holomorphicAt_pow_of (flat_equation_holomorphic Φ) k) =
      divisorEquationGerm Φ ^ k := by
  unfold chartTranslatedGerm translatedGerm divisorEquationGerm
  rw [← HolGerm.mk_pow]
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := (complexChartAt (n := m + 1) y).val
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e y) (𝓝 0) (𝓝 (e y)) := by
    simpa only [zero_add] using (continuous_add_const (e y)).tendsto 0
  filter_upwards [ht.eventually (e.open_target.mem_nhds
    (e.map_source (mem_complexChartAt_source y)))] with z hz
  change (Φ.Φ.toFun (e (e.symm (z + e y))) (Fin.last m)) ^ k =
    (Φ.Φ.toFun (z + e y) (Fin.last m)) ^ k
  rw [e.right_inv hz]

private theorem principalSpan_iff_chartTranslatedGerm_mem_span
    (u f : Y → ℂ) (hu : HolomorphicAt (m + 1) u y) (hf : HolomorphicAt (m + 1) f y) :
    IsInSpanAt (n := m + 1) (· = u) y f ↔
      chartTranslatedGerm y y (mem_chart_source _ y) f hf ∈
        Ideal.span {chartTranslatedGerm y y (mem_chart_source _ y) u hu} := by
  have hchart := ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff
    (mem_chart_source (ComplexModel (m + 1)) y) (fun _ : Fin 1 => u) f
  have htranslated := isInSpanAt_iff_translatedGerm_mem
    (fun _ : Fin 1 => fun z => u ((chartAt (ComplexModel (m + 1)) y).symm z))
    ((chartAt (ComplexModel (m + 1)) y) y)
    (fun _ => CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ y) hu)
    (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ y) hf)
  simpa only [translatedIdeal, chartTranslatedGerm, range_const, mem_singleton_iff] using
    hchart.trans htranslated

/-- Original power-stalk membership is true preferred-germ divisibility, for every original germ. -/
theorem mem_idealPow_iff_equation_pow_dvd (Φ : DivisorFlattening (m := m) E y)
    (k : ℕ) (f : Y → ℂ) (hf : HolomorphicAt (m + 1) f y) :
    (IdealWeightPowers.idealPow (vanishingIdeal (n := m + 1) E) k).mem y f ↔
      divisorEquationGerm Φ ^ k ∣ chartTranslatedGerm y y (mem_chart_source _ y) f hf := by
  rw [idealPow_mem_iff_flat_equation Φ k f]
  have hspan := principalSpan_iff_chartTranslatedGerm_mem_span
    (fun z => flatCoord Φ.Φ (Fin.last m) z ^ k) f
    (CompanionReduction.holomorphicAt_pow_of (flat_equation_holomorphic Φ) k) hf
  rw [chartTranslatedGerm_flat_equation_pow Φ k, Ideal.mem_span_singleton] at hspan
  exact hspan

/-- The genuine ENTIRE original membership stalk computes actual near-divisibility, including infinity. -/
theorem natCast_le_originalStalkNormalOrder_iff_isDivNear
    (Φ : DivisorFlattening (m := m) E y) (A : GermIdeal (m + 1) Y) (hA : A.IsCoherent) (k : ℕ) :
    (k : ℕ∞) ≤ originalStalkNormalOrder Φ A ↔ DivisorExponent.IsDivNear (m + 1) A E k y := by
  change (k : ℕ∞) ≤ idealNormalOrder Φ (wholeChartStalkIdeal A y y (mem_chart_source _ y)) ↔ _
  rw [natCast_le_idealNormalOrder_iff]
  constructor
  · intro h
    apply (DivisorExponent.isDivNear_iff hA (regularAtDim_of_divisorFlattening Φ)).mpr
    intro f hfA
    have hf := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hfA
    apply (mem_idealPow_iff_equation_pow_dvd Φ k f hf).mpr
    apply Ideal.mem_span_singleton.mp
    apply h
    exact Ideal.subset_span ⟨f, hf, hfA, rfl⟩
  · intro h
    have hdiv := (DivisorExponent.isDivNear_iff hA (regularAtDim_of_divisorFlattening Φ)).mp h
    unfold wholeChartStalkIdeal
    apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hfA, rfl⟩
    exact Ideal.mem_span_singleton.mpr ((mem_idealPow_iff_equation_pow_dvd Φ k f hf).mp (hdiv f hfA))

/-- Finite native divExp is identified only with an ACTUAL nonzero stalk member. -/
theorem originalStalkNormalOrder_eq_divExp
    (Φ : DivisorFlattening (m := m) E y) (A : GermIdeal (m + 1) Y) (hA : A.IsCoherent)
    (hne : DivisorExponent.IsNonzeroAt A y) :
    originalStalkNormalOrder Φ A = (DivisorExponent.divExp (m + 1) A E y : ℕ∞) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  rw [natCast_le_originalStalkNormalOrder_iff_isDivNear Φ A hA k]
  have hhol : ∀ z f, A.mem z f → HolomorphicAt (m + 1) f z :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hf
  exact (DivisorExponent.isDivNear_iff_le_divExp hhol
    (regularAtDim_of_divisorFlattening Φ).2.1 hne).trans ENat.natCast_le_natCast.symm

/-- Genuine connected analytic continuation gives one finite natural order, without compactness. -/
theorem exists_originalStalkNormalOrder_on_connected_hypersurface
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (A : GermIdeal (m + 1) Y) (hA : A.IsCoherent)
    (hne : ∀ z, DivisorExponent.IsNonzeroAt A z) :
    ∃ a : ℕ, ∀ y ∈ E, ∀ Φ : DivisorFlattening (m := m) E y,
      originalStalkNormalOrder Φ A = (a : ℕ∞) := by
  obtain ⟨a, ha⟩ := HironakaDivisorResidual.exists_divExp_on_connected_submanifold hE hA hne
  refine ⟨a, fun y hy Φ => ?_⟩
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  exact (natCast_le_originalStalkNormalOrder_iff_isDivNear Φ A hA k).trans
    ((ha y hy k).trans ENat.natCast_le_natCast.symm)

end SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder
