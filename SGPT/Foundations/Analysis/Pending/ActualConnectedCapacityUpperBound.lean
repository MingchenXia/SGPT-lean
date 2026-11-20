import SGPT.Foundations.Analysis.Pending.ActualChartTruncatedCapacityConvergence
import SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum

set_option autoImplicit false

/-! # Actual eventual upper bounds from capacity convergence

Independent connected-ambient adaptation of the normalized Harnack
volume bound. Supremum normalization, positive finite-value bands and
genuine polar nullity produce the bound; it is not a caller certificate.
The nonconnected component transport and unbounded mixed mass liminf
remain separate obligations.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualConnectedCapacityUpperBound

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
  IntegrationCurrent ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem normalized_integral_bound (omega : KahlerBackground n M)
    (α : ClosedRealOneOneForm n M) [Nonempty M] :
    ∃ B : ENNReal, B < ⊤ ∧ ∀ u : M → EReal, IsThetaPshPotential α.val u →
      ∫⁻ x, (-(u x - (((⨆ y, u y).toReal : ℝ) : EReal))).toENNReal
        ∂kahlerVolume omega ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    SingularModelUniformModelL1.exists_uniform_lintegral_neg_le_kahlerVolume α omega 1
  refine ⟨B, hB, fun u hu => ?_⟩
  let S : ℝ := (⨆ y, u y).toReal
  have hfin := ModelRaySupremum.iSup_ne_top_ne_bot hu
  have hS : (S : EReal) = ⨆ y, u y := EReal.coe_toReal hfin.1 hfin.2
  have hnonpos : ∀ x, u x - (S : EReal) ≤ 0 := by
    intro x
    apply (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot S))
      (Or.inl (EReal.coe_ne_top S))).mpr
    simpa only [zero_add] using (hS.symm ▸ le_iSup u x)
  have hpoint : ∃ x, ((-(1 : ℝ) : ℝ) : EReal) ≤ u x - (S : EReal) := by
    by_contra hn
    have hlow : ∀ x, u x ≤ ((S - 1 : ℝ) : EReal) := by
      intro x
      have hx : u x - (S : EReal) < ((-(1 : ℝ) : ℝ) : EReal) :=
        lt_of_not_ge (fun hh => hn ⟨x, hh⟩)
      have hxle := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot S))
        (Or.inl (EReal.coe_ne_top S))).mp hx.le
      simpa only [← EReal.coe_add, show -(1 : ℝ) + S = S - 1 by ring] using hxle
    have hc : S ≤ S - 1 := EReal.coe_le_coe_iff.mp (hS.symm ▸ iSup_le hlow)
    linarith
  exact hbound _ (hu.sub_const S).1 hnonpos hpoint

omit [ConnectedSpace M] in
private theorem exists_positive_finite_band (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {v : M → EReal}
    (hv : IsThetaPshPotential α.val v) [Nonempty M] :
    ∃ k : ℕ, 0 < (kahlerVolume omega) {x | v x ≠ ⊥ ∧ |(v x).toReal| ≤ (k : ℝ)} := by
  let μ := kahlerVolume omega
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hpole : μ {x | v x = ⊥} = 0 :=
    GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate (fun _ => hzero.1) hv
  have haefinite : ∀ᵐ x ∂μ, v x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not] using hpole
  have hunion : (⋃ k : ℕ, {x | v x ≠ ⊥ ∧ |(v x).toReal| ≤ (k : ℝ)}) =ᵐ[μ] univ := by
    filter_upwards [haefinite] with x hx
    obtain ⟨k, hk⟩ := exists_nat_ge |(v x).toReal|
    have hmem : x ∈ ⋃ k : ℕ, {x | v x ≠ ⊥ ∧ |(v x).toReal| ≤ (k : ℝ)} :=
      mem_iUnion.mpr ⟨k, hx, hk⟩
    exact propext ⟨fun _ => mem_univ x, fun _ => hmem⟩
  have hpos : 0 < μ univ := KahlerVolumePositive.diagonalPotentialMass_zero_pos omega
  exact exists_measure_pos_of_not_measure_iUnion_null
    (by rw [measure_congr hunion]; exact hpos.ne')

/-- Actual capacity convergence to a genuine potential internally produces
an eventual everywhere upper bound, without an incoming family bound. -/
theorem exists_eventual_upper_bound (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {I : Type*} {F : Filter I}
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential α.val (u j)) (hv : IsThetaPshPotential α.val v)
    (hcap : ∀ a : ℝ, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}) F (𝓝 0)) :
    ∃ H : ℝ, ∀ᶠ j in F, ∀ x, u j x ≤ (H : EReal) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hE =>
      let _ := hE
      exact ⟨0, Eventually.of_forall fun _ x => isEmptyElim x⟩
  | inr hE =>
      let _ := hE
      let μ := kahlerVolume omega
      let _ : IsFiniteMeasure μ := inferInstance
      obtain ⟨B, hB, hnorm⟩ := normalized_integral_bound omega α
      obtain ⟨k, hk⟩ := exists_positive_finite_band omega hv
      let T : Set M := {x | v x ≠ ⊥ ∧ |(v x).toReal| ≤ (k : ℝ)}
      let m : ℝ := μ.real T
      have hm : 0 < m := ENNReal.toReal_pos hk.ne' (measure_ne_top μ T)
      have hvmeas : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      have hpv : MeasurableSet {x | v x = ⊥} := measurableSet_eq_fun hvmeas measurable_const
      have hvabs : Measurable (fun x => |(v x).toReal|) := by
        simpa only [Real.norm_eq_abs] using hvmeas.ereal_toReal.norm
      have hT : MeasurableSet T := hpv.compl.inter
        (measurableSet_le hvabs measurable_const)
      let t : ℝ := 2 * (B.toReal + 1) / m
      have ht : 0 < t := div_pos (by positivity) hm
      have htm : t * m / 2 = B.toReal + 1 := by
        dsimp [t]
        field_simp
      let H : ℝ := (k : ℝ) + 1 + t
      refine ⟨H, ?_⟩
      have hevent := (hcap 1 one_pos).eventually_lt_const
        (ENNReal.ofReal_pos.mpr (half_pos hm))
      filter_upwards [hevent] with j hj
      let S : Set M := {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧
        1 < |(u j x).toReal - (v x).toReal|}
      let P : Set M := {x | u j x = ⊥}
      let G : Set M := T \ (S ∪ P)
      have humeas : Measurable (u j) :=
        (hu j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      have hP : MeasurableSet P := measurableSet_eq_fun humeas measurable_const
      have hgapmeas : Measurable (fun x => |(u j x).toReal - (v x).toReal|) := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using
          (humeas.ereal_toReal.sub hvmeas.ereal_toReal).norm
      have hS : MeasurableSet S := hP.compl.inter (hpv.compl.inter
        (measurableSet_lt measurable_const hgapmeas))
      have hG : MeasurableSet G := hT.diff (hS.union hP)
      have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
      have hpole : μ P = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ => hzero.1) (hu j)
      have hdom : μ S ≤ thetaCapacity omega.form (fun _ => 0) S :=
        diagonalPotentialMeasure_le_thetaCapacity hzero le_rfl (fun _ => by norm_num) S
      have hbad : μ.real S ≤ m / 2 := by
        have he : μ S ≤ ENNReal.ofReal (m / 2) := hdom.trans hj.le
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
          (ENNReal.toReal_ofReal (half_pos hm).le)
      have hpoleReal : μ.real P = 0 := by simp only [Measure.real, hpole, ENNReal.toReal_zero]
      have hbadUnion : μ.real (S ∪ P) ≤ m / 2 := by
        have hh := measureReal_union_le (μ := μ) S P
        linarith
      have hgood : m / 2 ≤ μ.real G := by
        have hadd : μ.real G + μ.real (T ∩ (S ∪ P)) = m :=
          measureReal_sdiff_add_inter (hS.union hP)
        have hint : μ.real (T ∩ (S ∪ P)) ≤ m / 2 :=
          (measureReal_mono inter_subset_right).trans hbadUnion
        linarith
      let A : ℝ := (⨆ x, u j x).toReal
      have hfin := ModelRaySupremum.iSup_ne_top_ne_bot (hu j)
      have hA : (A : EReal) = ⨆ x, u j x := EReal.coe_toReal hfin.1 hfin.2
      have hAH : A ≤ H := by
        by_contra hn
        have hHlt : H < A := lt_of_not_ge hn
        have hgap : ∀ x ∈ G, t ≤ A - (u j x).toReal := by
          intro x hx
          have hxT : x ∈ T := hx.1
          have hxb : u j x ≠ ⊥ := fun hh => hx.2 (Or.inr hh)
          have habs : |(u j x).toReal - (v x).toReal| ≤ 1 := by
            by_contra hh
            exact hx.2 (Or.inl ⟨hxb, hxT.1, lt_of_not_ge hh⟩)
          have hvup : (v x).toReal ≤ (k : ℝ) := le_trans (le_abs_self _) hxT.2
          have huup : (u j x).toReal ≤ (k : ℝ) + 1 := by
            linarith [(abs_le.mp habs).2]
          dsimp [H] at hHlt
          linarith
        have hlin : ENNReal.ofReal t * μ G ≤
            ∫⁻ x, (-(u j x - (A : EReal))).toENNReal ∂μ := by
          rw [← lintegral_indicator_const hG (ENNReal.ofReal t)]
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ G
          · rw [indicator_of_mem hx]
            change ENNReal.ofReal t ≤ (-(u j x - (A : EReal))).toENNReal
            have hxb : u j x ≠ ⊥ := fun hh => hx.2 (Or.inr hh)
            have hxt : u j x ≠ ⊤ := (hu j).quasiPshPotential.1.ne_top x
            rw [← EReal.coe_toReal hxt hxb, ← EReal.coe_sub, ← EReal.coe_neg,
              EReal.real_coe_toENNReal]
            apply ENNReal.ofReal_le_ofReal
            linarith [hgap x hx]
          · rw [indicator_of_notMem hx]
            exact bot_le
        have hlower : t * μ.real G ≤ B.toReal := by
          have hh := ENNReal.toReal_mono hB.ne (hlin.trans (hnorm (u j) (hu j)))
          simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, Measure.real] using hh
        have hprod : t * (m / 2) ≤ t * μ.real G :=
          mul_le_mul_of_nonneg_left hgood ht.le
        rw [← mul_div_assoc, htm] at hprod
        linarith
      intro x
      exact (hA.symm ▸ le_iSup (u j) x).trans (EReal.coe_le_coe_iff.mpr hAH)

end
end SGPT.Foundations.Analysis.Pending.ActualConnectedCapacityUpperBound
