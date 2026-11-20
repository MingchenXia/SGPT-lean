import SGPT.Foundations.Analysis.Pending.ActualChartCapacityCompetitor
import SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

set_option autoImplicit false

/-! # Genuine compact relative-to-global Kähler capacity comparison

Independent bounded local competitor globalization and actual positive
Bedford--Taylor slot expansion. No capacity or weak-limit certificate is input.
All dimensions and the empty compact are retained.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualChartCapacityReverse

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  BedfordTaylor MixedMongeAmpere GlobalNonPluripolar BoundedGlobalProduct
  GlobalSlotStokes ThetaCapacity ThetaCapacityChart ThetaCapacityChartLocal

noncomputable section

/-- Internal positive slot expansion for the selected actual BT limits. -/
private theorem bt_le_add {n : ℕ} {D : Opens (ComplexModel n)}
    {a b : Fin n → ComplexModel n → ℝ}
    (ha : ∀ i, IsLocallyBoundedPshOn D (a i))
    (hb : ∀ i, IsLocallyBoundedPshOn D (b i))
    {μ ν : Measure (ComplexModel n)} (hμ : IsBTLimit D a μ)
    (hν : IsBTLimit D (fun i z => a i z + b i z) ν) : μ ≤ ν := by
  classical
  let P : ℕ → Fin n → ComplexModel n → ℝ := fun k i =>
    if i.val < k then a i else fun z => a i z + b i z
  have hPb (k : ℕ) (i : Fin n) : IsLocallyBoundedPshOn D (P k i) := by
    dsimp only [P]
    split_ifs
    · exact ha i
    · exact LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_add (ha i) (hb i)
  have key : ∀ k, k ≤ n → ∃ σ, IsBTLimit D (P k) σ ∧ σ ≤ ν := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨ν, by simpa [P] using hν, le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨σ, hσ, hσν⟩ := ih (by omega)
      let i₀ : Fin n := ⟨k, hk⟩
      have hupd (c : ComplexModel n → ℝ) (hc : IsLocallyBoundedPshOn D c)
          (i : Fin n) : IsLocallyBoundedPshOn D (Function.update (P k) i₀ c i) := by
        by_cases hi : i = i₀
        · subst i
          simpa using hc
        · simpa [Function.update_of_ne hi] using hPb k i
      obtain ⟨σa, hσa⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (hupd (a i₀) (ha i₀))
      obtain ⟨σb, hσb⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (hupd (b i₀) (hb i₀))
      have hPk : Function.update (P k) i₀ (fun z => a i₀ z + b i₀ z) = P k := by
        funext i
        by_cases hi : i = i₀
        · subst i
          simp [P, i₀]
        · simp [Function.update_of_ne hi]
      have hPk1 : Function.update (P k) i₀ (a i₀) = P (k + 1) := by
        funext i
        by_cases hi : i = i₀
        · subst i
          simp [P, i₀]
        · have hne : i.val ≠ k := fun heq => hi (Fin.ext heq)
          simp only [Function.update_of_ne hi, P]
          split_ifs with hlt hlt'
          · rfl
          · omega
          · omega
          · rfl
      have heq : σ = σa + σb := IsBTLimit.add_slot i₀ (hPk.symm ▸ hσ) hσa hσb
      refine ⟨σa, hPk1 ▸ hσa, ?_⟩
      calc σa ≤ σa + σb := Measure.le_add_right le_rfl
           _ = σ := heq.symm
           _ ≤ ν := hσν
  obtain ⟨σ, hσ, hσν⟩ := key n le_rfl
  have hPn : P n = a := by
    funext i
    simp [P, i.isLt]
  rw [hPn] at hσ
  rw [hμ.unique hσ]
  exact hσν

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The reverse comparison is produced uniformly over all local capacity
competitors on an actual compact chart core. -/
theorem exists_compact_capacity_reverse (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : Set (ComplexModel n), E ⊆ K →
      relCapacity D E ≤ ENNReal.ofReal C *
        thetaCapacity omega.form (fun _ => 0) (e.val.symm '' E) := by
  obtain ⟨δ, hδ, _h3δ, O, hO, hKO, hOU, hcomp⟩ :=
    ActualChartCapacityCompetitor.exists_global_capacity_competitor omega e hDt hρ hK hKD
  have hp : 0 < δ ^ n := pow_pos hδ n
  have hp0 : ENNReal.ofReal δ ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  have hpt : ENNReal.ofReal δ ^ n ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  refine ⟨(δ ^ n)⁻¹, inv_pos.mpr hp, fun E hEK => ?_⟩
  apply relCapacity_le_of_forall
  intro f hf hb
  obtain ⟨v, hv, hv01, hvc⟩ := hcomp f hf hb
  let J := diagSlotChart omega.form e D hDt ρ hρ
  have hvbound : ∀ i : Fin n, PatchLocalBoundedMeasure.IsBoundedPotentialOn v
      (J.source : Set M) := fun _ => ⟨-1, 0, fun x _ => hv01 x⟩
  obtain ⟨ν, hν, hνglob⟩ := exists_isBTLimit_of_boundedOn J
    (u := fun _ => v) (fun _ => hv.1) hvbound
  let Q : Opens (ComplexModel n) :=
    ⟨(D : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' O,
      (e.val.continuousOn_symm.mono hDt).isOpen_inter_preimage D.isOpen hO⟩
  have hQD : Q ≤ D := inter_subset_left
  have hEQ : E ⊆ (Q : Set (ComplexModel n)) := by
    intro z hz
    exact ⟨hKD (hEK hz), hKO ⟨z, hEK hz, rfl⟩⟩
  let μ := Pending.MongeAmpere.canonicalBedfordTaylorMeasure D f hf
  have hμ : IsBTLimit D (fun _ : Fin n => f) μ := isBTLimit_canonicalBedfordTaylorMeasure hf
  have hμscaled : IsBTLimit Q (fun _ z => δ * f z)
      (ENNReal.ofReal δ ^ n • μ.restrict (Q : Set (ComplexModel n))) :=
    (hμ.restrict_opens hQD).const_mul_all hδ.le
  have hνQ : IsBTLimit Q (fun _ z => δ * f z - δ + ρ z)
      (ν.restrict (Q : Set (ComplexModel n))) :=
    (hν.restrict_opens hQD).congr fun i z hz => by
      change (v (e.val.symm z)).toReal + ρ z = δ * f z - δ + ρ z
      rw [hvc (e.val.symm z) hz.2, e.val.right_inv (hDt hz.1), EReal.toReal_coe]
  have hνsum : IsBTLimit Q (fun _ z => δ * f z + ρ z)
      (ν.restrict (Q : Set (ComplexModel n))) :=
    (hνQ.add_pluriharmonic (fun _ => isSmoothPluriharmonicOn_const Q δ)).congr
      fun _ _ _ => by ring
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hρpsh : PlurisubharmonicOn (fun z => (ρ z : EReal)) (D : Set (ComplexModel n)) := by
    simpa [chartFunction] using
      BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hzero.1 e hρ
  have hρb : IsLocallyBoundedPshOn Q ρ :=
    LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
      (hρpsh.mono hQD) (hρ.2.2.1.continuousOn.mono hQD)
  have hfb : IsLocallyBoundedPshOn Q (fun z => δ * f z) := by
    apply isLocallyBoundedPshOn_of_abs_le (C := δ)
    · simpa only [← EReal.coe_mul] using (hf.1.const_mul hδ).mono hQD
    · intro z hz
      have hh := hb z hz.1
      rw [abs_mul, abs_of_pos hδ, abs_of_nonpos hh.2]
      nlinarith
  have hle := bt_le_add (fun _ : Fin n => hfb) (fun _ : Fin n => hρb) hμscaled hνsum
  have hmass : ENNReal.ofReal δ ^ n * μ E ≤ ν E := by
    have hh := hle E
    simpa only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' Q.isOpen.measurableSet,
      inter_eq_self_of_subset_left hEQ] using hh
  have hsrc : e.val.symm '' E ⊆ (J.source : Set M) := by
    rintro x ⟨z, hz, rfl⟩
    change e.val.symm z ∈ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n))
    refine ⟨e.val.map_target (hDt (hKD (hEK hz))), ?_⟩
    change e.val (e.val.symm z) ∈ (D : Set (ComplexModel n))
    rw [e.val.right_inv (hDt (hKD (hEK hz)))]
    exact hKD (hEK hz)
  have himg : e.val '' (e.val.symm '' E) = E := by
    ext z
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      rwa [e.val.right_inv (hDt (hKD (hEK hy)))]
    · intro hz
      exact ⟨e.val.symm z, ⟨z, hz, rfl⟩, e.val.right_inv (hDt (hKD (hEK hz)))⟩
  have hglobal : DiagonalMass.diagonalPotentialMeasure omega.form v hv (e.val.symm '' E) = ν E := by
    have hrestr : DiagonalMass.diagonalPotentialMeasure omega.form v hv (e.val.symm '' E) =
        ((DiagonalMass.diagonalPotentialMeasure omega.form v hv).restrict (J.source : Set M))
          (e.val.symm '' E) := by
      rw [Measure.restrict_apply' J.source.isOpen.measurableSet,
        inter_eq_self_of_subset_left hsrc]
    rw [hrestr]
    change ((globalMixedMeasure (fun _ : Fin n => omega.form) (fun _ => v)
      (fun _ => hv.1)).restrict (J.source : Set M)) (e.val.symm '' E) = _
    rw [hνglob, Patch.pushMeasure_apply_image]
    change ν (e.val '' ((e.val.symm '' E) ∩ (J.source : Set M))) = _
    rw [inter_eq_self_of_subset_left hsrc, himg]
  have hcap : ν E ≤ thetaCapacity omega.form (fun _ => 0) (e.val.symm '' E) := by
    rw [← hglobal]
    apply diagonalPotentialMeasure_le_thetaCapacity hv (fun x => (hv01 x).2)
    intro x
    have hh : (-1 : EReal) + 1 ≤ v x + 1 := add_le_add (hv01 x).1 (le_refl (1 : EReal))
    have hz : (-1 : EReal) + 1 = 0 := by
      change ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) = ((0 : ℝ) : EReal)
      rw [← EReal.coe_add]
      norm_num
    rwa [hz] at hh
  change μ E ≤ _
  calc μ E = (ENNReal.ofReal δ ^ n)⁻¹ * (ENNReal.ofReal δ ^ n * μ E) :=
         (ENNReal.inv_mul_cancel_left hp0 hpt).symm
       _ ≤ (ENNReal.ofReal δ ^ n)⁻¹ * thetaCapacity omega.form (fun _ => 0) (e.val.symm '' E) :=
         mul_le_mul_right (hmass.trans hcap) _
       _ = _ := by rw [← ENNReal.ofReal_pow hδ.le, ENNReal.ofReal_inv_of_pos hp]

/-- Actual closed-form local-potential existence produces a reverse-capacity
neighborhood at each actual chart point, with no local geometry witness input. -/
theorem exists_capacity_reverse_neighborhood (omega : KahlerBackground n M)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ (D : Opens (ComplexModel n)) (r C : ℝ), 0 < r ∧ 0 < C ∧
      (D : Set (ComplexModel n)) ⊆ e.val.target ∧
      Metric.closedBall z r ⊆ (D : Set (ComplexModel n)) ∧
      ∀ E : Set (ComplexModel n), E ⊆ Metric.closedBall z r →
        relCapacity D E ≤ ENNReal.ofReal C *
          thetaCapacity omega.form (fun _ => 0) (e.val.symm '' E) := by
  obtain ⟨W, ρ, hzW, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials omega.form e z hz
  let D : Opens (ComplexModel n) := ⟨W, hρ.1⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hρ.1 z hzW
  have hR : 0 < r / 2 := by positivity
  have hKD : Metric.closedBall z (r / 2) ⊆ (D : Set (ComplexModel n)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC, hcomp⟩ := exists_compact_capacity_reverse omega e hρ.2.1 hρ
    (isCompact_closedBall z (r / 2)) hKD
  exact ⟨D, r / 2, C, hR, hC, hρ.2.1, hKD, hcomp⟩

end
end SGPT.Foundations.Analysis.Pending.ActualChartCapacityReverse
