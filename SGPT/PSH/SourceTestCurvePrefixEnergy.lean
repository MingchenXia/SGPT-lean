import SGPT.Foundations.Analysis.Pending.FiniteThetaPshAnalyticMaxima
import SGPT.PSH.SourceTestCurveLegendreBounded
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- An actual ordinary fixed point is concentrated on its zero contact set.
No positive-mass premise is imposed, so the genuine cutoff is included. -/
theorem sourceOrdinaryFixedPoint_contact_zero (omega : KahlerBackground n M)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hfix : sourceSingularityEnvelope θ u = u) :
    sourcePotentialNonPluripolarMeasure θ u hu {x | u x ≠ 0} = 0 := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have heq : singularityEnvelope (atlasClosedFormToNative θ).val u = u :=
    (sourceSingularityEnvelope_eq_native θ u).symm.trans hfix
  have hP : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (singularityEnvelope (atlasClosedFormToNative θ).val u) := by
    rw [heq]
    exact hn
  have hc := SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero
    omega (atlasClosedFormToNative θ) hn hP
  have hzero : {x : M | u x ≠ 0} = {x : M | u x < 0} := by
    ext x
    have hle : u x ≤ 0 := by
      rw [← hfix]
      exact sourceSingularityEnvelope_le_zero θ u x
    exact ne_iff_lt_iff_le.mpr hle
  rw [hzero]
  simpa only [sourcePotentialNonPluripolarMeasure, heq] using hc

/-- The literal whole integer prefix, without a finite-max replacement or
regularization in its definition. -/
def sourceTestCurveIntegerPrefix (Γ : SourceTestCurvePredata θ)
    (d t : ℝ) (j : ℤ) : M → EReal := fun x ↦
  ⨆ k : Iic j, sourceTestCurveAt Γ ((k.1 : ℝ) * d) x +
    ((t * (k.1 : ℝ) * d : ℝ) : EReal)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Original atBot equality internally manufactures an actual finite
maximum representing the SAME whole prefix. No finite-max output is input. -/
theorem SourceTestCurve.integerPrefix_finite {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ) :
    ∃ L : ℤ, L ≤ j ∧ sourceTestCurveAt Γ.toSourceTestCurvePredata ((L : ℝ) * d) = φ ∧
      sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j =
        fun x ↦ ⨆ k : {k : ℤ // k ∈ Finset.Icc L j},
          sourceTestCurveAt Γ.toSourceTestCurvePredata ((k.1 : ℝ) * d) x +
            ((t * (k.1 : ℝ) * d : ℝ) : EReal) := by
  obtain ⟨b, hb⟩ := eventually_atBot.mp hΓ.2
  let K : ℤ := Int.floor (b.1 / d)
  have hK : (K : ℝ) * d ≤ b.1 :=
    (le_div_iff₀ hd).mp (Int.floor_le (b.1 / d))
  have hmodel (k : ℤ) (hk : k ≤ K) :
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((k : ℝ) * d) = φ := by
    have hkr : (k : ℝ) * d ≤ b.1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hd.le).trans hK
    have hlt : (k : ℝ) * d < Γ.max := hkr.trans_lt b.2
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hlt]
    exact hb ⟨(k : ℝ) * d, hlt⟩ hkr
  let L : ℤ := min K j
  have hLK : L ≤ K := min_le_left _ _
  have hLj : L ≤ j := min_le_right _ _
  refine ⟨L, hLj, hmodel L hLK, ?_⟩
  funext x
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hL : L ≤ k.1
    · exact le_iSup (fun q : {q : ℤ // q ∈ Finset.Icc L j} ↦
        sourceTestCurveAt Γ.toSourceTestCurvePredata ((q.1 : ℝ) * d) x +
          ((t * (q.1 : ℝ) * d : ℝ) : EReal))
        ⟨k.1, Finset.mem_Icc.mpr ⟨hL, k.2⟩⟩
    · have hkL : k.1 < L := lt_of_not_ge hL
      have hterm : sourceTestCurveAt Γ.toSourceTestCurvePredata ((k.1 : ℝ) * d) x +
          ((t * (k.1 : ℝ) * d : ℝ) : EReal) ≤
          sourceTestCurveAt Γ.toSourceTestCurvePredata ((L : ℝ) * d) x +
            ((t * (L : ℝ) * d : ℝ) : EReal) := by
        rw [hmodel k.1 (hkL.le.trans hLK), hmodel L hLK]
        apply add_le_add le_rfl
        apply EReal.coe_le_coe
        have hc : (k.1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkL.le
        nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg ht.le hd.le)]
      exact hterm.trans (le_iSup (fun q : {q : ℤ // q ∈ Finset.Icc L j} ↦
        sourceTestCurveAt Γ.toSourceTestCurvePredata ((q.1 : ℝ) * d) x +
          ((t * (q.1 : ℝ) * d : ℝ) : EReal))
        ⟨L, Finset.mem_Icc.mpr ⟨le_rfl, hLj⟩⟩)
  · apply iSup_le
    intro k
    exact le_iSup (fun q : Iic j ↦
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((q.1 : ℝ) * d) x +
        ((t * (q.1 : ℝ) * d : ℝ) : EReal))
      ⟨k.1, (Finset.mem_Icc.mp k.2).2⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The exact integer index split gives the actual binary-max recursion. -/
theorem SourceTestCurvePredata.integerPrefix_succ (Γ : SourceTestCurvePredata θ)
    (d t : ℝ) (j : ℤ) :
    sourceTestCurveIntegerPrefix Γ d t (j + 1) = fun x ↦
      Max.max (sourceTestCurveIntegerPrefix Γ d t j x)
        (sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
          ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal)) := by
  funext x
  simp only [sourceTestCurveIntegerPrefix]
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : k.1 ≤ j
    · exact (le_iSup (fun q : Iic j ↦ sourceTestCurveAt Γ ((q.1 : ℝ) * d) x +
        ((t * (q.1 : ℝ) * d : ℝ) : EReal)) ⟨k.1, hk⟩).trans (le_max_left _ _)
    · have heq : k.1 = j + 1 := by have hh : k.1 ≤ j + 1 := k.2; omega
      simpa only [heq] using le_max_right
        (⨆ q : Iic j, sourceTestCurveAt Γ ((q.1 : ℝ) * d) x +
          ((t * (q.1 : ℝ) * d : ℝ) : EReal))
        (sourceTestCurveAt Γ (((j + 1 : ℤ) : ℝ) * d) x +
          ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal))
  · apply max_le
    · apply iSup_le
      intro k
      exact le_iSup (fun q : Iic (j + 1) ↦ sourceTestCurveAt Γ ((q.1 : ℝ) * d) x +
        ((t * (q.1 : ℝ) * d : ℝ) : EReal)) ⟨k.1, show k.1 ≤ j + 1 from (show k.1 ≤ j from k.2).trans (by omega)⟩
    · exact le_iSup (fun q : Iic (j + 1) ↦ sourceTestCurveAt Γ ((q.1 : ℝ) * d) x +
        ((t * (q.1 : ℝ) * d : ℝ) : EReal)) ⟨j + 1, show (j + 1 : ℤ) ≤ j + 1 from le_rfl⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem finite_iSup_thetaPSH {I : Type*} [Fintype I] [Nonempty I]
    (u : I → M → EReal) (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i)) :
    (ofFixedModel n M).IsThetaPSH θ (fun x ↦ ⨆ i, u i x) := by
  classical
  have hc : 0 < Fintype.card I := Fintype.card_pos
  let k := Fintype.card I - 1
  have hk : Fintype.card I = k + 1 := by dsimp [k]; omega
  let e : I ≃ Fin (k + 1) := (Fintype.equivFin I).trans (finCongr hk)
  have hn := QuasiEquisingularFiniteGluing.isThetaPshPotential_fin_iSup
    (fun i ↦ u (e.symm i))
    (fun i ↦ (isThetaPSH_iff_nativeThetaPotential θ (u (e.symm i))).mp (hu _))
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  convert hn using 1
  funext x
  apply le_antisymm
  · apply iSup_le
    intro i
    exact le_iSup_of_le (e i) (by simp)
  · apply iSup_le
    intro i
    exact le_iSup (fun j ↦ u j x) (e.symm i)

omit [BorelSpace M] in
/-- Every original bounded whole prefix through the genuine cutoff is a
source theta-PSH potential; the finite index set is produced internally. -/
theorem SourceTestCurve.integerPrefix_thetaPSH {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (j : ℝ) * d ≤ Γ.max) :
    (ofFixedModel n M).IsThetaPSH θ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j) := by
  classical
  obtain ⟨L, hLj, _, heq⟩ := Γ.integerPrefix_finite hΓ hd ht j
  let I := {k : ℤ // k ∈ Finset.Icc L j}
  let : Nonempty I := ⟨⟨L, Finset.mem_Icc.mpr ⟨le_rfl, hLj⟩⟩⟩
  rw [heq]
  apply finite_iSup_thetaPSH
  intro k
  have hk : (k.1 : ℝ) * d ≤ Γ.max :=
    (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.mem_Icc.mp k.2).2) hd.le).trans hj
  have hp := (source_test_curve_extension_whole Γ.toSourceTestCurvePredata).2.2.2
    ((k.1 : ℝ) * d) hk
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  exact ((isThetaPSH_iff_nativeThetaPotential θ _).mp hp).add_const _

omit [BorelSpace M] in
/-- The genuine whole prefix has relatively minimal singularities for the
original arbitrary model; both finite additive constants are manufactured. -/
theorem SourceTestCurve.integerPrefix_eInfinity {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (j : ℝ) * d ≤ Γ.max) :
    SourceRelativeEInfinity θ φ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j) := by
  refine ⟨Γ.integerPrefix_thetaPSH hΓ hd ht j hj, ?_⟩
  obtain ⟨L, hLj, hmodel, _⟩ := Γ.integerPrefix_finite hΓ hd ht j
  have hupper := Γ.toSourceTestCurvePredata.rawLegendre_le_limit_add ht.le
  have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ.1
  rw [hbase] at hupper
  have hraw : sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j ≤
      sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t := by
    intro x
    apply iSup_le
    intro k
    simpa only [mul_assoc, add_comm, sourceTestCurveRawLegendre] using
      (le_iSup (fun τ : ℝ ↦ ((t * τ : ℝ) : EReal) +
        sourceTestCurveAt Γ.toSourceTestCurvePredata τ x) ((k.1 : ℝ) * d))
  have hlower (x : M) : φ x + ((t * (L : ℝ) * d : ℝ) : EReal) ≤
      sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x := by
    rw [← hmodel]
    exact le_iSup (fun k : Iic j ↦
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((k.1 : ℝ) * d) x +
        ((t * (k.1 : ℝ) * d : ℝ) : EReal)) ⟨L, hLj⟩
  refine ⟨⟨t * Γ.max, fun x _ ↦ (hraw x).trans (hupper x)⟩,
    ⟨-(t * (L : ℝ) * d), fun x _ ↦ ?_⟩⟩
  simpa only [sub_eq_add_neg, EReal.coe_neg] using
    (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr (hlower x)

/-- The SAME actual prefix energy is a finite real minimal-type energy,
with both infinite endpoints excluded by this exact equality. -/
theorem SourceTestCurve.integerPrefix_energy_finite (omega : KahlerBackground n M)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (j : ℝ) * d ≤ Γ.max) :
    sourceRelativeEnergy θ φ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j) hφ =
      (sourceRelativeEnergyOfMinimalType θ φ
        (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j)
        hφ.thetaPSH (Γ.integerPrefix_thetaPSH hΓ hd ht j hj) : EReal) :=
  sourceRelativeEnergy_eq_of_eInfinity omega (Γ.integerPrefix_eInfinity hΓ hd ht j hj)

end SGPT.PSH.VariableComplexAtlas
