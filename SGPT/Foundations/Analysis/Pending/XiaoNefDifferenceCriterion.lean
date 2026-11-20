import SGPT.Foundations.Analysis.Pending.XiaoCompatibleGlobalPotential
import SGPT.Foundations.Analysis.Pending.XiaoNefPerturbation
import SGPT.Foundations.Analysis.Pending.UniformNefCoreSupport

set_option autoImplicit false

/-! # Xiao's actual numerical nef difference criterion produces genuine Kähler currents -/

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoNefDifferenceCriterion

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses NonKahlerLocus
  NefMixedMass ProductTestForms IntegrationCurrent TopDegreeDensity
  ThetaPshChartLimitGluing XiaoPoissonChartCompatibility XiaoCompatibleGlobalPotential
  XiaoNefPerturbation MixedMassClassInvariance ManifoldTubePositivity

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual one-slot integrals are invariant under moving the last actual slot to the first. -/
theorem slotIntegral_snoc_eq_cons (w : KahlerBackground (m + 1) M)
    (θ : Fin m → ClosedRealOneOneForm (m + 1) M) (B : ClosedRealOneOneForm (m + 1) M) :
    slotIntegral w (Fin.snoc θ B) = slotIntegral w (Fin.cons B θ) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact UniformNefCoreSupport.slotIntegral_comp_perm w (Fin.cons B θ) (finRotate (m + 1))

omit [BorelSpace M] in
/-- A strict actual slot-integral gap forces the actual manifold to be nonempty. -/
theorem nonempty_of_slot_gap (w : KahlerBackground (m + 1) M)
    (θ η : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M) (c : ℝ)
    (hgap : 0 < slotIntegral w θ - c * slotIntegral w η) : Nonempty M := by
  classical
  rcases isEmpty_or_nonempty M with hEmpty | hNonempty
  · let := hEmpty
    simp only [slotIntegral, integral_of_isEmpty, mul_zero, sub_self, lt_self_iff_false] at hgap
  · exact hNonempty

/-- The actual Kähler one-slot mixed mass is strictly positive, by actual domination and multilinearity. -/
theorem slotIntegral_cons_kahler_pos [Nonempty M] (w B : KahlerBackground (m + 1) M) :
    0 < slotIntegral w (Fin.cons B.form (fun _ : Fin m => w.form)) := by
  obtain ⟨c, hc, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul B (-w.form)
  have heq : -w.form + c • B.form = c • B.form - w.form := by module
  rw [heq] at hdom
  have hnonneg : 0 ≤ slotIntegral w
      (Fin.snoc (fun _ : Fin m => w.form) (c • B.form - w.form)) := by
    apply slotIntegral_nonneg
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hdom
    · simpa only [Fin.snoc_castSucc] using w.isSemipositive
  rw [slotIntegral_snoc_sub_smul, slotIntegral_snoc_eq_cons, slotIntegral_snoc_eq_cons] at hnonneg
  have hconst : Fin.cons w.form (fun _ : Fin m => w.form) = fun _ : Fin (m + 1) => w.form := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hconst, UniformNefCoreSupport.slotIntegral_form] at hnonneg
  nlinarith [NefCoreKahlerCurrent.kahlerVolume_real_univ_pos w]

variable [PreconnectedSpace M]

/-- The genuine numerical Kähler gap produces bigness of the actual difference class. -/
theorem isBigClass_sub_of_kahler_gap (w B : KahlerBackground (m + 1) M)
    (hgap : 4 * (m + 1 : ℝ) * slotIntegral w
      (Fin.cons B.form (fun _ : Fin m => w.form)) < (kahlerVolume w).real univ) :
    IsBigClass (RealBottChern.ofRepresentative (w.form - B.form)) := by
  have hslotgap : 0 < slotIntegral w (fun _ => w.form) - 4 * (m + 1 : ℝ) *
      slotIntegral w (Fin.cons B.form (fun _ : Fin m => w.form)) := by
    rw [UniformNefCoreSupport.slotIntegral_form]
    linarith
  let : Nonempty M := nonempty_of_slot_gap w _ _ (4 * (m + 1 : ℝ)) hslotgap
  let : ConnectedSpace M := { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  obtain ⟨A⟩ := HolderAtlas.nonempty (n := m + 1) (M := M)
  obtain ⟨δ, hδ0, _, U, hU, hLevi⟩ :=
    exists_gap_compatible_locally_theta_psh_distributions (r := (1 / 2 : ℝ≥0))
      w B A (by norm_num) (by norm_num) (slotIntegral_cons_kahler_pos w B) hgap
  let ωδ := KahlerBackground.smul hδ0 w
  have heq : (w.form - B.form) - ωδ.form = (1 - δ) • w.form - B.form := by
    dsimp only [ωδ]
    rw [KahlerBackground.smul_form]
    module
  have hLevi' : ∀ e, IsLocallyThetaPshDistribution volume ((w.form - B.form) - ωδ.form).val e (U e) := by
    intro e
    rw [heq]
    exact hLevi e
  obtain ⟨K, _, _, _⟩ := exists_kahlerCurrent_of_isCoordinateCompatible volume
    (w.form - B.form) ωδ U hU hLevi'
  exact ⟨K⟩

/-- Actual nefness and Xiao's strict numerical gap produce bigness of the genuine difference class. -/
theorem isBigClass_sub_of_nef_gap (w : KahlerBackground (m + 1) M)
    (A B : ClosedRealOneOneForm (m + 1) M)
    (hA : NefWithRespectTo w A) (hB : NefWithRespectTo w B)
    (hgap : 0 < slotIntegral w (fun _ => A) - 4 * (m + 1 : ℝ) *
      slotIntegral w (Fin.cons B (fun _ : Fin m => A))) :
    IsBigClass (RealBottChern.ofRepresentative (A - B)) := by
  classical
  have hcons : ∀ α β : ClosedRealOneOneForm (m + 1) M,
      Function.update (fun _ : Fin (m + 1) => α) 0 β = Fin.cons β (fun _ : Fin m => α) := by
    intro α β
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hgap' : 0 < slotIntegral w (fun _ => A) - 4 * (m + 1 : ℝ) *
      slotIntegral w (Function.update (fun _ => A) 0 B) := by
    rw [hcons]
    exact hgap
  obtain ⟨t, _, f, hf, g, hg, hAf, hBg, hgap''⟩ :=
    exists_kahler_representatives_preserving_gap w A B 0 hA hB
      (by simpa only [Nat.cast_add, Nat.cast_one] using hgap')
  let WA : KahlerBackground (m + 1) M := ⟨A + t • w.form + ddcClosedForm f hf, hAf⟩
  let WB : KahlerBackground (m + 1) M := ⟨B + t • w.form + ddcClosedForm g hg, hBg⟩
  have hgapAB : 0 < slotIntegral w (fun _ => WA.form) - 4 * (m + 1 : ℝ) *
      slotIntegral w (Fin.cons WB.form (fun _ : Fin m => WA.form)) := by
    rw [← hcons]
    simpa only [WA, WB, Nat.cast_add, Nat.cast_one] using hgap''
  rw [← UniformNefCoreSupport.slotIntegral_eq_of_background w WA (fun _ => WA.form),
    ← UniformNefCoreSupport.slotIntegral_eq_of_background w WA
      (Fin.cons WB.form (fun _ : Fin m => WA.form)),
    UniformNefCoreSupport.slotIntegral_form] at hgapAB
  have hbig := isBigClass_sub_of_kahler_gap WA WB (by linarith)
  have hrel : ClosedRealOneOneForm.BottChernRel (A - B) (WA.form - WB.form) := by
    refine ⟨fun x => f x - g x, fun e => (hf e).sub (hg e), ?_⟩
    intro e z hz
    simp only [WA, WB, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg, ddcClosedForm_coeff]
    have hddc := smoothDDC_sub e.val.open_target (hf e) (hg e) hz
    simp only [sub_eq_add_neg] at hddc
    erw [hddc]
    module
  have hclass : RealBottChern.ofRepresentative (A - B) =
      RealBottChern.ofRepresentative (WA.form - WB.form) :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mpr hrel
  rw [← hclass] at hbig
  exact hbig

end

end SGPT.Foundations.Analysis.Pending.XiaoNefDifferenceCriterion
