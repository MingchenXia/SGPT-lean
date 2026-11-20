import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedTruncation

set_option autoImplicit false

/-! # Real-level mixed cutoffs for the actual mass deficit in SGPT (4.47)

The reference need only be a genuine potential, and need not be bounded,
model, or of positive mass. No finite-energy or full-mass hypothesis on
the lower endpoint is used.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelNormalizedMixedCutoff

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativeEnergyIntegrability DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling
  SingularModelFiniteEnergyMixedGap

noncomputable section

/-- The actual maximum with a translate of the singular reference. -/
def realCutoff {X : Type*} (φ u : X → EReal) (C : ℝ) : X → EReal :=
  fun x => max (u x) (φ x - (C : EReal))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}

/-- Actual real-level cutoffs are genuine and have the reference singularity type. -/
theorem relativeEInfinity_realCutoff
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ) (C : ℝ) : RelativeEInfinity θ φ (realCutoff φ u C) := by
  have hs : SameSingularityTypeOn (fun x => φ x - (C : EReal)) φ univ := by
    simpa only [EReal.coe_neg, ← sub_eq_add_neg] using sameSingularityTypeOn_add_const φ univ (-C)
  refine ⟨IsThetaPshPotential.max hu (hp.sub_const C), ?_⟩
  exact ⟨DominationPrincipleReduction.moreSingularOn_max huφ hs.1,
    hs.2.trans (MoreSingularOn.of_le fun x _ => le_max_right _ _)⟩

private theorem sub_coe_le_self {p : EReal} (hp : p ≠ ⊤) {C : ℝ} (hC : 0 ≤ C) :
    p - (C : EReal) ≤ p := by
  by_cases hb : p = ⊥
  · simp [hb]
  rw [← EReal.coe_toReal hp hb, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

private theorem canonicalDiff_cutoff_bounds {p a : EReal} (hp : p ≠ ⊤)
    (hap : a ≤ p) {C : ℝ} (hC : 0 ≤ C) :
    -C ≤ canonicalERealDiffToReal (max a (p - (C : EReal))) p ∧
      canonicalERealDiffToReal (max a (p - (C : EReal))) p ≤ 0 := by
  by_cases hb : p = ⊥
  · have hab : a = ⊥ := bot_unique (hb ▸ hap)
    simp [hb, hab, hC]
  have hcutle : max a (p - (C : EReal)) ≤ p := max_le hap (sub_coe_le_self hp hC)
  rw [← EReal.coe_toReal hp hb, ← EReal.coe_sub] at hcutle ⊢
  have hfloor : (((p.toReal - C : ℝ) : EReal)) ≤ max a ((p.toReal - C : ℝ) : EReal) :=
    le_max_right _ _
  have hcb : max a ((p.toReal - C : ℝ) : EReal) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hfloor
  have hct : max a ((p.toReal - C : ℝ) : EReal) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hcutle
  rw [canonicalDiff_eq_sub_toReal hct (EReal.coe_ne_top _)
    ⟨fun h => (hcb h).elim, fun h => (EReal.coe_ne_bot _ h).elim⟩]
  have hlo := EReal.toReal_le_toReal hfloor (EReal.coe_ne_bot _) hct
  have hhi := EReal.toReal_le_toReal hcutle hcb (EReal.coe_ne_top _)
  simp only [EReal.toReal_coe] at hlo hhi ⊢
  constructor <;> linarith

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual strict mixed locality holds at arbitrary nonnegative real levels. -/
theorem binaryMixedMeasure_realCutoff_restrict
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hup : u ≤ φ) (σ : Fin n → Bool) {C : ℝ} (hC : 0 ≤ C) :
    (binaryMixedMeasure (relativeEInfinity_realCutoff hp hu
      (MoreSingularOn.of_le fun x _ => hup x) C).1 hp σ).restrict {x | φ x - (C : EReal) < u x} =
    (binaryMixedMeasure hu hp σ).restrict {x | φ x - (C : EReal) < u x} := by
  let ht := relativeEInfinity_realCutoff hp hu (MoreSingularOn.of_le fun x _ => hup x) C
  let G := {x | φ x - (C : EReal) < u x}
  let S := {x | ∀ i : Fin n, φ x - (C : EReal) < (if σ i then u else φ) x}
  have hG : G ⊆ S := by
    intro x hx i
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hx | exact hx.trans_le (hup x)
  have hslots (i : Fin n) : ThetaPlurisubharmonic θ.val (if σ i then u else φ) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hp.1 | exact hu.1
  have htrunc (i : Fin n) : ThetaPlurisubharmonic θ.val (if σ i then realCutoff φ u C else φ) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hp.1 | exact ht.1.1
  have heq : (fun i : Fin n => fun x => max ((if σ i then u else φ) x) (φ x - (C : EReal))) =
      (fun i => if σ i then realCutoff φ u C else φ) := by
    funext i x
    cases σ i
    · exact max_eq_left (sub_coe_le_self (hp.1.quasiPlurisubharmonic.ne_top x) hC)
    · rfl
  have hmax : ∀ i : Fin n, ThetaPlurisubharmonic θ.val
      (fun x => max ((if σ i then u else φ) x) (φ x - (C : EReal))) := by
    intro i
    rw [show (fun x => max ((if σ i then u else φ) x) (φ x - (C : EReal))) =
      (if σ i then realCutoff φ u C else φ) from congrFun heq i]
    exact htrunc i
  have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq hslots
    (fun _ => (hp.sub_const C).1) hmax
  rw [globalMixedMeasure_congr rfl heq _ htrunc] at hloc
  change (binaryMixedMeasure ht.1 hp σ).restrict S = (binaryMixedMeasure hu hp σ).restrict S at hloc
  calc (binaryMixedMeasure ht.1 hp σ).restrict G =
      ((binaryMixedMeasure ht.1 hp σ).restrict S).restrict G :=
        (Measure.restrict_restrict_of_subset hG).symm
    _ = ((binaryMixedMeasure hu hp σ).restrict S).restrict G := congrArg (fun μ => μ.restrict G) hloc
    _ = _ := Measure.restrict_restrict_of_subset hG

/-- Actual same-type mixed mass produces the reference mass for every real cutoff. -/
theorem binaryMixedMeasure_realCutoff_univ (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ) (σ : Fin n → Bool) (C : ℝ) :
    binaryMixedMeasure (relativeEInfinity_realCutoff hp hu huφ C).1 hp σ univ =
      diagonalPotentialMass θ φ hp := by
  let ht := relativeEInfinity_realCutoff hp hu huφ C
  have htrunc (i : Fin n) : IsThetaPshPotential θ.val (if σ i then realCutoff φ u C else φ) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hp | exact ht.1
  have htype (i : Fin n) : SameSingularityTypeOn (if σ i then realCutoff φ u C else φ) φ univ := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact SameSingularityTypeOn.refl φ univ | exact ht.2
  exact FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega
    htrunc (fun _ => hp) htype

/-- The actual all-real-parameter normalized cutoff integral converges to the
actual binary mixed mass minus the reference mass, without E1 or full mass. -/
theorem tendsto_normalized_binaryMixedMeasure_realCutoff (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hup : u ≤ φ) (σ : Fin n → Bool) :
    Tendsto (fun C : ℝ => (∫ x, canonicalERealDiffToReal (realCutoff φ u C x) (φ x)
      ∂binaryMixedMeasure (relativeEInfinity_realCutoff hp hu
        (MoreSingularOn.of_le fun x _ => hup x) C).1 hp σ) / C)
      atTop (𝓝 ((binaryMixedMeasure hu hp σ).real univ -
        (diagonalPotentialMass θ φ hp).toReal)) := by
  classical
  let ht := fun C => relativeEInfinity_realCutoff hp hu (MoreSingularOn.of_le fun x _ => hup x) C
  let μ := binaryMixedMeasure hu hp σ
  let ν := fun C => binaryMixedMeasure (ht C).1 hp σ
  let G := fun C : ℝ => {x | φ x - (C : EReal) < u x}
  let d := fun x => canonicalERealDiffToReal (u x) (φ x)
  let g := fun C x => canonicalERealDiffToReal (realCutoff φ u C x) (φ x) / C
  let f := fun C => (G C).indicator (fun x => 1 + d x / C)
  have : IsFiniteMeasure μ := globalMixedMeasure_isFiniteMeasure omega _
  have hνfin (C : ℝ) : IsFiniteMeasure (ν C) := globalMixedMeasure_isFiniteMeasure omega _
  have hGm (C : ℝ) : MeasurableSet (G C) :=
    measurableSet_lt ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hp.1).sub measurable_const)
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)
  have hdm : Measurable d := measurable_canonicalERealDiffToReal.comp
    ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1).prodMk
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hp.1))
  have hfmeas (C : ℝ) : AEStronglyMeasurable (f C) μ :=
    ((measurable_const.add (hdm.div_const C)).indicator (hGm C)).aestronglyMeasurable
  have hgoodbounds (C : ℝ) (hC : 0 < C) {x : M} (hx : x ∈ G C) :
      0 ≤ 1 + d x / C ∧ 1 + d x / C ≤ 1 := by
    have hcut : realCutoff φ u C x = u x := max_eq_left hx.le
    have hb := canonicalDiff_cutoff_bounds (hp.1.quasiPlurisubharmonic.ne_top x) (hup x) hC.le
    change -C ≤ canonicalERealDiffToReal (realCutoff φ u C x) (φ x) ∧
      canonicalERealDiffToReal (realCutoff φ u C x) (φ x) ≤ 0 at hb
    rw [hcut] at hb
    change -C ≤ d x ∧ d x ≤ 0 at hb
    constructor
    · have := (le_div_iff₀ hC).mpr (show (-1 : ℝ) * C ≤ d x by linarith)
      linarith
    · have := div_nonpos_of_nonpos_of_nonneg hb.2 hC.le
      linarith
  have hlim : Tendsto (fun C => ∫ x, f C x ∂μ) atTop (𝓝 (μ.real univ)) := by
    have htend : Tendsto (fun C => ∫ x, f C x ∂μ) atTop
        (𝓝 (∫ _x : M, (1 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _x => (1 : ℝ))
        (Eventually.of_forall hfmeas) ?_ (integrable_const _) ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with C hC
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ G C
        · rw [show f C x = 1 + d x / C from indicator_of_mem hx _]
          rw [Real.norm_eq_abs, abs_of_nonneg (hgoodbounds C hC hx).1]
          exact (hgoodbounds C hC hx).2
        · rw [show f C x = 0 from indicator_of_notMem hx _, norm_zero]
          norm_num
      · have hslots (i : Fin n) : ThetaPlurisubharmonic θ.val (if σ i then u else φ) := by
          cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            first | exact hp.1 | exact hu.1
        have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μ, w x ≠ ⊥ := by
          apply ae_iff.mpr
          simpa only [not_not, μ, binaryMixedMeasure] using
            globalMixedMeasure_pole_null_of_nondegenerate hslots hw
        filter_upwards [hpole u hu, hpole φ hp] with x hub hpb
        have hxevent : ∀ᶠ C : ℝ in atTop, x ∈ G C := by
          filter_upwards [eventually_gt_atTop ((φ x).toReal - (u x).toReal)] with C hC
          change φ x - (C : EReal) < u x
          rw [← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb,
            ← EReal.coe_sub, ← EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hub]
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
        have hdlim : Tendsto (fun C : ℝ => d x / C) atTop (𝓝 (0 : ℝ)) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have hone : Tendsto (fun _C : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
        have hs : Tendsto (fun C : ℝ => 1 + d x / C) atTop (𝓝 1) := by
          simpa only [add_zero] using hone.add hdlim
        apply hs.congr'
        exact hxevent.mono fun C hx =>
          (indicator_of_mem hx (fun y => 1 + d y / C)).symm
    simpa only [integral_const, smul_eq_mul, mul_one] using htend
  have heq (C : ℝ) (hC : 0 < C) : (∫ x, g C x ∂ν C) =
      (∫ x, f C x ∂μ) - (diagonalPotentialMass θ φ hp).toReal := by
    let : IsFiniteMeasure (ν C) := hνfin C
    have hgj : Integrable (g C) (ν C) :=
      (integrable_canonicalDiff_globalMixedMeasure omega (ht C).1.1 hp.1 (ht C).2
        (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact hp.1 | exact (ht C).1.1)).div_const C
    have hloc : (ν C).restrict (G C) = μ.restrict (G C) :=
      binaryMixedMeasure_realCutoff_restrict hp hu hup σ hC.le
    have hgoodint : (∫ x in G C, g C x ∂ν C) = ∫ x in G C, d x / C ∂μ := by
      rw [hloc]
      apply setIntegral_congr_fun (hGm C)
      intro x hx
      change canonicalERealDiffToReal (max (u x) (φ x - (C : EReal))) (φ x) / C = _
      rw [max_eq_left hx.le]
    have hbadint : (∫ x in (G C)ᶜ, g C x ∂ν C) = -(ν C).real (G C)ᶜ := by
      have hbad : g C =ᵐ[(ν C).restrict (G C)ᶜ] fun _ => (-1 : ℝ) := by
        have hpnull : ∀ᵐ x ∂ν C, φ x ≠ ⊥ := by
          apply ae_iff.mpr
          simpa only [not_not, ν, binaryMixedMeasure] using
            globalMixedMeasure_pole_null_of_nondegenerate
              (fun i : Fin n => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
                first | exact hp.1 | exact (ht C).1.1) hp
        filter_upwards [ae_restrict_of_ae hpnull, ae_restrict_mem (hGm C).compl] with x hpb hx
        have hle : u x ≤ φ x - (C : EReal) := not_lt.mp hx
        change canonicalERealDiffToReal (max (u x) (φ x - (C : EReal))) (φ x) / C = -1
        rw [max_eq_right hle, ← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb,
          ← EReal.coe_sub, canonicalERealDiffToReal_coe_coe]
        field_simp
        ring
      rw [integral_congr_ae hbad, setIntegral_const, smul_eq_mul]
      ring
    have hmass : (ν C).real univ = (diagonalPotentialMass θ φ hp).toReal :=
      congrArg ENNReal.toReal (binaryMixedMeasure_realCutoff_univ omega hp hu
        (MoreSingularOn.of_le fun x _ => hup x) σ C)
    have hgmass : (ν C).real (G C) = μ.real (G C) := by
      apply congrArg ENNReal.toReal
      rw [← Measure.restrict_apply_self, hloc, Measure.restrict_apply_self]
    have hcompl : (ν C).real (G C)ᶜ = (diagonalPotentialMass θ φ hp).toReal - μ.real (G C) := by
      linarith [measureReal_add_measureReal_compl (μ := ν C) (hGm C)]
    have hgoodintegrable : IntegrableOn (fun x => d x / C) (G C) μ := by
      have hi := hgj.restrict (s := G C)
      rw [hloc] at hi
      apply hi.congr
      filter_upwards [ae_restrict_mem (hGm C)] with x hx
      change canonicalERealDiffToReal (max (u x) (φ x - (C : EReal))) (φ x) / C = _
      rw [max_eq_left hx.le]
    have hfint : (∫ x, f C x ∂μ) = μ.real (G C) + ∫ x in G C, d x / C ∂μ := by
      rw [show f C = (G C).indicator (fun x => 1 + d x / C) from rfl,
        integral_indicator (hGm C), integral_add (integrable_const _) hgoodintegrable,
        setIntegral_const, smul_eq_mul, mul_one]
    rw [← integral_add_compl (hGm C) hgj, hgoodint, hbadint, hcompl, hfint]
    ring
  have hfinal := hlim.sub_const (diagonalPotentialMass θ φ hp).toReal
  apply hfinal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with C hC
  rw [← heq C hC]
  change (∫ x, g C x ∂ν C) = (∫ x, canonicalERealDiffToReal
    (realCutoff φ u C x) (φ x) ∂ν C) / C
  exact integral_div C _

end

end SGPT.Foundations.Analysis.Pending.SingularModelNormalizedMixedCutoff
