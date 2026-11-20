import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedGap
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality

set_option autoImplicit false

/-!
# Actual weighted binary mixed truncation convergence over singular models

Xia SGPT PDF0124--0126, the weighted mixed convergence in (3.40)--(3.41).
Actual strict max locality and actual equal full mixed masses replace the
moving bad-set mass by the fixed one; produced E1 mixed gap integrability
then makes its actual weighted tail vanish.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedTruncation

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass GlobalNonPluripolar
  GlobalDiagonalScaling MongeAmpereEnergyDecreasing SingularModelEnergyTruncation
  SingularModelFiniteEnergyMixedGap FiniteEnergyCharacterization

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual binary mixed truncations agree with the actual fixed mixed product
on the strict common good set, including dimension zero. -/
theorem binaryMixedMeasure_truncation_restrict
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : MoreSingularOn u φ univ) (hvφ : MoreSingularOn v φ univ)
    (σ : Fin n → Bool) (j : ℕ) :
    (binaryMixedMeasure (relativeEInfinity_truncation hp hu huφ j).1
      (relativeEInfinity_truncation hp hv hvφ j).1 σ).restrict
        {x | φ x - ((j : ℝ) : EReal) < u x ∧ φ x - ((j : ℝ) : EReal) < v x} =
    (binaryMixedMeasure hu hv σ).restrict
        {x | φ x - ((j : ℝ) : EReal) < u x ∧ φ x - ((j : ℝ) : EReal) < v x} := by
  let htu := relativeEInfinity_truncation hp hu huφ j
  let htv := relativeEInfinity_truncation hp hv hvφ j
  let G := {x | φ x - ((j : ℝ) : EReal) < u x ∧ φ x - ((j : ℝ) : EReal) < v x}
  let S := {x | ∀ i : Fin n, φ x - ((j : ℝ) : EReal) < (if σ i then u else v) x}
  have hG : G ⊆ S := by
    intro x hx i
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hx.2 | exact hx.1
  have hslots (i : Fin n) : ThetaPlurisubharmonic θ.val (if σ i then u else v) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hv.1 | exact hu.1
  have htrunc (i : Fin n) : ThetaPlurisubharmonic θ.val
      (if σ i then truncation φ u j else truncation φ v j) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact htv.1.1 | exact htu.1.1
  have heq : (fun i : Fin n => fun x => max ((if σ i then u else v) x)
      (φ x - ((j : ℝ) : EReal))) =
      (fun i => if σ i then truncation φ u j else truncation φ v j) := by
    funext i
    cases σ i <;> rfl
  have hmax : ∀ i : Fin n, ThetaPlurisubharmonic θ.val
      (fun x => max ((if σ i then u else v) x) (φ x - ((j : ℝ) : EReal))) := by
    intro i
    rw [show (fun x => max ((if σ i then u else v) x) (φ x - ((j : ℝ) : EReal))) =
      (if σ i then truncation φ u j else truncation φ v j) from congrFun heq i]
    exact htrunc i
  have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq hslots
    (fun _ => (hp.sub_const (j : ℝ)).1) hmax
  rw [globalMixedMeasure_congr rfl heq _ htrunc] at hloc
  change (binaryMixedMeasure htu.1 htv.1 σ).restrict S =
    (binaryMixedMeasure hu hv σ).restrict S at hloc
  calc (binaryMixedMeasure htu.1 htv.1 σ).restrict G =
      ((binaryMixedMeasure htu.1 htv.1 σ).restrict S).restrict G :=
        (Measure.restrict_restrict_of_subset hG).symm
    _ = ((binaryMixedMeasure hu hv σ).restrict S).restrict G := congrArg (fun μ => μ.restrict G) hloc
    _ = _ := Measure.restrict_restrict_of_subset hG

/-- Genuine same-type truncations produce the actual reference mixed mass,
without any endpoint finite-energy or mixed-mass premise. -/
theorem binaryMixedMeasure_truncation_univ (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : MoreSingularOn u φ univ) (hvφ : MoreSingularOn v φ univ)
    (σ : Fin n → Bool) (j : ℕ) :
    binaryMixedMeasure (relativeEInfinity_truncation hp hu huφ j).1
      (relativeEInfinity_truncation hp hv hvφ j).1 σ univ = diagonalPotentialMass θ φ hp := by
  let htu := relativeEInfinity_truncation hp hu huφ j
  let htv := relativeEInfinity_truncation hp hv hvφ j
  have htrunc (i : Fin n) : IsThetaPshPotential θ.val
      (if σ i then truncation φ u j else truncation φ v j) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact htv.1 | exact htu.1
  have htype (i : Fin n) : SameSingularityTypeOn
      (if σ i then truncation φ u j else truncation φ v j) φ univ := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact htv.2 | exact htu.2
  exact FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega
    htrunc (fun _ => hp) htype

omit [BorelSpace M] in
/-- Swapping endpoint names and their slot labels preserves the actual tuple. -/
theorem binaryMixedMeasure_swap (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (σ : Fin n → Bool) :
    binaryMixedMeasure hv hu (fun i => !(σ i)) = binaryMixedMeasure hu hv σ := by
  apply globalMixedMeasure_congr rfl
  funext i
  change (if !(σ i) then v else u) = (if σ i then u else v)
  cases σ i <;> rfl

private theorem canonicalDiff_nonneg {a b : EReal} (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hba : b ≤ a) : 0 ≤ canonicalERealDiffToReal a b := by
  by_cases hab : a = ⊥
  · have hbb : b = ⊥ := bot_unique (hab ▸ hba)
    simp [hab, hbb]
  by_cases hbb : b = ⊥
  · simp [hbb, canonicalERealDiffToReal, hab]
  have hpole : a = ⊥ ↔ b = ⊥ := ⟨fun h => (hab h).elim, fun h => (hbb h).elim⟩
  rw [canonicalDiff_eq_sub_toReal hat hbt hpole]
  exact sub_nonneg.mpr (EReal.toReal_le_toReal hba hbb hat)

/-- The actual moving mixed reference-gap integral converges, with actual
mixed integrability and the weighted bad-set error both produced internally. -/
theorem tendsto_integral_referenceGap_truncations [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (σ : Fin n → Bool) :
    Tendsto (fun j => ∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
      ∂binaryMixedMeasure
        (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
          (preceq_of_relativePSH hu.1.relativePSH).2 j).1
        (relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
          (preceq_of_relativePSH hv.1.relativePSH).2 j).1 σ)
      atTop (𝓝 (∫ x, canonicalERealDiffToReal (φ x) (u x)
        ∂binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ)) := by
  classical
  let hp := hφ.plurisubharmonic
  let hup := hu.1.plurisubharmonic
  let hvp := hv.1.plurisubharmonic
  let htu := fun j => relativeEInfinity_truncation hp hup (preceq_of_relativePSH hu.1.relativePSH).2 j
  let htv := fun j => relativeEInfinity_truncation hp hvp (preceq_of_relativePSH hv.1.relativePSH).2 j
  let μ := binaryMixedMeasure hup hvp σ
  let ν := fun j => binaryMixedMeasure (htu j).1 (htv j).1 σ
  let fu := fun x => canonicalERealDiffToReal (φ x) (u x)
  let fv := fun x => canonicalERealDiffToReal (φ x) (v x)
  let f := fun x => fu x + fv x
  let gj := fun j x => canonicalERealDiffToReal (φ x) (truncation φ u j x)
  let G := fun j : ℕ => {x | φ x - ((j : ℝ) : EReal) < u x ∧ φ x - ((j : ℝ) : EReal) < v x}
  have : IsFiniteMeasure μ := globalMixedMeasure_isFiniteMeasure omega _
  have hνfin (j : ℕ) : IsFiniteMeasure (ν j) := globalMixedMeasure_isFiniteMeasure omega _
  have hGm (j : ℕ) : MeasurableSet (G j) :=
    (measurableSet_lt_truncation hp.1 hup.1 j).inter (measurableSet_lt_truncation hp.1 hvp.1 j)
  have hGmono : Monotone G := fun i j hij x hx => ⟨
    lt_of_le_of_lt (EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))) hx.1,
    lt_of_le_of_lt (EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hij))) hx.2⟩
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μ, w x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, μ, binaryMixedMeasure] using globalMixedMeasure_pole_null_of_nondegenerate
      (θ := fun _ : Fin n => θ) (u := fun i => if σ i then u else v)
      (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact hvp.1 | exact hup.1) hw
  have hGevent (x : M) (hub : u x ≠ ⊥) (hvb : v x ≠ ⊥) : ∀ᶠ j in atTop, x ∈ G j := by
    have hpb : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hub (hu.1.le_reference x)
    obtain ⟨k, hk⟩ := exists_nat_gt (max ((φ x).toReal - (u x).toReal)
      ((φ x).toReal - (v x).toReal))
    have hxk : x ∈ G k := by
      constructor
      · rw [← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb, ← EReal.coe_sub,
          ← EReal.coe_toReal (hup.1.quasiPlurisubharmonic.ne_top x) hub]
        exact EReal.coe_lt_coe_iff.mpr (by have := lt_of_le_of_lt (le_max_left _ _) hk; linarith)
      · rw [← EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb, ← EReal.coe_sub,
          ← EReal.coe_toReal (hvp.1.quasiPlurisubharmonic.ne_top x) hvb]
        exact EReal.coe_lt_coe_iff.mpr (by have := lt_of_le_of_lt (le_max_right _ _) hk; linarith)
    exact (eventually_ge_atTop k).mono fun j hj => hGmono hj hxk
  have hi := integrable_referenceGaps_binaryMixedMeasure omega hu hv σ
  have hfu : Integrable fu μ := hi.1
  have hf : Integrable f μ := hi.1.add hi.2
  have hgj (j : ℕ) : Integrable (gj j) (ν j) :=
    integrable_canonicalDiff_globalMixedMeasure omega hp.1 (htu j).1.1 (htu j).2.symm
      (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact (htv j).1.1 | exact (htu j).1.1)
  have hgnn (j : ℕ) (x : M) : 0 ≤ gj j x := canonicalDiff_nonneg
    (hp.1.quasiPlurisubharmonic.ne_top x) ((htu j).1.1.quasiPlurisubharmonic.ne_top x)
    (truncation_le hu.1.le_reference j x)
  have hgb (j : ℕ) (x : M) : gj j x ≤ (j : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ j)).mp
    rw [show gj j x = canonicalERealDiffToReal (φ x) (truncation φ u j x) from rfl,
      SingularModelEnergyCappedGap.ofReal_canonicalDiff_truncation_eq_min
        hp.1.quasiPlurisubharmonic.ne_top hup.1.quasiPlurisubharmonic.ne_top hu.1.le_reference]
    exact min_le_left _ _
  have hgood : Tendsto (fun j => ∫ x in G j, fu x ∂μ) atTop (𝓝 (∫ x, fu x ∂μ)) := by
    simp_rw [← integral_indicator (hGm _)]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖fu x‖)
      (fun j => (hfu.indicator (hGm j)).aestronglyMeasurable) hfu.norm
      (fun j => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _) ?_
    filter_upwards [hpole u hup, hpole v hvp] with x hub hvb
    apply tendsto_const_nhds.congr'
    exact (hGevent x hub hvb).mono fun j hx => (indicator_of_mem hx fu).symm
  have htail : Tendsto (fun j => ∫ x in (G j)ᶜ, f x ∂μ) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun j => ∫ x, (G j)ᶜ.indicator f x ∂μ)
        atTop (𝓝 (∫ _x : M, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
        (fun j => (hf.indicator (hGm j).compl).aestronglyMeasurable) hf.norm
        (fun j => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _) ?_
      filter_upwards [hpole u hup, hpole v hvp] with x hub hvb
      apply tendsto_const_nhds.congr'
      exact (hGevent x hub hvb).mono fun j hx => (indicator_of_notMem (notMem_compl_iff.mpr hx) f).symm
    simpa only [integral_indicator (hGm _).compl, integral_zero] using ht
  have hloc (j : ℕ) : (ν j).restrict (G j) = μ.restrict (G j) :=
    binaryMixedMeasure_truncation_restrict hp hup hvp
      (preceq_of_relativePSH hu.1.relativePSH).2 (preceq_of_relativePSH hv.1.relativePSH).2 σ j
  have hcompl (j : ℕ) : (ν j).real (G j)ᶜ = μ.real (G j)ᶜ := by
    let : IsFiniteMeasure (ν j) := hνfin j
    have htotal : ν j univ = μ univ := (binaryMixedMeasure_truncation_univ omega hp hup hvp
      (preceq_of_relativePSH hu.1.relativePSH).2 (preceq_of_relativePSH hv.1.relativePSH).2 σ j).trans
        (binaryMixedMeasure_univ omega hu hv σ).symm
    have ha : ν j (G j) = μ (G j) := by
      rw [← Measure.restrict_apply_self, hloc, Measure.restrict_apply_self]
    have ht : (ν j).real univ = μ.real univ := congrArg ENNReal.toReal htotal
    have hGr : (ν j).real (G j) = μ.real (G j) := congrArg ENNReal.toReal ha
    linarith [measureReal_add_measureReal_compl (μ := ν j) (hGm j),
      measureReal_add_measureReal_compl (μ := μ) (hGm j)]
  have hbad (j : ℕ) : (∫ x in (G j)ᶜ, gj j x ∂ν j) ≤ ∫ x in (G j)ᶜ, f x ∂μ := by
    let : IsFiniteMeasure (ν j) := hνfin j
    calc (∫ x in (G j)ᶜ, gj j x ∂ν j) ≤ ∫ _x in (G j)ᶜ, (j : ℝ) ∂ν j :=
        integral_mono_ae (hgj j).restrict (integrable_const _) (Eventually.of_forall fun x => hgb j x)
      _ = ∫ _x in (G j)ᶜ, (j : ℝ) ∂μ := by simp only [setIntegral_const, smul_eq_mul, hcompl]
      _ ≤ ∫ x in (G j)ᶜ, f x ∂μ := by
        refine integral_mono_ae (integrable_const _) hf.restrict ?_
        filter_upwards [ae_restrict_of_ae (hpole φ hp), ae_restrict_of_ae (hpole u hup),
          ae_restrict_of_ae (hpole v hvp), ae_restrict_mem (hGm j).compl] with x hpb hub hvb hx
        have hcu := EReal.coe_toReal (hup.1.quasiPlurisubharmonic.ne_top x) hub
        have hcv := EReal.coe_toReal (hvp.1.quasiPlurisubharmonic.ne_top x) hvb
        have hcp := EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpb
        have hfun : 0 ≤ fu x := canonicalDiff_nonneg (hp.1.quasiPlurisubharmonic.ne_top x)
          (hup.1.quasiPlurisubharmonic.ne_top x) (hu.1.le_reference x)
        have hfvn : 0 ≤ fv x := canonicalDiff_nonneg (hp.1.quasiPlurisubharmonic.ne_top x)
          (hvp.1.quasiPlurisubharmonic.ne_top x) (hv.1.le_reference x)
        have hefu : fu x = (φ x).toReal - (u x).toReal := by
          change canonicalERealDiffToReal (φ x) (u x) = _
          rw [canonicalDiff_eq_sub_toReal (hp.1.quasiPlurisubharmonic.ne_top x)
            (hup.1.quasiPlurisubharmonic.ne_top x) ⟨fun h => (hpb h).elim, fun h => (hub h).elim⟩]
        have hefv : fv x = (φ x).toReal - (v x).toReal := by
          change canonicalERealDiffToReal (φ x) (v x) = _
          rw [canonicalDiff_eq_sub_toReal (hp.1.quasiPlurisubharmonic.ne_top x)
            (hvp.1.quasiPlurisubharmonic.ne_top x) ⟨fun h => (hpb h).elim, fun h => (hvb h).elim⟩]
        change ¬ (φ x - ((j : ℝ) : EReal) < u x ∧ φ x - ((j : ℝ) : EReal) < v x) at hx
        change (j : ℝ) ≤ fu x + fv x
        rcases not_and_or.mp hx with hx | hx
        · have hl := not_lt.mp hx
          rw [← hcp, ← hcu, ← EReal.coe_sub] at hl
          have hh := EReal.coe_le_coe_iff.mp hl
          rw [hefu]
          linarith
        · have hl := not_lt.mp hx
          rw [← hcp, ← hcv, ← EReal.coe_sub] at hl
          have hh := EReal.coe_le_coe_iff.mp hl
          rw [hefv]
          linarith
  have hbad0 : Tendsto (fun j => ∫ x in (G j)ᶜ, gj j x ∂ν j) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun j => integral_nonneg fun x => hgnn j x) hbad
  have heq (j : ℕ) : (∫ x, gj j x ∂ν j) =
      (∫ x in G j, fu x ∂μ) + ∫ x in (G j)ᶜ, gj j x ∂ν j := by
    rw [← integral_add_compl (hGm j) (hgj j), hloc]
    congr 1
    apply setIntegral_congr_fun (hGm j)
    intro x hx
    change canonicalERealDiffToReal (φ x) (truncation φ u j x) = _
    rw [truncation_eq_of_lt hx.1]
  change Tendsto (fun j => ∫ x, gj j x ∂ν j) atTop (𝓝 (∫ x, fu x ∂μ))
  simpa only [← heq, add_zero] using hgood.add hbad0

private theorem canonicalDiff_sub_reference {a b p : EReal}
    (hat : a ≠ ⊤) (hbt : b ≠ ⊤) (hpt : p ≠ ⊤)
    (hap : a = ⊥ ↔ p = ⊥) (hbp : b = ⊥ ↔ p = ⊥) :
    canonicalERealDiffToReal a b =
      canonicalERealDiffToReal p b - canonicalERealDiffToReal p a := by
  by_cases hpb : p = ⊥
  · have hab : a = ⊥ := hap.mpr hpb
    have hbb : b = ⊥ := hbp.mpr hpb
    simp [hab, hbb, hpb]
  rw [canonicalDiff_eq_sub_toReal hat hbt (hap.trans hbp.symm),
    canonicalDiff_eq_sub_toReal hpt hbt hbp.symm,
    canonicalDiff_eq_sub_toReal hpt hat hap.symm]
  ring

/-- Actual signed weighted binary mixed truncation convergence follows by
subtracting the two genuinely produced reference-gap convergences. -/
theorem tendsto_integral_canonicalDiff_truncations [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (σ : Fin n → Bool) :
    Tendsto (fun j => ∫ x, canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x)
      ∂binaryMixedMeasure
        (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
          (preceq_of_relativePSH hu.1.relativePSH).2 j).1
        (relativeEInfinity_truncation hφ.plurisubharmonic hv.1.plurisubharmonic
          (preceq_of_relativePSH hv.1.relativePSH).2 j).1 σ)
      atTop (𝓝 (∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ)) := by
  let hp := hφ.plurisubharmonic
  let htu := fun j => relativeEInfinity_truncation hp hu.1.plurisubharmonic
    (preceq_of_relativePSH hu.1.relativePSH).2 j
  let htv := fun j => relativeEInfinity_truncation hp hv.1.plurisubharmonic
    (preceq_of_relativePSH hv.1.relativePSH).2 j
  let μ := binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ
  let ν := fun j => binaryMixedMeasure (htu j).1 (htv j).1 σ
  have hTu := tendsto_integral_referenceGap_truncations omega hu hv σ
  have hTv := tendsto_integral_referenceGap_truncations omega hv hu (fun i => !(σ i))
  simp only [binaryMixedMeasure_swap] at hTv
  change Tendsto (fun j => ∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x) ∂ν j)
    atTop (𝓝 (∫ x, canonicalERealDiffToReal (φ x) (u x) ∂μ)) at hTu
  change Tendsto (fun j => ∫ x, canonicalERealDiffToReal (φ x) (truncation φ v j x) ∂ν j)
    atTop (𝓝 (∫ x, canonicalERealDiffToReal (φ x) (v x) ∂μ)) at hTv
  have hgj (j : ℕ) (w : M → EReal) (hw : RelativeEInfinity θ φ w) :
      Integrable (fun x => canonicalERealDiffToReal (φ x) (w x)) (ν j) :=
    integrable_canonicalDiff_globalMixedMeasure omega hp.1 hw.1.1 hw.2.symm
      (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact (htv j).1.1 | exact (htu j).1.1)
  have heqj (j : ℕ) : (∫ x, canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x) ∂ν j) =
      (∫ x, canonicalERealDiffToReal (φ x) (truncation φ v j x) ∂ν j) -
        ∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x) ∂ν j := by
    rw [← integral_sub (hgj j _ (htv j)) (hgj j _ (htu j))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => canonicalDiff_sub_reference
      ((htu j).1.1.quasiPlurisubharmonic.ne_top x) ((htv j).1.1.quasiPlurisubharmonic.ne_top x)
      (hp.1.quasiPlurisubharmonic.ne_top x)
      (sameSingularityTypeOn_eq_bot_iff (htu j).2 (mem_univ x))
      (sameSingularityTypeOn_eq_bot_iff (htv j).2 (mem_univ x))
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μ, w x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, μ, binaryMixedMeasure] using globalMixedMeasure_pole_null_of_nondegenerate
      (θ := fun _ : Fin n => θ) (u := fun i => if σ i then u else v)
      (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact hv.1.plurisubharmonic.1 | exact hu.1.plurisubharmonic.1) hw
  have heq : (∫ x, canonicalERealDiffToReal (u x) (v x) ∂μ) =
      (∫ x, canonicalERealDiffToReal (φ x) (v x) ∂μ) -
        ∫ x, canonicalERealDiffToReal (φ x) (u x) ∂μ := by
    have hi := integrable_referenceGaps_binaryMixedMeasure omega hu hv σ
    rw [← integral_sub hi.2 hi.1]
    apply integral_congr_ae
    filter_upwards [hpole φ hp, hpole u hu.1.plurisubharmonic,
      hpole v hv.1.plurisubharmonic] with x hpb hub hvb
    exact canonicalDiff_sub_reference (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
      (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) (hp.1.quasiPlurisubharmonic.ne_top x)
      ⟨fun h => (hub h).elim, fun h => (hpb h).elim⟩
      ⟨fun h => (hvb h).elim, fun h => (hpb h).elim⟩
  change Tendsto (fun j => ∫ x, canonicalERealDiffToReal (truncation φ u j x) (truncation φ v j x) ∂ν j)
    atTop (𝓝 (∫ x, canonicalERealDiffToReal (u x) (v x) ∂μ))
  simpa only [← heqj, ← heq] using hTv.sub hTu

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedTruncation
