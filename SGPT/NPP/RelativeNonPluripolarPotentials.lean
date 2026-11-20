import SGPT.NPP.RelativeNonPluripolarMass
import SGPT.NPP.NonPluripolarCurrent3Gauge

/-! Body-preserving consolidation PLAN ONLY. Fresh proper-name checking is
required; private flat objects are provenance, never providers for this file. -/

-- Exact frozen body: RelativeLocalityDraft
section OriginalFragment_01

/-! Actual arbitrary-base-current relative NPP restriction and local finite
mass. Original open subsets and actual compact trace measures are retained. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalBedfordTaylorCollar
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {U V : Opens (ComplexModel n)}

theorem relativeTruncatedBT_restrict
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hVU : V ≤ U) (k : ℕ) :
    relativeTruncatedBT V φ (restrict hVU T) k =
      restrict hVU (relativeTruncatedBT U φ T k) :=
  btProduct_restrict hVU p r _ T hT hTc
    (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)

theorem relativeTruncAt_restrict
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hVU : V ≤ U) (k : ℕ) :
    truncAt (relativeTruncatedBT V φ (restrict hVU T))
        (BedfordTaylorTopDegree.strictLocus V φ) k =
      restrict hVU (truncAt (relativeTruncatedBT U φ T)
        (BedfordTaylorTopDegree.strictLocus U φ) k) := by
  let hφV : ∀ i, PlurisubharmonicOn (φ i) V := fun i => (hφ i).mono hVU
  have hB := (isTruncationFamily_relative T hT hTc φ hφ).isPositive k
  have hBR := isPositive_restrict hB hVU
  unfold truncAt
  rw [relativeTruncatedBT_restrict T hT hTc φ hφ hVU k]
  calc
    mulBorel (restrict hVU (relativeTruncatedBT U φ T k))
        ((BedfordTaylorTopDegree.strictLocus V φ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (restrict hVU (relativeTruncatedBT U φ T k))
        ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) :=
      mulBorel_congr hBR
        (measurable_const.indicator (BedfordTaylorTopDegree.measurableSet_strictLocus hφV k))
        (isLocallyBoundedOn_indicator_one _)
        (measurable_const.indicator (BedfordTaylorTopDegree.measurableSet_strictLocus hφ k))
        (isLocallyBoundedOn_indicator_one _)
        (fun x hx => indicator_strictLocus_restrict hVU hx k)
    _ = _ := mulBorel_restrict hB hVU
      (measurable_const.indicator (BedfordTaylorTopDegree.measurableSet_strictLocus hφ k))
      (isLocallyBoundedOn_indicator_one _)

private theorem restricted_relative_strict_readback
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) (hVU : V ≤ U) (k : ℕ) :
    mulBorel (restrict hVU (relativeNonPluripolarProduct T hT hTc φ hφ hm).val)
      ((BedfordTaylorTopDegree.strictLocus V φ k).indicator fun _ => (1 : ℝ)) =
      truncAt (relativeTruncatedBT V φ (restrict hVU T))
        (BedfordTaylorTopDegree.strictLocus V φ) k := by
  let hφV : ∀ i, PlurisubharmonicOn (φ i) V := fun i => (hφ i).mono hVU
  let S := (relativeNonPluripolarProduct T hT hTc φ hφ hm).val
  have hS : IsPositive S := (relativeNonPluripolarProduct T hT hTc φ hφ hm).property
  have hSV := isPositive_restrict hS hVU
  calc
    mulBorel (restrict hVU S)
        ((BedfordTaylorTopDegree.strictLocus V φ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (restrict hVU S)
        ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) :=
      mulBorel_congr hSV
        (measurable_const.indicator (BedfordTaylorTopDegree.measurableSet_strictLocus hφV k))
        (isLocallyBoundedOn_indicator_one _)
        (measurable_const.indicator (BedfordTaylorTopDegree.measurableSet_strictLocus hφ k))
        (isLocallyBoundedOn_indicator_one _)
        (fun x hx => indicator_strictLocus_restrict hVU hx k)
    _ = restrict hVU (mulBorel S
        ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ))) :=
      mulBorel_restrict hS hVU
        (measurable_const.indicator (BedfordTaylorTopDegree.measurableSet_strictLocus hφ k))
        (isLocallyBoundedOn_indicator_one _)
    _ = restrict hVU (truncAt (relativeTruncatedBT U φ T)
        (BedfordTaylorTopDegree.strictLocus U φ) k) :=
      congrArg (restrict hVU) (mulBorel_relativeNonPluripolarProduct_strictLocus T hT hTc φ hφ hm k)
    _ = _ := (relativeTruncAt_restrict T hT hTc φ hφ hVU k).symm

/-- Genuine finite mass is inherited by original open subsets, with the
same original base current actually restricted rather than replaced. -/
theorem hasFiniteRelativeMass_restrict
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) (hVU : V ≤ U) :
    HasFiniteRelativeMass (restrict hVU T) (isPositive_restrict hT hVU)
      (isClosedAny_restrict hTc hVU) φ (fun i => (hφ i).mono hVU) :=
  hasFiniteRelativeMass_of_positive_extension (restrict hVU T) (isPositive_restrict hT hVU)
    (isClosedAny_restrict hTc hVU) φ (fun i => (hφ i).mono hVU)
    (isPositive_restrict (relativeNonPluripolarProduct T hT hTc φ hφ hm).property hVU)
    (restricted_relative_strict_readback T hT hTc φ hφ hm hVU)

/-- The actual finite-mass relative current commutes with genuine open
restriction. All defining strict identities and mass on V are manufactured. -/
theorem restrict_relativeNonPluripolarProduct
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) (hVU : V ≤ U) :
    restrict hVU (relativeNonPluripolarProduct T hT hTc φ hφ hm).val =
      (relativeNonPluripolarProduct (restrict hVU T) (isPositive_restrict hT hVU)
        (isClosedAny_restrict hTc hVU) φ (fun i => (hφ i).mono hVU)
        (hasFiniteRelativeMass_restrict T hT hTc φ hφ hm hVU)).val := by
  let hφV : ∀ i, PlurisubharmonicOn (φ i) V := fun i => (hφ i).mono hVU
  let S := (relativeNonPluripolarProduct T hT hTc φ hφ hm).val
  have hS : IsPositive S := (relativeNonPluripolarProduct T hT hTc φ hφ hm).property
  have hSV := isPositive_restrict hS hVU
  refine eq_relativeNonPluripolarProduct_of_mulBorel (restrict hVU T)
    (isPositive_restrict hT hVU) (isClosedAny_restrict hTc hVU) φ hφV
    (hasFiniteRelativeMass_restrict T hT hTc φ hφ hm hVU) hSV
    (restricted_relative_strict_readback T hT hTc φ hφ hm hVU) ?_
  have hA : MeasurableSet (⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ :=
    (MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus hφ)).compl
  have hAV : MeasurableSet (⋃ k, BedfordTaylorTopDegree.strictLocus V φ k)ᶜ :=
    (MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus hφV)).compl
  rw [mulBorel_congr hSV (measurable_const.indicator hAV) (isLocallyBoundedOn_indicator_one _)
    (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _)
    (fun x hx => indicator_compl_strictLocus_restrict hVU hx),
    mulBorel_restrict hS hVU (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _),
    mulBorel_relativeNonPluripolarProduct_compl T hT hTc φ hφ hm]
  ext γ ψ
  simp [LocalBedfordTaylorLocality.restrict_apply]

/-- Actual compact trace mass is local on ANY original open cover; the
finite subcover and compact refinement are internally produced. -/
theorem hasFiniteRelativeMass_of_cover
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {ι : Type*}
    (V : ι → Opens (ComplexModel n)) (hVU : ∀ i, V i ≤ U)
    (hcov : (U : Set (ComplexModel n)) ⊆ ⋃ i, (V i : Set (ComplexModel n)))
    (hm : ∀ i, HasFiniteRelativeMass (restrict (hVU i) T)
      (isPositive_restrict hT (hVU i)) (isClosedAny_restrict hTc (hVU i))
      φ (fun j => (hφ j).mono (hVU i))) :
    HasFiniteRelativeMass T hT hTc φ hφ := by
  classical
  let hφV : ∀ i j, PlurisubharmonicOn (φ j) (V i) := fun i j => (hφ j).mono (hVU i)
  let hF := isTruncationFamily_relative T hT hTc φ hφ
  let hFV := fun i => isTruncationFamily_relative (restrict (hVU i) T)
    (isPositive_restrict hT (hVU i)) (isClosedAny_restrict hTc (hVU i)) φ (hφV i)
  intro K hK hKU
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i => (V i : Set (ComplexModel n)))
    (fun i => (V i).isOpen) (hKU.trans hcov)
  obtain ⟨L, hLc, hLV, hKL⟩ := hK.finite_compact_cover t
    (fun i => (V i : Set (ComplexModel n))) (fun i _ => (V i).isOpen) ht
  have hb (i : ι) : ⨆ k, ((hFV i).isPositive k).traceMeasure
      (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k) < ⊤ :=
    hm i (L i) (hLc i) (hLV i)
  have heq (i : ι) (k : ℕ) :
      (hF.isPositive k).traceMeasure (L i ∩ BedfordTaylorTopDegree.strictLocus U φ k) =
      ((hFV i).isPositive k).traceMeasure
        (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k) := by
    rw [traceMeasure_congr ((hFV i).isPositive k) (isPositive_restrict (hF.isPositive k) (hVU i))
      (relativeTruncatedBT_restrict T hT hTc φ hφ (hVU i) k),
      traceMeasure_restrict (hF.isPositive k) (hVU i), strictLocus_restrict (hVU i),
      Measure.restrict_apply ((hLc i).measurableSet.inter
        ((hF.measurableSet k).inter (V i).isOpen.measurableSet))]
    congr 1
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hxL, hxO⟩
      exact ⟨⟨hxL, hxO, hLV i hxL⟩, hLV i hxL⟩
    · rintro ⟨⟨hxL, hxO, _⟩, _⟩
      exact ⟨hxL, hxO⟩
  refine lt_of_le_of_lt (b := ∑ i ∈ t, ⨆ k, ((hFV i).isPositive k).traceMeasure
    (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k)) (iSup_le fun k => ?_)
    (ENNReal.sum_lt_top.mpr fun i _ => hb i)
  calc
    (hF.isPositive k).traceMeasure (K ∩ BedfordTaylorTopDegree.strictLocus U φ k) ≤
        ∑ i ∈ t, (hF.isPositive k).traceMeasure
          (L i ∩ BedfordTaylorTopDegree.strictLocus U φ k) := by
      refine (measure_mono ?_).trans (measure_biUnion_finset_le _ _)
      rintro x ⟨hxK, hxO⟩
      rw [hKL] at hxK
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxK
      exact mem_iUnion₂.mpr ⟨i, hi, hxi, hxO⟩
    _ ≤ ∑ i ∈ t, ⨆ k, ((hFV i).isPositive k).traceMeasure
        (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k) :=
      Finset.sum_le_sum fun i _ => (heq i k).le.trans
        (le_iSup (fun k => ((hFV i).isPositive k).traceMeasure
          (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k)) k)

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT_restrict
#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncAt_restrict
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_restrict
#check @SGPT.NPP.RelativeNonPluripolar.restrict_relativeNonPluripolarProduct
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_cover
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncAt_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.restrict_relativeNonPluripolarProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_cover

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_01

-- Exact frozen body: RelativePluriharmonicTruncationDraft
section OriginalFragment_02

/-! Genuine relative Bedford--Taylor pluriharmonic invariance and the
cofinal strict-level comparison of ORIGINAL shifted PSH truncations.
Only the already proved constant-maximum locality is used. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalBedfordTaylorDecreasing
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {U : Opens (ComplexModel n)}

private theorem negative_pluriharmonic_ddc {h : ComplexModel n → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ x ∈ U, smoothDDC h x = 0) :
    ∀ x ∈ U, smoothDDC (fun y => -h y) x = 0 := by
  intro x hx
  have heq : (fun y => -h y) = fun y => (-1 : ℝ) • h y := by
    funext y
    simp
  rw [heq, smoothDDC_smul U.isOpen hh (-1) hx, h0 x hx, smul_zero]

/-- Every ORIGINAL slot can be shifted by its own genuine smooth
pluriharmonic function against the SAME arbitrary closed positive T. -/
theorem btProduct_add_pluriharmonic_all
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (h : Fin p → ComplexModel n → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (h0 : ∀ i, ∀ x ∈ U, smoothDDC (h i) x = 0) :
    btProduct p r (fun i x => u i x + h i x) T = btProduct p r u T := by
  classical
  have hhp (i : Fin p) : IsLocallyBoundedPshOn U (h i) :=
    isLocallyBoundedPshOn_of_continuousOn
      (plurisubharmonicOn_coe_of_smoothDDC_eq_zero U.isOpen (hh i) (h0 i))
      (hh i).continuousOn
  let us : Finset (Fin p) → Fin p → ComplexModel n → ℝ :=
    fun s i x => if i ∈ s then u i x + h i x else u i x
  have hus (s : Finset (Fin p)) (i : Fin p) : IsLocallyBoundedPshOn U (us s i) := by
    by_cases hi : i ∈ s
    · simpa only [us, if_pos hi] using isLocallyBoundedPshOn_add (hu i) (hhp i)
    · simpa only [us, if_neg hi] using hu i
  have stage (s : Finset (Fin p)) : btProduct p r (us s) T = btProduct p r u T := by
    induction s using Finset.induction_on with
    | empty =>
      have heq : us ∅ = u := by funext i x; simp [us]
      rw [heq]
    | @insert j s hj ih =>
      have hjval : us s j = u j := by funext x; simp [us, hj]
      have hnew : us (insert j s) =
          Function.update (us s) j (fun x => u j x + h j x) := by
        funext i x
        by_cases hij : i = j
        · subst i
          simp [us]
        · simp [us, hij]
      rw [hnew]
      have hstep := btProduct_update_add_pluriharmonic p r T hT hTc (us s) (hus s) j (hh j) (h0 j)
      calc
        btProduct p r (Function.update (us s) j (fun x => u j x + h j x)) T =
            btProduct p r (us s) T := by simpa only [hjval] using hstep
        _ = _ := ih
  have hall : us Finset.univ = (fun i x => u i x + h i x) := by funext i x; simp [us]
  simpa only [hall] using stage Finset.univ

private theorem shifted_truncation_max_identity
    (φ ψ : Fin p → ComplexModel n → EReal)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal))
    {C : ℝ} (hb : ∀ i, ∀ x ∈ U, |h i x| ≤ C)
    {k l : ℕ} (hkl : (k : ℝ) + C ≤ (l : ℝ)) :
    ∀ i, ∀ x ∈ U,
      max (truncationReal (φ i) l x - h i x) (-(k : ℝ)) = truncationReal (ψ i) k x := by
  intro i x hx
  have hlo : -C ≤ h i x := (abs_le.mp (hb i x hx)).1
  by_cases hψbot : ψ i x = ⊥
  · have hφbot : φ i x = ⊥ := by rw [heq i x hx, hψbot]; simp
    rw [truncationReal_of_le l (by rw [hφbot]; exact bot_le),
      truncationReal_of_le k (by rw [hψbot]; exact bot_le)]
    exact max_eq_right (by linarith)
  · let b := (ψ i x).toReal
    have hψval : ψ i x = (b : EReal) := (EReal.coe_toReal (hψ i x hx).ne_top hψbot).symm
    have hφval : φ i x = ((b + h i x : ℝ) : EReal) := by
      rw [heq i x hx, hψval, EReal.coe_add]
    have hφtr : truncationReal (φ i) l x = max (b + h i x) (-(l : ℝ)) := by
      unfold truncationReal truncation
      rw [hφval, ← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe]
    have hψtr : truncationReal (ψ i) k x = max b (-(k : ℝ)) := by
      unfold truncationReal truncation
      rw [hψval, ← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe]
    rw [hφtr, hψtr]
    by_cases hcut : b + h i x ≤ -(l : ℝ)
    · rw [max_eq_right hcut, max_eq_right (by linarith), max_eq_right (by linarith)]
    · rw [max_eq_left (not_le.mp hcut).le, add_sub_cancel_right]

/-- The ORIGINAL shifted truncations have the same actual relative
Borel current on each cofinal ORIGINAL strict locus. Inclusion of the
loci and the current identity are both manufactured from the shifts. -/
theorem relativeTruncatedBT_pluriharmonic_cofinal
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ ψ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (h0 : ∀ i, ∀ x ∈ U, smoothDDC (h i) x = 0)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal))
    {C : ℝ} (hb : ∀ i, ∀ x ∈ U, |h i x| ≤ C)
    {k l : ℕ} (hkl : (k : ℝ) + C ≤ (l : ℝ)) :
    BedfordTaylorTopDegree.strictLocus U ψ k ⊆ BedfordTaylorTopDegree.strictLocus U φ l ∧
      mulBorel (relativeTruncatedBT U φ T l)
        ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (relativeTruncatedBT U ψ T k)
        ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)) := by
  let a : Fin p → ComplexModel n → ℝ := fun i x => truncationReal (φ i) l x - h i x
  have hneg (i : Fin p) : IsLocallyBoundedPshOn U (fun x => -h i x) :=
    isLocallyBoundedPshOn_of_continuousOn
      (plurisubharmonicOn_coe_of_smoothDDC_eq_zero U.isOpen (hh i).neg
        (negative_pluriharmonic_ddc (hh i) (h0 i))) (hh i).neg.continuousOn
  have ha (i : Fin p) : IsLocallyBoundedPshOn U (a i) := by
    simpa only [a, sub_eq_add_neg] using
      isLocallyBoundedPshOn_add (truncationReal_isLocallyBoundedPshOn (hφ i) l) (hneg i)
  have hid := shifted_truncation_max_identity φ ψ hψ h heq hb hkl
  have hs : ∀ x ∈ BedfordTaylorTopDegree.strictLocus U ψ k, ∀ i, -(k : ℝ) < a i x := by
    intro x hx i
    have htr := (neg_lt_truncationReal_iff (hψ i) k hx.1).mpr (hx.2 i)
    rw [← hid i x hx.1] at htr
    exact (lt_max_iff.mp htr).resolve_right (lt_irrefl _)
  constructor
  · intro x hx
    refine ⟨hx.1, fun i => ?_⟩
    by_contra hn
    have hle : φ i x ≤ ((-(l : ℝ) : ℝ) : EReal) := le_of_not_gt hn
    have htr := truncationReal_of_le l hle
    have hstrict := hs x hx i
    dsimp only [a] at hstrict
    rw [htr] at hstrict
    have hlo : -C ≤ h i x := (abs_le.mp (hb i x hx.1)).1
    linarith
  · have hmax := btProduct_max_all_indicator_global T hT hTc a ha (fun _ => -(k : ℝ))
      (BedfordTaylorTopDegree.measurableSet_strictLocus hψ k) hs
    have hBTmax : btProduct p r (fun i x => max (a i x) (-(k : ℝ))) T =
        relativeTruncatedBT U ψ T k :=
      btProduct_congr p r _ _ T hid
    rw [hBTmax] at hmax
    have hgauge := btProduct_add_pluriharmonic_all T hT hTc a ha h hh h0
    have hall : (fun i x => a i x + h i x) = (fun i => truncationReal (φ i) l) := by
      funext i x
      exact sub_add_cancel _ _
    rw [hall] at hgauge
    exact (congrArg (fun S => mulBorel S
      ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ))) hgauge).trans hmax.symm

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.btProduct_add_pluriharmonic_all
#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT_pluriharmonic_cofinal
#print axioms SGPT.NPP.RelativeNonPluripolar.btProduct_add_pluriharmonic_all
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT_pluriharmonic_cofinal

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_02

-- Exact frozen body: RelativeBoundedPluriharmonicDraft
section OriginalFragment_03

/-! Bounded pluriharmonic shifts produce actual relative finite mass and
the SAME actual relative current, by cofinal original strict loci and
positive-current uniqueness. No current/limit/output premise is supplied. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {U : Opens (ComplexModel n)}

private theorem shifted_strictLocus_union_eq
    (φ ψ : Fin p → ComplexModel n → EReal)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal)) :
    (⋃ k, BedfordTaylorTopDegree.strictLocus U φ k) =
      ⋃ k, BedfordTaylorTopDegree.strictLocus U ψ k := by
  rw [iUnion_strictLocus_eq_nonpole φ, iUnion_strictLocus_eq_nonpole ψ]
  ext x
  constructor
  · rintro ⟨hxU, hφfin⟩
    refine ⟨hxU, fun i hψbot => hφfin i ?_⟩
    rw [heq i x hxU, hψbot]
    simp
  · rintro ⟨hxU, hψfin⟩
    refine ⟨hxU, fun i => ?_⟩
    have hval : ψ i x = ((ψ i x).toReal : EReal) :=
      (EReal.coe_toReal (hψ i x hxU).ne_top (hψfin i)).symm
    rw [heq i x hxU, hval, ← EReal.coe_add]
    exact EReal.coe_ne_bot _

/-- Actual bounded pluriharmonic data manufacture the shifted tuple's
finite relative mass and equality of its genuine relative current with
the original one. The common mass/limit/current is never an input. -/
theorem exists_relative_product_of_bounded_pluriharmonic
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ ψ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (h0 : ∀ i, ∀ x ∈ U, smoothDDC (h i) x = 0)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal))
    {C : ℝ} (hb : ∀ i, ∀ x ∈ U, |h i x| ≤ C)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    ∃ hmψ : HasFiniteRelativeMass T hT hTc ψ hψ,
      (relativeNonPluripolarProduct T hT hTc φ hφ hm).val =
        (relativeNonPluripolarProduct T hT hTc ψ hψ hmψ).val := by
  let S := (relativeNonPluripolarProduct T hT hTc φ hφ hm).val
  have hS : IsPositive S := (relativeNonPluripolarProduct T hT hTc φ hφ hm).property
  let hFφ := isTruncationFamily_relative T hT hTc φ hφ
  let hFψ := isTruncationFamily_relative T hT hTc ψ hψ
  have hread (k : ℕ) :
      mulBorel S ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)) =
        truncAt (relativeTruncatedBT U ψ T) (BedfordTaylorTopDegree.strictLocus U ψ) k := by
    obtain ⟨l, hl⟩ := exists_nat_ge ((k : ℝ) + C)
    obtain ⟨hsub, hcmp⟩ := relativeTruncatedBT_pluriharmonic_cofinal
      T hT hTc φ ψ hφ hψ h hh h0 heq hb hl
    have hrest := mulBorel_indicator_eq_of_indicator_eq_of_subset
      hS (hFφ.isPositive l) (hFψ.measurableSet k) (hFφ.measurableSet l) hsub
      (mulBorel_relativeNonPluripolarProduct_strictLocus T hT hTc φ hφ hm l)
    exact hrest.trans hcmp
  have hmψ := hasFiniteRelativeMass_of_positive_extension T hT hTc ψ hψ hS hread
  refine ⟨hmψ, eq_relativeNonPluripolarProduct_of_mulBorel T hT hTc ψ hψ hmψ hS hread ?_⟩
  have hz := mulBorel_relativeNonPluripolarProduct_compl T hT hTc φ hφ hm
  rw [shifted_strictLocus_union_eq φ ψ hψ h heq] at hz
  exact hz

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_bounded_pluriharmonic
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_bounded_pluriharmonic

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_03

-- Exact frozen body: RelativePluriharmonicGlobalDraft
section OriginalFragment_04

/-! Unbounded smooth pluriharmonic changes preserve genuine relative mass
and current by internally produced compact neighborhoods. Actual native
Weyl differences then establish independence from original L1-PSH potentials. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {U : Opens (ComplexModel n)}

private theorem exists_shift_bounded_neighborhood
    (h : Fin p → ComplexModel n → ℝ) (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (x : ComplexModel n) (hx : x ∈ U) :
    ∃ (A : Opens (ComplexModel n)) (_hAU : A ≤ U), x ∈ A ∧
      ∃ C : ℝ, ∀ i, ∀ y ∈ A, |h i y| ≤ C := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds hx)
  let A : Opens (ComplexModel n) := ⟨ball x (R / 2), isOpen_ball⟩
  have hA : RelativelyCompactIn A U := relativelyCompactIn_half_ball hR hball
  have hAU : A ≤ U := subset_closure.trans hA.2
  choose C hC using fun i => hA.1.exists_bound_of_continuousOn ((hh i).continuousOn.mono hA.2)
  refine ⟨A, hAU, mem_ball_self (half_pos hR), ∑ i, |C i|, ?_⟩
  intro i y hy
  calc
    |h i y| ≤ C i := by simpa only [Real.norm_eq_abs] using hC i y (subset_closure hy)
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ j, |C j| := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)

/-- Arbitrary smooth pluriharmonic shifts preserve actual finite relative
mass and current on the ORIGINAL domain. Every bounded neighborhood, local
mass and original current restriction is internally produced. -/
theorem exists_relative_product_of_pluriharmonic
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ ψ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (h0 : ∀ i, ∀ x ∈ U, smoothDDC (h i) x = 0)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal))
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    ∃ hmψ : HasFiniteRelativeMass T hT hTc ψ hψ,
      (relativeNonPluripolarProduct T hT hTc φ hφ hm).val =
        (relativeNonPluripolarProduct T hT hTc ψ hψ hmψ).val := by
  classical
  choose A hAU hxA C hbound using fun x : U =>
    exists_shift_bounded_neighborhood h hh x.val x.property
  let hφA (x : U) (i : Fin p) := (hφ i).mono (hAU x)
  let hψA (x : U) (i : Fin p) := (hψ i).mono (hAU x)
  let hTA (x : U) := isPositive_restrict hT (hAU x)
  let hTcA (x : U) := isClosedAny_restrict hTc (hAU x)
  let hmφA (x : U) := hasFiniteRelativeMass_restrict T hT hTc φ hφ hm (hAU x)
  have hlocal (x : U) :
      ∃ hmψA : HasFiniteRelativeMass (restrict (hAU x) T) (hTA x) (hTcA x) ψ (hψA x),
        (relativeNonPluripolarProduct (restrict (hAU x) T) (hTA x) (hTcA x) φ (hφA x)
          (hmφA x)).val =
        (relativeNonPluripolarProduct (restrict (hAU x) T) (hTA x) (hTcA x) ψ (hψA x) hmψA).val :=
    exists_relative_product_of_bounded_pluriharmonic (restrict (hAU x) T) (hTA x) (hTcA x)
      φ ψ (hφA x) (hψA x) h (fun i => (hh i).mono (hAU x))
      (fun i y hy => h0 i y (hAU x hy)) (fun i y hy => heq i y (hAU x hy))
      (hbound x) (hmφA x)
  choose hmψA hlocaleq using hlocal
  have hcov : (U : Set (ComplexModel n)) ⊆ ⋃ x : U, (A x : Set (ComplexModel n)) :=
    fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxA ⟨y, hy⟩⟩
  have hmψ := hasFiniteRelativeMass_of_cover T hT hTc ψ hψ A hAU hcov hmψA
  refine ⟨hmψ, ?_⟩
  apply eq_of_local
  intro x hx
  let j : U := ⟨x, hx⟩
  refine ⟨A j, hAU j, hxA j, ?_⟩
  exact (restrict_relativeNonPluripolarProduct T hT hTc φ hφ hm (hAU j)).trans
    ((hlocaleq j).trans (restrict_relativeNonPluripolarProduct T hT hTc ψ hψ hmψ (hAU j)).symm)

private theorem reverse_shift_relation
    (φ ψ : Fin p → ComplexModel n → EReal)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal)) :
    ∀ i, ∀ x ∈ U, ψ i x = φ i x + ((-h i x : ℝ) : EReal) := by
  intro i x hx
  by_cases hbot : ψ i x = ⊥
  · rw [heq i x hx, hbot]
    simp
  · have hval : ψ i x = ((ψ i x).toReal : EReal) :=
      (EReal.coe_toReal (hψ i x hx).ne_top hbot).symm
    rw [heq i x hx, hval, ← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

/-- Finite relative mass is genuinely invariant under arbitrary smooth
pluriharmonic changes, with no global boundedness or limit premise. -/
theorem hasFiniteRelativeMass_pluriharmonic_iff
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ ψ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (h0 : ∀ i, ∀ x ∈ U, smoothDDC (h i) x = 0)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal)) :
    HasFiniteRelativeMass T hT hTc φ hφ ↔ HasFiniteRelativeMass T hT hTc ψ hψ := by
  constructor
  · intro hm
    exact (exists_relative_product_of_pluriharmonic T hT hTc φ ψ hφ hψ h hh h0 heq hm).choose
  · intro hm
    have hneg0 : ∀ i, ∀ x ∈ U, smoothDDC (fun y => -h i y) x = 0 := by
      intro i x hx
      have hneg : (fun y => -h i y) = fun y => (-1 : ℝ) • h i y := by funext y; simp
      rw [hneg, smoothDDC_smul U.isOpen (hh i) (-1) hx, h0 i x hx, smul_zero]
    exact (exists_relative_product_of_pluriharmonic T hT hTc ψ φ hψ hφ
      (fun i x => -h i x) (fun i => (hh i).neg) hneg0
      (reverse_shift_relation φ ψ hψ h heq) hm).choose

/-- The SAME actual relative current is independent of arbitrary smooth
pluriharmonic changes; the mass witnesses are ordinary actual trace bounds. -/
theorem relative_product_eq_of_pluriharmonic
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ ψ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : ∀ i, PlurisubharmonicOn (ψ i) U) (h : Fin p → ComplexModel n → ℝ)
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U)
    (h0 : ∀ i, ∀ x ∈ U, smoothDDC (h i) x = 0)
    (heq : ∀ i, ∀ x ∈ U, φ i x = ψ i x + (h i x : EReal))
    (hmφ : HasFiniteRelativeMass T hT hTc φ hφ)
    (hmψ : HasFiniteRelativeMass T hT hTc ψ hψ) :
    (relativeNonPluripolarProduct T hT hTc φ hφ hmφ).val =
      (relativeNonPluripolarProduct T hT hTc ψ hψ hmψ).val := by
  obtain ⟨_, he⟩ := exists_relative_product_of_pluriharmonic T hT hTc φ ψ hφ hψ h hh h0 heq hmφ
  exact he

/-- ACTUAL equality of the original distributional current factors
manufactures every pluriharmonic difference by native Weyl/PSH rigidity;
the relative mass domain and genuine relative current then agree.
This current-factor theorem explicitly uses the native n=m+1 carrier. -/
theorem relative_product_independent_of_ddcL1 {m : ℕ} {A : Opens (ComplexModel (m + 1))}
    (T : LocalProductCurrent (m + 1) A (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ ψ : Fin p → ComplexModel (m + 1) → EReal)
    (hφ : ∀ i, IsL1PshOn A (φ i)) (hψ : ∀ i, IsL1PshOn A (ψ i))
    (he : ∀ i, ddcL1 A (φ i) = ddcL1 A (ψ i)) :
    (HasFiniteRelativeMass T hT hTc φ (fun i => (hφ i).psh) ↔
      HasFiniteRelativeMass T hT hTc ψ (fun i => (hψ i).psh)) ∧
    ∀ (hmφ : HasFiniteRelativeMass T hT hTc φ (fun i => (hφ i).psh))
      (hmψ : HasFiniteRelativeMass T hT hTc ψ (fun i => (hψ i).psh)),
      (relativeNonPluripolarProduct T hT hTc φ (fun i => (hφ i).psh) hmφ).val =
        (relativeNonPluripolarProduct T hT hTc ψ (fun i => (hψ i).psh) hmψ).val := by
  choose h hh h0 heq using fun i =>
    SGPT.Currents.exists_pluriharmonic_of_ddcL1_eq (hψ i) (hφ i) (he i).symm
  exact ⟨hasFiniteRelativeMass_pluriharmonic_iff T hT hTc φ ψ
    (fun i => (hφ i).psh) (fun i => (hψ i).psh) h hh h0 heq,
    fun hmφ hmψ => relative_product_eq_of_pluriharmonic T hT hTc φ ψ
      (fun i => (hφ i).psh) (fun i => (hψ i).psh) h hh h0 heq hmφ hmψ⟩

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_pluriharmonic
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_pluriharmonic_iff
#check @SGPT.NPP.RelativeNonPluripolar.relative_product_eq_of_pluriharmonic
#check @SGPT.NPP.RelativeNonPluripolar.relative_product_independent_of_ddcL1
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_pluriharmonic
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_pluriharmonic_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_product_eq_of_pluriharmonic
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_product_independent_of_ddcL1

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_04
