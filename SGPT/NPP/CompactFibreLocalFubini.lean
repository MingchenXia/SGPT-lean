import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
import SGPT.NPP.NonPluripolarCurrent5Fubini
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
import SGPT.NPP.NonPluripolarCurrentNonCharging
import SGPT.NPP.NonPluripolarCurrent2Measure
import SGPT.NPP.NonPluripolarCurrent5Slicing
import SGPT.Foundations.Analysis.Pending.IncreasingMeasureIntegrals
import Lean.Elab.Command

/-! Genuine compact fibre slicing, original source proof fragments under proper canonical module identity. -/

section CompactFibreCanonicalFragment005

/-! Actual positive coefficient measures and Borel readings of the SAME current.
Every measure and density is constructed from the original current's trace. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalCurrentLebesgue LocalBedfordTaylorForms

variable {N q : ℕ} {Ω : Opens (ComplexModel N)} {T : LocalProductCurrent N Ω q}

/-- The actual positive coefficient measure against an original constant
strongly positive form; the representation is proved below. -/
def positiveCoefficientMeasure (hT : IsPositive T) (β : formSpan N q) : Measure (ComplexModel N) :=
  hT.traceMeasure.withDensity (fun x => ENNReal.ofReal (densityForm hT x β))

theorem positiveCoefficientMeasure_compl (hT : IsPositive T) (β : formSpan N q) :
    positiveCoefficientMeasure hT β (Ω : Set (ComplexModel N))ᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ hT.traceMeasure_compl

theorem positiveCoefficientMeasure_lt_top (hT : IsPositive T) (β : formSpan N q)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    positiveCoefficientMeasure hT β K < ⊤ := by
  obtain ⟨C, _, hC⟩ := exists_abs_densityForm_le hT β
  rw [positiveCoefficientMeasure, withDensity_apply _ hK.measurableSet]
  calc
    (∫⁻ x in K, ENNReal.ofReal (densityForm hT x β) ∂hT.traceMeasure) ≤
        ∫⁻ _ in K, ENNReal.ofReal C ∂hT.traceMeasure :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x)))
    _ = ENNReal.ofReal C * hT.traceMeasure K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hT.traceMeasure_lt_top hK hKΩ)

/-- All Borel readings use the same actual current coefficient, including
signed functions and the totalized nonintegrable convention on both sides. -/
theorem integral_positiveCoefficientMeasure (hT : IsPositive T) (β : formSpan N q)
    (hβ : β ∈ posCone N q) (g : ComplexModel N → ℝ) :
    (∫ x, g x ∂positiveCoefficientMeasure hT β) =
      ∫ x, g x * densityForm hT x β ∂hT.traceMeasure := by
  have hfm : Measurable (fun x => ENNReal.ofReal (densityForm hT x β)) :=
    ENNReal.measurable_ofReal.comp (measurable_densityForm hT β)
  have hflt : ∀ᵐ x ∂hT.traceMeasure, ENNReal.ofReal (densityForm hT x β) < ⊤ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [positiveCoefficientMeasure, integral_withDensity_eq_integral_toReal_smul hfm hflt]
  apply integral_congr_ae
  filter_upwards [ae_densityForm_nonneg hT] with x hx
  rw [ENNReal.toReal_ofReal (hx β hβ), smul_eq_mul, mul_comm]

theorem current_apply_eq_integral_positiveCoefficientMeasure (hT : IsPositive T)
    (β : formSpan N q) (hβ : β ∈ posCone N q) (ψ : 𝓓(Ω, ℝ)) :
    T β ψ = ∫ x, ψ x ∂positiveCoefficientMeasure hT β := by
  rw [integral_positiveCoefficientMeasure hT β hβ, apply_eq_integral_densityForm hT]

/-- Local finiteness and the representing density ONE are manufactured from
the original current, never supplied as a target-shaped representation field. -/
theorem positiveCoefficientMeasure_localDensity (hT : IsPositive T) (β : formSpan N q) :
    IsLocalDensity (U := Ω) (positiveCoefficientMeasure hT β) (fun _ => 1) := by
  refine ⟨positiveCoefficientMeasure_compl hT β,
    fun K hK hKΩ => positiveCoefficientMeasure_lt_top hT β hK hKΩ,
    measurable_const, ?_⟩
  intro K _ _
  exact ⟨1, fun _ _ => by simp⟩

/-- Literal Borel multiplication of the original current reads as integration
against its actual coefficient measure. -/
theorem mulBorel_apply_eq_integral_positiveCoefficientMeasure (hT : IsPositive T)
    (β : formSpan N q) (hβ : β ∈ posCone N q)
    {g : ComplexModel N → ℝ} (hg : Measurable g) (hgb : IsLocallyBoundedOn g Ω)
    (ψ : 𝓓(Ω, ℝ)) :
    mulBorel T g β ψ = ∫ x, ψ x * g x ∂positiveCoefficientMeasure hT β := by
  simpa only [mul_one] using mulBorel_apply_of_integral_eq hT β
    (positiveCoefficientMeasure_localDensity hT β)
    (fun φ => by simpa only [mul_one] using
      current_apply_eq_integral_positiveCoefficientMeasure hT β hβ φ) hg hgb ψ

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment005

section CompactFibreCanonicalFragment006

/-! Exact original joint/fibre strict truncation dictionaries.
The augmented top-degree tuple retains the original primary functions. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending
open SGPT.NPP.FibreSlicing

/-- The original primary EReal tuple with the actual base quadratics appended. -/
def augmentedFibreTuple {n m : ℕ} (u : Fin n → ComplexModel (n + m) → EReal) :
    Fin (n + m) → ComplexModel (n + m) → EReal :=
  Fin.append u (fun k q => (baseNormSq n m k q : EReal))

/-- Restriction commutes with the actual real max truncation, retaining poles. -/
theorem truncationReal_fibreMapM {n m : ℕ}
    (u : ComplexModel (n + m) → EReal) (z : ComplexModel m) (k : ℕ) :
    (fun x => truncationReal u k (fibreMapM n m z x)) =
      truncationReal (fun x => u (fibreMapM n m z x)) k := rfl

/-- The original common strict level set restricts to EXACTLY the fibre set. -/
theorem strictLocus_fibreMapM {n m : ℕ}
    (Q : Opens (ComplexModel n)) (D : Opens (ComplexModel m))
    (u : Fin n → ComplexModel (n + m) → EReal) {z : ComplexModel m} (hz : z ∈ D) (k : ℕ) :
    fibreMapM n m z ⁻¹' BedfordTaylorTopDegree.strictLocus (prodOpens Q D) u k =
      BedfordTaylorTopDegree.strictLocus Q (fun i x => u i (fibreMapM n m z x)) k := by
  ext x
  simp only [mem_preimage, BedfordTaylorTopDegree.strictLocus, mem_ofPred_eq,
    mem_prodOpens, projFst_fibreMapM, projSnd_fibreMapM, hz, and_true]

/-- Base quadratics never change under the actual nonnegative-level truncation. -/
theorem mixedTruncationReal_augmentedFibreTuple {n m : ℕ}
    (u : Fin n → ComplexModel (n + m) → EReal) (k : ℕ) :
    mixedTruncationReal (augmentedFibreTuple u) k =
      fullTuple (fun i => truncationReal (u i) k) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [mixedTruncationReal, augmentedFibreTuple, fullTuple, Fin.append_left]
  · funext q
    have hq : -(k : ℝ) ≤ baseNormSq n m b q := by
      have := sq_nonneg ‖q (Fin.natAdd n b)‖
      have := Nat.cast_nonneg (α := ℝ) k
      dsimp only [baseNormSq]
      linarith
    simp only [mixedTruncationReal, augmentedFibreTuple, Fin.append_right, fullTuple,
      truncationReal, truncation, max_eq_left (EReal.coe_le_coe_iff.mpr hq), EReal.toReal_coe]
    rfl

/-- At positive levels the augmented tuple has EXACTLY the original primary
strict locus; no base coordinate is cut out. -/
theorem commonStrictLocus_augmentedFibreTuple {n m : ℕ}
    (Ω : Opens (ComplexModel (n + m)))
    (u : Fin n → ComplexModel (n + m) → EReal) {k : ℕ} (hk : 0 < k) :
    commonStrictLocus Ω (augmentedFibreTuple u) k =
      BedfordTaylorTopDegree.strictLocus Ω u k := by
  ext q
  constructor
  · rintro ⟨hq, h⟩
    exact ⟨hq, fun i => by simpa only [augmentedFibreTuple, Fin.append_left] using h (Fin.castAdd m i)⟩
  · rintro ⟨hq, h⟩
    refine ⟨hq, fun i => ?_⟩
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [augmentedFibreTuple, Fin.append_left] using h a
    · have hq0 : 0 ≤ baseNormSq n m b q := sq_nonneg _
      have hqk : -(k : ℝ) < baseNormSq n m b q := by
        have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
        linarith
      simpa only [augmentedFibreTuple, Fin.append_right] using EReal.coe_lt_coe_iff.mpr hqk

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment006

section CompactFibreCanonicalFragment007

/-! The actual finite-level Fubini measures ARE the existing original NPP
truncation measures, jointly and on every actual base fibre. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.NPP.FibreSlicing

theorem plurisubharmonicOn_augmentedFibreTuple {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) :
    ∀ i, PlurisubharmonicOn (augmentedFibreTuple u i) Ω := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa only [augmentedFibreTuple, Fin.append_left] using hu a
  · simpa only [augmentedFibreTuple, Fin.append_right, baseNormSq, sqCoord] using
      (isLocallyBoundedPshOn_sqCoord (Fin.natAdd n b) Ω).1

/-- Actual affine fibre inclusion, with no restriction on either dimension. -/
theorem plurisubharmonicOn_original_fibre {n m : ℕ}
    (Q : Opens (ComplexModel n)) (D : Opens (ComplexModel m))
    {u : ComplexModel (n + m) → EReal} (hu : PlurisubharmonicOn u (prodOpens Q D))
    {z : ComplexModel m} (hz : z ∈ D) :
    PlurisubharmonicOn (fun x => u (fibreMapM n m z x)) Q := by
  have h := hu.comp_affine (inclFstC n m) (fibreMapM n m z 0)
  simp only [← fibreMapM_eq_add] at h
  apply h.mono
  intro x hx
  change ProductMixedMeasure.projFst n m (fibreMapM n m z x) ∈ (Q : Set (ComplexModel n)) ∧
    ProductMixedMeasure.projSnd n m (fibreMapM n m z x) ∈ (D : Set (ComplexModel m))
  rw [projFst_fibreMapM, projSnd_fibreMapM]
  exact ⟨hx, hz⟩

/-- The joint strict-level measure is exactly the ORIGINAL mixed NPP
truncation measure of the augmented original tuple. -/
theorem strict_joint_measure_eq_mixedTruncationMeasure {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) {k : ℕ} (hk : 0 < k) :
    (fullMeasure (fun i => truncationReal_isLocallyBoundedPshOn (hu i) k)).restrict
        (BedfordTaylorTopDegree.strictLocus Ω u k) =
      MixedNonPluripolar.mixedTruncationMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu) k := by
  have hcanon := IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec Ω _
      (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_augmentedFibreTuple hu) k))
  have hcanon' : IsBTLimit Ω (fullTuple (fun i => truncationReal (u i) k))
      (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal (augmentedFibreTuple u) k)
        (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_augmentedFibreTuple hu) k)) :=
    hcanon.congr (fun i x _ => congrFun (congrFun (mixedTruncationReal_augmentedFibreTuple u k) i) x)
  have heq := (isBTLimit_fullMeasure
    (fun i => truncationReal_isLocallyBoundedPshOn (hu i) k)).unique hcanon'
  unfold MixedNonPluripolar.mixedTruncationMeasure
  rw [commonStrictLocus_augmentedFibreTuple Ω u hk]
  exact congrArg (fun ν => ν.restrict (BedfordTaylorTopDegree.strictLocus Ω u k)) heq

/-- The every-fibre strict-level measure is the ORIGINAL fibre NPP truncation
measure, on the same entire original fibre open set. -/
theorem strict_fibre_measure_eq_mixedTruncationMeasure {n m : ℕ}
    (Q : Opens (ComplexModel n)) (D : Opens (ComplexModel m))
    {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) (prodOpens Q D))
    {z : ComplexModel m} (hz : z ∈ D) (k : ℕ) :
    ((slicingFamily (fun i => truncationReal_isLocallyBoundedPshOn (hu i) k) z).restrict
        (fibreMapM n m z ⁻¹' BedfordTaylorTopDegree.strictLocus (prodOpens Q D) u k)) =
      MixedNonPluripolar.mixedTruncationMeasure Q (fun i x => u i (fibreMapM n m z x))
        (fun i => plurisubharmonicOn_original_fibre Q D (hu i) hz) k := by
  rw [slicingFamily_of_mem _ hz, strictLocus_fibreMapM Q D u hz k]
  have hcanon := IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec Q _
      (mixedTruncationReal_isLocallyBounded
        (fun i => plurisubharmonicOn_original_fibre Q D (hu i) hz) k))
  have hBT := isBTLimit_fibreMeasure
    (fun i => truncationReal_isLocallyBoundedPshOn (hu i) k) hz
  have heq := hBT.unique hcanon
  exact congrArg (fun ν => ν.restrict
    (BedfordTaylorTopDegree.strictLocus Q (fun i x => u i (fibreMapM n m z x)) k)) heq

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment007

section CompactFibreCanonicalFragment008

/-! The actual original NPP current's base-form coefficient IS the actual
canonical augmented NPP measure. The equality is produced from strict loci. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalCurrentLebesgue LocalBedfordTaylorForms
open LocalBedfordTaylorLocality LocalBedfordTaylorProducts
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

/-- Full actual current/measure dictionary for the original base form. Neither
the current coefficient equality nor augmented measure finiteness is supplied. -/
theorem current_basePower_coefficient_eq_original_npLimit {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hW : IsWellDefinedOn (Nat.add_comm m n) Ω u) :
    positiveCoefficientMeasure
        (isPositive_nonPluripolarProduct (Nat.add_comm m n) hu hW) (basePowerSpan n m) =
      MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu) := by
  let hP := isPositive_nonPluripolarProduct (Nat.add_comm m n) hu hW
  let β := basePowerSpan n m
  have hβ : β ∈ posCone (n + m) m := basePowerSpan_mem_posCone
  let ν := positiveCoefficientMeasure hP β
  let μ := MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
    (plurisubharmonicOn_augmentedFibreTuple hu)
  let O := fun k => BedfordTaylorTopDegree.strictLocus Ω u k
  have hO (k : ℕ) : MeasurableSet (O k) := BedfordTaylorTopDegree.measurableSet_strictLocus hu k
  have hrestrict (k : ℕ) : ν.restrict (O (k + 1)) = μ.restrict (O (k + 1)) := by
    let U := fun i => truncationReal (u i) (k + 1)
    let hU := fun i => truncationReal_isLocallyBoundedPshOn (hu i) (k + 1)
    let ξ := fullMeasure hU
    have hξ := isBTLimit_fullMeasure hU
    have hνξ : ν.restrict (O (k + 1)) = ξ.restrict (O (k + 1)) := by
      apply eq_of_forall_testFunction_integral_eq (U := Ω)
      · exact le_antisymm ((Measure.restrict_le_self _).trans_eq
          (positiveCoefficientMeasure_compl hP β)) bot_le
      · exact le_antisymm ((Measure.restrict_le_self _).trans_eq hξ.1) bot_le
      · intro K hK hKΩ
        exact (Measure.restrict_le_self K).trans_lt (positiveCoefficientMeasure_lt_top hP β hK hKΩ)
      · intro K hK hKΩ
        exact (Measure.restrict_le_self K).trans_lt (hξ.2.1 K hK hKΩ)
      · intro ψ
        have hp := mulBorel_apply_eq_integral_positiveCoefficientMeasure hP β hβ
          (measurable_const.indicator (hO (k + 1))) (isLocallyBoundedOn_indicator_one _) ψ
        have hξdens : IsLocalDensity (U := Ω) ξ (fun _ => 1) :=
          ⟨hξ.1, hξ.2.1, measurable_const, fun K _ _ => ⟨1, fun _ _ => by simp⟩⟩
        have hb := mulBorel_apply_of_integral_eq (isPositive_productBT hU) β hξdens
          (fun φ => by simpa only [productBT, β, basePowerSpan, ξ, mul_one] using
            btProduct_apply_basePower hU φ)
          (measurable_const.indicator (hO (k + 1))) (isLocallyBoundedOn_indicator_one _) ψ
        simp only [mul_one] at hb
        have heq := congrArg (fun R => R β ψ)
          (mulBorel_nonPluripolarProduct_strictLocus (Nat.add_comm m n) hu hW (k + 1))
        change mulBorel (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct (Nat.add_comm m n) Ω u)
            ((O (k + 1)).indicator (fun _ => (1 : ℝ))) β ψ =
          mulBorel (productBT Ω U) ((O (k + 1)).indicator (fun _ => (1 : ℝ))) β ψ at heq
        have hi : (fun x => ψ x * (O (k + 1)).indicator (fun _ => (1 : ℝ)) x) =
            (O (k + 1)).indicator (fun x => ψ x) := by
          funext x
          by_cases hx : x ∈ O (k + 1) <;> simp [hx]
        rw [hp, hb, hi] at heq
        simpa only [integral_indicator (hO (k + 1))] using heq
    have hμξ : μ.restrict (O (k + 1)) = ξ.restrict (O (k + 1)) := by
      have hs := MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_commonStrictLocus
        (plurisubharmonicOn_augmentedFibreTuple hu) (k + 1)
      rw [commonStrictLocus_augmentedFibreTuple Ω u (Nat.zero_lt_succ k)] at hs
      exact hs.trans (strict_joint_measure_eq_mixedTruncationMeasure hu (Nat.zero_lt_succ k)).symm
    exact hνξ.trans hμξ.symm
  let F := isTruncationFamily (Nat.add_comm m n) hu
  have hm : F.HasLocallyFiniteMass := (isWellDefinedOn_iff (Nat.add_comm m n) hu).mp hW
  have htrace : hP.traceMeasure = F.glueMeasure :=
    (traceMeasure_congr hP (F.isPositive_glue hm)
      (nonPluripolarProduct_eq (Nat.add_comm m n) hu)).trans (F.traceMeasure_glue hm)
  have hνae : ∀ᵐ x ∂ν, x ∈ ⋃ k, O (k + 1) := by
    have ht : ∀ᵐ x ∂hP.traceMeasure, ∃ k, x ∈ O k := by
      rw [htrace]
      exact F.ae_glueMeasure_mem
    have hac : ν ≪ hP.traceMeasure := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le ht] with x hx
    obtain ⟨k, hk⟩ := hx
    exact mem_iUnion.mpr ⟨k, BedfordTaylorTopDegree.strictLocus_mono Ω u (Nat.le_succ k) hk⟩
  have hμae : ∀ᵐ x ∂μ, x ∈ ⋃ k, O (k + 1) := by
    have hnull : μ (⋃ k, commonStrictLocus Ω (augmentedFibreTuple u) k)ᶜ = 0 := by
      rw [compl_iUnion_commonStrictLocus]
      exact measure_union_null
        (MixedNonPluripolar.mixedTruncationLimitMeasure_compl (plurisubharmonicOn_augmentedFibreTuple hu))
        (MixedNonPluripolar.mixedTruncationLimitMeasure_poleSet (plurisubharmonicOn_augmentedFibreTuple hu))
    have ha : ∀ᵐ x ∂μ, x ∈ ⋃ k, commonStrictLocus Ω (augmentedFibreTuple u) k :=
      ae_iff.mpr hnull
    filter_upwards [ha] with x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have hp : x ∈ O k := ⟨hk.1, fun i => by
      simpa only [augmentedFibreTuple, Fin.append_left] using hk.2 (Fin.castAdd m i)⟩
    exact mem_iUnion.mpr ⟨k, BedfordTaylorTopDegree.strictLocus_mono Ω u (Nat.le_succ k) hp⟩
  have heq := Measure.restrict_iUnion_congr.mpr hrestrict
  rw [Measure.restrict_eq_self_of_ae_mem hνae, Measure.restrict_eq_self_of_ae_mem hμae] at heq
  exact heq

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment008

section CompactFibreCanonicalFragment009

/-! The existing actual smooth wedge measure of the original current equals
the same canonical augmented NP measure with its produced smooth base density. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms TopDegreeDensity
open LocalProductCurrents LocalCurrentLebesgue
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

def baseTwoFormPullback {n m : ℕ} (a : ComplexModel m → RealForm m 2)
    (q : ComplexModel (n + m)) : RealForm (n + m) 2 :=
  (a (ProductMixedMeasure.projSnd n m q)).compContinuousLinearMap (ProductMixedMeasure.projSnd n m)

def basePowerDensity {n m : ℕ} (Q : Opens (ComplexModel n)) (D : Opens (ComplexModel m))
    (a : ComplexModel m → RealForm m 2) : ComplexModel (n + m) → ℝ :=
  (prodOpens Q D : Set (ComplexModel (n + m))).indicator
    (fun q => Real.pi ^ m * topDensity (formPower (a (ProductMixedMeasure.projSnd n m q)) m))

private theorem formPower_pullback {N M : ℕ} (L : ComplexModel N →L[ℝ] ComplexModel M)
    (a : RealForm M 2) (k : ℕ) :
    formPower (a.compContinuousLinearMap L) k = (formPower a k).compContinuousLinearMap L := by
  induction k with
  | zero => rw [formPower_zero, formPower_zero, coordinateWedgeUnit_compContinuousLinearMap]
  | succ k ih =>
    rw [formPower_succ, formPower_succ, coordinateWedge_compContinuousLinearMap, ih]

theorem measurable_basePowerDensity {n m : ℕ} {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {a : ComplexModel m → RealForm m 2} (ha : ContDiffOn ℝ ∞ a D) :
    Measurable (basePowerDensity Q D a) := by
  classical
  exact (contDiffOn_topDensity_comp (contDiffOn_formPower ha m)).continuousOn.measurable_piecewise
    continuousOn_const (prodOpens Q D).isOpen.measurableSet

theorem wedgePowerMeasure_base_eq_coefficient {n m : ℕ}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {T : LocalProductCurrent (n + m) (prodOpens Q D) m} (hT : IsPositive T)
    {a : ComplexModel m → RealForm m 2} (ha : ContDiffOn ℝ ∞ a D)
    (hap : ∀ z ∈ D, IsSemipositiveOneOne (a z)) :
    wedgePowerMeasure T (baseTwoFormPullback a) =
      (positiveCoefficientMeasure hT (basePowerSpan n m)).withDensity
        (fun q => ENNReal.ofReal (basePowerDensity Q D a q)) := by
  have hd0 (q : ComplexModel (n + m)) : 0 ≤ basePowerDensity Q D a q := by
    by_cases hq : q ∈ prodOpens Q D
    · rw [basePowerDensity, indicator_of_mem hq]
      exact mul_nonneg (pow_pos Real.pi_pos m).le
        (topDensity_nonneg_of_mem_spCone (formPower_mem_spCone (hap _ hq.2) m))
    · rw [basePowerDensity, indicator_of_notMem hq]
  have hspan {q : ComplexModel (n + m)} (hq : q ∈ prodOpens Q D) :
      powerSpan m (baseTwoFormPullback a q) = basePowerDensity Q D a q • basePowerSpan n m := by
    have hapos : IsSemipositiveOneOne (baseTwoFormPullback a q) :=
      (hap _ hq.2).comp (ProductMixedMeasure.projSnd n m)
        (fun v => ProductMixedMeasure.projSnd_smul Complex.I v)
    apply Subtype.ext
    rw [coe_powerSpan hapos, Submodule.coe_smul]
    change formPower ((a (ProductMixedMeasure.projSnd n m q)).compContinuousLinearMap
        (ProductMixedMeasure.projSnd n m)) m = _
    rw [formPower_pullback, basePowerDensity, indicator_of_mem hq]
    exact pullbackSnd_eq (formPower (a (ProductMixedMeasure.projSnd n m q)) m)
  have hdm : Measurable (fun q => ENNReal.ofReal (basePowerDensity Q D a q)) :=
    ENNReal.measurable_ofReal.comp (measurable_basePowerDensity ha (Q := Q))
  have hcm : Measurable (fun q => ENNReal.ofReal (densityForm hT q (basePowerSpan n m))) :=
    ENNReal.measurable_ofReal.comp (measurable_densityForm hT (basePowerSpan n m))
  rw [wedgePowerMeasure, dif_pos hT, positiveCoefficientMeasure,
    ← withDensity_mul hT.traceMeasure hcm hdm]
  apply withDensity_congr_ae
  filter_upwards [ae_iff.mpr hT.traceMeasure_compl] with q hq
  rw [hspan hq, map_smul, smul_eq_mul, ENNReal.ofReal_mul (hd0 q)]
  exact mul_comm _ _

theorem original_np_wedgePowerMeasure_base_eq_npLimit {n m : ℕ}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) (prodOpens Q D))
    (hW : IsWellDefinedOn (Nat.add_comm m n) (prodOpens Q D) u)
    {a : ComplexModel m → RealForm m 2} (ha : ContDiffOn ℝ ∞ a D)
    (hap : ∀ z ∈ D, IsSemipositiveOneOne (a z)) :
    wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
      (Nat.add_comm m n) (prodOpens Q D) u) (baseTwoFormPullback a) =
      (MixedNonPluripolar.mixedTruncationLimitMeasure (prodOpens Q D) (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu)).withDensity
        (fun q => ENNReal.ofReal (basePowerDensity Q D a q)) := by
  rw [wedgePowerMeasure_base_eq_coefficient
    (isPositive_nonPluripolarProduct (Nat.add_comm m n) hu hW) ha hap,
    current_basePower_coefficient_eq_original_npLimit hu hW]

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment009

section CompactFibreCanonicalFragment011

/-! Actual positive finite-level fibre Fubini for arbitrary base dimension.
This is the genuine monotone-limit input, not an assumption on the limit. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.NPP.FibreSlicing

/-- Actual nonnegative Borel BT slicing, all base dimensions including zero,
with joint/every-fibre integrability and outer AE measurability produced. -/
theorem lintegral_mul_isBTLimit_eq_fibreM {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))}
    {u : Fin (n + m) → ComplexModel (n + m) → ℝ}
    (hbase : ∀ k : Fin m, u (Fin.natAdd n k) = baseNormSq n m k)
    {ν : Measure (ComplexModel (n + m))} (hν : IsBTLimit Ω u ν)
    {μ : ComplexModel m → Measure (ComplexModel n)}
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    {χ : ComplexModel (n + m) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hχ0 : ∀ q, 0 ≤ χ q)
    {F : ComplexModel (n + m) → ℝ} (hFm : Measurable F) {C : ℝ}
    (hFb : ∀ q, ‖F q‖ ≤ C) (hF0 : ∀ q, 0 ≤ F q) :
    AEMeasurable (fun z => ∫⁻ x,
      ENNReal.ofReal (χ (fibreMapM n m z x) * F (fibreMapM n m z x)) ∂μ z) ∧
      (∫⁻ q, ENNReal.ofReal (χ q * F q) ∂ν) =
        (∫⁻ z, ∫⁻ x, ENNReal.ofReal
          (χ (fibreMapM n m z x) * F (fibreMapM n m z x)) ∂μ z) /
            ENNReal.ofReal (Real.pi ^ m) := by
  let I : ComplexModel m → ℝ := fun z => ∫ x,
    χ (fibreMapM n m z x) * F (fibreMapM n m z x) ∂μ z
  have hf0 (q : ComplexModel (n + m)) : 0 ≤ χ q * F q := mul_nonneg (hχ0 q) (hF0 q)
  have hχν : Integrable χ ν := VaguePortmanteau.integrable_of_tsupport_subset hν.2.1 hχ hχc hχΩ
  have hjoint : Integrable (fun q => χ q * F q) ν :=
    hχν.mul_bdd hFm.aestronglyMeasurable (Eventually.of_forall hFb)
  have hinnerInt (z : ComplexModel m) : Integrable
      (fun x => χ (fibreMapM n m z x) * F (fibreMapM n m z x)) (μ z) :=
    integrable_fibre_test_mul hμ hχ hχc hχΩ hFm hFb z
  have hs := integral_mul_isBTLimit_eq_fibreIntegral hbase hν hμ hχ hχc hχΩ hχ0 hFm hFb
  have hI : Integrable I := hs.1
  have hI0 (z : ComplexModel m) : 0 ≤ I z := integral_nonneg (fun x => hf0 _)
  have hinner (z : ComplexModel m) : ENNReal.ofReal (I z) = ∫⁻ x,
      ENNReal.ofReal (χ (fibreMapM n m z x) * F (fibreMapM n m z x)) ∂μ z :=
    ofReal_integral_eq_lintegral_ofReal (hinnerInt z) (Eventually.of_forall (fun x => hf0 _))
  refine ⟨?_, ?_⟩
  · have hm := ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      hI.aestronglyMeasurable.aemeasurable
    simpa only [Function.comp_def, hinner] using hm
  · rw [← ofReal_integral_eq_lintegral_ofReal hjoint (Eventually.of_forall hf0), hs.2,
      ENNReal.ofReal_div_of_pos (pow_pos Real.pi_pos m)]
    change ENNReal.ofReal (∫ z, I z) / ENNReal.ofReal (Real.pi ^ m) = _
    rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hI0)]
    congr 1
    exact lintegral_congr hinner

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment011

section CompactFibreCanonicalFragment012

/-! Actual positive NPP fibre slicing over an arbitrary-dimensional base.
The original joint and every-fibre measures are actual increasing truncation
limits. No finite limit-mass or disintegration premise is supplied. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.NPP.FibreSlicing

def originalFibrePotentialsM {n m : ℕ}
    (u : Fin n → ComplexModel (n + m) → EReal) (z : ComplexModel m) :
    Fin n → ComplexModel n → EReal := fun i x => u i (fibreMapM n m z x)

theorem plurisubharmonicOn_originalFibrePotentialsM {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (z : ComplexModel m) (i : Fin n) :
    PlurisubharmonicOn (originalFibrePotentialsM u z i) (fibreOpensM Ω z) := by
  have h := (hu i).comp_affine (inclFstC n m) (fibreMapM n m z 0)
  change PlurisubharmonicOn (fun x => u i (fibreMapM n m z x))
    ((fun x => fibreMapM n m z x) ⁻¹' (Ω : Set (ComplexModel (n + m))))
  simpa only [← fibreMapM_eq_add] using h

private theorem fibre_augmented_commonStrictLocus {n m : ℕ}
    (Ω : Opens (ComplexModel (n + m))) (u : Fin n → ComplexModel (n + m) → EReal)
    (z : ComplexModel m) (k : ℕ) :
    fibreMapM n m z ⁻¹' commonStrictLocus Ω (augmentedFibreTuple u) (k + 1) =
      commonStrictLocus (fibreOpensM Ω z) (originalFibrePotentialsM u z) (k + 1) := by
  rw [commonStrictLocus_augmentedFibreTuple Ω u (Nat.zero_lt_succ k)]
  rfl

/-- Original positive strict-level NPP Fubini; actual canonical measures and
the actual whole-base fibre PSH relations are produced internally. -/
theorem lintegral_original_np_level_eq_fibreM {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {χ : ComplexModel (n + m) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hχ0 : ∀ q, 0 ≤ χ q)
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ q, ‖G q‖ ≤ C) (hG0 : ∀ q, 0 ≤ G q) (k : ℕ) :
    AEMeasurable (fun z => ∫⁻ x,
      ENNReal.ofReal (χ (fibreMapM n m z x) * G (fibreMapM n m z x))
        ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpensM Ω z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z) (k + 1)) ∧
      (∫⁻ q, ENNReal.ofReal (χ q * G q)
        ∂MixedNonPluripolar.mixedTruncationMeasure Ω (augmentedFibreTuple u)
          (plurisubharmonicOn_augmentedFibreTuple hu) (k + 1)) =
        (∫⁻ z, ∫⁻ x, ENNReal.ofReal
          (χ (fibreMapM n m z x) * G (fibreMapM n m z x))
            ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpensM Ω z)
              (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z) (k + 1)) /
                ENNReal.ofReal (Real.pi ^ m) := by
  classical
  let S := commonStrictLocus Ω (augmentedFibreTuple u) (k + 1)
  let ν := canonicalMixedBedfordTaylorMeasure Ω
    (mixedTruncationReal (augmentedFibreTuple u) (k + 1))
      (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_augmentedFibreTuple hu) (k + 1))
  let μ := fun z => canonicalMixedBedfordTaylorMeasure (fibreOpensM Ω z)
    (mixedTruncationReal (originalFibrePotentialsM u z) (k + 1))
      (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_originalFibrePotentialsM hu z) (k + 1))
  have hS : MeasurableSet S := measurableSet_commonStrictLocus
    (plurisubharmonicOn_augmentedFibreTuple hu) (k + 1)
  have hν : IsBTLimit Ω (mixedTruncationReal (augmentedFibreTuple u) (k + 1)) ν :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Ω _ _)
  have hμ (z : ComplexModel m) : IsBTLimit (fibreOpensM Ω z)
      (fibreTupleM (mixedTruncationReal (augmentedFibreTuple u) (k + 1)) z) (μ z) := by
    have hμ0 : IsBTLimit (fibreOpensM Ω z)
        (mixedTruncationReal (originalFibrePotentialsM u z) (k + 1)) (μ z) :=
      IsLocalMixedBedfordTaylorMeasure.isBTLimit
        (canonicalMixedBedfordTaylorMeasure_spec (fibreOpensM Ω z) _ _)
    apply hμ0.congr
    intro i x _
    simp only [mixedTruncationReal, fibreTupleM, fibreRestrictM,
      augmentedFibreTuple, Fin.append_left]
    rfl
  have hbase (b : Fin m) : mixedTruncationReal (augmentedFibreTuple u) (k + 1)
      (Fin.natAdd n b) = baseNormSq n m b := by
    rw [mixedTruncationReal_augmentedFibreTuple]
    exact fullTuple_natAdd _ b
  have hF : Measurable (S.indicator G) := hG.indicator hS
  have hFbound (q : ComplexModel (n + m)) : ‖S.indicator G q‖ ≤ max C 0 := by
    by_cases hq : q ∈ S
    · simpa only [indicator_of_mem hq] using (hGb q).trans (le_max_left C 0)
    · simpa only [indicator_of_notMem hq, norm_zero] using le_max_right C 0
  have hF0 (q : ComplexModel (n + m)) : 0 ≤ S.indicator G q := by
    by_cases hq : q ∈ S <;> simp [hq, hG0 q]
  have hs := lintegral_mul_isBTLimit_eq_fibreM hbase hν hμ hχ hχc hχΩ hχ0 hF hFbound hF0
  have hj : (∫⁻ q, ENNReal.ofReal (χ q * G q)
      ∂MixedNonPluripolar.mixedTruncationMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu) (k + 1)) =
      ∫⁻ q, ENNReal.ofReal (χ q * S.indicator G q) ∂ν := by
    change (∫⁻ q, ENNReal.ofReal (χ q * G q) ∂ν.restrict S) = _
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro q
    by_cases hq : q ∈ S <;> simp [hq]
  have hf (z : ComplexModel m) : (∫⁻ x,
      ENNReal.ofReal (χ (fibreMapM n m z x) * G (fibreMapM n m z x))
        ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpensM Ω z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z) (k + 1)) =
      ∫⁻ x, ENNReal.ofReal
        (χ (fibreMapM n m z x) * S.indicator G (fibreMapM n m z x)) ∂μ z := by
    change (∫⁻ x, ENNReal.ofReal (χ (fibreMapM n m z x) * G (fibreMapM n m z x))
      ∂(μ z).restrict (commonStrictLocus (fibreOpensM Ω z) (originalFibrePotentialsM u z) (k + 1))) = _
    rw [← lintegral_indicator (measurableSet_commonStrictLocus
      (plurisubharmonicOn_originalFibrePotentialsM hu z) (k + 1))]
    apply lintegral_congr
    intro x
    have heq : x ∈ commonStrictLocus (fibreOpensM Ω z) (originalFibrePotentialsM u z) (k + 1) ↔
        fibreMapM n m z x ∈ S := by
      rw [← fibre_augmented_commonStrictLocus Ω u z k]
      rfl
    by_cases hx : fibreMapM n m z x ∈ S <;> simp [heq, hx]
  refine ⟨?_, ?_⟩
  · simpa only [hf] using hs.1
  · rw [hj]
    simpa only [hf] using hs.2

private theorem lintegral_npLimit_eq_iSup_shift {N : ℕ} {V : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → EReal} (hv : ∀ i, PlurisubharmonicOn (v i) V)
    {f : ComplexModel N → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂MixedNonPluripolar.mixedTruncationLimitMeasure V v hv) =
      ⨆ k, ∫⁻ x, f x ∂MixedNonPluripolar.mixedTruncationMeasure V v hv (k + 1) := by
  let μ := MixedNonPluripolar.mixedTruncationMeasure V v hv
  have hμ : Monotone μ := MixedNonPluripolar.mixedTruncationMeasure_mono hv
  change (∫⁻ x, f x ∂FirstPass.IncreasingMeasures.increasingLimit μ hμ) = _
  rw [← IncreasingMeasureIntegrals.increasingLimit_add μ hμ 1]
  exact IncreasingMeasureIntegrals.lintegral_increasingLimit (fun k => μ (k + 1))
    (fun _ _ hkl => hμ (Nat.add_le_add_right hkl 1)) hf

/-- Actual positive local NPP fibre Fubini for ALL base dimensions. Both joint
and every-fibre measures are the ORIGINAL canonical truncation limits, possibly
infinite. Their AE kernel and equality are conclusions, never supplied premises. -/
theorem lintegral_original_npLimit_eq_fibreM {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    {χ : ComplexModel (n + m) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hχ0 : ∀ q, 0 ≤ χ q)
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ q, ‖G q‖ ≤ C) (hG0 : ∀ q, 0 ≤ G q) :
    AEMeasurable (fun z => ∫⁻ x,
      ENNReal.ofReal (χ (fibreMapM n m z x) * G (fibreMapM n m z x))
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) ∧
      (∫⁻ q, ENNReal.ofReal (χ q * G q)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
          (plurisubharmonicOn_augmentedFibreTuple hu)) =
        (∫⁻ z, ∫⁻ x, ENNReal.ofReal
          (χ (fibreMapM n m z x) * G (fibreMapM n m z x))
            ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
              (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) /
                ENNReal.ofReal (Real.pi ^ m) := by
  let f := fun q => ENNReal.ofReal (χ q * G q)
  let I := fun k z => ∫⁻ x, f (fibreMapM n m z x)
    ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpensM Ω z)
      (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z) (k + 1)
  have hf : Measurable f := ENNReal.continuous_ofReal.measurable.comp (hχ.measurable.mul hG)
  have hlevel (k : ℕ) := lintegral_original_np_level_eq_fibreM hu hχ hχc hχΩ hχ0 hG hGb hG0 k
  have hIae (k : ℕ) : AEMeasurable (I k) := (hlevel k).1
  have hImono (z : ComplexModel m) : Monotone (fun k => I k z) := by
    intro k l hkl
    exact lintegral_mono'
      (MixedNonPluripolar.mixedTruncationMeasure_mono
        (plurisubharmonicOn_originalFibrePotentialsM hu z) (Nat.add_le_add_right hkl 1)) le_rfl
  have hfibre (z : ComplexModel m) : (∫⁻ x, f (fibreMapM n m z x)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
        (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) = ⨆ k, I k z :=
    lintegral_npLimit_eq_iSup_shift (plurisubharmonicOn_originalFibrePotentialsM hu z)
      (hf.comp (continuous_fibreMapM z).measurable)
  refine ⟨?_, ?_⟩
  · change AEMeasurable (fun z => ∫⁻ x, f (fibreMapM n m z x)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
        (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z))
    simpa only [hfibre] using AEMeasurable.iSup hIae
  · change (∫⁻ q, f q ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
      (plurisubharmonicOn_augmentedFibreTuple hu)) =
      (∫⁻ z, ∫⁻ x, f (fibreMapM n m z x)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) /
            ENNReal.ofReal (Real.pi ^ m)
    rw [lintegral_npLimit_eq_iSup_shift (plurisubharmonicOn_augmentedFibreTuple hu) hf]
    have hjlevel (k : ℕ) : (∫⁻ q, f q ∂MixedNonPluripolar.mixedTruncationMeasure Ω
        (augmentedFibreTuple u) (plurisubharmonicOn_augmentedFibreTuple hu) (k + 1)) =
        (∫⁻ z, I k z) / ENNReal.ofReal (Real.pi ^ m) := (hlevel k).2
    simp_rw [hjlevel]
    rw [← ENNReal.iSup_div, ← lintegral_iSup' hIae (Eventually.of_forall hImono)]
    simp_rw [hfibre]

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment012

section CompactFibreCanonicalFragment018

/-! Real local NPP Fubini with all needed integrability manufactured from
the original current. No finite fibre masses or integral conclusions are inputs. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

/-- Actual REAL local Fubini, with joint and outer integrability and actual
AE inner integrability, all produced from the original local current. -/
theorem integral_original_npLimit_eq_fibreM_nonneg {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hW : IsWellDefinedOn (Nat.add_comm m n) Ω u)
    {χ : ComplexModel (n + m) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hχ0 : ∀ q, 0 ≤ χ q)
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ q, ‖G q‖ ≤ C) (hG0 : ∀ q, 0 ≤ G q) :
    Integrable (fun q => χ q * G q)
      (MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu)) ∧
    (∀ᵐ z, Integrable (fun x => χ (fibreMapM n m z x) * G (fibreMapM n m z x))
      (MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
        (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z))) ∧
    Integrable (fun z => ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
        (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) ∧
    (∫ q, χ q * G q
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu)) =
      (∫ z, ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) /
            Real.pi ^ m := by
  let μ := MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
    (plurisubharmonicOn_augmentedFibreTuple hu)
  let ν := fun z => MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
    (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)
  let f := fun q => χ q * G q
  let I := fun z => ∫⁻ x, ENNReal.ofReal (f (fibreMapM n m z x)) ∂ν z
  have hf : Measurable f := hχ.measurable.mul hG
  have hf0 (q) : 0 ≤ f q := mul_nonneg (hχ0 q) (hG0 q)
  have hμfin : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤ := by
    intro K hK hKΩ
    dsimp only [μ]
    rw [← current_basePower_coefficient_eq_original_npLimit hu hW]
    exact positiveCoefficientMeasure_lt_top _ _ hK hKΩ
  have hχint : Integrable χ μ :=
    VaguePortmanteau.integrable_of_tsupport_subset hμfin hχ hχc hχΩ
  have hjoint : Integrable f μ :=
    hχint.mul_bdd hG.aestronglyMeasurable (Eventually.of_forall hGb)
  have hpos := lintegral_original_npLimit_eq_fibreM hu hχ hχc hχΩ hχ0 hG hGb hG0
  have hIae : AEMeasurable I := hpos.1
  have heq : (∫⁻ q, ENNReal.ofReal (f q) ∂μ) =
      (∫⁻ z, I z) / ENNReal.ofReal (Real.pi ^ m) := hpos.2
  have hJfin : (∫⁻ q, ENNReal.ofReal (f q) ∂μ) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hjoint (Eventually.of_forall hf0)]
    exact ENNReal.ofReal_lt_top
  have hden0 : ENNReal.ofReal (Real.pi ^ m) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos Real.pi_pos m)).ne'
  have hIfin : (∫⁻ z, I z) < ⊤ := by
    rw [← (ENNReal.eq_div_iff hden0 ENNReal.ofReal_ne_top).mp heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJfin
  have hIfinite : ∀ᵐ z, I z < ⊤ := ae_lt_top' hIae hIfin.ne
  have hreal (z : ComplexModel m) : (∫ x, f (fibreMapM n m z x) ∂ν z) = (I z).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => hf0 _)
      (hf.comp (continuous_fibreMapM z).measurable).aestronglyMeasurable
  refine ⟨hjoint, ?_, ?_, ?_⟩
  · filter_upwards [hIfinite] with z hz
    exact (lintegral_ofReal_ne_top_iff_integrable
      (hf.comp (continuous_fibreMapM z).measurable).aestronglyMeasurable
      (Eventually.of_forall fun _ => hf0 _)).mp hz.ne
  · change Integrable (fun z => ∫ x, f (fibreMapM n m z x) ∂ν z)
    simp_rw [hreal]
    exact integrable_toReal_of_lintegral_ne_top hIae hIfin.ne
  · change (∫ q, f q ∂μ) = (∫ z, ∫ x, f (fibreMapM n m z x) ∂ν z) / Real.pi ^ m
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable,
      heq, ENNReal.toReal_div, ENNReal.toReal_ofReal (pow_pos Real.pi_pos m).le]
    simp_rw [hreal]
    rw [integral_toReal hIae hIfinite]

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment018

section CompactFibreCanonicalFragment019

/-! Actual signed bounded multipliers in local NPP Fubini. Integrability
is produced by positive and negative parts, not supplied by a certificate. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

theorem integral_original_npLimit_eq_fibreM_signed_multiplier {n m : ℕ}
    {Ω : Opens (ComplexModel (n + m))} {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hW : IsWellDefinedOn (Nat.add_comm m n) Ω u)
    {χ : ComplexModel (n + m) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hχ0 : ∀ q, 0 ≤ χ q)
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ q, ‖G q‖ ≤ C) :
    Integrable (fun q => χ q * G q)
      (MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu)) ∧
    (∀ᵐ z, Integrable (fun x => χ (fibreMapM n m z x) * G (fibreMapM n m z x))
      (MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
        (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z))) ∧
    Integrable (fun z => ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
        (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) ∧
    (∫ q, χ q * G q
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu)) =
      (∫ z, ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) /
            Real.pi ^ m := by
  let μ := MixedNonPluripolar.mixedTruncationLimitMeasure Ω (augmentedFibreTuple u)
    (plurisubharmonicOn_augmentedFibreTuple hu)
  let ν := fun z => MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM Ω z)
    (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)
  let Gp := fun q => max (G q) 0
  let Gm := fun q => max (-G q) 0
  have hC : 0 ≤ C := (norm_nonneg (G 0)).trans (hGb 0)
  have hGp0 (q) : 0 ≤ Gp q := le_max_right _ _
  have hGm0 (q) : 0 ≤ Gm q := le_max_right _ _
  have hGpb (q) : ‖Gp q‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hGp0 q)]
    exact max_le ((le_abs_self _).trans (hGb q)) hC
  have hGmb (q) : ‖Gm q‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hGm0 q)]
    exact max_le ((neg_le_abs _).trans (hGb q)) hC
  have hdiff (q) : χ q * G q = χ q * Gp q - χ q * Gm q := by
    dsimp only [Gp, Gm]
    by_cases h : 0 ≤ G q
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      ring
  have hp := integral_original_npLimit_eq_fibreM_nonneg hu hW hχ hχc hχΩ hχ0
    (hG.max measurable_const) hGpb hGp0
  have hm := integral_original_npLimit_eq_fibreM_nonneg hu hW hχ hχc hχΩ hχ0
    (hG.neg.max measurable_const) hGmb hGm0
  let Ip := fun z => ∫ x, χ (fibreMapM n m z x) * Gp (fibreMapM n m z x) ∂ν z
  let Im := fun z => ∫ x, χ (fibreMapM n m z x) * Gm (fibreMapM n m z x) ∂ν z
  have hpe : (∫ q, χ q * Gp q ∂μ) = (∫ z, Ip z) / Real.pi ^ m := hp.2.2.2
  have hme : (∫ q, χ q * Gm q ∂μ) = (∫ z, Im z) / Real.pi ^ m := hm.2.2.2
  have hIp : Integrable Ip := hp.2.2.1
  have hIm : Integrable Im := hm.2.2.1
  have hinner : ∀ᵐ z, Integrable
      (fun x => χ (fibreMapM n m z x) * G (fibreMapM n m z x)) (ν z) := by
    filter_upwards [hp.2.1, hm.2.1] with z hzp hzm
    exact (hzp.sub hzm).congr (Eventually.of_forall fun x => (hdiff _).symm)
  have hread : (fun z => ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x) ∂ν z) =ᵐ[volume]
      (fun z => Ip z - Im z) := by
    filter_upwards [hp.2.1, hm.2.1] with z hzp hzm
    calc
      _ = ∫ x, χ (fibreMapM n m z x) * Gp (fibreMapM n m z x) -
          χ (fibreMapM n m z x) * Gm (fibreMapM n m z x) ∂ν z :=
        integral_congr_ae (Eventually.of_forall fun _ => hdiff _)
      _ = Ip z - Im z := integral_sub hzp hzm
  refine ⟨(hp.1.sub hm.1).congr (Eventually.of_forall fun q => (hdiff q).symm), hinner,
    (hp.2.2.1.sub hm.2.2.1).congr hread.symm, ?_⟩
  change (∫ q, χ q * G q ∂μ) =
    (∫ z, ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x) ∂ν z) / Real.pi ^ m
  calc
    _ = ∫ q, χ q * Gp q - χ q * Gm q ∂μ :=
      integral_congr_ae (Eventually.of_forall hdiff)
    _ = (∫ q, χ q * Gp q ∂μ) - (∫ q, χ q * Gm q ∂μ) := integral_sub hp.1 hm.1
    _ = (∫ z, Ip z - Im z) / Real.pi ^ m := by
      rw [hpe, hme, integral_sub hIp hIm]
      ring
    _ = _ := by rw [integral_congr_ae hread]

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment019

section CompactFibreCanonicalFragment020

/-! Literal smooth-base-form and Borel-weighted readings of the original
local non-pluripolar current. Neither form nor multiplier is assumed positive. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalCurrentLebesgue LocalBedfordTaylorForms
open LocalBedfordTaylorSmooth ConstantFormProducts StronglyPositiveForms
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

variable {n m : ℕ} {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}

/-- The full top tensor computation applies to EVERY original current. -/
theorem wedgeForm_pullbackSnd_apply_current
    (S : LocalProductCurrent (n + m) (prodOpens Q D) m)
    {η : ComplexModel m → RealForm m (2 * m)} (hη : ContDiffOn ℝ ∞ η D)
    (φ : 𝓓(prodOpens Q D, ℝ)) :
    wedgeForm (Nat.zero_add m) S (contDiffOn_pullbackSnd hη)
        (kahlerPower (n + m) 0) φ =
      S (basePowerSpan n m) (mulSmoothOnCLM (contDiffOn_topDensity_comp hη) φ) := by
  have hrep : ∀ q ∈ prodOpens Q D, (pullbackSnd η q : RealForm (n + m) (2 * m)) =
      ∑ j : Unit, (fun _ q => Real.pi ^ m *
        TopDegreeDensity.topDensity (η (ProductMixedMeasure.projSnd n m q))) j q •
          ((fun _ => basePowerSpan n m) j : RealForm (n + m) (2 * m)) := by
    intro q _
    simp only [Finset.univ_unique, Finset.sum_singleton, coe_pullbackSnd, pullbackSnd_eq]
    rfl
  rw [wedgeForm_apply_eq (Nat.zero_add m) _ _ (fun q _ => (pullbackSnd η q).2) _
    (fun _ => contDiffOn_topDensity_comp hη) _ hrep]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  congr 2
  apply Subtype.ext
  rw [coe_wedgeSpan_apply (Nat.zero_add m) _ _ (by omega)]
  change wedgeTo (by omega : 0 + 2 * m = 2 * m) (coordinateWedgeUnit : RealForm (n + m) 0)
    (basePower n m) = _
  rw [wedgeTo_unit_left _ rfl]
  rfl

/-- Exact original NPP-current pairing, for the SAME unbounded tuple, actual
signed original base tensor, and actual signed bounded Borel multiplier. -/
theorem original_current_pullbackSnd_apply_eq_npLimit
    {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) (prodOpens Q D))
    (hW : IsWellDefinedOn (Nat.add_comm m n) (prodOpens Q D) u)
    {η : ComplexModel m → RealForm m (2 * m)} (hη : ContDiffOn ℝ ∞ η D)
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G)
    (hGb : IsLocallyBoundedOn G (prodOpens Q D)) (φ : 𝓓(prodOpens Q D, ℝ)) :
    wedgeForm (Nat.zero_add m)
        (mulBorel (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
          (Nat.add_comm m n) (prodOpens Q D) u) G) (contDiffOn_pullbackSnd hη)
        (kahlerPower (n + m) 0) φ =
      ∫ q, φ q * (Real.pi ^ m *
        TopDegreeDensity.topDensity (η (ProductMixedMeasure.projSnd n m q))) * G q
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (prodOpens Q D)
          (augmentedFibreTuple u) (plurisubharmonicOn_augmentedFibreTuple hu) := by
  rw [wedgeForm_pullbackSnd_apply_current _ hη]
  rw [mulBorel_apply_eq_integral_positiveCoefficientMeasure
    (isPositive_nonPluripolarProduct (Nat.add_comm m n) hu hW)
    (basePowerSpan n m) basePowerSpan_mem_posCone hG hGb]
  rw [current_basePower_coefficient_eq_original_npLimit hu hW]
  rfl

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment020

section CompactFibreCanonicalFragment021

/-! Literal original local-current Fubini, with the exact smooth pulled-back
base tensor and an arbitrary signed bounded Borel multiplier. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalCurrentLebesgue LocalBedfordTaylorForms LocalBedfordTaylorSmooth
open StronglyPositiveForms TopDegreeDensity
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

theorem original_current_fibre_fubini_positive_base {n m : ℕ}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) (prodOpens Q D))
    (hW : IsWellDefinedOn (Nat.add_comm m n) (prodOpens Q D) u)
    {η : ComplexModel m → RealForm m (2 * m)} (hη : ContDiffOn ℝ ∞ η D)
    (hη0 : ∀ z ∈ D, η z ∈ spCone m)
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ q, ‖G q‖ ≤ C) (φ : 𝓓(prodOpens Q D, ℝ)) (hφ0 : ∀ q, 0 ≤ φ q) :
    Integrable (fun z => topDensity (η z) *
      ∫ x, φ (fibreMapM n m z x) * G (fibreMapM n m z x)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) ∧
    wedgeForm (Nat.zero_add m)
        (mulBorel (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
          (Nat.add_comm m n) (prodOpens Q D) u) G) (contDiffOn_pullbackSnd hη)
        (kahlerPower (n + m) 0) φ =
      ∫ z, topDensity (η z) *
        ∫ x, φ (fibreMapM n m z x) * G (fibreMapM n m z x)
          ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
            (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z) := by
  let χ := mulSmoothOnCLM (contDiffOn_topDensity_comp hη) φ
  let ν := fun z => MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
    (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)
  let F := fun z => topDensity (η z) *
    ∫ x, φ (fibreMapM n m z x) * G (fibreMapM n m z x) ∂ν z
  have hχ0 (q) : 0 ≤ χ q := by
    change 0 ≤ φ q * (Real.pi ^ m * topDensity (η (ProductMixedMeasure.projSnd n m q)))
    by_cases hq : φ q = 0
    · rw [hq, zero_mul]
    · have hqΩ : q ∈ prodOpens Q D := φ.tsupport_subset (subset_tsupport _ (Function.mem_support.mpr hq))
      exact mul_nonneg (hφ0 q)
        (mul_nonneg (pow_pos Real.pi_pos m).le (topDensity_nonneg_of_mem_spCone (hη0 _ hqΩ.2)))
  have hs := integral_original_npLimit_eq_fibreM_signed_multiplier hu hW χ.continuous
    χ.hasCompactSupport χ.tsupport_subset hχ0 hG hGb
  have hkernel (z : ComplexModel m) :
      (∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x) ∂ν z) = Real.pi ^ m * F z := by
    calc
      _ = ∫ x, (Real.pi ^ m * topDensity (η z)) *
          (φ (fibreMapM n m z x) * G (fibreMapM n m z x)) ∂ν z := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [χ, mulSmoothOnCLM_apply, projSnd_fibreMapM]
          ring
      _ = _ := by rw [integral_const_mul]; dsimp only [F]; ring
  have hπ : Real.pi ^ m ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hout : Integrable F := by
    have hstd : Integrable (fun z => ∫ x,
        χ (fibreMapM n m z x) * G (fibreMapM n m z x) ∂ν z) := hs.2.2.1
    have hscale : Integrable (fun z => Real.pi ^ m * F z) := by
      simpa only [hkernel] using hstd
    have hi := hscale.const_mul (Real.pi ^ m)⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hπ, one_mul] using hi
  refine ⟨hout, ?_⟩
  have hGbLocal : IsLocallyBoundedOn G (prodOpens Q D) :=
    fun _ _ _ => ⟨C, fun q _ => by simpa only [Real.norm_eq_abs] using hGb q⟩
  rw [original_current_pullbackSnd_apply_eq_npLimit hu hW hη hG hGbLocal]
  change (∫ q, χ q * G q
    ∂MixedNonPluripolar.mixedTruncationLimitMeasure (prodOpens Q D) (augmentedFibreTuple u)
      (plurisubharmonicOn_augmentedFibreTuple hu)) = ∫ z, F z
  have hseq : (∫ q, χ q * G q
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (prodOpens Q D) (augmentedFibreTuple u)
        (plurisubharmonicOn_augmentedFibreTuple hu)) =
      (∫ z, ∫ x, χ (fibreMapM n m z x) * G (fibreMapM n m z x) ∂ν z) / Real.pi ^ m := hs.2.2.2
  rw [hseq]
  simp_rw [hkernel]
  rw [integral_const_mul]
  exact mul_div_cancel_left₀ _ hπ

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment021

section CompactFibreCanonicalFragment022

/-! Real Fubini for the existing actual original smooth-wedge measure,
with joint and outer integrability produced internally. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalCurrentLebesgue LocalBedfordTaylorForms LocalBedfordTaylorSmooth
open StronglyPositiveForms TopDegreeDensity
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent

theorem original_wedgePowerMeasure_fibre_fubini {n m : ℕ}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {u : Fin n → ComplexModel (n + m) → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) (prodOpens Q D))
    (hW : IsWellDefinedOn (Nat.add_comm m n) (prodOpens Q D) u)
    {a : ComplexModel m → RealForm m 2} (ha : ContDiffOn ℝ ∞ a D)
    (hap : ∀ z ∈ D, IsSemipositiveOneOne (a z))
    {G : ComplexModel (n + m) → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ q, ‖G q‖ ≤ C) (φ : 𝓓(prodOpens Q D, ℝ)) (hφ0 : ∀ q, 0 ≤ φ q) :
    Integrable (fun q => φ q * G q)
      (wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
        (Nat.add_comm m n) (prodOpens Q D) u) (baseTwoFormPullback a)) ∧
    Integrable (fun z => topDensity (formPower (a z) m) *
      ∫ x, φ (fibreMapM n m z x) * G (fibreMapM n m z x)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
          (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z)) ∧
    (∫ q, φ q * G q ∂wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
        (Nat.add_comm m n) (prodOpens Q D) u) (baseTwoFormPullback a)) =
      ∫ z, topDensity (formPower (a z) m) *
        ∫ x, φ (fibreMapM n m z x) * G (fibreMapM n m z x)
          ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
            (originalFibrePotentialsM u z) (plurisubharmonicOn_originalFibrePotentialsM hu z) := by
  let μ := MixedNonPluripolar.mixedTruncationLimitMeasure (prodOpens Q D) (augmentedFibreTuple u)
    (plurisubharmonicOn_augmentedFibreTuple hu)
  let d := basePowerDensity Q D a
  let η := fun z => formPower (a z) m
  have hη : ContDiffOn ℝ ∞ η D := contDiffOn_formPower ha m
  let χ := mulSmoothOnCLM (contDiffOn_topDensity_comp hη) φ
  have hχ0 (q) : 0 ≤ χ q := by
    change 0 ≤ φ q * (Real.pi ^ m * topDensity (η (ProductMixedMeasure.projSnd n m q)))
    by_cases hq : φ q = 0
    · rw [hq, zero_mul]
    · have hqΩ : q ∈ prodOpens Q D :=
        φ.tsupport_subset (subset_tsupport _ (Function.mem_support.mpr hq))
      exact mul_nonneg (hφ0 q) (mul_nonneg (pow_pos Real.pi_pos m).le
        (topDensity_nonneg_of_mem_spCone (formPower_mem_spCone (hap _ hqΩ.2) m)))
  have hs := integral_original_npLimit_eq_fibreM_signed_multiplier hu hW χ.continuous
    χ.hasCompactSupport χ.tsupport_subset hχ0 hG hGb
  have hm : wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
      (Nat.add_comm m n) (prodOpens Q D) u) (baseTwoFormPullback a) =
      μ.withDensity (fun q => ENNReal.ofReal (d q)) :=
    original_np_wedgePowerMeasure_base_eq_npLimit hu hW ha hap
  have hd0 (q : ComplexModel (n + m)) : 0 ≤ d q := by
    by_cases hq : q ∈ prodOpens Q D
    · change 0 ≤ basePowerDensity Q D a q
      rw [basePowerDensity, indicator_of_mem hq]
      exact mul_nonneg (pow_pos Real.pi_pos m).le
        (topDensity_nonneg_of_mem_spCone (formPower_mem_spCone (hap _ hq.2) m))
    · change 0 ≤ basePowerDensity Q D a q
      rw [basePowerDensity, indicator_of_notMem hq]
  have hdm : Measurable (fun q => ENNReal.ofReal (d q)) :=
    ENNReal.measurable_ofReal.comp (measurable_basePowerDensity ha)
  have hdfin : ∀ᵐ q ∂μ, ENNReal.ofReal (d q) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweight : (fun q => (ENNReal.ofReal (d q)).toReal • (φ q * G q)) =ᵐ[μ]
      (fun q => χ q * G q) := by
    filter_upwards [ae_iff.mpr (MixedNonPluripolar.mixedTruncationLimitMeasure_compl
      (plurisubharmonicOn_augmentedFibreTuple hu))] with q hq
    rw [ENNReal.toReal_ofReal (hd0 q), smul_eq_mul]
    simp only [d, basePowerDensity, indicator_of_mem hq, χ, mulSmoothOnCLM_apply, η]
    ring
  have hlocal := original_current_fibre_fubini_positive_base hu hW hη
    (fun z hz => formPower_mem_spCone (hap z hz) m) hG hGb φ hφ0
  refine ⟨?_, hlocal.1, ?_⟩
  · rw [hm, integrable_withDensity_iff_integrable_smul' hdm hdfin]
    exact hs.1.congr hweight.symm
  · rw [hm, integral_withDensity_eq_integral_toReal_smul hdm hdfin,
      integral_congr_ae hweight]
    have hGbLocal : IsLocallyBoundedOn G (prodOpens Q D) :=
      fun _ _ _ => ⟨C, fun q _ => by simpa only [Real.norm_eq_abs] using hGb q⟩
    exact (original_current_pullbackSnd_apply_eq_npLimit hu hW hη hG hGbLocal φ).symm.trans hlocal.2

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment022

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.mainModule == `SGPT.NPP.CompactFibreLocalFubini do throwError "Wrong proper module identity: {env.mainModule}"
  let forbidden : Array Name := #[`OriginalCurrentProductDictionaryDraft, `AllDimensionCurrentProductDraft, `GlobalWedgeChartDictionaryDraft, `OriginalProductPotentialsDraft, `OriginalProductPartitionDraft, `PositiveCoefficientMeasureDraft, `FibreTruncationDictionaryDraft, `FibreTruncationMeasureDraft, `CurrentBasePowerMeasureDraft, `SmoothBaseWedgeMeasureDraft, `OriginalBaseFormDictionaryDraft, `PositiveFibreMRegularizationDraft, `NonPluripolarFibreMPositiveDraft, `FibreOriginalMeasureDictionaryDraft, `OriginalGlobalCurrentMeasureDraft, `OriginalFibreIntegralDraft, `BaseVolumeBorelDictionaryDraft, `OriginalOuterFibreIntegralDraft, `RealNonPluripolarFibreDraft, `SignedMultiplierFibreDraft, `LocalSignedCurrentDictionaryDraft, `OriginalLocalCurrentFubiniDraft, `OriginalWedgeMeasureFubiniDraft, `OriginalPartitionTermDraft, `OriginalCompactFubiniDraft, `SignedTopFormDictionaryDraft, `OriginalSignedCurrentDictionaryDraft, `OriginalSignedFubiniDraft, `OriginalCompactSlicingSourceDraft, `LiteralCompactSlicingContractDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m then throwError "Historical flat private provider leaked: {m}"
  logInfo m!"CANONICAL_COMPACT_FIBRE_PAYLOAD module={env.mainModule} proper_root=true old_flat_modules=0"
