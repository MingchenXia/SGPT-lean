import SGPT.NAPotential.DecreasingInfimum
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.PSH.SourceIEnvelopeSingularityContinuity

/-! # Continuity of the non-Archimedean volume along increasing nets

Source `prop:vol_NA_incnet_cont` of `chapter_NApotential.tex`: for an increasing net
`(Γ^i)_{i ∈ I}` in `PSH^NA(X, θ)` with `sup_i Γ^i_max < ∞`,
`vol (uscsup_i Γ^i) = lim_i vol Γ^i`.

The proof follows the book.  At a fixed Kähler form the masses converge along the increasing net
(`prop:supsincnetteestcur`, `cor:incnetdSconv`, `thm:contvolu`).  The interchange of the limit
in `i` with the infimum over Kähler forms defining `vol` uses a uniform estimate: by the
polynomial expansion of `∫ (α + N ω₀ + dd^c u)^n` in `N`, for `0 < N ≤ 1`,
`∫ (α + N ω₀ + dd^c u)^n - ∫ (α + dd^c u)^n ≤ N ∫ (α + ω₀ + dd^c u)^n`, and the last mass is
bounded by `∫ Ω^n` for a fixed semipositive `Ω`, uniformly in `u ≤ 0`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Every selector except the constant one has positive background degree. -/
theorem sourceNA_backgroundDegree_pos {g : Fin n → Option (Fin n)}
    (hg : g ∈ Fintype.piFinset (CanonicalBackgroundPolynomial.backgroundChoices (n := n)))
    (hne : g ≠ fun i => some i) : 1 ≤ CanonicalBackgroundPolynomial.backgroundDegree g := by
  classical
  by_contra h
  have h0 : (Finset.univ.filter fun j => g j = none).card = 0 := by
    change CanonicalBackgroundPolynomial.backgroundDegree g = 0
    omega
  apply hne
  funext i
  have hi := Fintype.mem_piFinset.mp hg i
  simp only [CanonicalBackgroundPolynomial.backgroundChoices, Finset.mem_insert,
    Finset.mem_singleton] at hi
  rcases hi with hi | hi
  · exfalso
    have hempty := Finset.card_eq_zero.mp h0
    have hmem : i ∈ (Finset.univ.filter fun j => g j = none) := by simp [hi]
    simp [hempty] at hmem
  · exact hi

/-- For `0 < N ≤ 1`: `∫ (α + N ω + dd^c u)^n - ∫ (α + dd^c u)^n ≤ N ∫ (α + ω + dd^c u)^n`. -/
theorem sourceNA_diagonalMass_add_smul_sub_le (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential α.val u)
    {N : ℝ} (hN0 : 0 < N) (hN1 : N ≤ 1)
    (huN : IsThetaPshPotential (α + N • omega.form).val u)
    (hu1 : IsThetaPshPotential (α + (1 : ℝ) • omega.form).val u) :
    (DiagonalMass.diagonalPotentialMass (α + N • omega.form) u huN).toReal -
        (DiagonalMass.diagonalPotentialMass α u hu).toReal ≤
      N * (DiagonalMass.diagonalPotentialMass (α + (1 : ℝ) • omega.form) u hu1).toReal := by
  classical
  let Θ : Fin n → ClosedRealOneOneForm n M := fun _ => α
  let U : Fin n → M → EReal := fun _ => u
  let c : (Fin n → Option (Fin n)) → ℝ := fun g =>
    (MixedMass.globalMixedMass (fun i => MixedMassBoundedDifference.optForm omega Θ (g i))
      (fun i => MixedMassBoundedDifference.optPot U (g i))
      (fun i => MixedMassBoundedDifference.optPot_psh omega (fun _ => hu) (g i))).toReal
  let S := Fintype.piFinset (CanonicalBackgroundPolynomial.backgroundChoices (n := n))
  let g₀ : Fin n → Option (Fin n) := fun i => some i
  have hpN : (DiagonalMass.diagonalPotentialMass (α + N • omega.form) u huN).toReal =
      ∑ g ∈ S, N ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g :=
    SingularPBackgroundMassPolynomial.globalMixedMass_add_background_toReal_eq_sum omega
      (θ := Θ) (u := U) (fun _ => hu) hN0
  have hp1 : (DiagonalMass.diagonalPotentialMass (α + (1 : ℝ) • omega.form) u hu1).toReal =
      ∑ g ∈ S, (1 : ℝ) ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g :=
    SingularPBackgroundMassPolynomial.globalMixedMass_add_background_toReal_eq_sum omega
      (θ := Θ) (u := U) (fun _ => hu) one_pos
  have hc0 : c g₀ = (DiagonalMass.diagonalPotentialMass α u hu).toReal := by
    simp [c, g₀, Θ, U, MixedMassBoundedDifference.optForm, MixedMassBoundedDifference.optPot,
      DiagonalMass.diagonalPotentialMass, DiagonalMass.diagonalPotentialMeasure,
      MixedMass.globalMixedMass]
  have hdeg0 : CanonicalBackgroundPolynomial.backgroundDegree g₀ = 0 := by
    simp [CanonicalBackgroundPolynomial.backgroundDegree, g₀]
  have hmem : g₀ ∈ S := by simp [S, g₀, CanonicalBackgroundPolynomial.backgroundChoices]
  have hcnn : ∀ g, 0 ≤ c g := fun g => ENNReal.toReal_nonneg
  have hsplit : ∑ g ∈ S, N ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g =
      c g₀ + ∑ g ∈ S.erase g₀, N ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g := by
    rw [← Finset.add_sum_erase S _ hmem]
    simp only [hdeg0, pow_zero, one_mul]
  have hsum1 : ∑ g ∈ S, (1 : ℝ) ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g =
      ∑ g ∈ S, c g := by
    simp only [one_pow, one_mul]
  have hbound : ∑ g ∈ S.erase g₀, N ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g ≤
      N * ∑ g ∈ S, c g := by
    rw [Finset.mul_sum]
    calc ∑ g ∈ S.erase g₀, N ^ CanonicalBackgroundPolynomial.backgroundDegree g * c g
        ≤ ∑ g ∈ S.erase g₀, N * c g := by
          apply Finset.sum_le_sum
          intro g hg
          have hdeg := sourceNA_backgroundDegree_pos (Finset.mem_of_mem_erase hg)
            (Finset.ne_of_mem_erase hg)
          exact mul_le_mul_of_nonneg_right (pow_le_of_le_one hN0.le hN1 (by omega)) (hcnn g)
      _ ≤ ∑ g ∈ S, N * c g :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun g _ _ => mul_nonneg hN0.le (hcnn g))
  rw [hpN, hp1, hsplit, hsum1]
  linarith

/-- The uniform bound: there is `K` with `∫ (α₀ + δ ω + ω + dd^c u)^n ≤ K` for every
`δ ∈ (0, 1]` and every `u ≤ 0` that is psh in that class. -/
theorem sourceNA_uniform_mass_bound (omega : KahlerBackground n M) (α₀ : ClosedRealOneOneForm n M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → ∀ {u : M → EReal}, u ≤ 0 →
      ∀ (hu1 : IsThetaPshPotential ((α₀ + δ • omega.form) + (1 : ℝ) • omega.form).val u),
        (DiagonalMass.diagonalPotentialMass ((α₀ + δ • omega.form) + (1 : ℝ) • omega.form) u
          hu1).toReal ≤ K := by
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega (fun _ : Unit => α₀)
  let Ω : ClosedRealOneOneForm n M := α₀ + (A + 2) • omega.form
  have hΩ : Ω.val.IsSemipositive := by
    have h1 := hsemi ()
    have h2 : ((2 : ℝ) • omega.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul omega.isSemipositive (by norm_num)
    have heq : Ω = (α₀ + A • omega.form) + (2 : ℝ) • omega.form := by
      simp only [Ω]
      module
    rw [heq]
    intro e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
      add_nonneg (h1 e z hz v) (h2 e z hz v)
  have h0 : IsThetaPshPotential Ω.val (fun _ => 0) :=
    (LocalPotentials.isThetaPshPotential_zero_iff Ω).mpr hΩ
  refine ⟨(DiagonalMass.diagonalPotentialMass Ω (fun _ => 0) h0).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro δ hδ0 hδ1 u hu0 hu1
  have hc : 0 < A + 1 - δ := by linarith
  have hheq : ((α₀ + δ • omega.form) + (1 : ℝ) • omega.form) + (A + 1 - δ) • omega.form = Ω := by
    simp only [Ω]
    module
  have hu' := LocalPotentials.isThetaPshPotential_add_of_semipositive hu1
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hc.le)
  have huΩ : IsThetaPshPotential Ω.val u := hheq ▸ hu'
  have hle1 := AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
    omega.isSemipositive hc hu1 hu'
  have heq1 := sourceNA_diagonalMass_congr_form hheq hu' huΩ
  have hle2 : DiagonalMass.diagonalPotentialMass Ω u huΩ ≤
      DiagonalMass.diagonalPotentialMass Ω (fun _ => 0) h0 :=
    GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
      (θ := fun _ : Fin n => Ω) (u := fun _ => u) (v := fun _ => fun _ => 0)
      (fun _ => huΩ) (fun _ => h0)
      (fun _ => ⟨0, fun x _ => by simpa using hu0 x⟩)
  have hfin : DiagonalMass.diagonalPotentialMass Ω (fun _ => 0) h0 ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => h0.1)).ne
  exact ENNReal.toReal_mono hfin ((hle1.trans heq1.le).trans hle2)

variable [ConnectedSpace M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Uniform comparison of the masses at `δ ω₀` and `δ' ω₀`, `0 < δ' < δ ≤ 1`. -/
theorem sourceNAComponentMass_smul_le (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → ∀ {u : M → EReal}, u ≤ 0 →
      ∀ (hu1 : IsThetaPshPotential
        ((atlasClosedFormToNative θ + δ • omega.form) + (1 : ℝ) • omega.form).val u),
        (DiagonalMass.diagonalPotentialMass
          ((atlasClosedFormToNative θ + δ • omega.form) + (1 : ℝ) • omega.form) u hu1).toReal ≤ K)
    {δ δ' : ℝ} (hδ' : 0 < δ') (hδδ' : δ' < δ) (hδ : δ ≤ 1) :
    (sourceNAComponentMass Γ
        (sourceKahlerFormOfBackground (KahlerBackground.smul (hδ'.trans hδδ') omega))).toReal ≤
      (sourceNAComponentMass Γ
        (sourceKahlerFormOfBackground (KahlerBackground.smul hδ' omega))).toReal + δ * K := by
  let ωδ := KahlerBackground.smul (hδ'.trans hδδ') omega
  let ωδ' := KahlerBackground.smul hδ' omega
  have hN0 : 0 < δ - δ' := by linarith
  have hN1 : δ - δ' ≤ 1 := by linarith
  have hdiff : (ωδ.form - ωδ'.form).val.IsSemipositive := by
    have h : ωδ.form - ωδ'.form = (δ - δ') • omega.form := by
      simp only [ωδ, ωδ', KahlerBackground.smul_form]
      module
    rw [h]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive hN0.le
  have hαβ : (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ωδ θ) -
      atlasClosedFormToNative (sourceTestCurveEnlargedBackground ωδ' θ)).val.IsSemipositive := by
    rw [sourceTestCurveEnlargedBackground_native, sourceTestCurveEnlargedBackground_native]
    have h : (atlasClosedFormToNative θ + ωδ.form) - (atlasClosedFormToNative θ + ωδ'.form) =
        ωδ.form - ωδ'.form := by abel
    rw [h]
    exact hdiff
  let R := Γ.realizedComponent ωδ'
  let L := sourceTestCurveLimit R.val.toSourceTestCurvePredata
  have hi : sourceIModel (sourceTestCurveEnlargedBackground ωδ' θ) L :=
    R.val.limit_iModel ωδ' ((sourceIModelTestCurvesPositive_iff_slices ωδ' _).mp R.property)
  have hm := (sourceIModel_transition_envelope_and_mass ωδ hαβ hi R.val.positiveLimitMass).2
  have hL := Γ.realizedComponent_limit_transition hdiff
  have hmassδ : sourceNAComponentMass Γ (sourceKahlerFormOfBackground ωδ) =
      sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ωδ θ) L
        (sourceThetaPSH_of_semipositive_difference hαβ hi.1) univ := by
    rw [sourceNAComponentMass_realized]
    exact (sourcePotentialMass_congr hL _ _).trans hm
  have hmassδ' : sourceNAComponentMass Γ (sourceKahlerFormOfBackground ωδ') =
      sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ωδ' θ) L hi.1 univ :=
    sourceNAComponentMass_realized Γ ωδ'
  have hnat := (isThetaPSH_iff_nativeThetaPotential _ _).mp hi.1
  have hfα : atlasClosedFormToNative (sourceTestCurveEnlargedBackground ωδ' θ) =
      atlasClosedFormToNative θ + δ' • omega.form := by
    rw [sourceTestCurveEnlargedBackground_native]
    rfl
  have hfβ : atlasClosedFormToNative (sourceTestCurveEnlargedBackground ωδ θ) =
      (atlasClosedFormToNative θ + δ' • omega.form) + (δ - δ') • omega.form := by
    rw [sourceTestCurveEnlargedBackground_native]
    simp only [ωδ, KahlerBackground.smul_form]
    module
  have hα : IsThetaPshPotential (atlasClosedFormToNative θ + δ' • omega.form).val L := hfα ▸ hnat
  have hαN := LocalPotentials.isThetaPshPotential_add_of_semipositive hα
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hN0.le)
  have hα1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hα
    (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  have hC := sourceNA_diagonalMass_add_smul_sub_le omega hα hN0 hN1 hαN hα1
  have hbound := hK hδ' ((hδδ'.le).trans hδ)
    (SourceTestCurvePredata.limit_le_zero R.val.toSourceTestCurvePredata) hα1
  have e1 : (sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ωδ θ) L
      (sourceThetaPSH_of_semipositive_difference hαβ hi.1) univ) =
      DiagonalMass.diagonalPotentialMass
        ((atlasClosedFormToNative θ + δ' • omega.form) + (δ - δ') • omega.form) L hαN :=
    sourceNA_diagonalMass_congr_form hfβ _ _
  have e2 : (sourcePotentialNonPluripolarMeasure (sourceTestCurveEnlargedBackground ωδ' θ) L
      hi.1 univ) = DiagonalMass.diagonalPotentialMass
        (atlasClosedFormToNative θ + δ' • omega.form) L hα :=
    sourceNA_diagonalMass_congr_form hfα _ _
  change (sourceNAComponentMass Γ (sourceKahlerFormOfBackground ωδ)).toReal ≤
    (sourceNAComponentMass Γ (sourceKahlerFormOfBackground ωδ')).toReal + δ * K
  rw [hmassδ, hmassδ', e1, e2]
  have hNK : (δ - δ') * K ≤ δ * K := mul_le_mul_of_nonneg_right (by linarith) hK0
  have h3 := mul_le_mul_of_nonneg_left hbound hN0.le
  linarith

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Some multiple `δ' ω₀` with `0 < δ' < δ` lies below any given Kähler form. -/
theorem sourceKahlerForm_exists_smul_le (omega : KahlerBackground n M) (κ : SourceKahlerForm n M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (δ' : ℝ) (hδ' : 0 < δ'), δ' < δ ∧
      sourceKahlerFormLE (sourceKahlerFormOfBackground (KahlerBackground.smul hδ' omega)) κ := by
  let ρ := sourceKahlerFormRepresentative κ
  obtain ⟨A, hA, hs⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul ρ (fun _ : Unit => -omega.form)
  let δ' := min (δ / 2) (1 / A)
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by positivity)
  have hδ'lt : δ' < δ := (min_le_left _ _).trans_lt (by linarith)
  have hδ'A : δ' ≤ 1 / A := min_le_right _ _
  refine ⟨δ', hδ'pos, hδ'lt, ?_⟩
  have hsemi : (ρ.form - (KahlerBackground.smul hδ'pos omega).form).val.IsSemipositive := by
    have h : ρ.form - (KahlerBackground.smul hδ'pos omega).form =
        (1 / A) • (-omega.form + A • ρ.form) + (1 / A - δ') • omega.form := by
      simp only [KahlerBackground.smul_form]
      rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ hA.ne', one_smul]
      module
    rw [h]
    have h1 := KahlerDomination.isSemipositive_smul (hs ()) (by positivity : (0 : ℝ) ≤ 1 / A)
    have h2 := KahlerDomination.isSemipositive_smul omega.isSemipositive
      (by linarith : (0 : ℝ) ≤ 1 / A - δ')
    intro e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
      add_nonneg (h1 e z hz v) (h2 e z hz v)
  have h := (sourceKahlerFormLE_ofBackground_iff (KahlerBackground.smul hδ'pos omega) ρ).mpr hsemi
  simpa only [ρ, sourceKahlerFormRepresentative_class] using h

/-- The mass at `δ ω₀` exceeds the volume by at most `δ K`. -/
theorem sourceNAComponentMass_smul_le_volume (omega : KahlerBackground n M) (Γ : SourceNAPotential θ)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → ∀ {u : M → EReal}, u ≤ 0 →
      ∀ (hu1 : IsThetaPshPotential
        ((atlasClosedFormToNative θ + δ • omega.form) + (1 : ℝ) • omega.form).val u),
        (DiagonalMass.diagonalPotentialMass
          ((atlasClosedFormToNative θ + δ • omega.form) + (1 : ℝ) • omega.form) u hu1).toReal ≤ K)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    sourceNAComponentMass Γ (sourceKahlerFormOfBackground (KahlerBackground.smul hδ omega)) ≤
      sourceNAVolume Γ + ENNReal.ofReal (δ * K) := by
  rw [sourceNAVolume, ENNReal.iInf_add]
  apply le_iInf
  intro κ
  obtain ⟨δ', hδ', hlt, hle⟩ := sourceKahlerForm_exists_smul_le omega κ hδ
  have hE := sourceNAComponentMass_smul_le omega Γ hK0 hK hδ' hlt hδ1
  have hmono := sourceNAComponentMass_mono Γ hle
  have hfin := sourceNAComponentMass_lt_top omega Γ
    (sourceKahlerFormOfBackground (KahlerBackground.smul (hδ'.trans hlt) omega))
  have hfin' := sourceNAComponentMass_lt_top omega Γ
    (sourceKahlerFormOfBackground (KahlerBackground.smul hδ' omega))
  calc sourceNAComponentMass Γ (sourceKahlerFormOfBackground (KahlerBackground.smul hδ omega))
      = ENNReal.ofReal (sourceNAComponentMass Γ
          (sourceKahlerFormOfBackground (KahlerBackground.smul (hδ'.trans hlt) omega))).toReal :=
        (ENNReal.ofReal_toReal hfin.ne).symm
    _ ≤ ENNReal.ofReal ((sourceNAComponentMass Γ
          (sourceKahlerFormOfBackground (KahlerBackground.smul hδ' omega))).toReal + δ * K) :=
        ENNReal.ofReal_le_ofReal hE
    _ = sourceNAComponentMass Γ (sourceKahlerFormOfBackground (KahlerBackground.smul hδ' omega)) +
          ENNReal.ofReal (δ * K) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hδ.le hK0),
          ENNReal.ofReal_toReal hfin'.ne]
    _ ≤ sourceNAComponentMass Γ κ + ENNReal.ofReal (δ * K) := by gcongr

/-- At a fixed Kähler index the component masses of the usc supremum of an increasing net are
the supremum of the component masses (`prop:supsincnetteestcur`, `thm:contvolu`). -/
theorem sourceNAComponentMass_uscSup_le {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (hm : ∀ i j, i ≤ j → SourceNAPOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) (κ : SourceKahlerForm n M) :
    sourceNAComponentMass (SourceNAPotential.uscSup omega Γ hb) κ ≤
      ⨆ i, sourceNAComponentMass (Γ i) κ := by
  let ρ := sourceKahlerFormRepresentative κ
  let F : I → SourceTestCurve (sourceNAComponentBackground θ κ) := fun i => ((Γ i).component κ).val
  have hmF : ∀ i j, i ≤ j → SourceTestCurvePOrder (F i) (F j) :=
    fun i j hij => (sourceNAPOrder_iff_component (Γ i) (Γ j) κ).mp (hm i j hij)
  have hbκ := sourceNAFamily_component_bddAbove omega Γ hb κ
  have hcomp : ((SourceNAPotential.uscSup omega Γ hb).component κ).val =
      SourceTestCurve.increasingSup ρ F hmF hbκ :=
    SourceTestCurve.generalSup_eq_increasing_of_monotone ρ F hmF hbκ
  have hlimit : sourceTestCurveLimit
      ((SourceNAPotential.uscSup omega Γ hb).component κ).val.toSourceTestCurvePredata =
      uscRegularization (⨆ i, sourceTestCurveLimit (F i).toSourceTestCurvePredata) := by
    rw [hcomp]
    exact SourceTestCurve.increasingSup_limit ρ F hmF hbκ
  let i₀ : I := Classical.arbitrary I
  have hbig := sourcePositiveMass_isBig ρ (F i₀).limit_thetaPSH (F i₀).positiveLimitMass
  let w : I → SourceThetaPotentialL1 (sourceNAComponentBackground θ κ) :=
    fun i => ⟨sourceTestCurveLimit (F i).toSourceTestCurvePredata, (F i).limit_thetaPSH⟩
  have hmono : Monotone fun i => (w i).val :=
    fun i j hij => SourceTestCurvePOrder.limit_le ρ (hmF i j hij)
  have hC : ∀ i x, (w i).val x ≤ ((0 : ℝ) : EReal) := fun i x => by
    simpa using SourceTestCurvePredata.limit_le_zero (F i).toSourceTestCurvePredata x
  have hlim := tendsto_sourceSingularityTopology_of_monotone ρ _ hbig w hmono hC
  have hval : (sourceIncreasingSingularitySupremum (sourceNAComponentBackground θ κ) w hC).val =
      sourceTestCurveLimit
        ((SourceNAPotential.uscSup omega Γ hb).component κ).val.toSourceTestCurvePredata := by
    rw [sourceIncreasingSingularitySupremum_val, hlimit]
  have hpos : 0 < sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ)
      (sourceIncreasingSingularitySupremum (sourceNAComponentBackground θ κ) w hC).val
      (sourceIncreasingSingularitySupremum (sourceNAComponentBackground θ κ) w hC).property univ :=
    ((SourceNAPotential.uscSup omega Γ hb).component κ).val.positiveLimitMass.trans_eq
      (sourcePotentialMass_congr hval.symm _ _)
  have ht := (tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology ρ _ hbig atTop w _
    hpos hlim).2
  have hle := le_of_tendsto' ht (fun i => le_iSup
    (fun j => sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ) (w j).val
      (w j).property univ) i)
  exact (sourcePotentialMass_congr hval _ _).symm.trans_le hle

/-- Source `prop:vol_NA_incnet_cont`: for an increasing net in `PSH^NA(X, θ)` with bounded
cutoffs, `vol (uscsup_i Γ^i) = lim_i vol Γ^i = sup_i vol Γ^i`. -/
theorem sourceNAVolume_uscSup_of_monotone {I : Type*} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (hm : ∀ i j, i ≤ j → SourceNAPOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    sourceNAVolume (SourceNAPotential.uscSup omega Γ hb) = ⨆ i, sourceNAVolume (Γ i) ∧
      Tendsto (fun i => sourceNAVolume (Γ i)) atTop
        (𝓝 (sourceNAVolume (SourceNAPotential.uscSup omega Γ hb))) := by
  obtain ⟨K, hK0, hK⟩ := sourceNA_uniform_mass_bound omega (atlasClosedFormToNative θ)
  have heq : sourceNAVolume (SourceNAPotential.uscSup omega Γ hb) = ⨆ i, sourceNAVolume (Γ i) := by
    apply le_antisymm
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      let δ : ℝ := min 1 ((ε : ℝ) / (K + 1))
      have hδ : 0 < δ := lt_min one_pos (div_pos (by exact_mod_cast hε) (by linarith))
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδK : δ * K ≤ ε := by
        have h1 : δ ≤ (ε : ℝ) / (K + 1) := min_le_right _ _
        have h2 : δ * K ≤ (ε : ℝ) / (K + 1) * K := mul_le_mul_of_nonneg_right h1 hK0
        have h3 : (ε : ℝ) / (K + 1) * K ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [(by exact_mod_cast hε.le : (0 : ℝ) ≤ ε)]
        exact h2.trans h3
      let κ := sourceKahlerFormOfBackground (KahlerBackground.smul hδ omega)
      calc sourceNAVolume (SourceNAPotential.uscSup omega Γ hb)
          ≤ sourceNAComponentMass (SourceNAPotential.uscSup omega Γ hb) κ :=
            sourceNAVolume_le_component _ κ
        _ ≤ ⨆ i, sourceNAComponentMass (Γ i) κ :=
            sourceNAComponentMass_uscSup_le omega Γ hm hb κ
        _ ≤ ⨆ i, (sourceNAVolume (Γ i) + ENNReal.ofReal (δ * K)) :=
            iSup_mono fun i => sourceNAComponentMass_smul_le_volume omega (Γ i) hK0 hK hδ hδ1
        _ = (⨆ i, sourceNAVolume (Γ i)) + ENNReal.ofReal (δ * K) := (ENNReal.iSup_add _).symm
        _ ≤ (⨆ i, sourceNAVolume (Γ i)) + ε := by
            gcongr
            calc ENNReal.ofReal (δ * K) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hδK
              _ = ε := ENNReal.ofReal_coe_nnreal
    · exact iSup_le fun i => sourceNAVolume_mono omega (SourceNAPotential.le_uscSup omega Γ hb i)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact tendsto_atTop_iSup fun i j hij => sourceNAVolume_mono omega (hm i j hij)

end SGPT.PSH.VariableComplexAtlas
