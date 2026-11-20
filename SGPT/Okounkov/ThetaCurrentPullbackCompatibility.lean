import SGPT.Okounkov.FlagCurrentPullbackFirst
import SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.Pending.LocalSmoothFormDensityGluing

set_option autoImplicit false
universe u
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ComplexOrder MatrixOrder

namespace SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame
open LocalCurrentDensityMatrix TopDegreeDensity LocalBedfordTaylorCollar
open ActualQuasiPshPotentialSmoothCompatibility NaturalThetaPshGeometricCurrent LelongPoincareDivisor
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- Zero actual Levi diagonals determine the whole original smooth two-form. -/
theorem smoothDDC_eq_zero_of_levi_zero {n : ℕ} {h : ComplexModel n → ℝ}
    {z : ComplexModel n} (hh : ContDiffAt ℝ 2 h z)
    (hzero : ∀ v : ComplexModel n, leviForm h z v = 0) :
    smoothDDC h z = 0 := by
  let A := smoothDDC h z
  have hA : FirstPass.IsOneOne A := smoothDDC_isOneOne hh
  have hdiag (v : ComplexModel n) : A ![v, Complex.I • v] = 0 := by
    rw [show A = smoothDDC h z from rfl, smoothDDC_complexDiagonal_eq_leviForm hh,
      hzero v, zero_div]
  have hpos : StronglyPositiveForms.IsSemipositiveOneOne A :=
    ⟨hA, fun v => (hdiag v).ge⟩
  have hneg : StronglyPositiveForms.IsSemipositiveOneOne (-A) := by
    refine ⟨?_, ?_⟩
    · intro v w
      simp only [ContinuousAlternatingMap.neg_apply, hA v w]
    · intro v
      simp only [ContinuousAlternatingMap.neg_apply, hdiag v, neg_zero, le_refl]
  have hp := normalizedHermitianMatrix_posSemidef hpos
  have hn := normalizedHermitianMatrix_posSemidef hneg
  have hmat : normalizedHermitianMatrix (-A) = -normalizedHermitianMatrix A := by
    change normalizedHermitianMatrixₗ (-A) = -normalizedHermitianMatrixₗ A
    exact map_neg normalizedHermitianMatrixₗ A
  rw [hmat] at hn
  apply eq_zero_of_normalizedHermitianMatrix_eq_zero hA
  have hlo : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ normalizedHermitianMatrix A := by
    rw [Matrix.le_iff, sub_zero]
    exact hp
  have hhi : normalizedHermitianMatrix A ≤ 0 := by
    rw [Matrix.le_iff, zero_sub]
    exact hn
  exact le_antisymm hhi hlo

/-- The actual finite local density fields, supplied by the prescribed reader,
transport a pointwise smooth difference to equality of the full native ddC. -/
theorem ddC_regularLocalQuasiPsh_eq_of_smooth_zero_difference
    {n : ℕ} {Ω : Opens (ComplexModel n)} {a b : ComplexModel n → EReal}
    (ha : LocalQuasiPshPotentialOn a Ω) (hb : LocalQuasiPshPotentialOn b Ω)
    (haL : LocallyIntegrableOn (fun z => (a z).toReal) Ω volume)
    (hbL : LocallyIntegrableOn (fun z => (b z).toReal) Ω volume)
    (hbfin : ∀ᵐ z ∂volume.restrict Ω, b z ≠ ⊤ ∧ b z ≠ ⊥)
    {h : ComplexModel n → ℝ} (hh : ContDiffOn ℝ ∞ h Ω)
    (hdiff : EqOn a (fun z => b z + (h z : EReal)) Ω)
    (hzero : ∀ z ∈ Ω, smoothDDC h z = 0) :
    ddC (regularLocalQuasiPsh ha) = ddC (regularLocalQuasiPsh hb) := by
  have hhL : LocallyIntegrableOn h Ω volume :=
    hh.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hreal : (fun z => (a z).toReal) =ᵐ[volume.restrict Ω]
      (fun z => (b z).toReal + h z) := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet, hbfin] with z hz hzb
    rw [hdiff hz, EReal.toReal_add hzb.1 hzb.2 (EReal.coe_ne_top _)
      (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hdist : regularLocalQuasiPsh ha = regularLocalQuasiPsh hb +
      regularDistribution volume h hhL := by
    change regularDistribution volume (fun z => (a z).toReal) haL =
      regularDistribution volume (fun z => (b z).toReal) hbL + _
    rw [regularDistribution_congr_ae_on _ (hbL.add hhL) hreal]
    exact LelongPoincareDivisor.regularDistribution_add' hbL hhL (hbL.add hhL)
  have hdh : ddC (regularDistribution volume h hhL) = 0 := by
    ext v φ
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, LelongPoincareDivisor.ddC_regularDistribution_apply_of_contDiffOn hh]
    change (∫ z, φ z * smoothDDC h z ![v 0, v 1]) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [] with z
    by_cases hz : z ∈ Ω
    · rw [hzero z hz]
      simp
    · rw [image_eq_zero_of_notMem_tsupport (fun hzS => hz (φ.tsupport_subset hzS))]
      simp
  rw [hdist, ← ddCLM_apply, map_add]
  simp only [ddCLM_apply, hdh, add_zero]

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem corrected_chart_localQuasiPsh
    {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {e : ComplexChart (m + 1) M}
    {A : Opens (ComplexModel (m + 1))} {ρ : ComplexModel (m + 1) → ℝ}
    (hA : A ≤ chartTarget e)
    (hp : PlurisubharmonicOn (fun x => chartFunction u e x + (ρ x : EReal)) A) :
    LocalQuasiPshPotentialOn (fun x => chartFunction u e x + (ρ x : EReal)) A := by
  refine ⟨A.isOpen, fun x hx => (hp x hx).quasiPlurisubharmonicAt, ?_⟩
  intro x hx B hB hxB
  obtain ⟨y, hy, hyfin⟩ := hu.2.exists_chart_ne_bot e (A.isOpen.inter hB)
    (fun y hy => hA hy.1) ⟨hx, hxB⟩
  exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hyfin, EReal.coe_ne_bot _⟩⟩

/-- The actual SAME chart correction retains the smooth pointwise difference
and its full zero ddC, without projecting away the pluriharmonic data. -/
theorem exists_corrected_theta_current_pluriharmonic_difference
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (heq : thetaPotentialCurrent θ.val u hu = thetaPotentialCurrent σ.val v hv)
    (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target) :
    ∃ (W : Opens (ComplexModel (m + 1))) (ρ κ h : ComplexModel (m + 1) → ℝ),
      z ∈ W ∧ IsSmoothLocalPotential θ.val e W ρ ∧
      IsSmoothLocalPotential σ.val e W κ ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      EqOn (fun x => chartFunction u e x + (ρ x : EReal))
        (fun x => (chartFunction v e x + (κ x : EReal)) + (h x : EReal)) W ∧
      ∀ x ∈ W, smoothDDC h x = 0 := by
  obtain ⟨S, ρ, hzS, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
  obtain ⟨P, κ, hzP, hκ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials σ e z hz
  let U : Opens (ComplexModel (m + 1)) := ⟨S ∩ P, hρ.1.inter hκ.1⟩
  have hρU : IsSmoothLocalPotential θ.val e U ρ :=
    ⟨U.isOpen, fun _ hx => hρ.2.1 hx.1, hρ.2.2.1.mono inter_subset_left,
      fun x hx => hρ.2.2.2 hx.1⟩
  have hκU : IsSmoothLocalPotential σ.val e U κ :=
    ⟨U.isOpen, fun _ hx => hκ.2.1 hx.2, hκ.2.2.1.mono inter_subset_right,
      fun x hx => hκ.2.2.2 hx.2⟩
  let F : ComplexModel (m + 1) → EReal := fun x => chartFunction u e x + (ρ x : EReal)
  let G : ComplexModel (m + 1) → EReal := fun x => chartFunction v e x + (κ x : EReal)
  obtain ⟨hFp, _hFfin, _hLF, hFc, _hFs, _hFpos⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader θ.val hu e ρ hρU
  obtain ⟨hGp, _hGfin, _hLG, hGc, _hGs, _hGpos⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader σ.val hv e κ hκU
  let hF : LocalQuasiPshPotentialOn F U := corrected_chart_localQuasiPsh hu hρU.2.1 hFp
  let hG : LocalQuasiPshPotentialOn G U := corrected_chart_localQuasiPsh hv hκU.2.1 hGp
  have hddc : ddC (regularLocalQuasiPsh hF) = ddC (regularLocalQuasiPsh hG) := by
    have ht := congrArg (fun T => restrictForm (T.coefficients (canonicalBasis (m + 1)) e)
      hρU.2.1) heq
    exact hFc.symm.trans (ht.trans hGc)
  obtain ⟨W, hWU, h, hzW, hh, _hhL, hdiff, _hreg, hlevi⟩ :=
    exists_smooth_original_difference_of_equal_native_ddc hF hG hddc z ⟨hzS, hzP⟩
  refine ⟨W, ρ, κ, h, hzW, ?_, ?_, hh, hdiff, ?_⟩
  · exact ⟨W.isOpen, fun _ hx => hρU.2.1 (hWU hx),
      hρU.2.2.1.mono hWU, fun x hx => hρU.2.2.2 (hWU hx)⟩
  · exact ⟨W.isOpen, fun _ hx => hκU.2.1 (hWU hx),
      hκU.2.2.1.mono hWU, fun x hx => hκU.2.2.2 (hWU hx)⟩
  · intro x hx
    exact smoothDDC_eq_zero_of_levi_zero
      (hh.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hlevi x hx)

variable {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Pointwise pluriharmonic corrected germs compose through the actual coordinate
map, so all original upstairs coefficients agree, including exceptional support. -/
theorem thetaPotentialCurrent_modification_pullback_eq_of_eq
    {π : Y → M} (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification π)
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (heq : thetaPotentialCurrent θ.val u hu = thetaPotentialCurrent σ.val v hv) :
    thetaPotentialCurrent (ClosedRealOneOneForm.pullback hπ.1 θ).val (u ∘ π)
      (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        hπ θ hu) =
    thetaPotentialCurrent (ClosedRealOneOneForm.pullback hπ.1 σ).val (v ∘ π)
      (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        hπ σ hv) := by
  let hup := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ θ hu
  let hvp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ σ hv
  let T := thetaPotentialCurrent (ClosedRealOneOneForm.pullback hπ.1 θ).val (u ∘ π) hup
  let S := thetaPotentialCurrent (ClosedRealOneOneForm.pullback hπ.1 σ).val (v ∘ π) hvp
  change T = S
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  ext w φ
  have hd : (T.coefficients (canonicalBasis (m + 1)) e) w =
      (S.coefficients (canonicalBasis (m + 1)) e) w := by
    apply LocalSmoothFormDensityGluing.eq_of_restrict_eq_locally
    intro z hz
    let d := complexChartAt (n := m + 1) (π (e.val.symm z))
    have hzd : z ∈ HolomorphicMaps.coordinateDomain π e d :=
      ⟨hz, mem_complexChartAt_source _⟩
    obtain ⟨W, ρ, κ, h, hzW, hρ, hκ, hh, hdiff, hzero⟩ :=
      exists_corrected_theta_current_pluriharmonic_difference hu hv heq d
        (HolomorphicMaps.coordinateMap π e d z) (HolomorphicMaps.coordinateMap_mem_target hzd)
    let A : Opens (ComplexModel (m + 1)) :=
      ⟨LocalPotentialPullback.potentialDomain π e d W,
        LocalPotentialPullback.potentialDomain_isOpen hπ.1 e d W.isOpen⟩
    have hzA : z ∈ A := ⟨hzd, hzW⟩
    have hρA : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val e A
        (ρ ∘ HolomorphicMaps.coordinateMap π e d) :=
      LocalPotentialPullback.isSmoothLocalPotential_pullback hπ.1 e hρ
    have hκA : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hπ.1 σ).val e A
        (κ ∘ HolomorphicMaps.coordinateMap π e d) :=
      LocalPotentialPullback.isSmoothLocalPotential_pullback hπ.1 e hκ
    obtain ⟨hFp, _hFfin, hFL, hFc, _hFs, _hFm⟩ :=
      ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader
        (ClosedRealOneOneForm.pullback hπ.1 θ).val hup e
        (ρ ∘ HolomorphicMaps.coordinateMap π e d) hρA
    obtain ⟨hGp, hGfin, hGL, hGc, _hGs, _hGm⟩ :=
      ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader
        (ClosedRealOneOneForm.pullback hπ.1 σ).val hvp e
        (κ ∘ HolomorphicMaps.coordinateMap π e d) hκA
    let hF := corrected_chart_localQuasiPsh hup hρA.2.1 hFp
    let hG := corrected_chart_localQuasiPsh hvp hκA.2.1 hGp
    have hhA : ContDiffOn ℝ ∞ (h ∘ HolomorphicMaps.coordinateMap π e d) A :=
      hh.contDiffOn.comp
        ((HolomorphicMaps.coordinateMap_contDiffOn_real hπ.1 e d).mono inter_subset_left)
        (fun _ _ => mem_univ _)
    have hdiffA : EqOn
        (fun y => chartFunction (u ∘ π) e y +
          ((ρ ∘ HolomorphicMaps.coordinateMap π e d) y : EReal))
        (fun y => (chartFunction (v ∘ π) e y +
          ((κ ∘ HolomorphicMaps.coordinateMap π e d) y : EReal)) +
          ((h ∘ HolomorphicMaps.coordinateMap π e d) y : EReal)) A := by
      intro y hy
      have he := hdiff hy.2
      simpa only [chartFunction, HolomorphicMaps.coordinateMap, Function.comp_apply,
        d.val.left_inv hy.1.2] using he
    have hzeroA : ∀ y ∈ A, smoothDDC (h ∘ HolomorphicMaps.coordinateMap π e d) y = 0 := by
      intro y hy
      rw [show (h ∘ HolomorphicMaps.coordinateMap π e d) =
        (fun x => h (HolomorphicMaps.coordinateMap π e d x)) from rfl,
        HolomorphicDDC.smoothDDC_comp A.isOpen W.isOpen
          ((HolomorphicMaps.coordinateMap_contDiffOn hπ.1 e d).mono inter_subset_left)
          hh.contDiffOn (fun _ hx => hx.2) hy, hzero _ hy.2]
      ext v
      rfl
    have hc := ddC_regularLocalQuasiPsh_eq_of_smooth_zero_difference
      hF hG hFL hGL hGfin hhA hdiffA hzeroA
    refine ⟨A, hρA.2.1, hzA, ?_⟩
    have hforms : restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hρA.2.1 =
        restrictForm (S.coefficients (canonicalBasis (m + 1)) e) hρA.2.1 :=
      hFc.trans (hc.trans hGc.symm)
    exact congrArg (fun B => B w) hforms
  exact congrArg (fun D => D φ) hd

/-- Every original current internally supplies its representation; the produced
whole pullback is uniquely characterized by ALL genuine representations. -/
theorem exists_unique_original_current_modification_pullback
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : GlobalPositiveCurrentACRestriction.IsFullPositive T) :
    ∃! R : GlobalCurrent (m + 1) W.carrier (degreeTwo (Nat.succ_pos m)),
      R.IsClosed (canonicalBasis (m + 1)) ∧
      R.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
      GlobalPositiveCurrentACRestriction.IsFullPositive R ∧
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
        (hu : IsThetaPshPotential θ.val u), T = thetaPotentialCurrent θ.val u hu →
        R = thetaPotentialModificationCurrent hπ θ u hu := by
  obtain ⟨θ, u, hu, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hc h11 hT
  let R := thetaPotentialModificationCurrent hπ θ u hu
  have hp := thetaPotentialModificationCurrent_closed_type_positive hπ θ u hu
  refine ⟨R, ⟨hp.1, hp.2.1, hp.2.2, ?_⟩, ?_⟩
  · intro σ v hv hreadv
    exact thetaPotentialCurrent_modification_pullback_eq_of_eq hπ.1 hu hv
      (hread.symm.trans hreadv)
  · intro S hS
    exact hS.2.2.2 θ u hu hread

/-- The earlier literal whole-current lifting constructor now has genuine
representation independence; none of the remaining matrix clauses is assumed. -/
theorem thetaPotentialModificationCurrent_eq_of_thetaPotentialCurrent_eq
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    {θ σ : ClosedRealOneOneForm (m + 1) F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (heq : thetaPotentialCurrent θ.val u hu = thetaPotentialCurrent σ.val v hv) :
    thetaPotentialModificationCurrent hπ θ u hu =
      thetaPotentialModificationCurrent hπ σ v hv :=
  thetaPotentialCurrent_modification_pullback_eq_of_eq hπ.1 hu hv heq

end SGPT.Okounkov
