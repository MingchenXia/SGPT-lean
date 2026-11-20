import SGPT.Okounkov.TranscendentalVolIdLower
import SGPT.Okounkov.TranscendentalVolIdFubini
import SGPT.Okounkov.TranscendentalPartialVolumeIdentity

/-!
# Restricted volumes are slice volumes (`tok:Bn-implies-Cn`)

Package VOL (blueprint `claude-okounkov-transcendental`, node `tok:Bn-implies-Cn`; chapter
`claude-tok-volid`, nodes `tok-volid:restricted-mass`, `tok-volid:slice-lower`,
`tok-volid:slice-identity`): Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov
bodies* (DRWNXZ), Lemma 7.5.

For a flag geometry of dimension `n = m + 2`, a big class `ξ = {θ}`, a unit metric `E` of `Y₁`
and `t ∈ (ν_min, ν_max)`:

* `restrictedResidual_mass_eq` (`tok-volid:restricted-mass`): for resolution data
  `π^*R = [D] + R'` along a flag lifting, `∫_{W₁} ⟨(R'|_{W₁})^{n-1}⟩ = ∫_{Y₁} ⟨(R|_{Y₁})^{n-1}⟩`;
* `restrictedVolume_le_volume_slice` (lower bound, rational `t`): given `A_{n-1}` and
  `PushforwardAnalyticStatement`, `vol_{X|Y₁}(ξ_t) ≤ (n-1)! vol Δ_t(ξ)`;
* `restrictedVolume_eq_volume_slice_rat`: with the upper bound (`volume_slice_le`, from
  `B_{n-1}`), equality at rational `t`;
* `restrictedVolume_eq_volume_slice` (**`tok:Bn-implies-Cn`**, the slice identity `C_n`): equality
  for every `t ∈ (ν_min, ν_max)`, by continuity of both sides (`WNIntegratedStatement F` for the restricted
  volume, `ok:source-body-slice-continuity` for the slices).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory Matrix
open scoped ENNReal NNReal Topology Manifold ContDiff Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 2)}

/-! ### The restricted residual mass -/

section Mass

variable {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
  {W : OriginalFlagGeometry.{u} (m + 2)} {π : W.carrier → F.carrier} {hπ : IsFlagLifting F W π}
  {D : MeteredEffectiveQDivisor (m + 2) W.carrier} {b : W.carrier → EReal}

/-- The residual `b` of resolution data is finite everywhere. -/
theorem resolutionData_ne_bot (hR : IsResolutionData θ φ hπ D b) (y : W.carrier) : b y ≠ ⊥ := by
  obtain ⟨C, hC⟩ := hR.bounded
  intro h
  have := (hC y).1
  rw [h] at this
  exact EReal.coe_ne_bot _ (le_bot_iff.mp this)

/-- **`tok-volid:restricted-mass`**: if `φ|_{Y₁}` is a genuine potential, then for resolution
data `π^*R = [D] + R'` of `R = θ + dd^c φ`, the restriction of `R'` to the strict transform `W₁`
has the non-pluripolar mass of `R|_{Y₁}`. -/
theorem restrictedResidual_mass_eq (hφ : IsThetaPshPotential θ.val φ)
    (hR : IsResolutionData θ φ hπ D b)
    (hw : IsThetaPshPotential (firstFlagRestriction F θ).val (restrictFirst F φ))
    {z₀ : W.carrier} (hz₀ : z₀ ∈ W.flag (1 : Fin (m + 3))) (hDz₀ : D.weight z₀ ≠ ⊥) :
    letI : MeasurableSpace W.tail.carrier := borel W.tail.carrier
    haveI : BorelSpace W.tail.carrier := ⟨rfl⟩
    letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
    haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
    ∃ hb : IsThetaPshPotential
        (firstFlagRestriction W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature)).val
        (restrictFirst W b),
      diagonalPotentialMass
          (firstFlagRestriction W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature))
          (restrictFirst W b) hb =
        diagonalPotentialMass (firstFlagRestriction F θ) (restrictFirst F φ) hw := by
  let _ : MeasurableSpace W.tail.carrier := borel W.tail.carrier
  have _ : BorelSpace W.tail.carrier := ⟨rfl⟩
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have hιW := contMDiff_firstFlagInclusion W
  have hιF := contMDiff_firstFlagInclusion F
  have hπs : ContMDiff 𝓘(ℂ, ComplexModel (m + 2)) 𝓘(ℂ, ComplexModel (m + 2)) ∞ π := hπ.1.1
  have htm := hπ.tailMap_isFlagLifting.1
  have hφπ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπs θ).val (fun y => φ (π y)) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ.1 θ hφ
  have hDw := TranscendentalLifting.isThetaPshPotential_weight D
  have hnd : LocallyNondegenerate fun y : W.tail.carrier => D.weight (firstFlagInclusion W y) :=
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hιW hDw.1) ⟨⟨z₀, hz₀⟩, hDz₀⟩
  have hwW : IsThetaPshPotential (ClosedRealOneOneForm.pullback hιW
      (ClosedRealOneOneForm.pullback hπs θ)).val fun y => φ (π (firstFlagInclusion W y)) := by
    refine GlobalPotentialPullback.isThetaPshPotential_comp hιW hφπ.1 ?_
    intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := hnd x U hU hxU
    refine ⟨y, hyU, ?_⟩
    show φ (π (firstFlagInclusion W y)) ≠ ⊥
    rw [hR.eq]
    exact fun h => (EReal.add_eq_bot_iff.mp h).elim hy (resolutionData_ne_bot hR _)
  have hb : IsThetaPshPotential (ClosedRealOneOneForm.pullback hιW
      (ClosedRealOneOneForm.pullback hπs θ - D.curvature)).val fun y => b (firstFlagInclusion W y) :=
    GlobalPotentialPullback.isThetaPshPotential_comp hιW hR.psh.1
      (fun x U _ hxU => ⟨x, hxU, resolutionData_ne_bot hR _⟩)
  refine ⟨hb, ?_⟩
  have h1 := diagonalPotentialMass_pullback_residual_eq hιW (ClosedRealOneOneForm.pullback hπs θ) D
    (w := fun y => φ (π y)) (b := b) (fun x => hR.eq x) hnd hwW hb
  refine Eq.trans h1 ?_
  -- the two pullbacks to `W₁` agree geometrically
  have hgeom : (ClosedRealOneOneForm.pullback hιW (ClosedRealOneOneForm.pullback hπs θ)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback htm.1 (firstFlagRestriction F θ)).val := by
    have h₁ := pullback_comp_geometricallyEq' hπs hιW θ.val
    have h₂ := pullback_comp_geometricallyEq' hιF htm.1 θ.val
    exact h₁.symm.trans h₂
  have hw' : IsThetaPshPotential (ClosedRealOneOneForm.pullback htm.1 (firstFlagRestriction F θ)).val
      (fun y => restrictFirst F φ (hπ.tailMap y)) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification htm _ hw
  rw [ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hgeom hwW hw']
  exact AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification htm
    (firstFlagRestriction F θ) hw

end Mass

/-! ### The lower bound -/

section Lower

/-- **`tok-volid:slice-lower`** for one current: given `A_{n-1}` and `PushforwardAnalyticStatement`,
for `R ∈ Ω(ξ_t)` with `R|_{Y₁}` a genuine potential,
`∫_{Y₁} ⟨(R|_{Y₁})^{n-1}⟩ ≤ (n-1)! vol Δ_t(ξ)`. -/
theorem diagonalPotentialMass_restrict_le_volume_slice (hA : VolumeIdentityAllStatement.{u} m)
    (hP : PushforwardAnalyticStatement.{u}) {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 2) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ)
    {φ : F.carrier → EReal} (hφ : φ ∈ gentleKahlerCurrents (θ - (t : ℝ) • E.curvature))
    (hw : IsThetaPshPotential (firstFlagRestriction F (θ - (t : ℝ) • E.curvature)).val
      (restrictFirst F φ)) :
    (letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
     haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
     diagonalPotentialMass (firstFlagRestriction F (θ - (t : ℝ) • E.curvature))
      (restrictFirst F φ) hw) ≤
      ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t) := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  set θt := θ - (t : ℝ) • E.curvature with hθt
  have ht0 : (0 : ℚ) ≤ t := by
    have hmin0 : 0 ≤ firstValuationMin F θ :=
      le_csInf (firstValuations_nonempty hbig)
        (by rintro _ ⟨ψ, -, rfl⟩; exact flagValuation_nonneg ψ 0)
    exact_mod_cast (hmin0.trans h₁.le)
  have hbigt : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θt) := by
    rw [hθt, ofRepresentative_sub_smul]
    exact (isBigMeetingFirstDivisor_sub hbig hE h₁ h₂).1
  have hφg : φ ∈ globalAnalyticCurrents θt := gentleKahlerCurrents_subset_globalAnalyticCurrents hφ
  obtain ⟨W, π, hπ, D, b, hR⟩ := exists_resolutionData hφg
  obtain ⟨hbigβ, himg⟩ := partialOkounkovBody_birational hP hR hφ.2
    (globalAnalyticCurrents_subset_analyticCurrents θt hφg)
  obtain ⟨C, hC⟩ := hR.bounded
  set β := ClosedRealOneOneForm.pullback hπ.1.1 θt - D.curvature with hβ
  set g := correctionMatrixReal hπ with hg
  -- a point of `W₁` off `Supp D`
  obtain ⟨y₀s, hy₀s⟩ := F.firstDivisor.2.1.nonempty
  obtain ⟨y₀, -, hy₀⟩ := hw.2 (⟨y₀s, hy₀s⟩ : F.tail.carrier) univ isOpen_univ (mem_univ _)
  have hy₀mem : y₀.val ∈ π '' W.flag (1 : Fin (m + 3)) := by
    rw [hπ.component_image_eq]; exact y₀.2
  obtain ⟨z₀, hz₀, hπz₀⟩ := hy₀mem
  have hDz₀ : D.weight z₀ ≠ ⊥ := by
    intro h
    apply hy₀
    show φ (firstFlagInclusion F y₀) = ⊥
    rw [show firstFlagInclusion F y₀ = π z₀ from hπz₀.symm, hR.eq, h, EReal.bot_add]
  have hν0 : flagValuation W D.weight 0 = 0 :=
    flagValuation_zero_eq_zero_of_ne_bot W (TranscendentalLifting.isThetaPshPotential_weight D)
      hz₀ hDz₀
  -- the mass identity
  obtain ⟨hb, hmass⟩ := restrictedResidual_mass_eq hφ.1.1 hR hw hz₀ hDz₀
  rw [← hmass]
  set β' := firstFlagRestriction W β with hβ'
  set b' := restrictFirst W b with hb'
  let _ : MeasurableSpace W.tail.carrier := borel W.tail.carrier
  have _ : BorelSpace W.tail.carrier := ⟨rfl⟩
  -- trivial case
  rcases eq_or_ne (diagonalPotentialMass β' b' hb) 0 with h0 | hpos
  · rw [h0]; exact bot_le
  have hvol : sourceClassVolume (RealBottChern.ofRepresentative β') =
      diagonalPotentialMass β' b' hb :=
    sourceClassVolume_eq_of_bounded W.tail.omega β' hb (fun y => (hC y.val).1)
  have hbigβ' : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative β') := by
    refine (TranscendentalVolumeConcavity.volumePositiveIffBig W.tail.omega _).mp ?_
    rw [hvol]; exact pos_iff_ne_zero.mpr hpos
  have hAβ : volume (tradOkounkovBody W.tail β') =
      sourceClassVolume (RealBottChern.ofRepresentative β') / ((m + 1).factorial : ℝ≥0∞) := by
    have h := hA W.tail (RealBottChern.ofRepresentative β') hbigβ'
    rwa [← representativeIndependence W.tail β'] at h
  -- the volume-preserving map into the slice
  set A : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) := fun y j =>
    ((flagValuation W D.weight + Fin.cons 0 y) ᵥ* g⁻¹) j.succ with hA'
  have hdet : g⁻¹.det = 1 := by
    rw [Matrix.det_nonsing_inv, hg, det_correctionMatrixReal, Ring.inverse_one]
  have hvolA : volume (A '' tradOkounkovBody W.tail β') = volume (tradOkounkovBody W.tail β') :=
    volume_image_tail_vecMul g⁻¹ hdet (vecMul_correctionMatrixReal_inv_zero hπ) _ _
  have hincl : A '' tradOkounkovBody W.tail β' ⊆ firstCoordinateSlice (tradOkounkovBody F θ) t := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (Fin.cons 0 y : Fin (m + 2) → ℝ) ∈ tradOkounkovBody W β :=
      cons_zero_mem_tradOkounkovBody hbigβ hR.psh hC hy
    have h2 : flagValuation W D.weight + Fin.cons 0 y ∈
        (fun x => x ᵥ* g) '' partialOkounkovBody F θt φ := by
      rw [hg, himg]
      exact ⟨_, h1, rfl⟩
    obtain ⟨z, hz, hzx⟩ := h2
    have hzeq : z = (flagValuation W D.weight + Fin.cons 0 y) ᵥ* g⁻¹ := by
      rw [← hzx, hg, vecMul_correctionMatrixReal_inv]
    have hzΔ : z ∈ tradOkounkovBody F θt := partialOkounkovBody_subset_tradOkounkovBody θt φ hz
    have hz0 : z 0 = 0 := by
      rw [hzeq, hg, vecMul_correctionMatrixReal_inv_zero]
      simp [hν0]
    have hmem := add_smul_single_mem_tradOkounkovBody hbig hE ht0 hbigt hzΔ
    have hcons : z + (t : ℝ) • (Fin.cons 1 0 : Fin (m + 2) → ℝ) =
        Fin.cons (t : ℝ) (fun j : Fin (m + 1) => z j.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hz0]
      · simp
    rw [hcons] at hmem
    show Fin.cons (t : ℝ) (A y) ∈ tradOkounkovBody F θ
    have hAy : A y = fun j : Fin (m + 1) => z j.succ := by
      rw [hzeq]
    rw [hAy]
    exact hmem
  -- conclusion
  have hfac0 : ((m + 1).factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have hfact : ((m + 1).factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc diagonalPotentialMass β' b' hb
      = ((m + 1).factorial : ℝ≥0∞) * volume (tradOkounkovBody W.tail β') := by
        rw [hAβ, hvol, ENNReal.mul_div_cancel hfac0 hfact]
    _ = ((m + 1).factorial : ℝ≥0∞) * volume (A '' tradOkounkovBody W.tail β') := by rw [hvolA]
    _ ≤ ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t) := by
        gcongr

/-- **`tok-volid:slice-lower`**: given `A_{n-1}` and `PushforwardAnalyticStatement`,
`vol_{X|Y₁}(ξ_t) ≤ (n-1)! vol Δ_t(ξ)` for rational `t ∈ (ν_min, ν_max)`. -/
theorem restrictedVolume_le_volume_slice (hA : VolumeIdentityAllStatement.{u} m)
    (hP : PushforwardAnalyticStatement.{u}) {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 2) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    shiftedRestrictedVolume θ E t ≤
      ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t) := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  rw [shiftedRestrictedVolume_eq]
  unfold TranscendentalVolumeConcavity.restrictedVolume
  exact iSup₂_le fun φ hφ => iSup_le fun hw =>
    diagonalPotentialMass_restrict_le_volume_slice hA hP hbig hE h₁ h₂ hφ hw

end Lower

/-! ### The slice identity -/

section Identity

/-- **`tok:Bn-implies-Cn` at rational `t`**: given `A_{n-1}` and `PushforwardAnalyticStatement`
(hence `B_{n-1}`), `vol_{X|Y₁}(ξ - t{Y₁}) = (n-1)! vol Δ_t(ξ)` for rational `t ∈ (ν_min, ν_max)`. -/
theorem restrictedVolume_eq_volume_slice_rat (hA : VolumeIdentityAllStatement.{u} m)
    (hP : PushforwardAnalyticStatement.{u}) {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 2) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    shiftedRestrictedVolume θ E t =
      ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t) :=
  le_antisymm (restrictedVolume_le_volume_slice hA hP hbig hE h₁ h₂)
    (volume_slice_le (partialVolumeIdentity_of_volumeIdentityAll hP hA) hbig hE h₁ h₂)

/-- **`tok:Bn-implies-Cn`** (DRWNXZ Lemma 7.5, the slice identity `C_n`): given `WNIntegratedStatement F`,
`A_{n-1}` and `PushforwardAnalyticStatement`, `vol_{X|Y₁}(ξ - t{Y₁}) = (n-1)! vol Δ_t(ξ)` for every
`t ∈ (ν_min, ν_max)`. -/
theorem restrictedVolume_eq_volume_slice (hWN : WNIntegratedStatement F)
    (hA : VolumeIdentityAllStatement.{u} m) (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 2) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℝ} (ht : t ∈ Ioo (firstValuationMin F θ) (firstValuationMax F θ)) :
    shiftedRestrictedVolume θ E t =
      ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t) := by
  set I := Ioo (firstValuationMin F θ) (firstValuationMax F θ) with hI
  set Δ := tradOkounkovBody F θ with hΔ
  have hconv : Convex ℝ Δ := TranscendentalBody.convex_tradOkounkovBody θ
  have hcpt : IsCompact Δ := TranscendentalBody.isCompact_tradOkounkovBody θ
  have hproj := image_first_tradOkounkovBody_eq_Icc (F := F) hbig
  have hab := firstValuationMin_lt_firstValuationMax (F := F) hbig
  have hfin1 : ∀ s, shiftedRestrictedVolume θ E s ≠ ⊤ := fun s =>
    (shiftedRestrictedVolume_lt_top θ E s).ne
  have hfin2 : ∀ s, volume (firstCoordinateSlice Δ s) ≠ ⊤ := fun s => by
    have hcl : IsCompact (firstCoordinateSlice Δ s) := by
      have hc : Continuous fun y : Fin (m + 1) → ℝ => (Fin.cons s y : Fin (m + 2) → ℝ) := by
        fun_prop
      have hclosed := hcpt.isClosed.preimage hc
      obtain ⟨K, hK⟩ := hcpt.isBounded.subset_closedBall 0
      refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
      refine (Metric.isBounded_closedBall (x := (0 : Fin (m + 1) → ℝ)) (r := K)).subset ?_
      intro y hy
      have h := hK hy
      rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
      refine le_trans ?_ h
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
      have := norm_le_pi_norm (Fin.cons s y : Fin (m + 2) → ℝ) j.succ
      simpa using this
    exact hcl.measure_lt_top.ne
  -- both sides as real functions are continuous on `I` and agree at rational points
  set f : ℝ → ℝ := fun s => (shiftedRestrictedVolume θ E s).toReal -
    ((m + 1).factorial : ℝ) * (volume (firstCoordinateSlice Δ s)).toReal with hf
  have hfc : ContinuousOn f I := by
    refine (continuousOn_restrictedVolume_sub hWN hbig hE).sub (continuousOn_const.mul ?_)
    exact (continuousOn_volume_firstCoordinateSlice hconv hcpt hproj hab.le).mono
      Ioo_subset_Icc_self
  have hfq : ∀ q : ℚ, (q : ℝ) ∈ I → f q = 0 := by
    intro q hq
    have h := restrictedVolume_eq_volume_slice_rat hA hP hbig hE hq.1 hq.2
    rw [← hΔ] at h
    simp only [hf, h, ENNReal.toReal_mul, ENNReal.toReal_natCast, sub_self]
  have hft := eq_of_continuousOn_of_rat isOpen_Ioo hfc hfq ht
  simp only [hf, sub_eq_zero] at hft
  rw [← ENNReal.toReal_eq_toReal_iff' (hfin1 t) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (hfin2 t)), ENNReal.toReal_mul, ENNReal.toReal_natCast]
  exact hft

end Identity

end SGPT.Okounkov.TranscendentalVolId
