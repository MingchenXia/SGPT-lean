import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone
import SGPT.Foundations.Analysis.FirstPass.TopPowerDensityPositivity
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

set_option autoImplicit false

/-!
# Positivity of restricted volumes off the polar set of a Kähler current

Source: Copy-4, `it:rv-positive` and `eq:def-restricted-volume`
(`transcendental-nakamaye-copy4-20260911`); CT22, Section 2.

Let `T = θ + ddᶜu ≥ ω'` be a Kähler current in `α` whose potential has bounded
analytic singularities and is smooth off its polar set, and let `x` be a regular point of `V` (of dimension
`dim V`) outside the polar set of `u`.  For every `ε > 0`, `T` itself is an
`ε`-admissible presentation, and on a small closed parameter ball around `x`
the restriction `(T + εω)|_V` dominates `ω'|_V`, which is uniformly positive
there.  The top-power density of `(T + εω)|_V` is therefore bounded below by a
positive constant independent of `ε`, so the admissible mass envelopes, and
their infimum `⟨α^{dim V}⟩_{X|V}`, are positive.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumePositivity

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.NonKahlerLocus RestrictedMassEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section Envelope


/-- The admissible mass envelope is nondecreasing in the error. -/
theorem restrictedMassEnvelope_mono (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    {ε ε' : PositiveError} (h : (ε : ℝ) ≤ ε') :
    restrictedMassEnvelope (acTopMassData omega) alpha V ε ≤
      restrictedMassEnvelope (acTopMassData omega) alpha V ε' :=
  restrictedMassEnvelope_mono_of
    (fun _ _ hA hApos hB hBpos => actualTopPowerDensity_le_add hA hApos hB hBpos)
    omega alpha V h

/-- Off the non-nef locus, the restricted volume is the infimum of the envelopes. -/
theorem numericalRestrictedVolume_eq_iInf (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (hV : ¬ V.carrier ⊆ nonNefLocus omega alpha) :
    numericalRestrictedVolume omega alpha V =
      ⨅ ε : PositiveError, restrictedMassEnvelope (acTopMassData omega) alpha V ε := by
  classical
  unfold numericalRestrictedVolume
  simp only [hV, if_false]
  set f : ℝ → ℝ≥0∞ := fun ε =>
    if h : 0 < ε then restrictedMassEnvelope (acTopMassData omega) alpha V ⟨ε, h⟩ else 0
  have hf : Monotone f := by
    intro x y hxy
    simp only [f]
    by_cases hx : 0 < x
    · have hy : 0 < y := hx.trans_le hxy
      rw [dif_pos hx, dif_pos hy]
      exact restrictedMassEnvelope_mono omega alpha V hxy
    · rw [dif_neg hx]
      exact zero_le
  rw [(hf.tendsto_nhdsGT 0).limUnder_eq, sInf_image]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun ε => ?_
    refine (iInf₂_le (ε : ℝ) ε.2).trans_eq ?_
    simp only [f, dif_pos ε.2]
  · refine le_iInf₂ fun x (hx : 0 < x) => ?_
    refine (iInf_le _ ⟨x, hx⟩).trans_eq ?_
    simp only [f, dif_pos hx]

end Envelope

section Presentation

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- A Kähler current with analytic singularities smooth off its polar set whose
polar set does not contain `V` is an `ε`-admissible presentation for every
`ε > 0`. -/
def presentationOfKahlerCurrent (T : KahlerCurrent alpha)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) T.potential)
    (hV : ¬ V.carrier ⊆ poleSet T.potential) (ε : PositiveError) :
    AdmissibleRestrictedCurrentPresentation omega alpha V ε where
  representative := T.representative
  represents := T.represents
  potential := T.potential
  potential_psh := by
    have hsemi : (T.lowerBound.form + (ε : ℝ) • omega.form).val.IsSemipositive := by
      intro e z hz v
      rw [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
      exact add_nonneg
        (by
          rcases eq_or_ne v 0 with rfl | hv
          · rw [smul_zero, (T.lowerBound.form.val.coeff e z).map_eq_zero_of_eq ![0, 0]
              (i := 0) (j := 1) (by simp) (by decide)]
          · exact ((T.lowerBound.isKahler.1 e z hz).2 v hv).le)
        (kahler_smul_isSemipositive omega ε.2.le e z hz v)
    have hsum := LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hsemi
    have hform : T.representative - T.lowerBound.form +
        (T.lowerBound.form + (ε : ℝ) • omega.form) =
        T.representative + (ε : ℝ) • omega.form := by abel
    rwa [hform] at hsum
  smoothAnalyticSingularities := hsing
  not_carrier_subset_poleSet := hV

end Presentation

section Coercive

theorem twoForm_smul_smul {k : ℕ} (A : CoordinateRealTwoForm k) (a : ℝ)
    (x y : ComplexModel k) : A ![a • x, a • y] = a ^ 2 * A ![x, y] := by
  have h := A.toContinuousMultilinearMap.map_smul_univ (fun _ => a) ![x, y]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have hv : ![a • x, a • y] = fun i : Fin 2 => a • ![x, y] i := by
    ext1 i
    fin_cases i <;> rfl
  rw [hv]
  exact h

/-- A continuous family of strictly positive two-forms over a compact set is
uniformly coercive on complex lines. -/
theorem exists_uniform_coercive {k : ℕ} {K : Set (ComplexModel k)} (hK : IsCompact K)
    (F : ComplexModel k → CoordinateRealTwoForm k)
    (hF : ContinuousOn (fun p : ComplexModel k × ComplexModel k =>
      F p.1 ![p.2, Complex.I • p.2]) (K ×ˢ univ))
    (hpos : ∀ w ∈ K, IsStrictlyPositive (F w)) :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ F w ![v, Complex.I • v] := by
  set S : Set (ComplexModel k) := Metric.sphere 0 1
  have hKS : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere 0 1)
  set G : ComplexModel k × ComplexModel k → ℝ := fun p => F p.1 ![p.2, Complex.I • p.2]
  have hG : ContinuousOn G (K ×ˢ S) :=
    hF.mono (prod_mono subset_rfl (subset_univ _))
  have hscale : ∀ w, ∀ v : ComplexModel k, v ≠ 0 →
      F w ![v, Complex.I • v] = ‖v‖ ^ 2 * G (w, ‖v‖⁻¹ • v) := by
    intro w v hv
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    simp only [G]
    rw [smul_comm Complex.I (‖v‖⁻¹) v, ← twoForm_smul_smul, smul_smul, smul_smul,
      mul_inv_cancel₀ hn, one_smul, one_smul]
  have hmem : ∀ w ∈ K, ∀ v : ComplexModel k, v ≠ 0 → (w, ‖v‖⁻¹ • v) ∈ K ×ˢ S := by
    intro w hw v hv
    refine ⟨hw, ?_⟩
    simp [S, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hzero : ∀ w, F w ![(0 : ComplexModel k), Complex.I • 0] = 0 := fun w => by
    rw [smul_zero, (F w).map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp) (by decide)]
  rcases (K ×ˢ S).eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun w hw v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · have h0 := hzero w
      simp only [smul_zero] at h0
      simp [h0]
    · exact absurd (hmem w hw v hv) (by simp [hempty])
  · obtain ⟨p, hp, hmin⟩ := hKS.exists_isMinOn hne hG
    have hp0 : p.2 ≠ 0 := by
      intro h
      have := hp.2
      simp [S, h] at this
    refine ⟨G p, hpos p.1 hp.1 p.2 hp0, fun w hw v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · have h0 := hzero w
      simp only [smul_zero] at h0
      simp [h0]
    · rw [hscale w v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hmem w hw v hv)) (by positivity)

end Coercive

section Density

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **Uniform lower bound for the patch density of `T + εω`**: if the restriction
of the Kähler lower bound `ω'` of `T` is `c`-coercive at a parameter `w` off the
poles, then the density of `(T + εω)|_V` at `w` is at least `c^{dim V}` times the
standard density, for every `ε`. -/
theorem pow_mul_le_patchDensity
    (T : KahlerCurrent alpha)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) T.potential)
    (hV : ¬ V.carrier ⊆ poleSet T.potential) (ε : PositiveError)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hdom : w ∈ P.parameterDomain)
    (hpole : P.toManifold w ∉ poleSet T.potential) {c : ℝ} (hc : 0 ≤ c)
    (hcoer : ∀ v, c * ‖v‖ ^ 2 ≤
      (T.lowerBound.form.val.coeff (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w) ![v, Complex.I • v]) :
    c ^ V.dim * actualTopPowerDensity (standardHermitianTwoForm V.dim) ≤
      patchDensity (presentationOfKahlerCurrent (omega := omega) T hsing hV ε) P w := by
  set e := complexChartAt (n := n) P.center
  set z := P.coordinateParametrization w
  set L := fderiv ℝ P.coordinateParametrization w
  have hz : z ∈ e.val.target := P.source_subset (P.flattening.mapsTo_invFun hdom)
  have hL := RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hdom
  set X := (T.representative - T.lowerBound.form).val.coeff e z +
    smoothDDC (fun y => (T.potential (e.val.symm y)).toReal) z
  set Y := T.lowerBound.form.val.coeff e z + (ε : ℝ) • omega.form.val.coeff e z
  have hsplit : coordinateCurrentForm (presentationOfKahlerCurrent (omega := omega) T hsing hV ε)
      e z = Y + X := by
    ext v
    simp only [coordinateCurrentForm, perturbedRepresentative, presentationOfKahlerCurrent, X, Y,
      ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      sub_eq_add_neg, ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  obtain ⟨hX1, hX2⟩ := isOneOne_and_semipositive_add_smoothDDC_of_smoothOffPole
    (T.representative - T.lowerBound.form) T.strictlyPsh.1 hsing e hz hpole
  have hω' := T.lowerBound.isKahler.1 e z hz
  have hωε := omega.isKahler.1 e z hz
  have hY1 : IsOneOne Y := fun a b => by
    simp only [Y, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      hω'.1 a b, hωε.1 a b]
  have hY2 : CoefficientSemipositive Y := fun v => by
    simp only [Y, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rcases eq_or_ne v 0 with rfl | hv
    · rw [smul_zero, (T.lowerBound.form.val.coeff e z).map_eq_zero_of_eq ![0, 0]
        (i := 0) (j := 1) (by simp) (by decide),
        (omega.form.val.coeff e z).map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp)
        (by decide), mul_zero, add_zero]
    · exact add_nonneg (hω'.2 v hv).le (mul_nonneg ε.2.le (hωε.2 v hv).le)
  have hLY1 := isOneOne_compContinuousLinearMap hY1 L hL
  have hLY2 := coefficientSemipositive_compContinuousLinearMap hY2 L hL
  have hLX1 := isOneOne_compContinuousLinearMap hX1 L hL
  have hLX2 := coefficientSemipositive_compContinuousLinearMap hX2 L hL
  have hcoerY : ∀ v, c * ‖v‖ ^ 2 ≤ Y.compContinuousLinearMap L ![v, Complex.I • v] := by
    intro v
    refine (hcoer v).trans ?_
    have hωL := coefficientSemipositive_compContinuousLinearMap
      (A := omega.form.val.coeff e z) (fun u => by
        rcases eq_or_ne u 0 with rfl | hu
        · rw [smul_zero, (omega.form.val.coeff e z).map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1)
            (by simp) (by decide)]
        · exact (hωε.2 u hu).le) L hL v
    simp only [Y, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hωL ⊢
    exact le_add_of_nonneg_right (mul_nonneg ε.2.le hωL)
  have hlow := pow_mul_le_actualTopPowerDensity hLY1 hc hcoerY
  have hmono := actualTopPowerDensity_le_add hLY1 hLY2 hLX1 hLX2
  refine hlow.trans (hmono.trans (le_of_eq ?_))
  simp only [patchDensity]
  rw [hsplit]
  congr 1

end Density

section Main

open RegularPatchNeighborhood

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}

/-- **Positivity of restricted volumes** (Copy-4, `it:rv-positive`, analytic
core): if a Kähler current `T ∈ α` has analytic singularities smooth off its polar set with closed
polar set, `V ⊄ E_nn(α)`, and some point of `V` regular of dimension `dim V` lies
off the poles of `T`, then `⟨α^{dim V}⟩_{X|V} > 0`. -/
theorem numericalRestrictedVolume_pos_of_kahlerCurrent (T : KahlerCurrent alpha)
    (hsing : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) T.potential)
    (hclosed : IsClosed (poleSet T.potential))
    (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M}
    (hx : x ∈ regularLocus (n := n) V.carrier V.dim) (hxP : x ∉ poleSet T.potential)
    (hnn : ¬ V.carrier ⊆ nonNefLocus omega alpha) :
    0 < numericalRestrictedVolume omega alpha V := by
  have hV : ¬ V.carrier ⊆ poleSet T.potential := fun h =>
    hxP (h (regularLocus_subset (n := n) V.carrier V.dim hx))
  obtain ⟨-, hxA, Φ, hsrc, hzero, hflat⟩ := hx
  let P : RegularPatch V :=
    { center := x
      center_mem := hxA
      flattening := Φ
      source_subset := hsrc
      center_to_zero := hzero
      flattens := hflat }
  set e := complexChartAt (n := n) P.center
  have hopen := RegularPatchDerivative.isOpen_parameterDomain P
  -- smoothness of the parametrization
  have hparam : ContDiffOn ℝ ∞ P.coordinateParametrization P.parameterDomain := by
    have hinv : ContDiffOn ℝ ∞ P.flattening.invFun P.flattening.target :=
      contDiffOn_real_of_differentiableOn_complex P.flattening.invFun_holomorphic
        P.flattening.isOpen_target
    exact hinv.comp ((planeInclusionCLM V.dim n).restrictScalars ℝ).contDiff.contDiffOn
      fun w hw => hw
  have hderiv : ContinuousOn (fderiv ℝ P.coordinateParametrization) P.parameterDomain :=
    hparam.continuousOn_fderiv_of_isOpen hopen (by simp)
  -- a closed parameter ball off the poles
  have hnear : ∀ᶠ w in 𝓝 (0 : ComplexModel V.dim),
      w ∈ P.parameterDomain ∧ P.toManifold w ∉ poleSet T.potential := by
    refine Filter.Eventually.and (hopen.mem_nhds (RegularPatch.zero_mem_parameterDomain P)) ?_
    have hcont := RegularPatch.continuousAt_toManifold_zero P
    have hx0 : P.toManifold 0 ∈ (poleSet T.potential)ᶜ := by
      rw [RegularPatch.toManifold_zero]
      exact hxP
    exact hcont.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hx0)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  set K := Metric.closedBall (0 : ComplexModel V.dim) r
  have hKdom : ∀ w ∈ K, w ∈ P.parameterDomain := fun w hw => (hball hw).1
  -- uniform coercivity of the Kähler lower bound on the ball
  set F : ComplexModel V.dim → CoordinateRealTwoForm V.dim := fun w =>
    (T.lowerBound.form.val.coeff e (P.coordinateParametrization w)).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization w)
  have hFcont : ContinuousOn (fun p : ComplexModel V.dim × ComplexModel V.dim =>
      F p.1 ![p.2, Complex.I • p.2]) (K ×ˢ univ) := by
    have hcoeff : ContinuousOn
        (fun p : ComplexModel V.dim × ComplexModel V.dim =>
          T.lowerBound.form.val.coeff e (P.coordinateParametrization p.1)) (K ×ˢ univ) := by
      refine ((T.lowerBound.form.val.smooth e).continuousOn.comp
        (hparam.continuousOn.comp continuousOn_fst fun p hp => hKdom p.1 hp.1) ?_)
      intro p hp
      exact P.source_subset (P.flattening.mapsTo_invFun (hKdom p.1 hp.1))
    have hL : ContinuousOn (fun p : ComplexModel V.dim × ComplexModel V.dim =>
        fderiv ℝ P.coordinateParametrization p.1) (K ×ˢ univ) :=
      hderiv.comp continuousOn_fst fun p hp => hKdom p.1 hp.1
    have hfun : (fun p : ComplexModel V.dim × ComplexModel V.dim =>
        F p.1 ![p.2, Complex.I • p.2]) = fun p =>
        T.lowerBound.form.val.coeff e (P.coordinateParametrization p.1)
          ![fderiv ℝ P.coordinateParametrization p.1 p.2,
            fderiv ℝ P.coordinateParametrization p.1 (Complex.I • p.2)] := by
      funext p
      simp only [F, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      ext1 i
      fin_cases i <;> rfl
    rw [hfun]
    refine ContinuousOn.eval hcoeff (continuousOn_pi.mpr fun i => ?_)
    fin_cases i
    · simpa using hL.clm_apply continuousOn_snd
    · simpa using hL.clm_apply (continuousOn_snd.const_smul Complex.I)
  have hFpos : ∀ w ∈ K, IsStrictlyPositive (F w) := by
    intro w hw v hv
    have hdom := hKdom w hw
    have hz : P.coordinateParametrization w ∈ e.val.target :=
      P.source_subset (P.flattening.mapsTo_invFun hdom)
    have hLv : fderiv ℝ P.coordinateParametrization w v ≠ 0 := fun h0 =>
      hv (RegularPatchDerivative.fderiv_coordinateParametrization_injective P hdom
        (h0.trans (map_zero _).symm))
    simp only [F, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hvec : (fderiv ℝ P.coordinateParametrization w) ∘ ![v, Complex.I • v] =
        ![fderiv ℝ P.coordinateParametrization w v,
          Complex.I • fderiv ℝ P.coordinateParametrization w v] := by
      ext1 i
      fin_cases i
      · rfl
      · exact RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hdom v
    rw [hvec]
    exact (T.lowerBound.isKahler.1 e _ hz).2 _ hLv
  obtain ⟨c, hc, hcoer⟩ := exists_uniform_coercive (isCompact_closedBall 0 r) F hFcont hFpos
  set c0 : ℝ := c ^ V.dim * actualTopPowerDensity (standardHermitianTwoForm V.dim)
  have hc0 : 0 < c0 :=
    mul_pos (pow_pos hc _) (actualTopPowerDensity_standardHermitianTwoForm_pos V.dim)
  have hvol : 0 < volume K := Metric.measure_closedBall_pos volume 0 hr
  -- the lower bound for every envelope
  have hbound : ∀ ε : PositiveError, ENNReal.ofReal c0 * volume K ≤
      restrictedMassEnvelope (acTopMassData omega) alpha V ε := by
    intro ε
    let p := presentationOfKahlerCurrent (omega := omega) T hsing hV ε
    let Fam : RegularPieceFamily V (poleSet p.potential) :=
      { size := 1
        patch := fun _ => P
        piece := fun _ => K
        measurableSet_piece := fun _ => Metric.isClosed_closedBall.measurableSet
        piece_subset := fun _ => hKdom
        image_subset_regularLocus := by
          rintro - - ⟨w, hw, rfl⟩
          exact RegularPatch.toManifold_mem_regularLocus P (hKdom w hw)
        image_disjoint_avoid := by
          intro _
          rw [Set.disjoint_left]
          rintro - ⟨w, hw, rfl⟩
          exact (hball hw).2
        pairwise_disjoint_image := fun i j hij => absurd (Subsingleton.elim i j) hij }
    refine le_trans ?_ (le_iSup _ p)
    change _ ≤ acTopMass p
    refine le_trans ?_ (le_iSup _ Fam)
    simp only [Fam, Fin.sum_univ_one]
    rw [← setLIntegral_const]
    refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun w hw => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    exact pow_mul_le_patchDensity T hsing hV ε P (hKdom w hw) (hball hw).2 hc.le
      (hcoer w hw)
  rw [numericalRestrictedVolume_eq_iInf omega alpha V hnn]
  exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc0).ne' hvol.ne')
    (le_iInf hbound)

end Main

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumePositivity
