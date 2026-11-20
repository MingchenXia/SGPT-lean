import SGPT.Envelopes.MADirichlet2Jacobian
import SGPT.Envelopes.MADirichletSubsolution
import SGPT.Foundations.Analysis.Pending.PerronEnvelopeVanishingMass
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic

/-!
# Monge–Ampère subsolutions under the polydisk automorphisms

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`,
Step 2 (on the unit polydisk `P`): pulling back `(ddᶜH)ⁿ ≥ Fⁿ ηⁿ` by the automorphism
`T = T_{a,h}` gives

  `(ddᶜ(H ∘ T))ⁿ ≥ ((F ∘ T) |det J_T|^{2/n})ⁿ ηⁿ`   on `P`

(`ma_comp_polydiskAut_ge`): the Bedford–Taylor measure of `H ∘ T` is the push-forward of that of
`H` by `T⁻¹` (TN `IsBTLimit.comp_biholomorphic`), and the change of variables formula
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) with the real Jacobian `|det J_T|²`
(TN `det_fderiv_eq_normSq`) transports the density.

* `isBiholomorphicPair_polydiskAut`: `T_{a,h}` and `T_{a+h,-h}` are mutually inverse
  biholomorphisms of `P`.
* `isLocallyBoundedPshOn_comp_polydiskAut`: `H ∘ T_{a,h}` is locally bounded plurisubharmonic.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexConjugate ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- The disc Möbius maps are holomorphic where their denominators do not vanish. -/
theorem contDiffOn_discMobius (c : ℂ) :
    ContDiffOn ℂ ∞ (discMobius c) {w | 1 - conj c * w ≠ 0} := by
  have hnum : ContDiff ℂ ∞ fun w : ℂ => w - c := contDiff_id.sub contDiff_const
  have hden : ContDiff ℂ ∞ fun w : ℂ => 1 - conj c * w := contDiff_const.sub (contDiff_const.mul contDiff_id)
  have hinv : ContDiffOn ℂ ∞ (fun w : ℂ => (1 - conj c * w)⁻¹) {w | 1 - conj c * w ≠ 0} :=
    hden.contDiffOn.inv fun w hw => hw
  have := hnum.contDiffOn.mul hinv
  simpa only [discMobius_eq, div_eq_mul_inv] using this

section Automorphisms

variable {a h : ComplexModel n}

theorem contDiffOn_polydiskAut (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1) :
    ContDiffOn ℂ ∞ (polydiskAut a h) (unitPolydisk n) := by
  have hpi : ContDiffOn ℂ ∞ (fun y : ComplexModel n => fun i =>
      discMobius (-(a i + h i)) (discMobius (a i) (y i))) (unitPolydisk n) := by
    refine contDiffOn_pi.mpr fun i => ?_
    have hcoord : ContDiff ℂ ∞ (fun y : ComplexModel n => y i) :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).contDiff
    have h1 : ContDiffOn ℂ ∞ (fun y : ComplexModel n => discMobius (a i) (y i)) (unitPolydisk n) :=
      (contDiffOn_discMobius (a i)).comp hcoord.contDiffOn fun y hy =>
        discMobius_denom_ne_zero (ha i) (hy i).le
    exact (contDiffOn_discMobius (-(a i + h i))).comp h1 fun y hy =>
      discMobius_denom_ne_zero (by rw [norm_neg]; exact hah i)
        (norm_discMobius_le_one (ha i) (hy i).le)
  exact (EuclideanSpace.equiv (Fin n) ℂ).symm.contDiff.comp_contDiffOn hpi

theorem polydiskAut_polydiskAut_inv {z : ComplexModel n} (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) (hz : z ∈ closedUnitPolydisk n) :
    polydiskAut (a + h) (-h) (polydiskAut a h z) = z := by
  ext i
  rw [polydiskAut_apply, polydiskAut_apply]
  have e1 : (a + h) i + (-h) i = a i := by simp
  have e2 : (a + h) i = a i + h i := complexModel_add_apply a h i
  rw [e1, e2]
  have hw : ‖discMobius (a i) (z i)‖ ≤ 1 := norm_discMobius_le_one (ha i) (hz i)
  have h1 := discMobius_neg_discMobius (c := -(a i + h i)) (by rw [norm_neg]; exact hah i) hw
  rw [neg_neg] at h1
  rw [h1]
  exact discMobius_neg_discMobius (ha i) (hz i)

theorem polydiskAut_inv_polydiskAut {w : ComplexModel n} (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) (hw : w ∈ closedUnitPolydisk n) :
    polydiskAut a h (polydiskAut (a + h) (-h) w) = w := by
  ext i
  rw [polydiskAut_apply, polydiskAut_apply]
  have e1 : (a + h) i + (-h) i = a i := by simp
  have e2 : (a + h) i = a i + h i := complexModel_add_apply a h i
  rw [e1, e2]
  have hv : ‖discMobius (a i + h i) (w i)‖ ≤ 1 := norm_discMobius_le_one (hah i) (hw i)
  have h1 := discMobius_neg_discMobius (c := -(a i)) (by rw [norm_neg]; exact ha i) hv
  rw [neg_neg] at h1
  rw [h1]
  exact discMobius_neg_discMobius (hah i) (hw i)

/-- `T_{a,h}` and `T_{a+h,-h}` are mutually inverse biholomorphic automorphisms of the unit
polydisk. -/
theorem isBiholomorphicPair_polydiskAut (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1) :
    IsBiholomorphicPair (unitPolydiskOpens n) (unitPolydiskOpens n) (polydiskAut a h)
      (polydiskAut (a + h) (-h)) := by
  have hah' : ∀ i, ‖(a + h) i‖ < 1 := fun i => by rw [complexModel_add_apply]; exact hah i
  have hahh : ∀ i, ‖(a + h) i + (-h) i‖ < 1 := fun i => by
    have : (a + h) i + (-h) i = a i := by simp
    rw [this]; exact ha i
  exact
    { holo := contDiffOn_polydiskAut ha hah
      holo_inv := contDiffOn_polydiskAut hah' hahh
      mapsTo := fun z hz => polydiskAut_mem_unitPolydisk ha hah hz
      mapsTo_inv := fun z hz => polydiskAut_mem_unitPolydisk hah' hahh hz
      left_inv := fun z hz => polydiskAut_polydiskAut_inv ha hah fun i => (hz i).le
      right_inv := fun w hw => polydiskAut_inv_polydiskAut ha hah fun i => (hw i).le }

/-- `H ∘ T_{a,h}` is locally bounded plurisubharmonic on the polydisk. -/
theorem isLocallyBoundedPshOn_comp_polydiskAut {H : ComplexModel n → ℝ}
    (hH : IsLocallyBoundedPshOn (unitPolydiskOpens n) H) (ha : ∀ i, ‖a i‖ < 1)
    (hah : ∀ i, ‖a i + h i‖ < 1) :
    IsLocallyBoundedPshOn (unitPolydiskOpens n) fun z => H (polydiskAut a h z) := by
  have hb := isBiholomorphicPair_polydiskAut ha hah
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (u := fun z => (H z : EReal))
    isOpen_unitPolydisk (differentiableOn_polydiskAut ha hah) hb.mapsTo hH.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVP, C, hC⟩ := hH.2 _ (hb.mapsTo hz)
  have hopen : IsOpen ((unitPolydisk n) ∩ polydiskAut a h ⁻¹' V) :=
    hb.holo.continuousOn.isOpen_inter_preimage isOpen_unitPolydisk V.isOpen
  exact ⟨⟨_, hopen⟩, ⟨hz, hzV⟩, fun y hy => hy.1, C, fun y hy => hC _ hy.2⟩

end Automorphisms

/-- `((F ∘ T)|det J_T|^{2/n})ⁿ = (F ∘ T)ⁿ |det J_T|²`. -/
theorem polydiskDensity_pow (hn : 0 < n) (F : ComplexModel n → ℝ) (a h z : ComplexModel n) :
    polydiskDensity F a h z ^ n =
      F (polydiskAut a h z) ^ n * Complex.normSq (∏ i, autDeriv a h z i) := by
  rw [polydiskDensity, mul_pow, Real.rpow_inv_natCast_pow (Complex.normSq_nonneg _) hn.ne']

/-- **Monge–Ampère lower bounds under the polydisk automorphisms** (FPT
`thm:continuous-density-ball-dirichlet`, Step 2, on the polydisk): if `(ddᶜH)ⁿ ≥ Fⁿ ηⁿ` on `P`
then `(ddᶜ(H ∘ T_{a,h}))ⁿ ≥ ((F ∘ T_{a,h})|det J_{a,h}|^{2/n})ⁿ ηⁿ` on `P`. -/
theorem ma_comp_polydiskAut_ge (hn : 0 < n) {H : ComplexModel n → ℝ}
    (hH : IsLocallyBoundedPshOn (unitPolydiskOpens n) H) {F : ComplexModel n → ℝ}
    (hMA : (volume.restrict (unitPolydisk n)).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) ≤
      canonicalBedfordTaylorMeasure (unitPolydiskOpens n) H hH)
    {a h : ComplexModel n} (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1)
    (hT : IsLocallyBoundedPshOn (unitPolydiskOpens n) fun z => H (polydiskAut a h z)) :
    (volume.restrict (unitPolydisk n)).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * polydiskDensity F a h z ^ n)) ≤
      canonicalBedfordTaylorMeasure (unitPolydiskOpens n) _ hT := by
  classical
  set P : Opens (ComplexModel n) := unitPolydiskOpens n with hPdef
  set T := polydiskAut a h with hTdef
  set σ := polydiskAut (a + h) (-h) with hσdef
  have hb : IsBiholomorphicPair P P T σ := isBiholomorphicPair_polydiskAut ha hah
  set μ := canonicalBedfordTaylorMeasure P H hH with hμdef
  -- the measure of `H ∘ T` is the push-forward of that of `H`
  have hlim : IsBTLimit P (fun _ x => H (T x)) ((μ.restrict P).map σ) :=
    (isBTLimit_canonicalBedfordTaylorMeasure hH).comp_biholomorphic hb
  have heq : canonicalBedfordTaylorMeasure P _ hT = (μ.restrict P).map σ :=
    (isBTLimit_canonicalBedfordTaylorMeasure hT).unique hlim
  rw [heq]
  have hσm : AEMeasurable σ (μ.restrict P) :=
    hb.holo_inv.continuousOn.aemeasurable P.isOpen.measurableSet
  refine Measure.le_iff.mpr fun E hE => ?_
  rw [Measure.map_apply_of_aemeasurable hσm hE, Measure.restrict_apply' P.isOpen.measurableSet,
    withDensity_apply _ hE, Measure.restrict_restrict hE]
  set S : Set (ComplexModel n) := E ∩ P with hSdef
  have hS : MeasurableSet S := hE.inter P.isOpen.measurableSet
  have hSP : S ⊆ (P : Set (ComplexModel n)) := inter_subset_right
  -- derivatives and injectivity of `T` on `S`
  have hdiff : ∀ x ∈ S, DifferentiableAt ℂ T x := fun x hx =>
    differentiableAt_polydiskAut ha hah fun i => (hSP hx i).le
  have hf' : ∀ x ∈ S, HasFDerivWithinAt T (fderiv ℝ T x) S x := fun x hx =>
    ((hdiff x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn T S := fun x hx y hy hxy => by
    have hx' := hb.left_inv x (hSP hx)
    have hy' := hb.left_inv y (hSP hy)
    rw [← hx', ← hy', hxy]
  have hTS : T '' S ⊆ (P : Set (ComplexModel n)) := fun _ ⟨x, hx, hxy⟩ => hxy ▸ hb.mapsTo (hSP hx)
  have hTSm : MeasurableSet (T '' S) := measurable_image_of_fderivWithin hS hf' hinj
  -- `T(S) = σ⁻¹(E) ∩ P`
  have himage : T '' S = σ ⁻¹' E ∩ P := by
    rw [hb.image_eq hSP]
    ext w
    constructor
    · rintro ⟨hwP, hw⟩
      exact ⟨hw.1, hwP⟩
    · rintro ⟨hw, hwP⟩
      exact ⟨hwP, hw, hb.mapsTo_inv hwP⟩
  rw [← himage]
  -- the change of variables
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hf' hinj
    (fun x => ENNReal.ofReal (mongeAmpereConst n * F x ^ n))
  have hdens : ∀ x ∈ S, ENNReal.ofReal |(fderiv ℝ T x).det| *
      ENNReal.ofReal (mongeAmpereConst n * F (T x) ^ n) =
      ENNReal.ofReal (mongeAmpereConst n * polydiskDensity F a h x ^ n) := by
    intro x hx
    rw [det_fderiv_eq_normSq (hdiff x hx),
      det_jacobianMatrix_polydiskAut ha hah fun i => (hSP hx i).le,
      abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      polydiskDensity_pow hn]
    congr 1
    ring
  calc ∫⁻ x in S, ENNReal.ofReal (mongeAmpereConst n * polydiskDensity F a h x ^ n)
      = ∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ T x).det| *
          ENNReal.ofReal (mongeAmpereConst n * F (T x) ^ n) :=
        (setLIntegral_congr_fun hS fun x hx => (hdens x hx).symm)
    _ = ∫⁻ x in T '' S, ENNReal.ofReal (mongeAmpereConst n * F x ^ n) := hcv.symm
    _ = ((volume.restrict (unitPolydisk n)).withDensity
          (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n))) (T '' S) := by
        have hTS' : T '' S ⊆ unitPolydisk n := hTS
        rw [withDensity_apply _ hTSm, Measure.restrict_restrict hTSm, inter_eq_left.mpr hTS']
    _ ≤ μ (T '' S) := hMA _

end SGPT.Envelopes.MADirichlet
