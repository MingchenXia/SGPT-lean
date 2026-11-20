import SGPT.Okounkov.TranscendentalVolIdDimOne
import SGPT.Foundations.Analysis.Pending.YauTheoremInterface
import SGPT.Foundations.Analysis.Pending.YauNormalizingConstant
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity

/-!
# Curves: the degree of a class and the dimension-one volume identity

Package VOL (blueprint `claude-okounkov-transcendental`, nodes `tok:ext-curve` and `tok:A1`;
chapter `claude-tok-volid`, nodes `tok-volid:curve-degree`, `tok-volid:curve-rank-one`,
`tok-volid:curve-volume`, `tok-volid:A1-degree`): DRWNXZ Lemma 3.6.

Let `X` be a compact connected Kähler curve with Kähler form `ω` (`F : OriginalFlagGeometry 1`,
flag `X ⊇ {q}`), `V = ∫_X ω`.

* `curveDegree θ = ∫_X θ` (the integral of the `(1,1)`-form against the Kähler measure,
  `topRatio`); it is linear, kills `dd^c` of smooth functions (Stokes, TN
  `integral_topRatio_formPow_add_ddc`) and depends only on the class (`curveDegree_eq_of_class_eq`).
* `ofRepresentative_eq_smul_omega` (**`tok:ext-curve`**, the `dd^c`-lemma on a curve, from Yau's
  theorem with `N = 1`, TN `exists_kahler_mongeAmpere_eq_smul`): every class is
  `{θ} = (∫θ / V) {ω}`; in particular a class contains a Kähler form iff its degree is positive.
* `sourceClassVolume_eq_ofReal_curveDegree`: `vol({θ}) = max(∫θ, 0)`.
* `volumeIdentity_dimOne_of_pointDegree` (**`tok:A1`**): `vol Δ(ξ) = vol(ξ)`, given the degree of
  the point, `∫_X Θ_E = 1` for a unit metric `E` of `{q}` (`PointDegreeStatement F`).  The degree
  of a point is proved in `TranscendentalVolIdPointDegree` (`pointDegreeStatement`), which also
  states the unconditional `A_1` (`volumeIdentity_dimOne`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Okounkov.TranscendentalRelGen

/-! ### Two-forms on `ℂ¹` -/

section TwoForms

/-- In dimension one the top density of a two-form is its value on the frame `(e₀, I e₀)`. -/
theorem actualTopPowerDensity_one (A : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ) :
    actualTopPowerDensity A = A (coordinateRealFrame (n := 1)) := rfl

theorem actualTopPowerDensity_one_add (A B : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ) :
    actualTopPowerDensity (A + B) = actualTopPowerDensity A + actualTopPowerDensity B := rfl

theorem actualTopPowerDensity_one_smul (c : ℝ) (A : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ) :
    actualTopPowerDensity (c • A) = c * actualTopPowerDensity A := rfl

/-- A real two-form on `ℂ¹` is determined by its value on the frame `(e₀, I e₀)`. -/
theorem twoForm_eq_of_frame {A B : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ}
    (h : A (coordinateRealFrame (n := 1)) = B (coordinateRealFrame (n := 1))) : A = B := by
  set b := Module.Basis.smulTower Complex.basisOneI
    (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis with hb
  have hb00 : b (0, 0) = coordinateRealFrame (n := 1) 0 := by
    rw [hb, Module.Basis.smulTower_apply, coordinateRealFrame_one_zero]
    simp [coordinateVector]
  have hb10 : b (1, 0) = coordinateRealFrame (n := 1) 1 := by
    rw [hb, Module.Basis.smulTower_apply, coordinateRealFrame_one_one]
    simp [coordinateVector]
  have hframe : (fun i : Fin 2 => coordinateRealFrame (n := 1) i) = ![b (0, 0), b (1, 0)] := by
    funext i; fin_cases i <;> simp [hb00, hb10]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine b.ext_alternating fun v hv => ?_
  have hval : ∀ C : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ,
      C ![b (0, 0), b (1, 0)] = C (coordinateRealFrame (n := 1)) := fun C => by
    rw [← hframe]
  have h' : A ![b (0, 0), b (1, 0)] = B ![b (0, 0), b (1, 0)] := by rw [hval, hval, h]
  have hswap : ∀ C : (ComplexModel 1) [⋀^Fin 2]→L[ℝ] ℝ,
      C ![b (1, 0), b (0, 0)] = -C ![b (0, 0), b (1, 0)] := fun C => by
    have hsw : (![b (0, 0), b (1, 0)] ∘ Equiv.swap (0 : Fin 2) 1) = ![b (1, 0), b (0, 0)] := by
      funext i; fin_cases i <;> rfl
    have := C.toAlternatingMap.map_swap ![b (0, 0), b (1, 0)] (show (0 : Fin 2) ≠ 1 by decide)
    rw [hsw] at this
    exact this
  -- the injective pairs of `Fin 2 × Fin 1`
  have key : ∀ x y : Fin 2 × Fin 1, x ≠ y →
      A ![b x, b y] = B ![b x, b y] := by
    intro x y hxy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    obtain rfl : x2 = 0 := Subsingleton.elim _ _
    obtain rfl : y2 = 0 := Subsingleton.elim _ _
    fin_cases x1 <;> fin_cases y1
    all_goals simp only [Fin.zero_eta, Fin.mk_one] at hxy ⊢
    all_goals first
      | exact absurd rfl hxy
      | exact h'
      | (rw [hswap A, hswap B, h'])
  have hv' : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hne : v 0 ≠ v 1 := fun h01 => absurd (hv h01) (by decide)
  have := key (v 0) (v 1) hne
  change A (fun i => b (v i)) = B (fun i => b (v i))
  have hfun : (fun i => b (v i)) = ![b (v 0), b (v 1)] := by funext i; fin_cases i <;> rfl
  rw [hfun]
  exact this

end TwoForms

/-! ### The degree of a class on a curve -/

section Degree

variable {F : OriginalFlagGeometry.{u} 1}

/-- **The degree** `∫_X θ` of a closed real `(1,1)`-form on the curve `X`, the integral of
`θ / ω` against the Kähler measure `ω`. -/
def curveDegree (F : OriginalFlagGeometry.{u} 1) (θ : ClosedRealOneOneForm 1 F.carrier) : ℝ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  ∫ x, topRatio F.omega.form.val (formPow θ.val 1) x ∂(kahlerVolume F.omega)

/-- The integrand of the degree, read in the preferred chart. -/
theorem topRatio_formPow_one (θ : ClosedRealOneOneForm 1 F.carrier) (x : F.carrier) :
    topRatio F.omega.form.val (formPow θ.val 1) x =
      actualTopPowerDensity (θ.val.coeff (complexChartAt (n := 1) x)
          ((complexChartAt (n := 1) x).val x)) /
        actualTopPowerDensity (F.omega.form.val.coeff (complexChartAt (n := 1) x)
          ((complexChartAt (n := 1) x).val x)) := by
  unfold topRatio chartRatio
  rw [formPow_coeff, formPow_coeff, topDensity_formPower, topDensity_formPower]

theorem topRatio_formPow_one_add (θ θ' : ClosedRealOneOneForm 1 F.carrier) (x : F.carrier) :
    topRatio F.omega.form.val (formPow (θ + θ').val 1) x =
      topRatio F.omega.form.val (formPow θ.val 1) x +
        topRatio F.omega.form.val (formPow θ'.val 1) x := by
  rw [topRatio_formPow_one, topRatio_formPow_one, topRatio_formPow_one,
    ClosedRealOneOneForm.coeff_add, actualTopPowerDensity_one_add, add_div]

theorem topRatio_formPow_one_smul (c : ℝ) (θ : ClosedRealOneOneForm 1 F.carrier) (x : F.carrier) :
    topRatio F.omega.form.val (formPow (c • θ).val 1) x =
      c * topRatio F.omega.form.val (formPow θ.val 1) x := by
  rw [topRatio_formPow_one, topRatio_formPow_one, ClosedRealOneOneForm.coeff_smul,
    actualTopPowerDensity_one_smul, mul_div_assoc]

theorem curveDegree_add (θ θ' : ClosedRealOneOneForm 1 F.carrier) :
    curveDegree F (θ + θ') = curveDegree F θ + curveDegree F θ' := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  unfold curveDegree
  simp_rw [topRatio_formPow_one_add]
  exact integral_add (integrable_topRatio _ _) (integrable_topRatio _ _)

theorem curveDegree_smul (c : ℝ) (θ : ClosedRealOneOneForm 1 F.carrier) :
    curveDegree F (c • θ) = c * curveDegree F θ := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  unfold curveDegree
  simp_rw [topRatio_formPow_one_smul]
  exact integral_const_mul c _

theorem curveDegree_sub (θ θ' : ClosedRealOneOneForm 1 F.carrier) :
    curveDegree F (θ - θ') = curveDegree F θ - curveDegree F θ' := by
  have h := curveDegree_add (F := F) (θ - θ') θ'
  rw [sub_add_cancel] at h
  linarith

/-- `V = ∫_X ω > 0`. -/
def curveVolume (F : OriginalFlagGeometry.{u} 1) : ℝ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  (kahlerVolume F.omega).real univ

theorem curveVolume_pos : 0 < curveVolume F := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have _ : Nonempty F.carrier := ConnectedSpace.toNonempty
  exact NefCoreKahlerCurrent.kahlerVolume_real_univ_pos F.omega

theorem curveDegree_omega : curveDegree F F.omega.form = curveVolume F := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  unfold curveDegree curveVolume
  simp_rw [topRatio_formPow F.omega.isKahler.1]
  simp

/-- **Stokes**: `∫_X dd^c f = 0`. -/
theorem curveDegree_ddc {f : F.carrier → ℝ} (hf : ChartSmooth (n := 1) f) :
    curveDegree F (ManifoldTubePositivity.ddcClosedForm f hf) = 0 := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have h := YauNormalizingConstant.integral_topRatio_formPow_add_ddc F.omega hf
  have h' : curveDegree F (F.omega.form + ManifoldTubePositivity.ddcClosedForm f hf) =
      curveVolume F := h
  rw [curveDegree_add, curveDegree_omega] at h'
  linarith

/-- The degree only sees the coefficients on chart targets. -/
theorem curveDegree_congr {θ θ' : ClosedRealOneOneForm 1 F.carrier}
    (h : θ.val.GeometricallyEq θ'.val) : curveDegree F θ = curveDegree F θ' := by
  unfold curveDegree
  congr 1
  funext x
  rw [topRatio_formPow_one, topRatio_formPow_one,
    h _ ((complexChartAt (n := 1) x).val.map_source (mem_complexChartAt_source x))]

/-- **The degree depends only on the class.** -/
theorem curveDegree_eq_of_class_eq {θ θ' : ClosedRealOneOneForm 1 F.carrier}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    curveDegree F θ = curveDegree F θ' := by
  obtain ⟨g, hg, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp h
  have hgeom : θ'.val.GeometricallyEq (θ + ManifoldTubePositivity.ddcClosedForm g hg).val := by
    intro e z hz
    rw [heq e z hz, ClosedRealOneOneForm.coeff_add, ManifoldTubePositivity.ddcClosedForm_coeff]
  rw [curveDegree_congr hgeom, curveDegree_add, curveDegree_ddc, add_zero]

end Degree

/-! ### `H^{1,1}` of a curve is spanned by `{ω}` (`tok:ext-curve`) -/

section RankOne

variable {F : OriginalFlagGeometry.{u} 1}

/-- **Kähler classes are multiples of `{ω}`** (Yau's theorem in dimension one: `A + dd^c φ = c ω`
for `c = vol(A)/vol(ω)`). -/
theorem exists_ofRepresentative_kahler_eq_smul (A : KahlerBackground 1 F.carrier) :
    ∃ c : ℝ, RealBottChern.ofRepresentative A.form =
      c • RealBottChern.ofRepresentative F.omega.form := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  obtain ⟨φ, hφ, -, hMA⟩ := YauTheorem.exists_kahler_mongeAmpere_eq_smul Nat.one_pos A F.omega
  set c := (kahlerVolume A).real univ / (kahlerVolume F.omega).real univ with hc
  refine ⟨c, ?_⟩
  have hgeom : (A.form + ManifoldTubePositivity.ddcClosedForm φ hφ).val.GeometricallyEq
      (c • F.omega.form).val := by
    intro e z hz
    rw [ClosedRealOneOneForm.coeff_smul]
    apply twoForm_eq_of_frame
    have h := hMA e z hz
    rw [actualTopPowerDensity_one, actualTopPowerDensity_one] at h
    rw [h]
    rfl
  rw [← TranscendentalLifting.ofRepresentative_add_ddc A.form hφ,
    RealBottChern.ofRepresentative_eq_of_geometricallyEq hgeom, RealBottChern.ofRepresentative_smul]

/-- **`tok:ext-curve`** (the `dd^c`-lemma on a curve): every class is `{θ} = (∫θ / ∫ω) {ω}`. -/
theorem ofRepresentative_eq_smul_omega (θ : ClosedRealOneOneForm 1 F.carrier) :
    RealBottChern.ofRepresentative θ =
      (curveDegree F θ / curveVolume F) • RealBottChern.ofRepresentative F.omega.form := by
  obtain ⟨C, -, hK⟩ := KahlerDomination.exists_pos_isKahler_add_smul F.omega θ
  obtain ⟨c, hc⟩ := exists_ofRepresentative_kahler_eq_smul (F := F) ⟨θ + C • F.omega.form, hK⟩
  have hc' : RealBottChern.ofRepresentative θ + C • RealBottChern.ofRepresentative F.omega.form =
      c • RealBottChern.ofRepresentative F.omega.form := by
    rw [← RealBottChern.ofRepresentative_smul, ← RealBottChern.ofRepresentative_add]
    exact hc
  have h1 : RealBottChern.ofRepresentative θ =
      (c - C) • RealBottChern.ofRepresentative F.omega.form := by
    rw [sub_smul, ← hc']; abel
  have h2 : curveDegree F θ = (c - C) * curveVolume F := by
    rw [curveDegree_eq_of_class_eq (θ' := (c - C) • F.omega.form)
      (by rw [h1, RealBottChern.ofRepresentative_smul]), curveDegree_smul, curveDegree_omega]
  rw [h1, h2, mul_div_cancel_right₀ _ curveVolume_pos.ne']

/-- **`tok:ext-curve`**: a class of positive degree contains a Kähler form. -/
theorem exists_kahler_of_curveDegree_pos {θ : ClosedRealOneOneForm 1 F.carrier}
    (hθ : 0 < curveDegree F θ) :
    ∃ κ : KahlerBackground 1 F.carrier,
      RealBottChern.ofRepresentative κ.form = RealBottChern.ofRepresentative θ := by
  have hpos : 0 < curveDegree F θ / curveVolume F := div_pos hθ curveVolume_pos
  refine ⟨KahlerBackground.smul hpos F.omega, ?_⟩
  rw [KahlerBackground.smul_form, RealBottChern.ofRepresentative_smul,
    ofRepresentative_eq_smul_omega θ]

end RankOne

/-! ### The volume of a class on a curve -/

section Volume

variable {F : OriginalFlagGeometry.{u} 1}

theorem sourceClassVolume_omega :
    (letI : MeasurableSpace F.carrier := borel F.carrier
     sourceClassVolume (RealBottChern.ofRepresentative F.omega.form)) =
      ENNReal.ofReal (curveVolume F) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have h0 : IsThetaPshPotential F.omega.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff F.omega.form).mpr F.omega.isSemipositive
  rw [TranscendentalPartial.sourceClassVolume_eq_of_bounded F.omega F.omega.form h0
    (C := 0) (fun _ => by simp)]
  unfold curveVolume
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

theorem sourceClassVolume_zero_class :
    (letI : MeasurableSpace F.carrier := borel F.carrier
     sourceClassVolume (0 : RealBottChern 1 F.carrier)) = 0 := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have h := TranscendentalVolumeConcavity.sourceClassVolume_smul F.omega
    (0 : RealBottChern 1 F.carrier) (c := 2) two_pos
  rw [smul_zero] at h
  have hfin := (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega
    (0 : RealBottChern 1 F.carrier)).ne
  set x := sourceClassVolume (0 : RealBottChern 1 F.carrier)
  norm_num at h
  by_contra hx
  have h2 : (1 : ℝ≥0∞) * x = 2 * x := by rw [one_mul]; exact h
  have := (ENNReal.mul_left_inj hx hfin).mp h2
  norm_num at this

/-- **The volume on a curve is the positive part of the degree**: `vol({θ}) = max(∫θ, 0)`. -/
theorem sourceClassVolume_eq_ofReal_curveDegree (θ : ClosedRealOneOneForm 1 F.carrier) :
    (letI : MeasurableSpace F.carrier := borel F.carrier
     sourceClassVolume (RealBottChern.ofRepresentative θ)) =
      ENNReal.ofReal (curveDegree F θ) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  set β := RealBottChern.ofRepresentative F.omega.form with hβ
  set t := curveDegree F θ / curveVolume F with ht
  have hV := curveVolume_pos (F := F)
  have hdeg : curveDegree F θ = t * curveVolume F := by
    rw [ht, div_mul_cancel₀ _ hV.ne']
  rw [ofRepresentative_eq_smul_omega θ]
  by_cases htpos : 0 < t
  · rw [TranscendentalVolumeConcavity.sourceClassVolume_smul F.omega β htpos]
    have h := sourceClassVolume_omega (F := F)
    simp only [zero_add, pow_one]
    rw [hβ, h, ← ENNReal.ofReal_mul htpos.le, hdeg]
  · push Not at htpos
    rw [ENNReal.ofReal_of_nonpos (by rw [hdeg]; exact mul_nonpos_of_nonpos_of_nonneg htpos hV.le)]
    rcases htpos.lt_or_eq with htneg | htzero
    · by_contra hne
      have hpos : 0 < sourceClassVolume (t • β) := pos_iff_ne_zero.mpr hne
      have hbig := (TranscendentalVolumeConcavity.sourceClassVolume_pos_iff_isBigClass F.omega _).mp
        hpos
      have hpsef₁ := TranscendentalVolumeConcavity.classPseudoeffective_of_isBigClass F.omega hbig
      have hnt : 0 < -t := neg_pos.mpr htneg
      have hpsef₂ : ClassPseudoeffectiveViaPotentials ((-t) • β) := by
        rw [hβ, ← RealBottChern.ofRepresentative_smul, classPseudoeffectiveViaPotentials_ofRepresentative]
        refine ⟨fun _ => 0, ?_⟩
        rw [← KahlerBackground.smul_form hnt]
        exact (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
          (KahlerBackground.smul hnt F.omega).isSemipositive
      have hadd := TranscendentalVolumeConcavity.volumeRoot_add_le F.omega hpsef₁ hpsef₂
      rw [← add_smul, add_neg_cancel, zero_smul] at hadd
      unfold TranscendentalVolumeConcavity.volumeRoot at hadd
      rw [sourceClassVolume_zero_class] at hadd
      have hfin := (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega (t • β)).ne
      have hr : 0 < (sourceClassVolume (t • β)).toReal := ENNReal.toReal_pos hne hfin
      simp only [zero_add, Nat.cast_one, inv_one, Real.rpow_one, ENNReal.toReal_zero] at hadd
      have := ENNReal.toReal_nonneg (a := sourceClassVolume ((-t) • β))
      linarith
    · rw [show curveDegree F θ / curveVolume F = 0 from htzero, zero_smul]
      exact sourceClassVolume_zero_class

end Volume

/-! ### The volume identity on a curve -/

section A1

variable {F : OriginalFlagGeometry.{u} 1}

/-- **The degree of a point** (`tok-volid:point-degree`): for a unit metric `E` of the point
`Y₁ = {q}` of a curve, `∫_X Θ_E = 1`, i.e. `{q}` has degree one (Lelong--Poincaré:
`[q] = Θ_E + dd^c log |s_q|²_E`, and `∫_X [q] = 1`). -/
def PointDegreeStatement (F : OriginalFlagGeometry.{u} 1) : Prop :=
  ∀ E : MeteredEffectiveQDivisor 1 F.carrier, IsFirstDivisorUnitMetric F E →
    curveDegree F E.curvature = 1

/-- **`tok:A1`** (DRWNXZ Lemma 3.6), given the degree of a point (`PointDegreeStatement F`): on
a compact Kähler curve with flag `X ⊇ {q}`, `vol Δ(ξ) = vol(ξ)` for every big class. With
`vol(ξ - s{q}) = max(∫θ - s, 0)` (`sourceClassVolume_eq_ofReal_curveDegree`), the shift lemmas
`vol(ξ - ν_min{q}) = vol(ξ)` and `vol(ξ - ν_max{q}) = 0` give `ν_min = 0`, `ν_max ≥ ∫θ`, and a
current of `Ω(ξ)` with `ν(T, q) > ∫θ` would give a Kähler current `T - ν(T,q)[q]` in a class of
negative degree; so `Δ(ξ) = [0, ∫θ]` and `vol Δ(ξ) = ∫θ = vol(ξ)`. -/
theorem volumeIdentity_dimOne_of_pointDegree (hD : PointDegreeStatement F) :
    VolumeIdentityStatement F := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  intro α hα
  set θ := Quotient.out α with hθdef
  have hθ : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by rwa [hθ]
  obtain ⟨φ, hφ⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  obtain ⟨E, hE⟩ := exists_isFirstDivisorUnitMetric F hφ.1.1
  set δ := curveDegree F θ with hδ
  have hvol : ∀ s : ℝ, sourceClassVolume (RealBottChern.ofRepresentative (θ - s • E.curvature)) =
      ENNReal.ofReal (δ - s) := fun s => by
    rw [sourceClassVolume_eq_ofReal_curveDegree, curveDegree_sub, curveDegree_smul, hD E hE,
      mul_one]
  have hvol0 : sourceClassVolume (RealBottChern.ofRepresentative θ) = ENNReal.ofReal δ := by
    simpa using hvol 0
  have hδpos : 0 < δ := by
    have h := (TranscendentalVolumeConcavity.volumePositiveIffBig F.omega _).mpr hbig
    rw [hvol0] at h
    exact ENNReal.ofReal_pos.mp h
  set a := firstValuationMin F θ with ha
  set b := firstValuationMax F θ with hb
  have ha0 : 0 ≤ a :=
    le_csInf (firstValuations_nonempty hbig) (by rintro _ ⟨ψ, -, rfl⟩; exact flagValuation_nonneg ψ 0)
  -- `ν_min = 0`
  have hmin := sourceClassVolume_sub_firstValuationMin hbig hE
  rw [hvol, hvol0] at hmin
  have ha_eq : a = 0 := by
    have hpos : 0 < δ - a := by
      by_contra hle
      push Not at hle
      rw [ENNReal.ofReal_of_nonpos hle] at hmin
      exact (ENNReal.ofReal_pos.mpr hδpos).ne' hmin.symm
    have := (ENNReal.ofReal_eq_ofReal_iff hpos.le hδpos.le).mp hmin
    linarith
  -- `ν_max ≥ δ`
  have hmax := sourceClassVolume_sub_firstValuationMax hbig hE
  rw [hvol, ENNReal.ofReal_eq_zero] at hmax
  -- `ν_max ≤ δ`
  have hb_le : b ≤ δ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨_, ⟨T, hT, rfl⟩, hTδ⟩ := exists_lt_of_lt_csSup (firstValuations_nonempty hbig) hlt
    obtain ⟨v, ⟨κ, hκ⟩, -, -, -, -⟩ := exists_residual_of_fixedFirst hE hT (t := flagValuation F T 0) rfl
    have hbigc : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative
        (θ - flagValuation F T 0 • E.curvature)) := by
      rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass]
      exact ⟨⟨_, rfl, v, κ, hκ⟩⟩
    have h := (TranscendentalVolumeConcavity.volumePositiveIffBig F.omega _).mpr hbigc
    rw [hvol, ENNReal.ofReal_pos] at h
    change δ < flagValuation F T 0 at hTδ
    linarith
  have hb_eq : b = δ := le_antisymm hb_le (by linarith)
  change volume (tradOkounkovBody F θ) = _
  rw [volume_tradOkounkovBody_dimOne hbig, ← hb, ← ha, hb_eq, ha_eq, sub_zero, ← hθ, hvol0]
  simp

end A1

/-! ### The volume identity, given WN in dimensions `≥ 2` and the degree of a point -/

/-- **`tok:volume-identity`** (DRWNXZ Theorem 7.6, the book's `thm:Okounkovtranmain` (1)):
`vol Δ_{Y•}(α) = vol(α)/n!` for every flag geometry and big class, **conditional on**
Witt Nyström's integrated formula in dimensions `≥ 2` (`WNIntegratedStatement`, package WN),
RELGEN's `PushforwardAnalyticStatement`, and the degree of a point on a curve
(`PointDegreeStatement`, used for `A_1`). -/
theorem volumeIdentity_of_wn_of_pushforward_of_pointDegree
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNIntegratedStatement F)
    (hP : PushforwardAnalyticStatement.{u})
    (hD : ∀ F : OriginalFlagGeometry.{u} 1, PointDegreeStatement F) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentityAll_of_dimOne hWN hP (fun F => volumeIdentity_dimOne_of_pointDegree (hD F))

end SGPT.Okounkov.TranscendentalVolId
