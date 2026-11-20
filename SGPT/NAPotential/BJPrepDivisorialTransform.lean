import SGPT.NAPotential.BJPrepLegendreComparison
import SGPT.NAPotential.BJPrepLelongConvex
import SGPT.PSH.SourceNAOrder
import SGPT.PSH.CompactPrimeNumerical
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations
import SGPT.PSH.SourceIVolumeGoodness

/-!
# The divisorial values of `Γ^An` in Lelong-number form; order reflection

Source: the comparison theorem of `chapter_NApotential.tex` (`subsec:NA_comparison`).  For
`Γ ∈ PSH^NA(X, θ)`, a Kähler form `ω` and a divisorial valuation `v = t ord_E`, the book's
analytification (`def:Gammaana`) is

`Γ^An(t ord_E) = sup_{τ < Γ_max} (Γ_τ^{θ+ω,An}(t ord_E) + τ) = sup_{τ < Γ_max} (τ - t ν(Γ_τ^{θ+ω}, E))`,

the second equality by `φ^An(t ord_E) = -t ν(φ, E)` (stated after `def:NApotential:L975`,
`prop:Lelongnumfrommis`).  We define the right-hand side directly with the generic Lelong numbers
`ν(φ, E)` of the project (`presentationReader`, `def:pshfunctions:L1112`): this is the
`naDivisorialTransform` below.  It does not involve multiplier ideals of algebraic models, so it
is available without GAGA.

The results are the divisorial core of `lma:anaorder` (and of the injectivity in `thm:DXZ`):

* `naDivisorialTransform_independent`: independence of `ω` (the divisorial part of the remark
  "clearly independent of the choice of `ω`" after `def:Gammaana`);
* `naDivisorialTransform_mono`: `Γ ≤ Γ'` implies `Γ^An ≤ Γ'^An` on `X^Div` ("order preserving");
* `sourceNAPOrder_of_naDivisorialTransform_le`: if `Γ_max ≤ Γ'_max` (the values at the trivial
  valuation, `eq:Gammamax`) and `Γ^An ≤ Γ'^An` at every `t ord_E` with `t ∈ ℚ_{>0}`, then
  `Γ ≤ Γ'` (the book's argument: Legendre inversion, `prop:Iequivchar2`,
  `prop:Icomparandenvelope`);
* `eq_of_naDivisorialTransform_eq`: injectivity.

The identification of `naDivisorialTransform` with the analytification of
`SGPT.NAPotential.Berkovich.naPotentialAnAt` at `t ord_E`, and the extension from `X^Div` to
`X^An` (`thm:pshdetbydiv`), are not part of this file.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJPrep

universe u

open Set
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.PSH.CompactPrimeNumerical

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section Curve

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The Lelong-number form of the analytification of a test curve at a divisorial valuation
`t ord_E`: `sup_{τ < Γ_max} (τ - t ν(Γ_τ, E))`. -/
def curveDivisorialTransform (C : SourceTestCurvePredata θ) (p : PrimePresentation n M)
    (t : ℝ) : EReal :=
  ⨆ (τ : ℝ) (h : τ < C.max),
    (τ : EReal) - (t : EReal) * ((presentationReader (C.potential ⟨τ, h⟩) p : ℝ≥0∞) : EReal)

theorem le_curveDivisorialTransform (C : SourceTestCurvePredata θ) (p : PrimePresentation n M)
    (t : ℝ) {τ : ℝ} (h : τ < C.max) :
    (τ : EReal) - (t : EReal) * ((presentationReader (C.potential ⟨τ, h⟩) p : ℝ≥0∞) : EReal) ≤
      curveDivisorialTransform C p t :=
  le_iSup₂_of_le (f := fun (τ : ℝ) (h : τ < C.max) =>
    (τ : EReal) - (t : EReal) * ((presentationReader (C.potential ⟨τ, h⟩) p : ℝ≥0∞) : EReal))
    τ h le_rfl

/-- Each term of the transform is the real number `τ - t ν(Γ_τ, E)`. -/
theorem curveDivisorialTransform_term [CompactSpace M] (C : SourceTestCurvePredata θ)
    (p : PrimePresentation n M) (t : ℝ) {τ : ℝ} (h : τ < C.max) :
    (τ : EReal) - (t : EReal) * ((presentationReader (C.potential ⟨τ, h⟩) p : ℝ≥0∞) : EReal) =
      ((τ - t * sliceLelong C p τ : ℝ) : EReal) := by
  have hx : 0 ≤ sliceLelong C p τ := by
    rw [sliceLelong_of_lt C p h]
    exact ENNReal.toReal_nonneg
  rw [← coe_sliceLelong C p h, EReal.coe_ennreal_ofReal, max_eq_left hx, EReal.coe_sub,
    EReal.coe_mul]

/-- Two test curves with the same cutoff and the same slice Lelong numbers along `E` have the same
transform. -/
theorem curveDivisorialTransform_congr {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (C : SourceTestCurvePredata θ) (D : SourceTestCurvePredata σ) (p : PrimePresentation n M)
    (hmax : C.max = D.max)
    (hreader : ∀ (r : ℝ) (hr : r < C.max) (hs : r < D.max),
      presentationReader (C.potential ⟨r, hr⟩) p = presentationReader (D.potential ⟨r, hs⟩) p)
    (t : ℝ) : curveDivisorialTransform C p t = curveDivisorialTransform D p t := by
  apply le_antisymm
  · refine iSup₂_le fun τ h => ?_
    have hs : τ < D.max := hmax ▸ h
    rw [hreader τ h hs]
    exact le_curveDivisorialTransform D p t hs
  · refine iSup₂_le fun τ h => ?_
    have hs : τ < C.max := hmax ▸ h
    rw [← hreader τ hs h]
    exact le_curveDivisorialTransform C p t hs

/-- Monotonicity: a larger cutoff and smaller slice Lelong numbers give a larger transform. -/
theorem curveDivisorialTransform_mono {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (C : SourceTestCurvePredata θ) (D : SourceTestCurvePredata σ) (p : PrimePresentation n M)
    (hmax : C.max ≤ D.max)
    (hreader : ∀ (r : ℝ) (hr : r < C.max),
      presentationReader (D.potential ⟨r, hr.trans_le hmax⟩) p ≤
        presentationReader (C.potential ⟨r, hr⟩) p)
    {t : ℝ} (ht : 0 ≤ t) : curveDivisorialTransform C p t ≤ curveDivisorialTransform D p t := by
  refine iSup₂_le fun τ h => ?_
  refine le_trans ?_ (le_curveDivisorialTransform D p t (h.trans_le hmax))
  apply EReal.sub_le_sub le_rfl
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hreader τ h) (EReal.coe_nonneg.mpr ht)

/-- **Legendre inversion along `E`.**  If `C_max ≤ D_max` and the transform of `C` is at most that
of `D` at every rational `t > 0`, then `ν(D_τ, E) ≤ ν(C_τ, E)` for every `τ < C_max`. -/
theorem presentationReader_le_of_curveDivisorialTransform_le [CompactSpace M]
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (C : SourceTestCurvePredata θ) (D : SourceTestCurvePredata σ) (p : PrimePresentation n M)
    (hmax : C.max ≤ D.max)
    (hT : ∀ t : ℚ, 0 < t → curveDivisorialTransform C p t ≤ curveDivisorialTransform D p t)
    {r : ℝ} (hr : r < C.max) :
    presentationReader (D.potential ⟨r, hr.trans_le hmax⟩) p ≤
      presentationReader (C.potential ⟨r, hr⟩) p := by
  have key : sliceLelong D p r ≤ sliceLelong C p r := by
    refine le_of_forall_rat_legendre_le hmax (sliceLelong_convexOn D p)
      (sliceLelong_monotoneOn D p) ?_ hr
    intro t ht τ hτ c hc
    have hD : curveDivisorialTransform D p t ≤ (c : EReal) := by
      refine iSup₂_le fun τ' h' => ?_
      rw [curveDivisorialTransform_term D p t h']
      exact EReal.coe_le_coe_iff.mpr (hc τ' h')
    have hC := (le_curveDivisorialTransform C p t hτ).trans ((hT t ht).trans hD)
    rw [curveDivisorialTransform_term C p t hτ] at hC
    exact EReal.coe_le_coe_iff.mp hC
  rw [← coe_sliceLelong D p (hr.trans_le hmax), ← coe_sliceLelong C p hr]
  exact ENNReal.ofReal_le_ofReal key

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **Order reflection for positive `𝓘`-model test curves.**  If `C_max ≤ D_max` and
`sup_τ (τ - t ν(C_τ, E)) ≤ sup_τ (τ - t ν(D_τ, E))` for every prime divisor `E` over `M` and every
rational `t > 0`, then `C ≤ D`.  This is the book's argument in `lma:anaorder`: Legendre
inversion, `prop:Iequivchar2` and `prop:Icomparandenvelope`. -/
theorem sourceTestCurvePOrder_of_curveDivisorialTransform_le (omega : KahlerBackground n M)
    (C D : SourcePositiveIModelTestCurve θ) (hmax : C.val.max ≤ D.val.max)
    (hT : ∀ (p : PrimePresentation n M) (t : ℚ), 0 < t →
      curveDivisorialTransform C.val.toSourceTestCurvePredata p t ≤
        curveDivisorialTransform D.val.toSourceTestCurvePredata p t) :
    SourceTestCurvePOrder C.val D.val := by
  refine (sourceTestCurvePOrder_iff omega C.val D.val).mpr ⟨hmax, fun r hr => ?_⟩
  have hmC : sourceIModel θ (C.val.potential ⟨r, hr⟩) := (sourceIModel_iff_native θ _).mpr
    (((sourceIModelTestCurvesPositive_iff_slices omega C.val).mp C.property) ⟨r, hr⟩)
  have hmD : sourceIModel θ (D.val.potential ⟨r, hr.trans_le hmax⟩) :=
    (sourceIModel_iff_native θ _).mpr
      (((sourceIModelTestCurvesPositive_iff_slices omega D.val).mp D.property)
        ⟨r, hr.trans_le hmax⟩)
  have hI : sourceIOrder (ofFixedModel n M) (C.val.potential ⟨r, hr⟩)
      (D.val.potential ⟨r, hr.trans_le hmax⟩) := by
    apply (sourceIOrder_iff_presentationComparison ⟨θ, hmC.1⟩ ⟨θ, hmD.1⟩).mpr
    intro p
    exact presentationReader_le_of_curveDivisorialTransform_le C.val.toSourceTestCurvePredata
      D.val.toSourceTestCurvePredata p hmax (hT p) hr
  have hle := (sourceIOrder_iff_sourceIEnvelope_le hmC.1 hmD.1).mp hI
  rw [← hmC.2, ← hmD.2] at hle
  exact hle

end Curve

section NA

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The Lelong-number form of `Γ^An(t ord_E)` (`def:Gammaana` combined with
`φ^An(t ord_E) = -t ν(φ, E)`), computed with the component of `Γ` at the Kähler form `ω`:
`sup_{τ < Γ_max} (τ - t ν(Γ_τ^{θ+ω}, E))`. -/
def naDivisorialTransform (Γ : SourceNAPotential θ) (ω : SourceKahlerForm n M)
    (p : PrimePresentation n M) (t : ℝ) : EReal :=
  curveDivisorialTransform (Γ.component ω).val.toSourceTestCurvePredata p t

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- `𝓘`-projection does not change the generic Lelong numbers along prime divisors over `M`. -/
theorem presentationReader_sourceIEnvelope {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH α φ) [Nonempty M]
    (p : PrimePresentation n M) :
    presentationReader (sourceIEnvelope α φ) p = presentationReader φ p := by
  have hE := sourceIEquivalent_iEnvelope hφ
  have hφq : (ofFixedModel n M).IsQPSH φ := ⟨α, hφ⟩
  have hEq : (ofFixedModel n M).IsQPSH (sourceIEnvelope α φ) := ⟨α, isThetaPSH_sourceIEnvelope hφ⟩
  exact le_antisymm ((sourceIOrder_iff_presentationComparison hφq hEq).mp hE.1 p)
    ((sourceIOrder_iff_presentationComparison hEq hφq).mp hE.2 p)

/-- For `ω ≤ η` the transforms at `ω` and `η` agree: the component at `η` is the
`𝓘`-projection of the component at `ω`. -/
theorem naDivisorialTransform_eq_of_le (Γ : SourceNAPotential θ) {ω η : SourceKahlerForm n M}
    (h : sourceKahlerFormLE ω η) (p : PrimePresentation n M) (t : ℝ) :
    naDivisorialTransform Γ ω p t = naDivisorialTransform Γ η p t := by
  unfold naDivisorialTransform
  rw [← Γ.compatible ω η h]
  apply curveDivisorialTransform_congr
  · exact (sourceIModelTestCurveTransition_max _ _ _).symm
  · intro r hr hs
    rw [sourceIModelTestCurveTransition_potential _ _ _ r hr hs]
    exact (presentationReader_sourceIEnvelope (sourceThetaPSH_of_semipositive_difference
      (sourceNAComponentBackground_difference θ h) ((Γ.component ω).val.thetaPSH ⟨r, hr⟩))
      p).symm

/-- The divisorial values of `Γ^An` do not depend on the Kähler form used to compute them
(the remark after `def:Gammaana`, on `X^Div`). -/
theorem naDivisorialTransform_independent (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm n M) (p : PrimePresentation n M) (t : ℝ) :
    naDivisorialTransform Γ ω p t = naDivisorialTransform Γ η p t :=
  (naDivisorialTransform_eq_of_le Γ (sourceKahlerFormLE_commonUpper_left ω η) p t).trans
    (naDivisorialTransform_eq_of_le Γ (sourceKahlerFormLE_commonUpper_right ω η) p t).symm

/-- **Order preservation on `X^Div`** (first sentence of `lma:anaorder`, divisorial part):
`Γ ≤ Γ'` implies `Γ^An(t ord_E) ≤ Γ'^An(t ord_E)` for `t ≥ 0`. -/
theorem naDivisorialTransform_mono {Γ Γ' : SourceNAPotential θ} (h : SourceNAPOrder Γ Γ')
    (ω : SourceKahlerForm n M) (p : PrimePresentation n M) {t : ℝ} (ht : 0 ≤ t) :
    naDivisorialTransform Γ ω p t ≤ naDivisorialTransform Γ' ω p t := by
  obtain ⟨hcut, hle⟩ := (sourceTestCurvePOrder_iff (sourceKahlerFormRepresentative ω) _ _).mp
    ((sourceNAPOrder_iff_component Γ Γ' ω).mp h)
  exact curveDivisorialTransform_mono _ _ p hcut
    (fun r hr => presentationReader_anti (hle r hr) p) ht

/-- **Order reflection** (second sentence of `lma:anaorder`, in Lelong-number form).  If
`Γ_max ≤ Γ'_max` (the values at the trivial valuation, `eq:Gammamax`) and
`Γ^An(t ord_E) ≤ Γ'^An(t ord_E)` for every prime divisor `E` over `X` and every `t ∈ ℚ_{>0}`,
then `Γ ≤ Γ'`. -/
theorem sourceNAPOrder_of_naDivisorialTransform_le {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm n M)
    (hmax : (Γ.component ω).val.max ≤ (Γ'.component ω).val.max)
    (hT : ∀ (p : PrimePresentation n M) (t : ℚ), 0 < t →
      naDivisorialTransform Γ ω p t ≤ naDivisorialTransform Γ' ω p t) :
    SourceNAPOrder Γ Γ' :=
  (sourceNAPOrder_iff_component Γ Γ' ω).mpr
    (sourceTestCurvePOrder_of_curveDivisorialTransform_le (sourceKahlerFormRepresentative ω)
      (Γ.component ω) (Γ'.component ω) hmax hT)

/-- **Injectivity** (last sentence of `lma:anaorder`, in Lelong-number form): `Γ` is determined
by `Γ_max` and the values `Γ^An(t ord_E)`, `E` a prime divisor over `X`, `t ∈ ℚ_{>0}`. -/
theorem eq_of_naDivisorialTransform_eq {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm n M)
    (hmax : (Γ.component ω).val.max = (Γ'.component ω).val.max)
    (hT : ∀ (p : PrimePresentation n M) (t : ℚ), 0 < t →
      naDivisorialTransform Γ ω p t = naDivisorialTransform Γ' ω p t) :
    Γ = Γ' :=
  SourceNAPOrder.antisymm
    (sourceNAPOrder_of_naDivisorialTransform_le ω hmax.le fun p t ht => (hT p t ht).le)
    (sourceNAPOrder_of_naDivisorialTransform_le ω hmax.ge fun p t ht => (hT p t ht).ge)

/-- The order on `PSH^NA(X, θ)` is detected by `Γ_max` and the divisorial transform. -/
theorem sourceNAPOrder_iff_naDivisorialTransform_le {Γ Γ' : SourceNAPotential θ}
    (ω : SourceKahlerForm n M) :
    SourceNAPOrder Γ Γ' ↔ (Γ.component ω).val.max ≤ (Γ'.component ω).val.max ∧
      ∀ (p : PrimePresentation n M) (t : ℚ), 0 < t →
        naDivisorialTransform Γ ω p t ≤ naDivisorialTransform Γ' ω p t := by
  constructor
  · intro h
    refine ⟨((sourceNAPOrder_iff_component Γ Γ' ω).mp h).cutoff_le, fun p t ht => ?_⟩
    exact naDivisorialTransform_mono h ω p (by exact_mod_cast ht.le)
  · rintro ⟨hmax, hT⟩
    exact sourceNAPOrder_of_naDivisorialTransform_le ω hmax hT

end NA

end SGPT.NAPotential.BJPrep
