import SGPT.Okounkov.ValuativeTestCurve
import SGPT.Okounkov.DuistermaatHeckmanMoments
import SGPT.PSH.SourceNonArchimedeanVolume
import SGPT.PSH.SourceIModelTestCurveLimits

/-!
# Duistermaat–Heckman measures of non-Archimedean metrics

Source: `chapter_NApotential.tex`, Section *Duistermaat–Heckman measures*: `def:DHm` and
`thm:DHindep` (blueprint chapter `claude-naplan`, nodes `claude-naplan:dhm` and
`claude-naplan:dhindep`).

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag `Y•`,
`θ` a closed smooth real `(1,1)`-form representing a big class and
`Γ ∈ PSH^NA(X, θ)_{>0}` (`SGPT.PSH.VariableComplexAtlas.SourcePositiveIModelTestCurve θ`: a
positive-mass `𝓘`-model test curve, `def:Imodeltestcur`).  The Duistermaat–Heckman measure is

`DH(Γ) := n! · DH(Δ_{Y•}(θ, Γ))`,

where `Δ_{Y•}(θ, Γ)` is the Okounkov test curve of `thm:Okountescurvex`
(`SGPT.Okounkov.Valuative.okounkovTestCurve`) and `DH` of an Okounkov test curve is
`def:DHmeasureOTC` (`SGPT.Okounkov.TestCurve.duistermaatHeckman`).

The flag is the datum of an `OriginalFlagGeometry` `F` (a compact connected complex manifold
with a smooth flag and an auxiliary Kähler form used to define the partial Okounkov bodies).

## Main results

* `naDuistermaatHeckman`: source `def:DHm`.
* `naDuistermaatHeckman_Ici`: `DH(Γ)([t, ∞)) = ∫_X θ_{Γ_t}^n` for `t < Γ_max`, and
  `naDuistermaatHeckman_Ioi_max`: `DH(Γ)` is carried by `(-∞, Γ_max]`.
* `naDuistermaatHeckman_flag_independent` (source `thm:DHindep`, first assertion): for two flag
  geometries `ofOriginal ω Y` and `ofOriginal ω' Y'` on the same manifold the measures agree.
  ROUTE CHANGE: the book proves this with the moment identity for bounded `Γ` and an
  approximation `Γ^ε ↘ Γ`; here the distribution function `t ↦ DH(Γ)([t, ∞))` is computed
  directly by `thm:pobmain` (1) and a finite measure on `ℝ` is determined by it.
* `naDuistermaatHeckman_univ` (`eq:momentDHmtc2`): `DH(Γ)(ℝ) = vol Γ`.
* `naDuistermaatHeckman_moment` (`eq:momentDHmtc1`): the extended moment identity for every
  `p ∈ ℤ_{>0}`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.NAPotential.DH

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov SGPT.Okounkov.PartialBody
open SGPT.Okounkov.Valuative

/-! ### Finite measures on `ℝ` determined by their upper tails -/

/-- Two finite measures on `ℝ` that vanish on `(a, ∞)` and agree on every `[t, ∞)` with
`t < a` are equal. -/
theorem measure_eq_of_Ici_of_Ioi_eq_zero (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (a : ℝ) (hμ : μ (Ioi a) = 0) (hν : ν (Ioi a) = 0)
    (h : ∀ t < a, μ (Ici t) = ν (Ici t)) : μ = ν := by
  apply Measure.ext_of_Ici
  intro t
  rcases lt_trichotomy t a with hta | rfl | hta
  · exact h t hta
  · -- `[t, ∞) = ⋂_k [t - 1/(k+1), ∞)`
    have hI : Ici t = ⋂ k : ℕ, Ici (t - 1 / ((k : ℝ) + 1)) := by
      ext x
      simp only [mem_Ici, mem_iInter]
      constructor
      · intro hx k
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        by_contra hlt
        push Not at hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        have := hx k
        linarith
    have hanti : Antitone fun k : ℕ => Ici (t - 1 / ((k : ℝ) + 1)) := by
      intro i j hij x hx
      simp only [mem_Ici] at hx ⊢
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hij 1
      linarith
    have hlim : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ →
        Tendsto (fun k : ℕ => ρ (Ici (t - 1 / ((k : ℝ) + 1)))) atTop (𝓝 (ρ (Ici t))) := by
      intro ρ _
      rw [hI]
      exact tendsto_measure_iInter_atTop (fun _ => measurableSet_Ici.nullMeasurableSet) hanti
        ⟨0, measure_ne_top _ _⟩
    have hk : ∀ k : ℕ, t - 1 / ((k : ℝ) + 1) < t := fun k => by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    exact tendsto_nhds_unique (hlim μ inferInstance)
      (by simpa only [h _ (hk _)] using hlim ν inferInstance)
  · rw [measure_mono_null (Ici_subset_Ioi.mpr hta) hμ,
      measure_mono_null (Ici_subset_Ioi.mpr hta) hν]

/-! ### Scaling of extended signed integrals -/

/-- The extended signed integral against `c • μ`, `c ∈ ℕ`, is `c` times that against `μ`. -/
theorem extendedSignedIntegral_natCast_smul {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (c : ℕ) (g : A → EReal) :
    SGPT.Convex.extendedSignedIntegral ((c : ℝ≥0∞) • μ) g =
      ((c : ℝ) : EReal) * SGPT.Convex.extendedSignedIntegral μ g := by
  unfold SGPT.Convex.extendedSignedIntegral
  rw [lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul,
    EReal.coe_ennreal_mul, EReal.coe_ennreal_mul]
  have hc : ((c : ℝ≥0∞) : EReal) = ((c : ℝ) : EReal) := by
    rw [← ENNReal.ofReal_natCast, EReal.coe_ennreal_ofReal, max_eq_left (Nat.cast_nonneg c)]
  rw [hc, EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (Nat.cast_nonneg c))
    (EReal.coe_ne_top _)]

/-- The extended signed integral is positively homogeneous in the integrand. -/
theorem extendedSignedIntegral_const_mul {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {c : ℝ} (hc : 0 ≤ c) (g : A → EReal) :
    SGPT.Convex.extendedSignedIntegral μ (fun x => (c : EReal) * g x) =
      (c : EReal) * SGPT.Convex.extendedSignedIntegral μ g := by
  unfold SGPT.Convex.extendedSignedIntegral
  have h1 : ∀ x, ((c : EReal) * g x).toENNReal = ENNReal.ofReal c * (g x).toENNReal := fun x => by
    rw [EReal.toENNReal_mul (EReal.coe_nonneg.mpr hc), EReal.real_coe_toENNReal]
  have h2 : ∀ x, (-((c : EReal) * g x)).toENNReal = ENNReal.ofReal c * (-g x).toENNReal :=
    fun x => by
      rw [← mul_neg, EReal.toENNReal_mul (EReal.coe_nonneg.mpr hc), EReal.real_coe_toENNReal]
  simp_rw [h1, h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    EReal.coe_ennreal_mul, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hc,
    EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top _)]

/-- The extended signed integral only depends on the almost-everywhere class of the integrand. -/
theorem extendedSignedIntegral_congr_ae {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {f g : A → EReal} (h : f =ᵐ[μ] g) :
    SGPT.Convex.extendedSignedIntegral μ f = SGPT.Convex.extendedSignedIntegral μ g := by
  unfold SGPT.Convex.extendedSignedIntegral
  have h1 : (fun x => (f x).toENNReal) =ᵐ[μ] fun x => (g x).toENNReal :=
    h.mono fun x hx => by simp only [hx]
  have h2 : (fun x => (-f x).toENNReal) =ᵐ[μ] fun x => (-g x).toENNReal :=
    h.mono fun x hx => by simp only [hx]
  rw [lintegral_congr_ae h1, lintegral_congr_ae h2]

/-! ### The Duistermaat–Heckman measure of a non-Archimedean metric -/

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} [MeasurableSpace F.carrier]
  [BorelSpace F.carrier] {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}

/-- **Source `def:DHm`**: for `Γ ∈ PSH^NA(X, θ)_{>0}` and the smooth flag of `F`,
`DH(Γ) := n! · DH(Δ_{Y•}(θ, Γ))`, `n = m + 1`. -/
def naDuistermaatHeckman
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) : Measure ℝ :=
  ((m + 1).factorial : ℝ≥0∞) • (okounkovTestCurve (F := F) hbig Γ.val).duistermaatHeckman

variable (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))

instance naDuistermaatHeckman_finite (Γ : SourcePositiveIModelTestCurve θ) :
    IsFiniteMeasure (naDuistermaatHeckman (F := F) hbig Γ) where
  measure_univ_lt_top := by
    rw [naDuistermaatHeckman, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (measure_lt_top _ _)

omit [BorelSpace F.carrier] in
/-- The slices of a positive `𝓘`-model test curve are `𝓘`-model. -/
theorem isIModel_of_positive (Γ : SourcePositiveIModelTestCurve θ) :
    SourceTestCurveIsIModel Γ.val := by
  obtain ⟨φ, hφ, hΓ⟩ := Γ.property
  exact hΓ.2

/-- `n! vol Δ_{Y•}(θ, Γ_t) = ∫_X θ_{Γ_t}^n` (`thm:pobmain` (1), `Γ_t` `𝓘`-model). -/
theorem factorial_mul_volume_body (Γ : SourcePositiveIModelTestCurve θ) (t : Iio Γ.val.max) :
    ((m + 1).factorial : ℝ≥0∞) *
        volume ((okounkovTestCurve (F := F) hbig Γ.val).body t :
          Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      sourcePotentialNonPluripolarMeasure θ (Γ.val.potential t) (Γ.val.thetaPSH t) univ := by
  rw [coe_okounkovTestCurve_body, volume_euclideanImage,
    volume_generalPartialBody_of_borelSpace (Γ.val.native_thetaPSH t),
    iVolume_eq_sourceMass_of_isIModel (Γ.val.thetaPSH t) (isIModel_of_positive Γ t)]
  exact ENNReal.mul_div_cancel (by exact_mod_cast (Nat.factorial_pos _).ne')
    (ENNReal.natCast_ne_top _)

/-- `n! vol Δ_{Y•}(θ, Γ_{-∞}) = ∫_X θ_{Γ_{-∞}}^n = vol Γ` (`thm:pobmain` (1); `Γ_{-∞}` is
`𝓘`-model, `prop:GammaminfImodel`). -/
theorem factorial_mul_volume_base (Γ : SourcePositiveIModelTestCurve θ) :
    ((m + 1).factorial : ℝ≥0∞) *
        volume (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ.val) :
          Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ.val.toSourceTestCurvePredata)
        Γ.val.limit_thetaPSH univ := by
  have hI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val
      (sourceTestCurveLimit Γ.val.toSourceTestCurvePredata) :=
    (sourceIModel_iff_native θ _).mp (Γ.val.limit_iModel F.omega (isIModel_of_positive Γ))
  rw [coe_partialConvexBody, volume_euclideanImage,
    volume_generalPartialBody_of_borelSpace (nativeLimit Γ.val).property,
    iVolume_eq_sourceMass_of_isIModel Γ.val.limit_thetaPSH hI]
  exact ENNReal.mul_div_cancel (by exact_mod_cast (Nat.factorial_pos _).ne')
    (ENNReal.natCast_ne_top _)

/-- The upper tails: `DH(Γ)([t, ∞)) = ∫_X θ_{Γ_t}^n` for `t < Γ_max`. -/
theorem naDuistermaatHeckman_Ici (Γ : SourcePositiveIModelTestCurve θ) (t : Iio Γ.val.max) :
    naDuistermaatHeckman (F := F) hbig Γ (Ici (t : ℝ)) =
      sourcePotentialNonPluripolarMeasure θ (Γ.val.potential t) (Γ.val.thetaPSH t) univ := by
  rw [naDuistermaatHeckman, Measure.smul_apply, smul_eq_mul,
    (okounkovTestCurve (F := F) hbig Γ.val).duistermaatHeckman_Ici t]
  exact factorial_mul_volume_body hbig Γ t

/-- `DH(Γ)` is carried by `(-∞, Γ_max]`. -/
theorem naDuistermaatHeckman_Ioi_max (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman (F := F) hbig Γ (Ioi Γ.val.max) = 0 := by
  set K := okounkovTestCurve (F := F) hbig Γ.val
  have hK : K.duistermaatHeckman (Ioi K.max) = 0 := by
    rw [TestCurve.duistermaatHeckman, Measure.map_apply K.measurable_realLegendre
      measurableSet_Ioi]
    have h := ae_iff.mp K.realLegendre_le_max_ae
    simpa only [preimage, mem_Ioi, not_le] using h
  rw [naDuistermaatHeckman, Measure.smul_apply, smul_eq_mul]
  change _ * K.duistermaatHeckman (Ioi K.max) = 0
  rw [hK, mul_zero]

/-- **Source `eq:momentDHmtc2`**: `∫_ℝ DH(Γ) = vol Γ`. -/
theorem naDuistermaatHeckman_univ (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckman (F := F) hbig Γ univ = sourceNAVolume (sourcePositiveTestCurveToNA Γ) := by
  rw [sourceNAVolume_positiveTestCurve F.omega Γ, naDuistermaatHeckman, Measure.smul_apply,
    smul_eq_mul, TestCurve.duistermaatHeckman_univ]
  exact factorial_mul_volume_base Γ

/-- `vol(θ + dd^c Γ_τ)` (the volume `vol(θ, Γ_τ) = ∫_X (θ + dd^c P_θ[Γ_τ]_𝓘)^n` of the current,
`Pending.iVolume`) for `τ < Γ_max`, as a real number; `0` otherwise. -/
def naSliceVolume (Γ : SourcePositiveIModelTestCurve θ) (τ : ℝ) : ℝ :=
  if hτ : τ < Γ.val.max then
    (Pending.iVolume (atlasClosedFormToNative θ)
      (Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative θ))
      (Γ.val.potential ⟨τ, hτ⟩) (Γ.val.native_thetaPSH ⟨τ, hτ⟩)).toReal
  else 0

/-- `n! vol Δ_{Y•}(θ, Γ_t) = vol(θ, Γ_t)` (`thm:pobmain` (1)), real form. -/
theorem factorial_mul_volume_real_body (Γ : SourcePositiveIModelTestCurve θ) {t : ℝ}
    (ht : t < Γ.val.max) :
    ((m + 1).factorial : ℝ) *
        volume.real ((okounkovTestCurve (F := F) hbig Γ.val).bodyAt t :
          Set (EuclideanSpace ℝ (Fin (m + 1)))) = naSliceVolume Γ t := by
  have hb : ((okounkovTestCurve (F := F) hbig Γ.val).bodyAt t :
      Set (EuclideanSpace ℝ (Fin (m + 1)))) = TranscendentalMain.euclideanImage
        (generalPartialBody F (atlasClosedFormToNative θ) (Γ.val.potential ⟨t, ht⟩)) := by
    rw [TestCurve.bodyAt, dif_pos (show t < (okounkovTestCurve (F := F) hbig Γ.val).max from ht)]
    exact coe_okounkovTestCurve_body hbig Γ.val ⟨t, ht⟩
  rw [naSliceVolume, dif_pos ht, measureReal_def, hb, volume_euclideanImage,
    volume_generalPartialBody_of_borelSpace (Γ.val.native_thetaPSH _),
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hf : ((m + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- `n! vol Δ_{Y•}(θ, Γ_{-∞}) = vol Γ`, real form. -/
theorem factorial_mul_volume_real_base (Γ : SourcePositiveIModelTestCurve θ) :
    ((m + 1).factorial : ℝ) *
        volume.real (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ.val) :
          Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal := by
  rw [sourceNAVolume_positiveTestCurve F.omega Γ, ← factorial_mul_volume_base Γ,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def]

/-- **Source `eq:momentDHmtc1`**: for every `p ∈ ℤ_{>0}`, in the extended sense,
`∫_ℝ x^p DH(Γ)(x) = Γ_max^p vol Γ + p ∫_{-∞}^{Γ_max} τ^{p-1} (vol(θ + dd^c Γ_τ) - vol Γ) dτ`. -/
theorem naDuistermaatHeckman_moment (Γ : SourcePositiveIModelTestCurve θ) (p : ℕ) (hp : 0 < p) :
    SGPT.Convex.extendedSignedIntegral (naDuistermaatHeckman (F := F) hbig Γ)
        (fun t : ℝ => (t : EReal) ^ p) =
      ((Γ.val.max ^ p * (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal : ℝ) : EReal) +
        (p : EReal) * SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio Γ.val.max))
          (fun t : ℝ => ((t ^ (p - 1) * (naSliceVolume Γ t -
            (sourceNAVolume (sourcePositiveTestCurveToNA Γ)).toReal) : ℝ) : EReal)) := by
  set K := okounkovTestCurve (F := F) hbig Γ.val with hK
  set c : ℝ := ((m + 1).factorial : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  rw [naDuistermaatHeckman, extendedSignedIntegral_natCast_smul, K.polynomial_moment_eq p hp,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc0) (EReal.coe_ne_top _),
    ← EReal.coe_mul, ← mul_assoc (c : EReal), mul_comm (c : EReal) (p : EReal), mul_assoc,
    ← extendedSignedIntegral_const_mul _ hc0]
  congr 2
  · rw [← factorial_mul_volume_real_base Γ]
    change c * (Γ.val.max ^ p * _) = _
    ring
  · apply extendedSignedIntegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    have ht' : t < Γ.val.max := ht
    rw [← EReal.coe_mul, ← factorial_mul_volume_real_body hbig Γ ht',
      ← factorial_mul_volume_real_base Γ]
    congr 1
    ring

/-! ### Independence of the flag (`thm:DHindep`) -/

section FlagIndependence

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] {θ' : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M)}

/-- The measurable structure of `M` on the carrier of a flag geometry `ofOriginal ω Y` on `M`. -/
instance ofOriginalMeasurableSpace (ω : KahlerBackground (m + 1) M) (Y : Fin (m + 2) → Set M)
    (hY : IsSmoothFlag Y) : MeasurableSpace (OriginalFlagGeometry.ofOriginal ω Y hY).carrier :=
  ‹MeasurableSpace M›

instance ofOriginalBorelSpace (ω : KahlerBackground (m + 1) M) (Y : Fin (m + 2) → Set M)
    (hY : IsSmoothFlag Y) : BorelSpace (OriginalFlagGeometry.ofOriginal ω Y hY).carrier :=
  ‹BorelSpace M›

/-- **Source `thm:DHindep`, first assertion**: the Duistermaat–Heckman measure of
`Γ ∈ PSH^NA(X, θ)_{>0}` does not depend on the smooth flag `Y•` (nor on the auxiliary Kähler form
of the flag geometry): two flag geometries `(ω, Y•)` and `(ω', Y'•)` on the same manifold give
the same measure. -/
theorem naDuistermaatHeckman_flag_independent
    (hbig' : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    (ω ω' : KahlerBackground (m + 1) M) (Y Y' : Fin (m + 2) → Set M)
    (hY : IsSmoothFlag Y) (hY' : IsSmoothFlag Y') (Γ : SourcePositiveIModelTestCurve θ') :
    naDuistermaatHeckman (F := OriginalFlagGeometry.ofOriginal ω Y hY) hbig' Γ =
      naDuistermaatHeckman (F := OriginalFlagGeometry.ofOriginal ω' Y' hY') hbig' Γ := by
  have := naDuistermaatHeckman_finite (F := OriginalFlagGeometry.ofOriginal ω Y hY) hbig' Γ
  have := naDuistermaatHeckman_finite (F := OriginalFlagGeometry.ofOriginal ω' Y' hY') hbig' Γ
  apply measure_eq_of_Ici_of_Ioi_eq_zero _ _ Γ.val.max
  · exact naDuistermaatHeckman_Ioi_max (F := OriginalFlagGeometry.ofOriginal ω Y hY) hbig' Γ
  · exact naDuistermaatHeckman_Ioi_max (F := OriginalFlagGeometry.ofOriginal ω' Y' hY') hbig' Γ
  · intro t ht
    rw [naDuistermaatHeckman_Ici (F := OriginalFlagGeometry.ofOriginal ω Y hY) hbig' Γ ⟨t, ht⟩,
      naDuistermaatHeckman_Ici (F := OriginalFlagGeometry.ofOriginal ω' Y' hY') hbig' Γ ⟨t, ht⟩]
    rfl

end FlagIndependence

end SGPT.NAPotential.DH
