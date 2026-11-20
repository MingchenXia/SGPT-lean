import SGPT.Convex.AlexandrovMass
import SGPT.Convex.MixedAlexandrovFunctional

set_option autoImplicit false

/-!
# Bounded Legendre integral variation

Actual full-mass conjugate gradients attain the original Fenchel costs almost
everywhere. Integrating the two touching inequalities produces the original
factorial-normalized variation sandwich, without an energy identity premise.
This is the convex variation step in SGPT `prop:Etoric`.
-/

noncomputable section

namespace SGPT.Convex

open Set Filter MeasureTheory SGPT.PSH
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "B" => innerₗ E

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Two original finite bounded-growth inputs produce one genuine global gap bound. -/
theorem boundedGrowthPair_exists_abs_sub_le {P : Set E} {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    ∃ C : ℝ, ∀ x, |g.val x - f.val x| ≤ C := by
  have hfg := singularityEquiv_trans hf.2 (singularityEquiv_symm hg.2)
  obtain ⟨A, hA⟩ := (singularityLE_iff_exists_real _ _).mp hfg.1
  obtain ⟨D, hD⟩ := (singularityLE_iff_exists_real _ _).mp hfg.2
  refine ⟨|A| + |D|, fun x => ?_⟩
  have ha : f.val x ≤ g.val x + A := by
    simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hA x
  have hd : g.val x ≤ f.val x + D := by
    simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hD x
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self A, le_abs_self D, abs_nonneg A, abs_nonneg D]

/-- The actual conjugate's genuine finite bounds produce integrability on the body. -/
theorem integrable_conjugateToReal_of_mem_boundedGrowthClass
    (μ : Measure E) [μ.IsAddHaarMeasure] {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P) :
    Integrable (fun m => (conjugate B (fun x => (f.val x : EReal)) m).toReal)
      (μ.restrict P) := by
  let : IsFiniteMeasure (μ.restrict P) := ⟨by simpa using hP.measure_lt_top (μ := μ)⟩
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hf
  have hp := isProper_of_mem_boundedGrowthClass B hP hne hf
  have hcp := isProper_conjugate_of_isContPerfPair B hp
  have hfinite (m : E) (hm : m ∈ P) :
      conjugate B (fun x => (f.val x : EReal)) m =
        ((conjugate B (fun x => (f.val x : EReal)) m).toReal : EReal) := by
    exact (EReal.coe_toReal
      (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2) (hcp.2.2 m)).symm
  apply (integrable_const (|a| + |b|)).mono'
    (measurable_ereal_toReal.comp (measurable_conjugate B _)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hP.isClosed.measurableSet] with m hm
  have hbound := hab m hm
  rw [hfinite m hm] at hbound
  have ha : a ≤ (conjugate B (fun x => (f.val x : EReal)) m).toReal :=
    EReal.coe_le_coe_iff.mp hbound.1
  have hb : (conjugate B (fun x => (f.val x : EReal)) m).toReal ≤ b :=
    EReal.coe_le_coe_iff.mp hbound.2
  simp only [Real.norm_eq_abs, Function.comp_apply]
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]

/-- Genuine a.e. differentiability and inverse raw subgradients manufacture actual
Fenchel attainment; no touching or derivative certificate is an input. -/
theorem ae_conjugateGradient_fenchel_of_mem_fullMassClass
    (μ : Measure E) [μ.IsAddHaarMeasure] {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ FullMassClass B P) :
    ∀ᵐ m ∂μ.restrict P,
      (conjugate B (fun x => (f.val x : EReal)) m).toReal =
        B (conjugateGradient B (fun x => (f.val x : EReal)) m) m -
          f.val (conjugateGradient B (fun x => (f.val x : EReal)) m) := by
  let F : E → EReal := fun x => (f.val x : EReal)
  have hp : IsProper F := hf.1.1
  have hlsc : LowerSemicontinuous F := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_mem_growthClass B hP hne hf.1)
  have hcp := isProper_conjugate_of_isContPerfPair B hp
  have hInt := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass
    (ν := μ) B hP hne hconv hf
  have hd := ae_differentiableAt_toReal_of_isProper (μ := μ) hcp
  filter_upwards [ae_restrict_of_ae hInt, ae_restrict_of_ae hd,
    ae_restrict_mem hP.isClosed.measurableSet] with m hIm hdm hmP
  have hmI : m ∈ interior (effectiveDomain (conjugate B F)) := by
    change (interior (effectiveDomain (conjugate B (fun x => (f.val x : EReal))))) m
    exact Eq.mpr hIm hmP
  have hsingle := rawSubdifferential_conjugate_eq_singleton_of_differentiableAt
    B hp hmI (hdm hmI)
  let x := conjugateGradient B F m
  have hxdual : x ∈ rawSubdifferential (innerₗ E).flip (conjugate B F) m := by
    rw [hsingle]
    exact mem_singleton _
  have hxD : x ∈ effectiveDomain F := EReal.coe_lt_top _
  have hmD := interior_subset hmI
  have hxraw := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential
    B hp hlsc hxD hmD).mpr hxdual
  have hxsub : m ∈ subdifferential B F x := by
    rwa [← rawSubdifferential_eq_subdifferential_of_isProper B hp]
  have heq := (mem_subdifferential_iff_fenchel B hp hxD).mp hxsub
  have hfinite : conjugate B F m = ((conjugate B F m).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hmD) (hcp.2.2 m)).symm
  change conjugate B F m = (B x m : EReal) - (f.val x : EReal) at heq
  rw [hfinite, ← EReal.coe_sub] at heq
  exact EReal.coe_injective heq

/-- The actual bounded Legendre variation inequality with the original dimension
factorial and genuine original Alexandrov integrals on both endpoints. -/
theorem integral_conjugate_variation_bounds
    (μ : Measure E) [μ.IsAddHaarMeasure] {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    (∫ x, (g.val x - f.val x) ∂alexandrovMeasure B μ (fun x => (g.val x : EReal))) ≤
      ((Module.finrank ℝ E).factorial : ℝ) *
        (∫ m in P, ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
          (conjugate B (fun x => (g.val x : EReal)) m).toReal) ∂μ) ∧
    ((Module.finrank ℝ E).factorial : ℝ) *
        (∫ m in P, ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
          (conjugate B (fun x => (g.val x : EReal)) m).toReal) ∂μ) ≤
      ∫ x, (g.val x - f.val x) ∂alexandrovMeasure B μ (fun x => (f.val x : EReal)) := by
  let F : E → EReal := fun x => (f.val x : EReal)
  let G : E → EReal := fun x => (g.val x : EReal)
  let h : E → ℝ := fun x => g.val x - f.val x
  let D : E → ℝ := fun m => (conjugate B F m).toReal - (conjugate B G m).toReal
  have hF := mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hf
  have hG := mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hg
  have hDi : Integrable D (μ.restrict P) :=
    (integrable_conjugateToReal_of_mem_boundedGrowthClass μ hP hne hconv hf).sub
      (integrable_conjugateToReal_of_mem_boundedGrowthClass μ hP hne hconv hg)
  have hh : Measurable h :=
    (continuousOn_univ.mp (g.property.continuousOn isOpen_univ)).measurable.sub
      (continuousOn_univ.mp (f.property.continuousOn isOpen_univ)).measurable
  obtain ⟨C, hC⟩ := boundedGrowthPair_exists_abs_sub_le hf hg
  let : IsFiniteMeasure (μ.restrict P) := ⟨by simpa using hP.measure_lt_top (μ := μ)⟩
  have hgrad (K : E → EReal) :
      Integrable (fun m => h (conjugateGradient B K m)) (μ.restrict P) := by
    apply (integrable_const C).mono'
      (hh.comp (measurable_conjugateGradient B K)).aestronglyMeasurable
    exact Eventually.of_forall (fun m => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, h] using hC _)
  have htouchF := ae_conjugateGradient_fenchel_of_mem_fullMassClass μ hP hne hconv hF
  have htouchG := ae_conjugateGradient_fenchel_of_mem_fullMassClass μ hP hne hconv hG
  have hAE : ∀ᵐ m ∂μ.restrict P,
      h (conjugateGradient B G m) ≤ D m ∧ D m ≤ h (conjugateGradient B F m) := by
    filter_upwards [htouchF, htouchG, ae_restrict_mem hP.isClosed.measurableSet]
      with m hmF hmG hmP
    have hmDF : m ∈ effectiveDomain (conjugate B F) := by
      rw [effectiveDomain_conjugate_eq_of_mem_boundedGrowthClass B hP hconv hf]
      exact hmP
    have hmDG : m ∈ effectiveDomain (conjugate B G) := by
      rw [effectiveDomain_conjugate_eq_of_mem_boundedGrowthClass B hP hconv hg]
      exact hmP
    have hFp := isProper_conjugate_of_isContPerfPair B hF.1.1
    have hGp := isProper_conjugate_of_isContPerfPair B hG.1.1
    have hFfinite : conjugate B F m = ((conjugate B F m).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hmDF) (hFp.2.2 m)).symm
    have hGfinite : conjugate B G m = ((conjugate B G m).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hmDG) (hGp.2.2 m)).symm
    have hcostF := le_iSup (fun x => (B x m : EReal) - F x) (conjugateGradient B G m)
    have hcostG := le_iSup (fun x => (B x m : EReal) - G x) (conjugateGradient B F m)
    change _ ≤ conjugate B F m at hcostF
    change _ ≤ conjugate B G m at hcostG
    change (B (conjugateGradient B G m) m : EReal) -
      (f.val (conjugateGradient B G m) : EReal) ≤ _ at hcostF
    change (B (conjugateGradient B F m) m : EReal) -
      (g.val (conjugateGradient B F m) : EReal) ≤ _ at hcostG
    rw [hFfinite, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hcostF
    rw [hGfinite, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hcostG
    change _ = B (conjugateGradient B F m) m - f.val (conjugateGradient B F m) at hmF
    change _ = B (conjugateGradient B G m) m - g.val (conjugateGradient B G m) at hmG
    dsimp only [h, D]
    constructor <;> linarith
  have hl := integral_mono_ae (hgrad G) hDi (hAE.mono (fun _ hm => hm.1))
  have hr := integral_mono_ae hDi (hgrad F) (hAE.mono (fun _ hm => hm.2))
  have hfac : 0 ≤ ((Module.finrank ℝ E).factorial : ℝ) := Nat.cast_nonneg _
  have hl' := mul_le_mul_of_nonneg_left hl hfac
  have hr' := mul_le_mul_of_nonneg_left hr hfac
  rw [← integral_alexandrovMeasure_of_mem_fullMassClass B hP hne hconv hG hh] at hl'
  rw [← integral_alexandrovMeasure_of_mem_fullMassClass B hP hne hconv hF hh] at hr'
  exact ⟨hl', hr'⟩

end SGPT.Convex
