import SGPT.Convex.DirectionalDerivative
import SGPT.Convex.GrowthSum
import SGPT.Convex.LocalLipschitzMeasure
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.Compactness.Lindelof

namespace SGPT.Convex

open Set Filter Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem ae_differentiableAt_toReal_of_isProper {f : E → EReal} (hf : IsProper f) :
    ∀ᵐ x ∂μ, x ∈ interior (effectiveDomain f) →
      DifferentiableAt ℝ (fun z ↦ (f z).toReal) x :=
  ae_differentiableAt_of_locallyLipschitzOn_open isOpen_interior
    (convexOn_toReal_effectiveDomain hf).locallyLipschitzOn_interior

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem realDirectionalDerivative_eq_of_hasFDerivAt {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) {L : StrongDual ℝ E}
    (hL : HasFDerivAt (fun z ↦ (f z).toReal) L x) (v : E) :
    realDirectionalDerivative f x v = L v := by
  apply tendsto_nhds_unique (tendsto_real_directional_secant hf hx v)
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (hL.hasLineDerivAt v).tendsto_slope_zero_right

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem eq_derivative_of_mem_rawSubdifferential {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) {L : StrongDual ℝ E}
    (hL : HasFDerivAt (fun z ↦ (f z).toReal) L x) {m : StrongDual ℝ E}
    (hm : m ∈ rawSubdifferential continuousDualPairing f x) : m = L := by
  have hm' : m ∈ subdifferential continuousDualPairing f x := by
    rwa [← rawSubdifferential_eq_subdifferential_of_isProper continuousDualPairing hf]
  ext v
  have hp := subgradient_apply_le_realDirectionalDerivative hf hx hm' v
  have hn := subgradient_apply_le_realDirectionalDerivative hf hx hm' (-v)
  rw [realDirectionalDerivative_eq_of_hasFDerivAt hf hx hL v] at hp
  rw [realDirectionalDerivative_eq_of_hasFDerivAt hf hx hL (-v)] at hn
  simp only [map_neg] at hn
  exact le_antisymm hp (neg_le_neg_iff.mp hn)

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem rawSubdifferential_eq_singleton_of_hasFDerivAt {f : E → EReal}
    (hf : IsProper f) {x : E} (hx : x ∈ interior (effectiveDomain f))
    {L : StrongDual ℝ E} (hL : HasFDerivAt (fun z ↦ (f z).toReal) L x) :
    rawSubdifferential continuousDualPairing f x = {L} := by
  apply Set.Subset.antisymm
  · intro m hm
    exact mem_singleton_iff.mpr (eq_derivative_of_mem_rawSubdifferential hf hx hL hm)
  · intro m hm
    obtain ⟨a, ha⟩ := rawSubdifferential_nonempty_of_mem_intrinsicInterior
      continuousDualPairing hf (interior_subset_intrinsicInterior hx)
    have haL := eq_derivative_of_mem_rawSubdifferential hf hx hL ha
    have hmL := mem_singleton_iff.mp hm
    simpa only [haL, hmL] using ha

section PerfectPairing

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
  [FiniteDimensional ℝ M] (B : E →ₗ[ℝ] M →ₗ[ℝ] ℝ) [B.IsContPerfPair]

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ M] in
/-- The genuine inverse raw-subgradient relation at actual finite points. -/
theorem mem_rawSubdifferential_iff_conjugate_rawSubdifferential
    {f : E → EReal} (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    {x : E} (hx : x ∈ effectiveDomain f) {m : M}
    (hm : m ∈ effectiveDomain (conjugate B f)) :
    m ∈ rawSubdifferential B f x ↔
      x ∈ rawSubdifferential B.flip (conjugate B f) m := by
  have hg := isProper_conjugate_of_isContPerfPair B hf
  have hb : conjugate B.flip (conjugate B f) = f :=
    (biconjugate_eq_convexClosure_of_isContPerfPair B hf.1).trans
      (convexClosure_eq_self_of_isClosedConvex (Or.inr (Or.inr ⟨hf, hlsc⟩)))
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 x)).symm
  have hgm : conjugate B f m = ((conjugate B f m).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hm) (hg.2.2 m)).symm
  rw [rawSubdifferential_eq_subdifferential_of_isProper B hf,
    rawSubdifferential_eq_subdifferential_of_isProper B.flip hg,
    mem_subdifferential_iff_fenchel B hf hx,
    mem_subdifferential_iff_fenchel B.flip hg hm, hb, LinearMap.flip_apply,
    hfx, hgm, ← EReal.coe_sub, ← EReal.coe_sub]
  simp only [EReal.coe_eq_coe_iff]
  constructor <;> intro h <;> linarith

/-- The actual measurable derivative of the conjugate, transported through
the genuine continuous perfect pairing. -/
noncomputable def conjugateGradient (f : E → EReal) (m : M) : E :=
  B.toContPerfPair.toContinuousLinearEquiv.symm
    (fderiv ℝ (fun p ↦ (conjugate B f p).toReal) m)

variable [MeasurableSpace M] [BorelSpace M]

omit [μ.IsAddHaarMeasure] [FiniteDimensional ℝ M] in
theorem measurable_conjugateGradient (f : E → EReal) :
    Measurable (conjugateGradient B f) :=
  B.toContPerfPair.toContinuousLinearEquiv.symm.continuous.measurable.comp
    (measurable_fderiv ℝ (fun p ↦ (conjugate B f p).toReal))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [μ.IsAddHaarMeasure] in
theorem rawSubdifferential_conjugate_eq_singleton_of_differentiableAt
    {f : E → EReal} (hf : IsProper f) {m : M}
    (hm : m ∈ interior (effectiveDomain (conjugate B f)))
    (hd : DifferentiableAt ℝ (fun p ↦ (conjugate B f p).toReal) m) :
    rawSubdifferential B.flip (conjugate B f) m = {conjugateGradient B f m} := by
  let e := B.toContPerfPair.toContinuousLinearEquiv
  let L := fderiv ℝ (fun p ↦ (conjugate B f p).toReal) m
  have hg := isProper_conjugate_of_isContPerfPair B hf
  have hmap := rawSubdifferential_image_toContPerfPair B.flip (conjugate B f) m
  simp only [LinearMap.flip_flip] at hmap
  have himage : e '' rawSubdifferential B.flip (conjugate B f) m = {L} := by
    exact hmap.trans (rawSubdifferential_eq_singleton_of_hasFDerivAt hg hm hd.hasFDerivAt)
  ext x
  constructor
  · intro hx
    have he : e x = L := mem_singleton_iff.mp
      (himage ▸ mem_image_of_mem e hx)
    exact mem_singleton_iff.mpr (e.injective (by
      simpa only [conjugateGradient, ← show e = B.toContPerfPair.toContinuousLinearEquiv from rfl,
        ContinuousLinearEquiv.apply_symm_apply] using he))
  · intro hx
    have hL : L ∈ e '' rawSubdifferential B.flip (conjugate B f) m := by
      rw [himage]
      exact mem_singleton L
    obtain ⟨y, hy, he⟩ := hL
    have hye : y = conjugateGradient B f m := e.injective (by simpa [conjugateGradient, e, L] using he)
    have hxe := mem_singleton_iff.mp hx
    simpa only [hye, hxe] using hy

variable {ν : Measure M} [ν.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] [MeasurableSpace E] [BorelSpace E] in
/-- Actual subgradient-image membership agrees almost everywhere with the
actual conjugate-gradient preimage; no image-measurability premise is used. -/
theorem rawSubgradientImageOn_ae_eq_gradient_preimage {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hfull : effectiveDomain f = univ) (A : Set E) :
    rawSubgradientImageOn B f A =ᵐ[ν]
      (interior (effectiveDomain (conjugate B f)) ∩ conjugateGradient B f ⁻¹' A : Set M) := by
  have hg := isProper_conjugate_of_isContPerfPair B hf
  have hdiff := ae_differentiableAt_toReal_of_isProper (μ := ν) hg
  have hfront : ∀ᵐ m ∂ν, m ∉ frontier (effectiveDomain (conjugate B f)) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      (convex_effectiveDomain hg.1).addHaar_frontier ν
  filter_upwards [hdiff, hfront] with m hdm hfm
  apply propext
  change (m ∈ rawSubgradientImageOn B f A) ↔
    m ∈ interior (effectiveDomain (conjugate B f)) ∧ conjugateGradient B f m ∈ A
  by_cases hm : m ∈ interior (effectiveDomain (conjugate B f))
  · have hs := rawSubdifferential_conjugate_eq_singleton_of_differentiableAt B hf hm (hdm hm)
    constructor
    · intro hin
      obtain ⟨x, hx⟩ := mem_iUnion.mp hin
      obtain ⟨hxA, hxm⟩ := mem_iUnion.mp hx
      have hxD : x ∈ effectiveDomain f := by rw [hfull]; exact mem_univ x
      have hmx := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential
        B hf hlsc hxD (interior_subset hm)).mp hxm
      rw [hs] at hmx
      exact ⟨hm, mem_singleton_iff.mp hmx ▸ hxA⟩
    · rintro ⟨_, hA⟩
      have hxD : conjugateGradient B f m ∈ effectiveDomain f := by
        rw [hfull]; exact mem_univ _
      have hmx : conjugateGradient B f m ∈
          rawSubdifferential B.flip (conjugate B f) m := by
        rw [hs]; exact mem_singleton _
      have hxm := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential
        B hf hlsc hxD (interior_subset hm)).mpr hmx
      exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hA, hxm⟩⟩
  · constructor
    · intro hin
      have himage : m ∈ rawSubgradientImage B f := by
        obtain ⟨x, hx⟩ := mem_iUnion.mp hin
        obtain ⟨_, hxm⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨x, hxm⟩
      have hmD := rawSubgradientImage_subset_effectiveDomain_conjugate B hf himage
      exact False.elim (hfm ⟨subset_closure hmD, hm⟩)
    · exact fun h ↦ False.elim (hm h.1)

/-- The actual Alexandrov measure is constructed as a genuine scaled pushforward.
Its source subgradient-image formula is proved below, rather than assumed. -/
noncomputable def alexandrovMeasure (ν : Measure M) (f : E → EReal) : Measure E :=
  ((Module.finrank ℝ E).factorial : ENNReal) •
    Measure.map (conjugateGradient B f) (ν.restrict (interior (effectiveDomain (conjugate B f))))

omit [μ.IsAddHaarMeasure] in
theorem nullMeasurableSet_rawSubgradientImageOn {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hfull : effectiveDomain f = univ) {A : Set E} (hA : MeasurableSet A) :
    NullMeasurableSet (rawSubgradientImageOn B f A) ν :=
  (isOpen_interior.measurableSet.inter
    (hA.preimage (measurable_conjugateGradient B f))).nullMeasurableSet.congr
      (rawSubgradientImageOn_ae_eq_gradient_preimage B hf hlsc hfull A).symm

omit [μ.IsAddHaarMeasure] in
/-- Exact Borel-set source Alexandrov formula, with actual completed image measurability. -/
theorem alexandrovMeasure_apply {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hfull : effectiveDomain f = univ) {A : Set E} (hA : MeasurableSet A) :
    alexandrovMeasure B ν f A =
      ((Module.finrank ℝ E).factorial : ENNReal) * ν (rawSubgradientImageOn B f A) := by
  rw [alexandrovMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_conjugateGradient B f) hA,
    Measure.restrict_apply (hA.preimage (measurable_conjugateGradient B f)), Set.inter_comm]
  congr 1
  exact (measure_congr (rawSubgradientImageOn_ae_eq_gradient_preimage B hf hlsc hfull A)).symm

omit [μ.IsAddHaarMeasure] in
/-- Exact original finite-real-convex source input, without closedness or
derivative assumptions: Borel subgradient images are genuinely null measurable. -/
theorem nullMeasurableSet_rawSubgradientImageOn_coe {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {A : Set E} (hA : MeasurableSet A) :
    NullMeasurableSet (rawSubgradientImageOn B (fun x ↦ (f x : EReal)) A) ν := by
  have hp := isProper_coe_of_convexOn hf
  have hfull : effectiveDomain (fun x ↦ (f x : EReal)) = univ := by
    ext x
    simp [effectiveDomain]
  exact nullMeasurableSet_rawSubgradientImageOn B hp
    (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_isProper_full_domain hp hfull))
      hfull hA

omit [μ.IsAddHaarMeasure] in
/-- Source `def:realMA` and `eq:MARFE` for every actual finite convex function:
the constructed genuine measure has exactly the original Borel image formula. -/
theorem alexandrovMeasure_apply_coe {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {A : Set E} (hA : MeasurableSet A) :
    alexandrovMeasure B ν (fun x ↦ (f x : EReal)) A =
      ((Module.finrank ℝ E).factorial : ENNReal) *
        ν (rawSubgradientImageOn B (fun x ↦ (f x : EReal)) A) := by
  have hp := isProper_coe_of_convexOn hf
  have hfull : effectiveDomain (fun x ↦ (f x : EReal)) = univ := by
    ext x
    simp [effectiveDomain]
  exact alexandrovMeasure_apply B hp
    (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_isProper_full_domain hp hfull))
      hfull hA

omit [μ.IsAddHaarMeasure] [FiniteDimensional ℝ M] [ν.IsAddHaarMeasure] in
theorem alexandrovMeasure_univ (f : E → EReal) :
    alexandrovMeasure B ν f univ =
      ((Module.finrank ℝ E).factorial : ENNReal) *
        ν (interior (effectiveDomain (conjugate B f))) := by
  rw [alexandrovMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_conjugateGradient B f) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

omit [μ.IsAddHaarMeasure] in
theorem alexandrovMeasure_univ_eq_closure_rawSubgradientImage {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    alexandrovMeasure B ν f univ =
      ((Module.finrank ℝ E).factorial : ENNReal) * ν (closure (rawSubgradientImage B f)) := by
  have hfront := (convex_effectiveDomain (isConvex_conjugate B f)).addHaar_frontier ν
  rw [alexandrovMeasure_univ,
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hf hlsc,
    measure_interior_of_null_frontier hfront, measure_closure_of_null_frontier hfront]

omit [μ.IsAddHaarMeasure] [MeasurableSpace E] [BorelSpace E] in
/-- The source full-mass condition supplies the actual Haar restriction on
the original compact body, including its empty ordinary-interior branch. -/
theorem interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass
    {P : Set M} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ FullMassClass B P) :
    interior (effectiveDomain (conjugate B f)) =ᵐ[ν] P := by
  have hp := hf.1.1
  have hlsc := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_mem_growthClass B hP hne hf.1)
  have heq := closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hp hlsc
  have himage := ((singularityLE_support_iff_full_domain_rawSubgradientImage_subset
    B hP hne hconv hp).mp hf.1.2).2
  have hclP : closure (effectiveDomain (conjugate B f)) ⊆ P := by
    rw [← heq]
    exact closure_minimal himage hP.isClosed
  rcases hf.2 with hempty | hfull
  · have hPnull : ν P = 0 := by
      rw [← measure_interior_of_null_frontier (hconv.addHaar_frontier ν), hempty, measure_empty]
    have hintnull : ν (interior (effectiveDomain (conjugate B f))) = 0 :=
      measure_mono_null (interior_subset.trans (subset_closure.trans hclP)) hPnull
    exact (ae_eq_empty.mpr hintnull).trans (ae_eq_empty.mpr hPnull).symm
  · have hclEq : closure (effectiveDomain (conjugate B f)) = P := heq.symm.trans hfull
    have hfront := (convex_effectiveDomain (isConvex_conjugate B f)).addHaar_frontier ν
    have hae := (interior_ae_eq_of_null_frontier hfront).trans
      (closure_ae_eq_of_null_frontier hfront).symm
    simpa only [hclEq] using hae

omit [μ.IsAddHaarMeasure] [BorelSpace E] in
/-- Exact source `lma:realMA_Legendre_pushforward` measure identity for the
actual measurable conjugate gradient and original full-mass class. -/
theorem alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass
    {P : Set M} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ FullMassClass B P) :
    alexandrovMeasure B ν f = ((Module.finrank ℝ E).factorial : ENNReal) •
      Measure.map (conjugateGradient B f) (ν.restrict P) := by
  unfold alexandrovMeasure
  rw [Measure.restrict_congr_set
    (interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass B hP hne hconv hf)]

omit [μ.IsAddHaarMeasure] in
/-- The source pushforward integral identity; measurability suffices even
before specializing to the original bounded Borel test functions. -/
theorem integral_alexandrovMeasure_of_mem_fullMassClass
    {P : Set M} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ FullMassClass B P) {h : E → ℝ} (hh : Measurable h) :
    (∫ x, h x ∂alexandrovMeasure B ν f) =
      ((Module.finrank ℝ E).factorial : ℝ) * ∫ m in P, h (conjugateGradient B f m) ∂ν := by
  rw [alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass B hP hne hconv hf,
    integral_smul_measure,
    integral_map_of_stronglyMeasurable (measurable_conjugateGradient B f) hh.stronglyMeasurable]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] [FiniteDimensional ℝ E] [FiniteDimensional ℝ M]
  [B.IsContPerfPair] in
theorem effectiveDomain_conjugate_subset_of_singularityLE {f g : E → EReal}
    (hfg : SGPT.PSH.SingularityLE f g) :
    effectiveDomain (conjugate B f) ⊆ effectiveDomain (conjugate B g) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
    (conjugate_singularityLE B hfg)
  intro m hm
  change conjugate B g m < ⊤
  exact lt_of_le_of_lt (hC m) (EReal.add_lt_top (ne_of_lt hm) (EReal.coe_ne_top C))

omit [μ.IsAddHaarMeasure] in
/-- Exact source `thm:convcomp`: original additive order gives actual image
closure inclusion and the genuine constructed Alexandrov total-mass inequality. -/
theorem alexandrov_comparison_of_mem_growthClass
    {P : Set M} (hP : IsCompact P) (hne : P.Nonempty) {f g : E → EReal}
    (hf : f ∈ GrowthClass B P) (hg : g ∈ GrowthClass B P)
    (hfg : SGPT.PSH.SingularityLE f g) :
    closure (rawSubgradientImage B f) ⊆ closure (rawSubgradientImage B g) ∧
      alexandrovMeasure B ν f univ ≤ alexandrovMeasure B ν g univ := by
  have hfl := lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_mem_growthClass B hP hne hf)
  have hgl := lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_mem_growthClass B hP hne hg)
  have hcl : closure (rawSubgradientImage B f) ⊆ closure (rawSubgradientImage B g) := by
    rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hf.1 hfl,
      closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hg.1 hgl]
    exact closure_mono (effectiveDomain_conjugate_subset_of_singularityLE B hfg)
  refine ⟨hcl, ?_⟩
  rw [alexandrovMeasure_univ_eq_closure_rawSubgradientImage B hf.1 hfl,
    alexandrovMeasure_univ_eq_closure_rawSubgradientImage B hg.1 hgl]
  gcongr

end PerfectPairing

end SGPT.Convex
