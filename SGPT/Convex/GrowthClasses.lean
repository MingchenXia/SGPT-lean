import SGPT.Convex.SupportGrowth
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace SGPT.Convex
open Set Filter MeasureTheory
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual source proper compact-support growth class. -/
def GrowthClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) : Set (E → EReal) :=
  {f | IsProper f ∧ SGPT.PSH.SingularityLE f (support B.flip P)}

/-- Actual source closed functions with bounded mutual support comparison. -/
def BoundedGrowthClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) : Set (E → EReal) :=
  {f | IsClosedConvex f ∧ SGPT.PSH.SingularityEquiv f (support B.flip P)}

/-- Actual source full-mass class, with its explicit empty-interior branch. -/
def FullMassClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) : Set (E → EReal) :=
  {f | f ∈ GrowthClass B P ∧
    (interior P = ∅ ∨ closure (rawSubgradientImage B f) = P)}

/-- The original positive and negative extended-real parts, without projecting
infinite values to real zero. On the source classes the negative integral is finite. -/
noncomputable def extendedSignedIntegral [MeasurableSpace F] (μ : Measure F)
    (g : F → EReal) : EReal :=
  ((∫⁻ y, (g y).toENNReal ∂μ) : EReal) - ((∫⁻ y, (-g y).toENNReal ∂μ) : EReal)

/-- Actual source finite signed conjugate integral on the original support. -/
def EnergyOneClass [MeasurableSpace F] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F)
    (μ : Measure F) : Set (E → EReal) :=
  {f | f ∈ FullMassClass B P ∧ extendedSignedIntegral (μ.restrict P) (conjugate B f) < ⊤}

/-- Actual finite additive comparison reverses under finite-real subtraction. -/
theorem real_sub_le_real_sub_add (a C : ℝ) {u v : EReal}
    (h : u ≤ v + (C : EReal)) :
    (a : EReal) - v ≤ (a : EReal) - u + (C : EReal) := by
  cases u using EReal.rec <;> cases v using EReal.rec <;>
    simp_all [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

/-- Genuine source global additive comparison reverses under the actual
conjugate supremum, preserving every infinite value. -/
theorem conjugate_singularityLE (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f g : E → EReal}
    (hfg : SGPT.PSH.SingularityLE f g) :
    SGPT.PSH.SingularityLE (conjugate B g) (conjugate B f) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real f g).mp hfg
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨C, fun m ↦ ?_⟩
  apply iSup_le
  intro x
  exact (real_sub_le_real_sub_add (B x m) C (hC x)).trans
    (add_le_add (le_iSup (fun y ↦ (B y m : EReal) - f y) x) le_rfl)

/-- Actual source mutual comparison reverses under conjugation. -/
theorem conjugate_singularityEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f g : E → EReal}
    (hfg : SGPT.PSH.SingularityEquiv f g) :
    SGPT.PSH.SingularityEquiv (conjugate B f) (conjugate B g) :=
  ⟨conjugate_singularityLE B hfg.2, conjugate_singularityLE B hfg.1⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The genuine nonempty support takes exactly zero at zero. -/
theorem support_zero_of_nonempty (B : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) {P : Set F}
    (hne : P.Nonempty) : support B P 0 = 0 := by
  let : Nonempty P := hne.to_subtype
  simp [support]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The checked actual support-growth producer supplies the whole source domain. -/
theorem effectiveDomain_eq_univ_of_mem_growthClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    {f : E → EReal} (hf : f ∈ GrowthClass B P) : effectiveDomain f = univ :=
  effectiveDomain_eq_univ_of_singularityLE_support B hP hne hf.2

omit [FiniteDimensional ℝ F] in
/-- Actual closure agreement at every full-domain point proves source closedness. -/
theorem isClosedConvex_of_mem_growthClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    {f : E → EReal} (hf : f ∈ GrowthClass B P) : IsClosedConvex f := by
  have hDom := effectiveDomain_eq_univ_of_mem_growthClass B hP hne hf
  apply (convexClosure_eq_self_iff_isClosedConvex hf.1.1).mp
  funext x
  rw [convexClosure_of_forall_ne_bot hf.1.2.2]
  apply regularization_eq_of_mem_intrinsicInterior hf.1
  apply interior_subset_intrinsicInterior
  simp [hDom]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Actual finite support and both actual comparisons exclude the two improper
closed constants in the original E-infinity definition. -/
theorem isProper_of_mem_boundedGrowthClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [B.IsContPerfPair] {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    {f : E → EReal} (hf : f ∈ BoundedGrowthClass B P) : IsProper f := by
  obtain ⟨r, hr⟩ := exists_real_support_value B hP hne (0 : E)
  rcases hf.1 with hbot | htop | hproper
  · obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2.2
    have h := hC 0
    rw [hr, hbot] at h
    simp only [EReal.bot_add] at h
    exact False.elim ((EReal.coe_ne_bot r) (bot_unique h))
  · obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2.1
    have h := hC 0
    rw [hr, htop, ← EReal.coe_add] at h
    exact False.elim ((EReal.coe_ne_top (r + C)) (top_unique h))
  · exact hproper.1

omit [FiniteDimensional ℝ E] in
/-- Both original comparisons transport to the actual support indicator. -/
theorem conjugate_singularityEquiv_indicator_of_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal}
    (hf : f ∈ BoundedGrowthClass B P) :
    SGPT.PSH.SingularityEquiv (conjugate B f) (indicator P) := by
  have h := conjugate_singularityEquiv B hf.2
  rwa [conjugate_support_of_isContPerfPair B hconv hP.isClosed] at h

omit [FiniteDimensional ℝ E] in
/-- Exact source boundedness on the original support, with actual finite
constants produced by the original global comparisons. -/
theorem conjugate_bounds_of_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal}
    (hf : f ∈ BoundedGrowthClass B P) :
    ∃ a b : ℝ, ∀ m ∈ P, (a : EReal) ≤ conjugate B f m ∧ conjugate B f m ≤ (b : EReal) := by
  have heq := conjugate_singularityEquiv_indicator_of_mem_boundedGrowthClass B hP hconv hf
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp heq.1
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp heq.2
  refine ⟨-D, C, fun m hm ↦ ⟨?_, ?_⟩⟩
  · have h : (0 : EReal) ≤ conjugate B f m + (D : EReal) := by
      simpa only [indicator, if_pos hm] using hD m
    have h' := EReal.sub_le_of_le_add h
    simpa only [zero_sub, EReal.coe_neg] using h'
  · simpa only [indicator, if_pos hm, zero_add] using hC m

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Direct extended-real form of the actual zero-test bound. -/
theorem coe_lower_bound_conjugate_from_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    {f : E → EReal} (hf : IsProper f) (hzero : (0 : E) ∈ effectiveDomain f) (m : F) :
    ((-(f 0).toReal : ℝ) : EReal) ≤ conjugate B f m := by
  have hfinite : f 0 = ((f 0).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hzero) (hf.2.2 0)).symm
  have h := le_iSup (fun x ↦ (B x m : EReal) - f x) (0 : E)
  rw [show B 0 m = 0 by simp, hfinite, EReal.coe_zero, zero_sub, ← EReal.coe_neg] at h
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Actual finite upper bounds on a finite-measure set make the genuine
positive-part lintegral finite, without projecting infinite values away. -/
theorem lintegral_toENNReal_lt_top_of_bound [MeasurableSpace F]
    (μ : Measure F) {P : Set F} (hμ : μ P < ⊤) {g : F → EReal} {r : ℝ}
    (hbound : ∀ m ∈ P, g m ≤ (r : EReal)) :
    ∫⁻ m in P, (g m).toENNReal ∂μ < ⊤ := by
  apply lt_of_le_of_lt (setLIntegral_mono measurable_const
    (fun m hm ↦ EReal.toENNReal_le_toENNReal (hbound m hm)))
  rw [setLIntegral_const, EReal.real_coe_toENNReal]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- A finite actual negative-part lintegral makes signed finiteness precisely
positive-part finiteness. The top value is preserved on the positive branch. -/
theorem extendedSignedIntegral_lt_top_iff [MeasurableSpace F]
    (μ : Measure F) (g : F → EReal) (hneg : ∫⁻ m, (-g m).toENNReal ∂μ < ⊤) :
    extendedSignedIntegral μ g < ⊤ ↔ ∫⁻ m, (g m).toENNReal ∂μ < ⊤ := by
  rw [extendedSignedIntegral, ← EReal.coe_ennreal_toReal hneg.ne]
  constructor
  · intro h
    apply lt_top_iff_ne_top.mpr
    intro ht
    rw [ht, EReal.coe_ennreal_top, EReal.top_sub_coe] at h
    exact lt_irrefl _ h
  · intro h
    rw [← EReal.coe_ennreal_toReal h.ne, ← EReal.coe_sub]
    exact EReal.coe_lt_top _

omit [FiniteDimensional ℝ E] in
/-- Exact source off-support value, produced by the reversed actual comparison. -/
theorem conjugate_eq_top_of_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal}
    (hf : f ∈ BoundedGrowthClass B P) {m : F} (hm : m ∉ P) :
    conjugate B f m = ⊤ := by
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
    (conjugate_singularityEquiv_indicator_of_mem_boundedGrowthClass B hP hconv hf).2
  have h : (⊤ : EReal) ≤ conjugate B f m + (D : EReal) := by
    simpa only [indicator, if_neg hm] using hD m
  cases hval : conjugate B f m using EReal.rec
  · simp [hval] at h
  · simp [hval, ← EReal.coe_add] at h
  · rfl

omit [FiniteDimensional ℝ E] in
/-- The actual conjugate has exactly the original support as its finite domain. -/
theorem effectiveDomain_conjugate_eq_of_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal}
    (hf : f ∈ BoundedGrowthClass B P) : effectiveDomain (conjugate B f) = P := by
  obtain ⟨a, b, hb⟩ := conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hf
  ext m
  constructor
  · intro hm
    by_contra hout
    have ht := conjugate_eq_top_of_mem_boundedGrowthClass B hP hconv hf hout
    exact (ne_of_lt hm) ht
  · intro hm
    exact (hb m hm).2.trans_lt (EReal.coe_lt_top b)

/-- Actual closed-image/domain equality gives the original full-mass condition. -/
theorem mem_fullMassClass_of_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ BoundedGrowthClass B P) : f ∈ FullMassClass B P := by
  refine ⟨⟨isProper_of_mem_boundedGrowthClass B hP hne hf, hf.2.1⟩, Or.inr ?_⟩
  rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B
    (isProper_of_mem_boundedGrowthClass B hP hne hf)
    (lowerSemicontinuous_of_isClosedConvex hf.1),
    effectiveDomain_conjugate_eq_of_mem_boundedGrowthClass B hP hconv hf,
    hP.isClosed.closure_eq]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The actual source integral negative part is finite before signed subtraction. -/
theorem lintegral_neg_conjugate_lt_top_of_mem_growthClass
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) {f : E → EReal}
    (hf : f ∈ GrowthClass B P) :
    ∫⁻ m in P, (-conjugate B f m).toENNReal ∂μ < ⊤ := by
  have hzero : (0 : E) ∈ effectiveDomain f := by
    rw [effectiveDomain_eq_univ_of_mem_growthClass B hP hne hf]
    exact mem_univ 0
  apply lintegral_toENNReal_lt_top_of_bound μ hP.measure_lt_top
  intro m _
  have h := EReal.neg_le_neg_iff.mpr
    (coe_lower_bound_conjugate_from_zero B hf.1 hzero m)
  simpa only [EReal.coe_neg, neg_neg] using h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Signed finiteness on the source full-mass class is exactly actual
positive-part finiteness, including infinite positive conjugate values. -/
theorem mem_energyOneClass_iff
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) {f : E → EReal} :
    f ∈ EnergyOneClass B P μ ↔
      f ∈ FullMassClass B P ∧ ∫⁻ m in P, (conjugate B f m).toENNReal ∂μ < ⊤ := by
  constructor
  · intro hf
    exact ⟨hf.1, (extendedSignedIntegral_lt_top_iff _ _
      (lintegral_neg_conjugate_lt_top_of_mem_growthClass μ B hP hne hf.1.1)).mp hf.2⟩
  · intro hf
    exact ⟨hf.1, (extendedSignedIntegral_lt_top_iff _ _
      (lintegral_neg_conjugate_lt_top_of_mem_growthClass μ B hP hne hf.1.1)).mpr hf.2⟩

/-- The first source inclusion uses genuine finite conjugate bounds and the
actual Haar measure of the original compact support. -/
theorem boundedGrowthClass_subset_energyOneClass
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P) :
    BoundedGrowthClass B P ⊆ EnergyOneClass B P μ := by
  intro f hf
  rw [mem_energyOneClass_iff μ B hP hne]
  obtain ⟨a, b, hb⟩ := conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hf
  exact ⟨mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hf,
    lintegral_toENNReal_lt_top_of_bound μ hP.measure_lt_top (fun m hm ↦ (hb m hm).2)⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The second actual source inclusion. -/
theorem energyOneClass_subset_fullMassClass [MeasurableSpace F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) (μ : Measure F) :
    EnergyOneClass B P μ ⊆ FullMassClass B P := fun _ hf ↦ hf.1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The third actual source inclusion. -/
theorem fullMassClass_subset_growthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) :
    FullMassClass B P ⊆ GrowthClass B P := fun _ hf ↦ hf.1

omit [FiniteDimensional ℝ E] in
/-- Actual positive Haar uniqueness transports the genuine finiteness condition. -/
theorem lintegral_lt_top_iff_of_addHaarMeasure
    [MeasurableSpace F] [BorelSpace F] (μ ν : Measure F)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (P : Set F) (g : F → ENNReal) :
    (∫⁻ m in P, g m ∂μ < ⊤) ↔ ∫⁻ m in P, g m ∂ν < ⊤ := by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, setLIntegral_smul_measure]
  exact ENNReal.nnreal_smul_lt_top_iff
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'

omit [FiniteDimensional ℝ E] in
/-- The source E-one class is independent of the actual Lebesgue normalization. -/
theorem energyOneClass_eq_of_addHaarMeasure
    [MeasurableSpace F] [BorelSpace F] (μ ν : Measure F)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) :
    EnergyOneClass B P μ = EnergyOneClass B P ν := by
  ext f
  rw [mem_energyOneClass_iff μ B hP hne, mem_energyOneClass_iff ν B hP hne,
    lintegral_lt_top_iff_of_addHaarMeasure μ ν P]

omit [FiniteDimensional ℝ E] in
/-- The actual conjugate integrand is measurable for the source Lebesgue integral. -/
theorem measurable_conjugate [MeasurableSpace F] [BorelSpace F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Measurable (conjugate B f) :=
  (lowerSemicontinuous_conjugate B f).measurable

/-- Complete source growth inclusion chain for any original Lebesgue measure. -/
theorem growthClass_inclusions
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P) :
    BoundedGrowthClass B P ⊆ EnergyOneClass B P μ ∧
      EnergyOneClass B P μ ⊆ FullMassClass B P ∧ FullMassClass B P ⊆ GrowthClass B P :=
  ⟨boundedGrowthClass_subset_energyOneClass μ B hP hne hconv,
    energyOneClass_subset_fullMassClass B P μ, fullMassClass_subset_growthClass B P⟩

omit [FiniteDimensional ℝ E] in
/-- Complete original boundedness proposition, with the actual off-support value. -/
theorem conjugate_properties_of_mem_boundedGrowthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal}
    (hf : f ∈ BoundedGrowthClass B P) :
    (∀ m ∉ P, conjugate B f m = ⊤) ∧
      ∃ a b : ℝ, ∀ m ∈ P, (a : EReal) ≤ conjugate B f m ∧ conjugate B f m ≤ (b : EReal) :=
  ⟨fun _ hm ↦ conjugate_eq_top_of_mem_boundedGrowthClass B hP hconv hf hm,
    conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hf⟩

/-- The actual source maximum is attained at the original zero vector. -/
theorem isMaxOn_growth_difference_zero
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ GrowthClass B P) :
    IsMaxOn (fun x ↦ f x - support B.flip P x) univ 0 := by
  apply isMaxOn_iff.mpr
  intro x _
  rw [support_zero_of_nonempty B.flip hne, sub_zero]
  exact sharp_growth_bound_of_singularityLE_support B hP hne hconv hf.1 hf.2 x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The maximum has the exact original finite value f(0). -/
theorem growth_difference_zero_eq
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F} (hne : P.Nonempty) (f : E → EReal) :
    f 0 - support B.flip P 0 = f 0 := by
  rw [support_zero_of_nonempty B.flip hne, sub_zero]

/-- Actual attained maximum, rather than a target-shaped supremum certificate. -/
theorem growth_difference_iSup_eq_zero_value
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ GrowthClass B P) :
    (⨆ x, f x - support B.flip P x) = f 0 := by
  apply le_antisymm
  · exact iSup_le (sharp_growth_bound_of_singularityLE_support B hP hne hconv hf.1 hf.2)
  · exact (growth_difference_zero_eq B hne f).symm.le.trans
      (le_iSup (fun x ↦ f x - support B.flip P x) (0 : E))

end SGPT.Convex
