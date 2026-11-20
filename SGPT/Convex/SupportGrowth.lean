import SGPT.Convex.Subgradient
import SGPT.PSH.SingularityOrder

/-!
# Actual support growth and the source conjugate-domain characterization

The global comparison reuses the exact existing additive singularity API.
Actual support duality transports the checked full-dual producer. The sharp
growth bound tests a genuine destination subgradient at zero.
-/

namespace SGPT.Convex

open Set
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Genuine compact extrema make every actual nonempty compact support value finite. -/
theorem exists_real_support_value (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (x : E) :
    ∃ r : ℝ, support B.flip P x = (r : EReal) := by
  obtain ⟨p, hp, hmax⟩ := hP.exists_isMaxOn hne (B.toContPerfPair x).continuous.continuousOn
  refine ⟨B x p, le_antisymm ?_ ?_⟩
  · apply iSup_le
    intro q
    exact EReal.coe_le_coe (hmax q.property)
  · apply le_iSup_of_le (⟨p, hp⟩ : P)
    exact le_rfl

omit [FiniteDimensional ℝ E] in
/-- The actual continuous perfect pairing transports the checked full-dual
support-indicator producer, without repeating its separation argument. -/
theorem conjugate_support_of_isContPerfPair (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hconv : Convex ℝ P) (hclosed : IsClosed P) :
    conjugate B (support B.flip P) = indicator P := by
  let e : E ≃ₗ[ℝ] Module.Dual ℝ F := B.toContPerfPair.trans
    (LinearMap.toContinuousLinearMap : Module.Dual ℝ F ≃ₗ[ℝ] StrongDual ℝ F).symm
  have hreindex : conjugate B (support B.flip P) =
      conjugate (Module.Dual.eval ℝ F).flip (support (Module.Dual.eval ℝ F) P) := by
    funext m
    let G : Module.Dual ℝ F → EReal := fun L ↦
      (L m : EReal) - support (Module.Dual.eval ℝ F) P L
    change (⨆ x : E, G (e x)) = ⨆ L : Module.Dual ℝ F, G L
    exact e.toEquiv.iSup_comp
  rw [hreindex]
  exact conjugate_support_dual hconv hclosed

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Actual global support growth gives actual full effective domain. -/
theorem effectiveDomain_eq_univ_of_singularityLE_support
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) {f : E → EReal}
    (hfg : SGPT.PSH.SingularityLE f (support B.flip P)) : effectiveDomain f = univ := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hfg
  apply eq_univ_iff_forall.mpr
  intro x
  obtain ⟨r, hr⟩ := exists_real_support_value B hP hne x
  have h := hC x
  rw [hr, ← EReal.coe_add] at h
  exact h.trans_lt (EReal.coe_lt_top _)

/-- True global support growth excludes every actual conjugate-domain point
outside the actual compact convex support set. -/
theorem conjugate_eq_top_of_singularityLE_support
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hconv : Convex ℝ P) {f : E → EReal} (hf : IsProper f)
    (hfg : SGPT.PSH.SingularityLE f (support B.flip P))
    {m : F} (hm : m ∉ P) : conjugate B f m = ⊤ := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hfg
  by_contra htop
  have hnobot := (isProper_conjugate_of_isContPerfPair B hf).2.2 m
  let r : ℝ := (conjugate B f m).toReal
  have hfinite : conjugate B f m = (r : EReal) :=
    (EReal.coe_toReal htop hnobot).symm
  have hminor := (conjugate_le_coe_iff B f m r).mp hfinite.le
  have hbound : conjugate B (support B.flip P) m ≤ ((r + C : ℝ) : EReal) := by
    apply (conjugate_le_coe_iff B (support B.flip P) m (r + C)).mpr
    intro x
    have h := EReal.sub_le_of_le_add ((hminor x).trans (hC x))
    convert h using 1
    rw [← EReal.coe_sub]
    congr 1
    ring
  rw [conjugate_support_of_isContPerfPair B hconv hP.isClosed] at hbound
  simp only [indicator, if_neg hm] at hbound
  exact (EReal.coe_ne_top (r + C)) (top_unique hbound)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Genuine raw image/domain inclusion forces source covectors into the set
where the actual conjugate is not top. -/
theorem rawSubgradientImage_subset_of_conjugate_eq_top_outside
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {P : Set F} {f : E → EReal} (hf : IsProper f)
    (htop : ∀ m ∉ P, conjugate B f m = ⊤) : rawSubgradientImage B f ⊆ P := by
  intro m hm
  have hdom := rawSubgradientImage_subset_effectiveDomain_conjugate B hf hm
  by_contra hnot
  change conjugate B f m < ⊤ at hdom
  rw [htop m hnot] at hdom
  exact lt_irrefl _ hdom

omit [FiniteDimensional ℝ F] in
/-- The actual touching covector at the destination, tested at zero, gives
an actual sharp support growth bound without directional differentiation. -/
theorem le_support_add_zero_of_full_domain_rawSubgradientImage_subset
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F} {f : E → EReal}
    (hf : IsProper f) (hdom : effectiveDomain f = univ)
    (himage : rawSubgradientImage B f ⊆ P) (x : E) :
    f x ≤ support B.flip P x + f 0 := by
  have hxRI : x ∈ intrinsicInterior ℝ (effectiveDomain f) := by simp [hdom]
  obtain ⟨m, hm⟩ := rawSubdifferential_nonempty_of_mem_intrinsicInterior B hf hxRI
  have hmP : m ∈ P := himage (mem_iUnion.mpr ⟨x, hm⟩)
  have hfinite (y : E) : f y = ((f y).toReal : EReal) := by
    have hy : y ∈ effectiveDomain f := by simp [hdom]
    exact (EReal.coe_toReal (ne_of_lt hy) (hf.2.2 _)).symm
  have hneg : B (0 - x) m = -B x m := by simp
  have h := hm 0
  rw [hfinite x, hfinite 0, hneg, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have hreal : (f x).toReal ≤ B x m + (f 0).toReal := by linarith
  have hsupport : (B x m : EReal) ≤ support B.flip P x := by
    apply le_iSup_of_le (⟨m, hmP⟩ : P)
    exact le_rfl
  calc
    f x = ((f x).toReal : EReal) := hfinite x
    _ ≤ ((B x m + (f 0).toReal : ℝ) : EReal) := EReal.coe_le_coe hreal
    _ = (B x m : EReal) + f 0 := by rw [EReal.coe_add, ← hfinite 0]
    _ ≤ support B.flip P x + f 0 := add_le_add hsupport le_rfl

omit [FiniteDimensional ℝ F] in
/-- The actual sharp support estimate supplies the actual global source constant. -/
theorem singularityLE_support_of_full_domain_rawSubgradientImage_subset
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F} {f : E → EReal}
    (hf : IsProper f) (hdom : effectiveDomain f = univ)
    (himage : rawSubgradientImage B f ⊆ P) :
    SGPT.PSH.SingularityLE f (support B.flip P) := by
  have hzero : (0 : E) ∈ effectiveDomain f := by simp [hdom]
  have hfinite : f 0 = ((f 0).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hzero) (hf.2.2 _)).symm
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨(f 0).toReal, fun x ↦ ?_⟩
  rw [← hfinite]
  exact le_support_add_zero_of_full_domain_rawSubgradientImage_subset B hf hdom himage x

/-- Exact source support comparison iff full domain and top conjugate off the body. -/
theorem singularityLE_support_iff_full_domain_conjugate_eq_top_outside
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : IsProper f) :
    SGPT.PSH.SingularityLE f (support B.flip P) ↔
      effectiveDomain f = univ ∧ ∀ m ∉ P, conjugate B f m = ⊤ := by
  constructor
  · intro hfg
    exact ⟨effectiveDomain_eq_univ_of_singularityLE_support B hP hne hfg,
      fun m hm ↦ conjugate_eq_top_of_singularityLE_support B hP hconv hf hfg hm⟩
  · rintro ⟨hdom, htop⟩
    exact singularityLE_support_of_full_domain_rawSubgradientImage_subset B hf hdom
      (rawSubgradientImage_subset_of_conjugate_eq_top_outside B hf htop)

/-- Exact source support comparison iff full domain and the actual raw image lies in the body. -/
theorem singularityLE_support_iff_full_domain_rawSubgradientImage_subset
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : IsProper f) :
    SGPT.PSH.SingularityLE f (support B.flip P) ↔
      effectiveDomain f = univ ∧ rawSubgradientImage B f ⊆ P := by
  constructor
  · intro hfg
    obtain ⟨hdom, htop⟩ :=
      (singularityLE_support_iff_full_domain_conjugate_eq_top_outside B hP hne hconv hf).mp hfg
    exact ⟨hdom, rawSubgradientImage_subset_of_conjugate_eq_top_outside B hf htop⟩
  · rintro ⟨hdom, himage⟩
    exact singularityLE_support_of_full_domain_rawSubgradientImage_subset B hf hdom himage

/-- Complete source `prop:Fsuppchar`: both actual source equivalences. -/
theorem support_growth_characterization
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : IsProper f) :
    (SGPT.PSH.SingularityLE f (support B.flip P) ↔
      effectiveDomain f = univ ∧ ∀ m ∉ P, conjugate B f m = ⊤) ∧
    (SGPT.PSH.SingularityLE f (support B.flip P) ↔
      effectiveDomain f = univ ∧ rawSubgradientImage B f ⊆ P) :=
  ⟨singularityLE_support_iff_full_domain_conjugate_eq_top_outside B hP hne hconv hf,
    singularityLE_support_iff_full_domain_rawSubgradientImage_subset B hP hne hconv hf⟩

/-- Exact sharp estimate `eq:Fsupequal`, with the actual source constant f(0). -/
theorem sharp_growth_bound_of_singularityLE_support
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P : Set F}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : IsProper f)
    (hfg : SGPT.PSH.SingularityLE f (support B.flip P)) (x : E) :
    f x - support B.flip P x ≤ f 0 := by
  obtain ⟨hdom, himage⟩ :=
    (singularityLE_support_iff_full_domain_rawSubgradientImage_subset B hP hne hconv hf).mp hfg
  have h := le_support_add_zero_of_full_domain_rawSubgradientImage_subset B hf hdom himage x
  exact EReal.sub_le_of_le_add (by rwa [add_comm] at h)

end SGPT.Convex
