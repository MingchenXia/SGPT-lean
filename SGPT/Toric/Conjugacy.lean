import SGPT.Convex.PointwiseTopology
import SGPT.Convex.GrowthSum
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The original closed proper convex functions with top values off the original body. -/
def ClosedProperOnBody (P : Set F) : Set (F → EReal) :=
  {g | IsProper g ∧ LowerSemicontinuous g ∧ ∀ y ∉ P, g y = ⊤}

omit [FiniteDimensional ℝ F] in
/-- The true compact semicontinuous minimum is finite, by an actual original domain witness. -/
theorem exists_real_global_lower_bound_of_mem_closedProperOnBody
    {P : Set F} (hP : IsCompact P) {g : F → EReal} (hg : g ∈ ClosedProperOnBody P) :
    ∃ r : ℝ, ∀ y, (r : EReal) ≤ g y := by
  obtain ⟨z, hz⟩ := hg.1.2.1
  have hzP : z ∈ P := by
    by_contra h
    have ht := hg.2.2 z h
    change g z < ⊤ at hz
    rw [ht] at hz
    exact lt_irrefl _ hz
  obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨z, hzP⟩ hP (hg.2.1.lowerSemicontinuousOn P)
  have hptop : g p ≠ ⊤ := ne_of_lt ((hmin hzP).trans_lt hz)
  refine ⟨(g p).toReal, fun y ↦ ?_⟩
  rw [EReal.coe_toReal hptop (hg.1.2.2 p)]
  by_cases hy : y ∈ P
  · exact hmin hy
  · rw [hg.2.2 y hy]
    exact le_top

omit [FiniteDimensional ℝ F] in
/-- The actual finite minimum gives the genuine global additive indicator comparison. -/
theorem singularityLE_indicator_of_mem_closedProperOnBody
    {P : Set F} (hP : IsCompact P) {g : F → EReal} (hg : g ∈ ClosedProperOnBody P) :
    SGPT.PSH.SingularityLE (SGPT.Convex.indicator P) g := by
  classical
  obtain ⟨r, hr⟩ := exists_real_global_lower_bound_of_mem_closedProperOnBody hP hg
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨-r, fun y ↦ ?_⟩
  by_cases hy : y ∈ P
  · simp only [SGPT.Convex.indicator, if_pos hy]
    have hh := add_le_add (hr y) (le_refl ((-r : ℝ) : EReal))
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using hh
  · simp [SGPT.Convex.indicator, hy, hg.2.2 y hy]

omit [FiniteDimensional ℝ E] in
/-- Actual finite-additive conjugate reversal yields the original proper support-growth class. -/
theorem conjugate_mem_growthClass_of_mem_closedProperOnBody
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) {g : F → EReal} (hg : g ∈ ClosedProperOnBody P) :
    conjugate B.flip g ∈ GrowthClass B P := by
  refine ⟨isProper_conjugate_of_isContPerfPair B.flip hg.1, ?_⟩
  have hc := conjugate_singularityLE B.flip (singularityLE_indicator_of_mem_closedProperOnBody hP hg)
  rw [conjugate_indicator] at hc
  exact hc

/-- Original support growth produces actual closed proper conjugates with top values off the body. -/
theorem conjugate_mem_closedProperOnBody_of_mem_growthClass
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hconv : Convex ℝ P)
    {f : E → EReal} (hf : f ∈ GrowthClass B P) :
    conjugate B f ∈ ClosedProperOnBody P :=
  ⟨isProper_conjugate_of_isContPerfPair B hf.1,
    lowerSemicontinuous_conjugate B f,
    fun _y hy ↦ conjugate_eq_top_of_singularityLE_support B hP hconv hf.1 hf.2 hy⟩

/-- Literal conjugation and its reversal give actual inverse maps on the two original convex classes. -/
def growthClosedProperEquiv
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P) :
    {f // f ∈ GrowthClass B P} ≃ {g // g ∈ ClosedProperOnBody P} where
  toFun f := ⟨conjugate B f.val,
    conjugate_mem_closedProperOnBody_of_mem_growthClass B hP hconv f.property⟩
  invFun g := ⟨conjugate B.flip g.val,
    conjugate_mem_growthClass_of_mem_closedProperOnBody B hP g.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (biconjugate_eq_convexClosure_of_isContPerfPair B f.property.1.1).trans
      ((convexClosure_eq_self_iff_isClosedConvex f.property.1.1).mpr
        (isClosedConvex_of_mem_growthClass B hP hne f.property))
  right_inv g := by
    apply Subtype.ext
    exact (biconjugate_eq_convexClosure_of_isContPerfPair B.flip g.property.1.1).trans
      ((convexClosure_eq_self_iff_isClosedConvex g.property.1.1).mpr
        (Or.inr (Or.inr ⟨g.property.1, g.property.2.1⟩)))

omit [FiniteDimensional ℝ F] in
/-- Under original properness, this is exactly the source closed-convex predicate. -/
theorem mem_closedProperOnBody_iff {P : Set F} {g : F → EReal} :
    g ∈ ClosedProperOnBody P ↔ IsProper g ∧ IsClosedConvex g ∧ ∀ y ∉ P, g y = ⊤ := by
  constructor
  · intro hg
    exact ⟨hg.1, Or.inr (Or.inr ⟨hg.1, hg.2.1⟩), hg.2.2⟩
  · rintro ⟨hp, hc, ht⟩
    refine ⟨hp, ?_, ht⟩
    rcases hc with hb | htop | hproper
    · exact False.elim (hp.2.2 0 (congrFun hb 0))
    · obtain ⟨z, hz⟩ := hp.2.1
      change g z < ⊤ at hz
      rw [htop] at hz
      exact False.elim (lt_irrefl _ hz)
    · exact hproper.2

/-- The original real-valued convex support-growth class, without an extended-value substitution. -/
def RealGrowthClass (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) : Set (E → ℝ) :=
  {f | ConvexOn ℝ univ f ∧
    SGPT.PSH.SingularityLE (fun x ↦ (f x : EReal)) (support B.flip P)}

/-- Actual finite recovery identifies the original real and extended support-growth classes. -/
def realGrowthEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    {f // f ∈ RealGrowthClass B P} ≃ {f // f ∈ GrowthClass B P} where
  toFun f := ⟨fun x ↦ (f.val x : EReal),
    isProper_coe_of_convexOn f.property.1, f.property.2⟩
  invFun f := by
    refine ⟨(growthToRealConvex B hP hne f).val,
      (growthToRealConvex B hP hne f).property, ?_⟩
    have hh : (fun x ↦ ((growthToRealConvex B hP hne f).val x : EReal)) = f.val :=
      funext (coe_growthToRealConvex B hP hne f)
    rw [hh]
    exact f.property.2
  left_inv f := by
    apply Subtype.ext
    funext x
    exact EReal.toReal_coe (f.val x)
  right_inv f := by
    apply Subtype.ext
    exact funext (coe_growthToRealConvex B hP hne f)

/-- The literal source real-convex and closed-proper body classes have actual Legendre inverse maps. -/
def realGrowthClosedProperEquiv
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P) :
    {f // f ∈ RealGrowthClass B P} ≃ {g // g ∈ ClosedProperOnBody P} :=
  (realGrowthEquiv B hP hne).trans (growthClosedProperEquiv B hP hne hconv)

/-- The forward map is precisely the original Legendre conjugate in the original pairing. -/
theorem realGrowthClosedProperEquiv_apply
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f : {f // f ∈ RealGrowthClass B P}) :
    (realGrowthClosedProperEquiv B hP hne hconv f).val =
      conjugate B (fun x ↦ (f.val x : EReal)) := rfl

/-- The reverse map has the actual finite real values of the original reversed conjugate. -/
theorem realGrowthClosedProperEquiv_symm_apply
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (g : {g // g ∈ ClosedProperOnBody P}) (x : E) :
    ((realGrowthClosedProperEquiv B hP hne hconv).symm g).val x =
      (conjugate B.flip g.val x).toReal := rfl

end SGPT.Toric
