import SGPT.Toric.BigToricOperations
import SGPT.Envelopes.SourceEnvelopeContactSupport

/-!
# Newton bodies and the potential with minimal singularities in a big toric class

Source `chapter_toric_big.tex`:

* `def:toric-big:L430`: the Newton body `Δ(θ, φ) = cl ∇F_φ(N_ℝ)` (Alexandrov gradient);
  it is the closure of `{G_φ < ∞}` (`prop:gradDomFstar`) and a convex body contained in
  `P_D` (the inclusion is proved directly here, see below);
* `thm:FVtheta`, first assertion `eq:FVthetaE` / `eq:FSupp_bdd_temp1`:
  `F_{V_θ} ∈ 𝓔^∞(N_ℝ, P_D)`, i.e. `F_{V_θ} - Supp_{P_D}` is bounded, where
  `V_θ = sup {φ ∈ PSH(X, θ) : φ ≤ 0}`; consequently `Δ(θ, V_θ) = P_D`
  (`eq:DeltaVthetaPD_temp1`) and `G_{V_θ}` is bounded on `P_D`.

The source proves `thm:FVtheta` from the partial Okounkov body comparison `thm:toricpob` and
the regularity theorem of Berman--Berndtsson.  Here it is proved directly: the chart bounds
of the weights give `Supp_{P_D} - C ≤ F_θ`, so the extension of `Supp_{P_D} - C` is a
competitor for `V_θ`, while every toric potential has `F ≼ Supp_{P_D}`
(`realProfile_mem`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- Source `thm:toricpshbig` (3): `G_φ` is closed proper convex and `+∞` off `P_D`. -/
theorem legendre_mem_closedProperOnBody (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.legendre u ∈ ClosedProperOnBody (toricDivisorPolytope D) :=
  conjugate_mem_closedProperOnBody_of_mem_growthClass (innerₗ (EuclideanSpace ℝ (Fin n)))
    (isCompact_toricDivisorPolytope D) (convex_toricDivisorPolytope D)
    (h.profile_mem_growthClass hP hu)

/-- Source `def:toric-big:L430`: the Newton body `Δ(θ, φ) = cl ∇F_φ(N_ℝ)`, with the
(Alexandrov) subgradient image of `F_φ`. -/
def newtonBody (u : PolytopeToricVariety γ hs → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n))) (h.profile u))

/-- `Δ(θ, φ) = cl {G_φ < ∞}` (source `prop:gradDomFstar`). -/
theorem newtonBody_eq_closure_effectiveDomain (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.newtonBody u = convexNewtonBody (h.legendre u) := by
  have hf := h.profile_mem_growthClass hP hu
  exact closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate _ hf.1
    (lowerSemicontinuous_of_isClosedConvex (h.isClosedConvex_profile hP hu))

/-- Source `def:toric-big:L430` and `eq:DeltaVthetaPD_temp1` (last clause): `Δ(θ, φ)` is a
convex body contained in `P_D`. -/
theorem newtonBody_properties (hP : (toricDivisorPolytope D).Nonempty)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (h.newtonBody u).Nonempty ∧ IsCompact (h.newtonBody u) ∧
      Convex ℝ (h.newtonBody u) ∧ h.newtonBody u ⊆ toricDivisorPolytope D := by
  have hG := h.legendre_mem_closedProperOnBody hP hu
  have hDom : effectiveDomain (h.legendre u) ⊆ toricDivisorPolytope D := by
    intro m hm
    by_contra hmP
    exact (ne_of_lt hm) (hG.2.2 m hmP)
  have hsub : h.newtonBody u ⊆ toricDivisorPolytope D := by
    rw [h.newtonBody_eq_closure_effectiveDomain hP hu]
    exact closure_minimal hDom (isCompact_toricDivisorPolytope D).isClosed
  rw [h.newtonBody_eq_closure_effectiveDomain hP hu] at hsub ⊢
  refine ⟨hG.1.2.1.closure, (isCompact_toricDivisorPolytope D).of_isClosed_subset
    isClosed_closure hsub, (convex_effectiveDomain hG.1.1).closure, hsub⟩

/-! ### The potential with minimal singularities -/

/-- `V_θ = sup {φ ∈ PSH(X, θ) : φ ≤ 0}` (the source minimal envelope). -/
abbrev minimalEnvelope : PolytopeToricVariety γ hs → EReal := sourceMinimalEnvelope h.atlasForm

/-- A toric potential whose profile is at most `F_θ` (i.e. `≤ 0` on `T(ℂ)`) is `≤ 0`. -/
theorem le_zero_of_profile_le_potential {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hle : ∀ x, h.profile u x ≤ (h.potential x : EReal)) : u ≤ 0 := by
  rw [h.eq_analyticExtension hu.1]
  apply uscRegularization_le (continuous_const.upperSemicontinuous)
  intro p
  by_cases hp : p ∈ polytopeToricBoundary γ hs
  · simp only [if_pos hp]
    exact bot_le
  · simp only [if_neg hp]
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    rw [hu.2.embedding_eq γ hs a]
    have h1 := hle (unitTorusLog a)
    rw [profile] at h1
    have h2 : u (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a))) ≤
        ((0 : ℝ) : EReal) := by
      have h3 := (EReal.addLECancellable_coe (h.potential (unitTorusLog a))).add_le_add_iff_right.mp
        (h1.trans_eq (zero_add _).symm)
      simpa using h3
    exact h2

/-- The real support function `Supp_{P_D}`. -/
def supportReal (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x).toReal

theorem support_eq_supportReal (hP : (toricDivisorPolytope D).Nonempty) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) =
      fun x => (supportReal (D := D) x : EReal) := by
  funext x
  obtain ⟨r, hr⟩ := exists_real_support_value (innerₗ (EuclideanSpace ℝ (Fin n)))
    (isCompact_toricDivisorPolytope D) hP x
  rw [supportReal, hr, EReal.toReal_coe]

/-- `Supp_{P_D} - C ∈ 𝓟(N_ℝ, P_D)`. -/
theorem supportReal_sub_mem (hP : (toricDivisorPolytope D).Nonempty) (C : ℝ) :
    (fun x => supportReal (D := D) x - C) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  have hconv : ConvexOn ℝ univ (supportReal (D := D)) := by
    apply isConvex_coe_iff.mp
    rw [← support_eq_supportReal hP]
    exact isConvex_support _ _
  refine ⟨hconv.sub (concaveOn_const C convex_univ), ?_⟩
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨-C, fun x => ?_⟩
  rw [support_eq_supportReal hP, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- A constant `C₀` with `Supp_{P_D} - C₀ ≤ F_θ`. -/
theorem exists_supportReal_sub_le_potential (hP : (toricDivisorPolytope D).Nonempty) :
    ∃ C : ℝ, ∀ x, supportReal (D := D) x - C ≤ h.potential x := by
  obtain ⟨C, hC⟩ := h.exists_support_le_potential
  refine ⟨C, fun x => ?_⟩
  have h1 := hC x
  rw [support_eq_supportReal hP] at h1
  linarith [EReal.coe_le_coe_iff.mp h1]

/-- The toric competitor `W` for `V_θ`: the extension of `Supp_{P_D} - C₀`. -/
theorem exists_supportCompetitor (hP : (toricDivisorPolytope D).Nonempty) :
    ∃ W : PolytopeToricVariety γ hs → EReal, W ∈ h.PSHTor ∧ W ≤ 0 ∧
      ∃ C : ℝ, h.profile W = fun x => ((supportReal (D := D) x - C : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := h.exists_supportReal_sub_le_potential hP
  have hmem := supportReal_sub_mem hP C
  refine ⟨h.extension _ hmem, h.extension_mem _ hmem, ?_, C, h.profile_extension _ hmem⟩
  apply h.le_zero_of_profile_le_potential (h.extension_mem _ hmem)
  intro x
  rw [h.profile_extension]
  exact EReal.coe_le_coe_iff.mpr (hC x)

/-- `V_θ ∈ PSH(X, θ)` (`PSH(X, θ) ≠ ∅` since `P_D ≠ ∅`). -/
theorem minimalEnvelope_isThetaPSH (hP : (toricDivisorPolytope D).Nonempty) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm h.minimalEnvelope := by
  obtain ⟨W, hW, -, -⟩ := h.exists_supportCompetitor hP
  exact sourceMinimalEnvelope_thetaPSH_of_mem hW.1

/-- `V_θ` is `T_c`-invariant. -/
theorem minimalEnvelope_invariant : PolytopeToricInvariant γ hs h.minimalEnvelope := by
  have hle (a : Fin n → ℂˣ) (ha : IsCompactTorusElement a) (p : PolytopeToricVariety γ hs) :
      h.minimalEnvelope (polytopeToricAction γ hs a p) ≤ h.minimalEnvelope p := by
    apply iSup_le
    intro v
    have hv : (fun q => v.1 (polytopeToricAction γ hs a q)) ≤ 0 := fun q => v.2.2 _
    exact le_iSup (fun w : {w : PolytopeToricVariety γ hs → EReal //
        (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm w ∧ w ≤ 0} => w.1 p)
      ⟨_, h.isThetaPSH_comp_action v.2.1 ha, hv⟩
  intro a ha p
  apply le_antisymm (hle a ha p)
  have h' := hle a⁻¹ (isCompactTorusElement_inv ha) (polytopeToricAction γ hs a p)
  rwa [← polytopeToricAction_mul, inv_mul_cancel, polytopeToricAction_one] at h'

theorem minimalEnvelope_mem (hP : (toricDivisorPolytope D).Nonempty) :
    h.minimalEnvelope ∈ h.PSHTor :=
  ⟨h.minimalEnvelope_isThetaPSH hP, h.minimalEnvelope_invariant⟩

/-- Source `thm:FVtheta` (`eq:FVthetaE`, `eq:FSupp_bdd_temp1`):
`F_{V_θ} ∈ 𝓔^∞(N_ℝ, P_D)`, i.e. `F_{V_θ}` is closed convex and `F_{V_θ} - Supp_{P_D}`
is bounded. -/
theorem profile_minimalEnvelope_mem_boundedGrowthClass
    (hP : (toricDivisorPolytope D).Nonempty) :
    h.profile h.minimalEnvelope ∈
      BoundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  have hV := h.minimalEnvelope_mem hP
  refine ⟨h.isClosedConvex_profile hP hV, (h.profile_mem_growthClass hP hV).2, ?_⟩
  obtain ⟨W, hW, hW0, C, hWF⟩ := h.exists_supportCompetitor hP
  have hWV : W ≤ h.minimalEnvelope := fun p =>
    le_iSup (fun w : {w : PolytopeToricVariety γ hs → EReal //
        (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm w ∧ w ≤ 0} => w.1 p)
      ⟨W, hW.1, hW0⟩
  have hF := (h.le_iff hW hV).mp hWV
  rw [hWF] at hF
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨C, fun x => ?_⟩
  rw [support_eq_supportReal hP]
  calc (supportReal (D := D) x : EReal) = ((supportReal (D := D) x - C : ℝ) : EReal) + (C : EReal) := by
        rw [← EReal.coe_add]; ring_nf
    _ ≤ h.profile h.minimalEnvelope x + (C : EReal) := add_le_add (hF x) le_rfl

/-- `G_{V_θ} ∼ χ_{P_D}`: `G_{V_θ}` is bounded on `P_D` (and `+∞` off `P_D`). -/
theorem legendre_minimalEnvelope_bounds (hP : (toricDivisorPolytope D).Nonempty) :
    ∃ a b : ℝ, ∀ m ∈ toricDivisorPolytope D,
      (a : EReal) ≤ h.legendre h.minimalEnvelope m ∧
        h.legendre h.minimalEnvelope m ≤ (b : EReal) :=
  conjugate_bounds_of_mem_boundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n)))
    (isCompact_toricDivisorPolytope D) (convex_toricDivisorPolytope D)
    (h.profile_minimalEnvelope_mem_boundedGrowthClass hP)

/-- `{G_{V_θ} < ∞} = P_D`. -/
theorem effectiveDomain_legendre_minimalEnvelope (hP : (toricDivisorPolytope D).Nonempty) :
    effectiveDomain (h.legendre h.minimalEnvelope) = toricDivisorPolytope D := by
  obtain ⟨a, b, hab⟩ := h.legendre_minimalEnvelope_bounds hP
  have hG := h.legendre_mem_closedProperOnBody hP (h.minimalEnvelope_mem hP)
  ext m
  constructor
  · intro hm
    by_contra hmP
    exact (ne_of_lt hm) (hG.2.2 m hmP)
  · intro hm
    exact (hab m hm).2.trans_lt (EReal.coe_lt_top b)

/-- Source `eq:DeltaVthetaPD_temp1`: `Δ(θ, V_θ) = P_D`. -/
theorem newtonBody_minimalEnvelope (hP : (toricDivisorPolytope D).Nonempty) :
    h.newtonBody h.minimalEnvelope = toricDivisorPolytope D := by
  rw [h.newtonBody_eq_closure_effectiveDomain hP (h.minimalEnvelope_mem hP), convexNewtonBody,
    h.effectiveDomain_legendre_minimalEnvelope hP]
  exact (isClosed_toricDivisorPolytope D).closure_eq

end BigToricMetric

end SGPT.Toric
