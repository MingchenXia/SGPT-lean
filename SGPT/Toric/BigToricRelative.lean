import SGPT.Toric.BigToricEnvelope
import SGPT.Toric.BigToricMongeAmpere
import SGPT.Envelopes.SourceRelativeEnergy

/-!
# Toric potentials more singular than a toric model potential

Source `chapter_toric_big.tex`, `cor:toric-big:L860`: fix a model potential
`φ ∈ PSH_tor(X, θ)_{>0}` with Newton body `Δ = Δ(θ, φ)`.  There are canonical bijections

1. `PSH_tor(X, θ; φ) = {ψ ∈ PSH_tor(X, θ) : ψ ≼ φ}`,
2. `𝓟(N_ℝ, Δ)`,
3. closed proper convex `G` on `M_ℝ` with `G = +∞` off `Δ`;

and under these, `𝓔_tor(X, θ; φ) = 𝓔(X, θ; φ) ∩ PSH_tor(X, θ)` corresponds to
`𝓔(N_ℝ, Δ)` and to the closed proper convex `G` with `cl Int {G < ∞} = Δ`.

The proof: `φ = P_θ[φ]`, so `G_φ = G_{V_θ}` on `Δ` and `+∞` off `Δ` (`prop:GPenvelopebig`);
as `G_{V_θ}` is bounded on `P_D ⊇ Δ`, `G_φ ∼ χ_Δ`, hence `F_φ ∼ Supp_Δ`.  The full-mass
part uses `∫ θ_ψ^n = n! vol Δ(θ, ψ)` (`prop:toricMAandrealMA2`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Classical

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (hP : (toricDivisorPolytope D).Nonempty)
variable {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
  (hmodel : SourceModelPotential h.atlasForm φ)

/-- Source `cor:toric-big:L860`: `PSH_tor(X, θ; φ) = {ψ ∈ PSH_tor(X, θ) : ψ ≼ φ}`. -/
def PSHTorRel (φ : PolytopeToricVariety γ hs → EReal) : Set (PolytopeToricVariety γ hs → EReal) :=
  {ψ | ψ ∈ h.PSHTor ∧ SGPT.PSH.SingularityLE ψ φ}

/-- Source `cor:toric-big:L860`:
`𝓔_tor(X, θ; φ) = 𝓔(X, θ; φ) ∩ PSH_tor(X, θ)` (`SourceRelativeFullMass`). -/
def ETorRel (hmodel : SourceModelPotential h.atlasForm φ) :
    Set (PolytopeToricVariety γ hs → EReal) :=
  {ψ | SourceRelativeFullMass h.atlasForm φ ψ hmodel ∧ ψ ∈ h.PSHTor}

include hP hφ hmodel

/-- For a model potential, `G_φ = G_{V_θ}` on `Δ(θ, φ)` and `+∞` off it. -/
theorem legendre_model (m : EuclideanSpace ℝ (Fin n)) :
    h.legendre φ m = if m ∈ h.newtonBody φ then h.legendre h.minimalEnvelope m else ⊤ := by
  obtain ⟨_, heq, _⟩ := hmodel
  have hspec := (h.sourceSingularityEnvelope_spec hP hφ).2 m
  rw [← heq] at hspec
  exact hspec

/-- `G_φ ∼ χ_Δ` for a model potential. -/
theorem legendre_model_singularityEquiv_indicator :
    SGPT.PSH.SingularityEquiv (h.legendre φ) (indicator (h.newtonBody φ)) := by
  obtain ⟨a, b, hab⟩ := h.legendre_minimalEnvelope_bounds hP
  have hsub := (h.newtonBody_properties hP hφ).2.2.2
  refine ⟨(SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨b, fun m => ?_⟩,
    (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨-a, fun m => ?_⟩⟩
  · rw [h.legendre_model hP hφ hmodel m]
    by_cases hm : m ∈ h.newtonBody φ
    · simp only [if_pos hm, SGPT.Convex.indicator, zero_add]
      exact (hab m (hsub hm)).2
    · simp [hm, SGPT.Convex.indicator]
  · rw [h.legendre_model hP hφ hmodel m]
    by_cases hm : m ∈ h.newtonBody φ
    · simp only [if_pos hm, SGPT.Convex.indicator]
      obtain ⟨h1, h1'⟩ := hab m (hsub hm)
      have hfin : h.legendre h.minimalEnvelope m =
          ((h.legendre h.minimalEnvelope m).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt (h1'.trans_lt (EReal.coe_lt_top b)))
          (ne_of_gt ((EReal.bot_lt_coe a).trans_le h1))).symm
      rw [hfin] at h1 ⊢
      rw [← EReal.coe_add]
      have := EReal.coe_le_coe_iff.mp h1
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · simp [hm, SGPT.Convex.indicator]

/-- `F_φ ∼ Supp_Δ` for a model potential. -/
theorem profile_model_singularityEquiv_support :
    SGPT.PSH.SingularityEquiv (h.profile φ)
      (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody φ)) := by
  have h1 := conjugate_singularityEquiv (innerₗ (EuclideanSpace ℝ (Fin n))).flip
    (h.legendre_model_singularityEquiv_indicator hP hφ hmodel)
  rwa [h.conjugate_legendre hP hφ, conjugate_indicator] at h1

omit hmodel in
theorem support_newtonBody_le (x : EuclideanSpace ℝ (Fin n)) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.newtonBody φ) x ≤
      support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x := by
  apply iSup_le
  intro m
  exact le_iSup (fun y : toricDivisorPolytope D =>
    (((innerₗ (EuclideanSpace ℝ (Fin n))).flip y x : ℝ) : EReal))
    ⟨m.val, (h.newtonBody_properties hP hφ).2.2.2 m.property⟩

/-- Source `cor:toric-big:L860`, (1) ⇔ (2): for `ψ ∈ PSH_tor(X, θ)`, `ψ ≼ φ` iff
`F_ψ ∈ 𝓟(N_ℝ, Δ(θ, φ))`. -/
theorem singularityLE_model_iff {ψ : PolytopeToricVariety γ hs → EReal} (hψ : ψ ∈ h.PSHTor) :
    SGPT.PSH.SingularityLE ψ φ ↔
      h.realProfile ψ ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (h.newtonBody φ) := by
  have heqv := h.profile_model_singularityEquiv_support hP hφ hmodel
  rw [h.singularityLE_iff hψ hφ]
  constructor
  · intro hle
    refine ⟨(h.realProfile_mem hψ).1.1, ?_⟩
    rw [← (h.realProfile_mem hψ).2]
    exact SGPT.PSH.singularityLE_trans hle heqv.1
  · intro hmem
    have h1 := hmem.2
    rw [← (h.realProfile_mem hψ).2] at h1
    exact SGPT.PSH.singularityLE_trans h1 heqv.2

omit hmodel in
/-- `𝓟(N_ℝ, Δ(θ, φ)) ⊆ 𝓟(N_ℝ, P_D)`. -/
theorem realGrowth_of_rel {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (h.newtonBody φ)) :
    f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  refine ⟨hf.1, ?_⟩
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2
  exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    ⟨C, fun x => (hC x).trans (add_le_add (h.support_newtonBody_le hP hφ x) le_rfl)⟩

omit hP hφ hmodel in
theorem realProfile_extension (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    h.realProfile (h.extension f hf) = f := by
  funext x
  simp only [realProfile, profile_extension, EReal.toReal_coe]

/-- Source `cor:toric-big:L860`, bijection (1) ↔ (2):
`PSH_tor(X, θ; φ) ≃ 𝓟(N_ℝ, Δ(θ, φ))`, `ψ ↦ F_ψ`. -/
def equivRelRealGrowth :
    {ψ // ψ ∈ h.PSHTorRel φ} ≃
      {f // f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (h.newtonBody φ)} where
  toFun ψ := ⟨h.realProfile ψ.val,
    (h.singularityLE_model_iff hP hφ hmodel ψ.property.1).mp ψ.property.2⟩
  invFun f := ⟨h.extension f.val (h.realGrowth_of_rel hP hφ f.property),
    h.extension_mem _ _, (h.singularityLE_model_iff hP hφ hmodel (h.extension_mem _ _)).mpr
      ((h.realProfile_extension _ _).symm ▸ f.property)⟩
  left_inv ψ := Subtype.ext (h.extension_realProfile ψ.property.1)
  right_inv f := Subtype.ext (h.realProfile_extension f.val (h.realGrowth_of_rel hP hφ f.property))

theorem equivRelRealGrowth_apply (ψ : {ψ // ψ ∈ h.PSHTorRel φ}) :
    (h.equivRelRealGrowth hP hφ hmodel ψ).val = h.realProfile ψ.val := rfl

/-- Source `cor:toric-big:L860`, bijection (1) ↔ (3): `PSH_tor(X, θ; φ)` is in bijection
with the closed proper convex `G` on `M_ℝ` with `G = +∞` off `Δ(θ, φ)`, via `ψ ↦ G_ψ`. -/
def equivRelClosedProper :
    {ψ // ψ ∈ h.PSHTorRel φ} ≃ {g // g ∈ ClosedProperOnBody (h.newtonBody φ)} :=
  (h.equivRelRealGrowth hP hφ hmodel).trans
    (realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
      (h.newtonBody_properties hP hφ).2.1 (h.newtonBody_properties hP hφ).1
      (h.newtonBody_properties hP hφ).2.2.1)

theorem equivRelClosedProper_apply (ψ : {ψ // ψ ∈ h.PSHTorRel φ}) :
    (h.equivRelClosedProper hP hφ hmodel ψ).val = h.legendre ψ.val := by
  change conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
    (fun x => ((h.realProfile ψ.val x : ℝ) : EReal)) = _
  rw [← (h.realProfile_mem ψ.property.1).2]
  rfl

/-! ### The full-mass part -/

omit hmodel in
/-- `ψ ≼ φ` gives `Δ(θ, ψ) ⊆ Δ(θ, φ)`. -/
theorem newtonBody_mono {ψ : PolytopeToricVariety γ hs → EReal} (hψ : ψ ∈ h.PSHTor)
    (hle : SGPT.PSH.SingularityLE ψ φ) : h.newtonBody ψ ⊆ h.newtonBody φ := by
  rw [h.newtonBody_eq_closure_effectiveDomain hP hψ, h.newtonBody_eq_closure_effectiveDomain hP hφ]
  apply closure_mono
  have hG := (h.profile_singularityLE_iff_legendre hP hψ hφ).mp ((h.singularityLE_iff hψ hφ).mp hle)
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hG
  intro m hm
  change h.legendre φ m < ⊤
  calc h.legendre φ m ≤ h.legendre ψ m + (C : EReal) := hC m
    _ < ⊤ := EReal.add_lt_top (ne_of_lt hm) (EReal.coe_ne_top C)

omit hφ in
/-- The model has `vol Δ(θ, φ) > 0` (positive mass). -/
theorem volume_newtonBody_model_pos (hφ : φ ∈ h.PSHTor) : 0 < volume (h.newtonBody φ) := by
  obtain ⟨hφ', _, hpos⟩ := hmodel
  have hmass := h.MA_univ hP hφ
  change 0 < sourcePotentialNonPluripolarMeasure h.atlasForm φ hφ.1 univ at hpos
  change sourcePotentialNonPluripolarMeasure h.atlasForm φ hφ.1 univ = _ at hmass
  rw [hmass] at hpos
  exact pos_of_ne_zero fun h0 => by simp [h0] at hpos

theorem interior_newtonBody_model_nonempty : (interior (h.newtonBody φ)).Nonempty :=
  interior_nonempty_of_volume_pos (h.newtonBody_properties hP hφ).2.2.1
    (h.volume_newtonBody_model_pos hP hmodel hφ)

/-- Source `cor:toric-big:L860`, (1) ⇔ (2) of the full-mass part: for `ψ ∈ PSH_tor(X, θ; φ)`,
`ψ ∈ 𝓔(X, θ; φ)` iff `Δ(θ, ψ) = Δ(θ, φ)`. -/
theorem mem_ETorRel_iff_newtonBody_eq {ψ : PolytopeToricVariety γ hs → EReal}
    (hψ : ψ ∈ h.PSHTorRel φ) : ψ ∈ h.ETorRel hmodel ↔ h.newtonBody ψ = h.newtonBody φ := by
  have hmψ := h.MA_univ hP hψ.1
  have hmφ := h.MA_univ hP hφ
  have hfact : (n.factorial : ENNReal) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfactTop : (n.factorial : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hφfin : volume (h.newtonBody φ) ≠ ⊤ :=
    (h.newtonBody_properties hP hφ).2.1.measure_lt_top.ne
  constructor
  · rintro ⟨⟨hu, _, hmass⟩, _⟩
    change sourcePotentialNonPluripolarMeasure h.atlasForm ψ hψ.1.1 univ =
      sourcePotentialNonPluripolarMeasure h.atlasForm φ hφ.1 univ at hmass
    change sourcePotentialNonPluripolarMeasure h.atlasForm ψ hψ.1.1 univ = _ at hmψ
    change sourcePotentialNonPluripolarMeasure h.atlasForm φ hφ.1 univ = _ at hmφ
    rw [hmψ, hmφ] at hmass
    have hvol : volume (h.newtonBody ψ) = volume (h.newtonBody φ) :=
      (ENNReal.mul_right_inj hfact hfactTop).mp hmass
    exact eq_of_subset_of_volume_eq (h.newtonBody_mono hP hφ hψ.1 hψ.2) isClosed_closure
      (h.newtonBody_properties hP hφ).2.2.1 (h.interior_newtonBody_model_nonempty hP hφ hmodel)
      hφfin hvol
  · intro heq
    refine ⟨⟨hψ.1.1, hψ.2, ?_⟩, hψ.1⟩
    change sourcePotentialNonPluripolarMeasure h.atlasForm ψ hψ.1.1 univ =
      sourcePotentialNonPluripolarMeasure h.atlasForm φ hφ.1 univ
    change sourcePotentialNonPluripolarMeasure h.atlasForm ψ hψ.1.1 univ = _ at hmψ
    change sourcePotentialNonPluripolarMeasure h.atlasForm φ hφ.1 univ = _ at hmφ
    rw [hmψ, hmφ, heq]

/-- Source `cor:toric-big:L860`, (1) ⇔ (2) of the full-mass part: `ψ ∈ 𝓔_tor(X, θ; φ)` iff
`F_ψ ∈ 𝓔(N_ℝ, Δ(θ, φ))`. -/
theorem mem_ETorRel_iff_fullMassClass {ψ : PolytopeToricVariety γ hs → EReal}
    (hψ : ψ ∈ h.PSHTorRel φ) :
    ψ ∈ h.ETorRel hmodel ↔
      h.profile ψ ∈ FullMassClass (innerₗ (EuclideanSpace ℝ (Fin n))) (h.newtonBody φ) := by
  rw [h.mem_ETorRel_iff_newtonBody_eq hP hφ hmodel hψ]
  have hgrowth : h.profile ψ ∈ GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (h.newtonBody φ) := by
    have hmem := (h.singularityLE_model_iff hP hφ hmodel hψ.1).mp hψ.2
    rw [(h.realProfile_mem hψ.1).2]
    exact ((realGrowthEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
      (h.newtonBody_properties hP hφ).2.1 (h.newtonBody_properties hP hφ).1) ⟨_, hmem⟩).property
  have hint := h.interior_newtonBody_model_nonempty hP hφ hmodel
  constructor
  · intro heq
    exact ⟨hgrowth, Or.inr heq⟩
  · rintro ⟨_, hcase⟩
    rcases hcase with h0 | hcl
    · exact absurd h0 hint.ne_empty
    · exact hcl

omit hP hφ hmodel in
/-- For a convex set `C` and a convex body `Δ` with nonempty interior,
`cl Int C = Δ ⇔ cl C = Δ`. -/
theorem closure_interior_eq_iff {C Δ : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    (hΔ : (interior Δ).Nonempty) : closure (interior C) = Δ ↔ closure C = Δ := by
  have hint : closure C = Δ → (interior C).Nonempty := by
    intro hcl
    rw [← hcl] at hΔ
    apply (hC.interior_nonempty_iff_affineSpan_eq_top).mpr
    have h1 := (hC.closure.interior_nonempty_iff_affineSpan_eq_top).mp hΔ
    apply eq_top_iff.mpr
    rw [← h1]
    apply affineSpan_le.mpr
    exact closure_minimal (subset_affineSpan ℝ C) (AffineSubspace.closed_of_finiteDimensional _)
  constructor
  · intro hcl
    have hne : (interior C).Nonempty := by
      by_contra h0
      rw [not_nonempty_iff_eq_empty] at h0
      rw [h0, closure_empty] at hcl
      rw [← hcl] at hΔ
      simp at hΔ
    rw [← hC.closure_interior_eq_closure_of_nonempty_interior hne]
    exact hcl
  · intro hcl
    rw [hC.closure_interior_eq_closure_of_nonempty_interior (hint hcl)]
    exact hcl

/-- Source `cor:toric-big:L860`, (1) ⇔ (3) of the full-mass part: `ψ ∈ 𝓔_tor(X, θ; φ)` iff
`cl Int {G_ψ < ∞} = Δ(θ, φ)`. -/
theorem mem_ETorRel_iff_legendre {ψ : PolytopeToricVariety γ hs → EReal}
    (hψ : ψ ∈ h.PSHTorRel φ) :
    ψ ∈ h.ETorRel hmodel ↔
      closure (interior (effectiveDomain (h.legendre ψ))) = h.newtonBody φ := by
  rw [h.mem_ETorRel_iff_newtonBody_eq hP hφ hmodel hψ, h.newtonBody_eq_closure_effectiveDomain hP hψ.1,
    convexNewtonBody]
  have hG := h.legendre_mem_closedProperOnBody hP hψ.1
  exact (closure_interior_eq_iff (convex_effectiveDomain hG.1.1)
    (h.interior_newtonBody_model_nonempty hP hφ hmodel)).symm

omit hP hφ hmodel in
/-- A closed proper convex `G` with `cl Int {G < ∞} = Δ`, `Int Δ ≠ ∅`, is `+∞` off `Δ`; so
the third set of the full-mass part of `cor:toric-big:L860` lies in the third set of the
first part. -/
theorem mem_closedProperOnBody_of_closure_interior {G : EuclideanSpace ℝ (Fin n) → EReal}
    {Δ : Set (EuclideanSpace ℝ (Fin n))} (hΔ : (interior Δ).Nonempty) (hG : IsProper G)
    (hlsc : LowerSemicontinuous G) (hcl : closure (interior (effectiveDomain G)) = Δ) :
    G ∈ ClosedProperOnBody Δ := by
  refine ⟨hG, hlsc, fun m hm => ?_⟩
  have hcl' := (closure_interior_eq_iff (convex_effectiveDomain hG.1) hΔ).mp hcl
  by_contra hne
  exact hm (hcl' ▸ subset_closure (lt_top_iff_ne_top.mpr hne))

end BigToricMetric

end SGPT.Toric
