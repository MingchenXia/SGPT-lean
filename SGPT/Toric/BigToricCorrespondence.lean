import SGPT.Toric.BigToricMetric

/-!
# Toric `θ`-psh functions in a big toric class and convex functions

Source `chapter_toric_big.tex`:

* `def:toric-big:L416`: for `φ ∈ PSH_tor(X, θ)`, `φ|_{T(ℂ)} = Trop^* f` and
  `F_φ = F_θ + f` (`eq:Fvarphibig1`); `F_φ` is a finite convex function;
* `thm:toricpshbig`: canonical bijections between `PSH_tor(X, θ)`, the convex functions
  `F ∈ 𝓟(N_ℝ, P_D)` (`F ≼ Supp_{P_D}`) and the closed proper convex functions on `M_ℝ`
  which are `+∞` off `P_D`;
* `prop:toricpluscstbig`: `F_{φ+C} = F_φ + C`, `G_{φ+C} = G_φ - C`;
* the comparison of the pointwise and singularity orders (used throughout the section).

Here `θ = c_1(O(D), h)` for an arbitrary torus-invariant divisor `D` on the toric manifold
`X` and an arbitrary `T_c`-invariant metric `h` (`BigToricMetric`).  Unlike the ample case,
`F_θ` itself is in general not `≼ Supp_{P_D}`; the forward bound `F_φ ≼ Supp_{P_D}` is
obtained from the chart bounds `F_φ ≤ ⟨m_v, ·⟩ + C` on each `-σ_v` and Legendre duality
(`singularityLE_support_of_vertexBounds`), and the reverse construction uses
`Supp_{P_D} ≤ F_θ + C` (`exists_support_le_potential`).  The source deduces these bounds
from `thm:FVtheta`; here they are proved directly, so the bijection does not depend on the
partial Okounkov body theory.
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

/-- Source `sec:toricpob`: `PSH_tor(X, θ)`, the `T_c`-invariant `θ`-psh functions. -/
def PSHTor : Set (PolytopeToricVariety γ hs → EReal) :=
  {u | (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u ∧
    PolytopeToricInvariant γ hs u}

/-- Source `def:toric-big:L416` (`eq:Fvarphibig1`): `F_φ = F_θ + f`, where
`φ|_{T(ℂ)} = Trop^* f`; it is evaluated at the positive torus points `e^{x/2}`. -/
def profile (u : PolytopeToricVariety γ hs → EReal) (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  u (polytopeToricEmbedding γ hs (positiveTorusPoint x)) + (h.potential x : EReal)

/-- `G_φ = F_φ^*`. -/
def legendre (u : PolytopeToricVariety γ hs → EReal) : EuclideanSpace ℝ (Fin n) → EReal :=
  conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (h.profile u)

/-- Core chart identity: in the vertex chart at `v`, on the torus, the corrected local
potential `u + ψ_v` of a function with torus-invariant values is the tropical pullback of
`F_u - ⟨m_v, ·⟩`, composed with the inverse basis change. -/
theorem vertexChart_corrected_eq {u : PolytopeToricVariety γ hs → EReal}
    (hu : ∀ a, u (polytopeToricEmbedding γ hs a) =
      u (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a))))
    (v : latticePolytopeVertices γ) {w : ComplexModel n} (hw : w ∈ complexTorus n) :
    u ((originalPolytopeNativeModelChart γ hs v).symm w) + (h.weight v w : EReal) =
      tropicalPullback (fun y => h.profile u
          (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) +
        ((-latticeFunctional (toricCartierDatum D v)
          (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) : ℝ) : EReal)) w := by
  obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hw
  have hwt : w ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ w
  have hwa : originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) = w := by
    rw [ha]; exact (originalPolytopeNativeModelChart γ hs v).right_inv hwt
  have hlog : latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization w) =
      unitTorusLog a := by
    rw [← hwa, tropicalization_polytopeToricVertexChart_embedding,
      latticeBasisLogInverse_logMap]
  change u ((originalPolytopeNativeModelChart γ hs v).symm w) + (h.weight v w : EReal) =
    h.profile u
        (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization w)) +
      ((-latticeFunctional (toricCartierDatum D v)
        (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization w)) : ℝ) :
          EReal)
  rw [hlog, ← ha, ← hwa, h.weight_chart_embedding, profile, hu a, add_assoc, ← EReal.coe_add,
    sub_eq_add_neg]

/-- `θ`-psh functions have psh corrected potentials in each whole vertex chart. -/
theorem plurisubharmonicOn_vertexChart {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u)
    (v : latticePolytopeVertices γ) :
    PlurisubharmonicOn (fun z => u ((originalPolytopeNativeModelChart γ hs v).symm z) +
      (h.weight v z : EReal)) univ := by
  have hpsh := hu.preferred_chart_corrected (polytopeToricVertexChart γ hs v)
    (h.smooth v).contDiffOn (h.atlasForm_coeff_vertexChart v)
  rwa [polytopeToric_chart_target] at hpsh

/-- Upper bound of a `θ`-psh function on the compact manifold `X`. -/
theorem exists_upper_bound {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u) :
    ∃ C : ℝ, ∀ p, u p ≤ (C : EReal) :=
  exists_real_upper_bound_of_upperSemicontinuous hu.upperSemicontinuous hu.1

/-! ### From toric potentials to convex functions -/

/-- Source `def:toric-big:L416` and `lma:convextopsh`: the profile of a toric `θ`-psh
function is a finite convex function. -/
theorem profile_real_convex {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u)
    (hi : PolytopeToricInvariant γ hs u) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ univ f ∧
      h.profile u = fun x => (f x : EReal) := by
  let w : latticePolytopeVertices γ := polytopeToricBaseVertex γ
  let b := originalPolytopeNativeBasis γ hs w
  let c := originalPolytopeNativeModelChart γ hs w
  let H : EuclideanSpace ℝ (Fin n) → EReal := fun y =>
    h.profile u (latticeBasisLogInverse b y) +
      ((-latticeFunctional (toricCartierDatum D w) (latticeBasisLogInverse b y) : ℝ) : EReal)
  have hp := h.plurisubharmonicOn_vertexChart hu w
  have heq : ∀ z ∈ complexTorus n,
      u (c.symm z) + (h.weight w z : EReal) = tropicalPullback H z :=
    fun z hz => h.vertexChart_corrected_eq (fun a => hi.embedding_eq γ hs a) w hz
  have hraw : PlurisubharmonicOn (tropicalPullback H) (complexTorus n) := by
    intro z hz
    apply (hp z (mem_univ z)).congr
    filter_upwards [(isOpen_complexTorus n).mem_nhds hz] with y hy
    exact heq y hy
  have htarget (z : ComplexModel n) : z ∈ c.target := by
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ z
  have hpsh : PSHOn (tropicalPullback H) (complexTorus n) := by
    refine ⟨hraw.discPshOn, ?_⟩
    let z₀ := expCoordinates (0 : EuclideanSpace ℝ (Fin n))
    have hz₀ : z₀ ∈ complexTorus n := expCoordinates_mem_complexTorus 0
    let O := c.source ∩ c ⁻¹' complexTorus n
    have hO : IsOpen O := c.isOpen_inter_preimage (isOpen_complexTorus n)
    have hxO : c.symm z₀ ∈ O := by
      refine ⟨c.map_target (htarget z₀), ?_⟩
      change c (c.symm z₀) ∈ complexTorus n
      rw [c.right_inv (htarget z₀)]
      exact hz₀
    obtain ⟨p, hpO, hfin⟩ := hu.locallyNondegenerate (c.symm z₀) (mem_univ _) O hO hxO
    refine ⟨c p, hpO.2.2, ?_⟩
    rw [← heq (c p) hpO.2.2, c.left_inv hpO.2.1]
    intro hb
    rcases EReal.add_eq_bot_iff.mp hb with hb | hb
    · exact hfin hb
    · exact EReal.coe_ne_bot _ hb
  obtain ⟨g, hg, hH⟩ := exists_real_convex_of_pshOn_tropicalPullback hpsh
  refine ⟨fun x => g (latticeBasisLogMap b x) + latticeFunctional (toricCartierDatum D w) x, ?_, ?_⟩
  · have h1 : ConvexOn ℝ univ (g ∘ latticeBasisLogMap b) := by
      simpa only [preimage_univ] using hg.comp_linearMap (latticeBasisLogMap b)
    exact h1.add ((latticeFunctional (toricCartierDatum D w)).convexOn convex_univ)
  · funext x
    have hx := congrFun hH (latticeBasisLogMap b x)
    simp only [H, latticeBasisLogInverse_logMap] at hx
    rw [EReal.eq_coe_sub_of_add_coe_eq hx, sub_neg_eq_add]

/-- The real-valued profile `F_φ`. -/
def realProfile (u : PolytopeToricVariety γ hs → EReal) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (h.profile u x).toReal

/-- An upper bound `u ≤ C` gives `F_u ≤ C + F_θ`. -/
theorem profile_le_of_le {u : PolytopeToricVariety γ hs → EReal} {C : ℝ}
    (hC : ∀ p, u p ≤ (C : EReal)) (x : EuclideanSpace ℝ (Fin n)) :
    h.profile u x ≤ ((C + h.potential x : ℝ) : EReal) := by
  rw [profile, EReal.coe_add]
  exact add_le_add (hC _) le_rfl

/-- A finite convex function `≤ C + F_θ` has support growth `≼ Supp_{P_D}`. -/
theorem singularityLE_support_of_le_potential {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ univ f) (C : ℝ) (hle : ∀ x, f x ≤ C + h.potential x) :
    SGPT.PSH.SingularityLE (fun x => (f x : EReal))
      (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D)) := by
  apply singularityLE_support_of_vertexBounds D hf
  intro v
  obtain ⟨C', hC'⟩ := h.exists_potential_le_cartier v
  exact ⟨C + C', fun x hx => by linarith [hle x, hC' x hx]⟩

/-- Source `thm:toricpshbig`, map (1) → (2): `F_φ ∈ 𝓟(N_ℝ, P_D)`. -/
theorem realProfile_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.realProfile u ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) ∧
      h.profile u = fun x => (h.realProfile u x : EReal) := by
  obtain ⟨f, hf, heq⟩ := h.profile_real_convex hu.1 hu.2
  have hreal : h.realProfile u = f := by
    funext x
    simp only [realProfile, heq, EReal.toReal_coe]
  have hcoe : h.profile u = fun x => (h.realProfile u x : EReal) := by
    rw [hreal]; exact heq
  obtain ⟨C, hC⟩ := h.exists_upper_bound hu.1
  refine ⟨⟨by rw [hreal]; exact hf, ?_⟩, hcoe⟩
  rw [hreal]
  apply h.singularityLE_support_of_le_potential hf C
  intro x
  have h1 := h.profile_le_of_le hC x
  rw [heq] at h1
  exact EReal.coe_le_coe_iff.mp h1

/-- The set `P_D` is nonempty as soon as `PSH_tor(X, θ)` is (`G_φ` is proper and `+∞` off
`P_D`). -/
theorem nonempty_toricDivisorPolytope_of_mem {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) : (toricDivisorPolytope D).Nonempty := by
  obtain ⟨hmem, _⟩ := h.realProfile_mem hu
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hmem.2
  have h0 := hC 0
  rw [hne] at h0
  simp [support] at h0

variable (hne : (toricDivisorPolytope D).Nonempty)
include hne

/-- The extended-valued profile lies in the growth class `𝓟(N_ℝ, P_D)`. -/
theorem profile_mem_growthClass {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.profile u ∈
      GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  have hmem := h.realProfile_mem hu
  rw [hmem.2]
  exact ((realGrowthEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
    (isCompact_toricDivisorPolytope D) hne) ⟨_, hmem.1⟩).property

/-- The profile of a toric potential is closed convex. -/
theorem isClosedConvex_profile {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    IsClosedConvex (h.profile u) :=
  isClosedConvex_of_mem_growthClass _ (isCompact_toricDivisorPolytope D) hne
    (h.profile_mem_growthClass hne hu)

omit hne

/-! ### From convex functions to toric potentials -/

/-- The torus potential `Trop^*(F - F_θ)` attached to a convex function `F`. -/
def offPotential (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : PolytopeToricVariety γ hs) : EReal :=
  ((f (polytopeToricLog γ hs p) - h.potential (polytopeToricLog γ hs p) : ℝ) : EReal)

theorem offPotential_embedding (f : EuclideanSpace ℝ (Fin n) → ℝ) (a : Fin n → ℂˣ) :
    h.offPotential f (polytopeToricEmbedding γ hs a) =
      ((f (unitTorusLog a) - h.potential (unitTorusLog a) : ℝ) : EReal) := by
  rw [offPotential, polytopeToricLog_embedding]

theorem offPotential_invariantValues (f : EuclideanSpace ℝ (Fin n) → ℝ) (a : Fin n → ℂˣ) :
    h.offPotential f (polytopeToricEmbedding γ hs a) =
      h.offPotential f (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a))) := by
  rw [offPotential_embedding, offPotential_embedding, unitTorusLog_positiveTorusPoint]

theorem profile_offPotential (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    h.profile (h.offPotential f) = fun x => (f x : EReal) := by
  funext x
  rw [profile, offPotential_embedding, unitTorusLog_positiveTorusPoint, ← EReal.coe_add]
  congr 1
  ring

/-- `Trop^*(F - F_θ)` is `θ`-psh on the open torus for every finite convex `F`. -/
theorem isThetaPSHOn_offPotential {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ univ f) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSHOn h.atlasForm
      (h.offPotential f) (polytopeToricBoundary γ hs)ᶜ := by
  let w := polytopeToricBaseVertex γ
  let b := originalPolytopeNativeBasis γ hs w
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    f (latticeBasisLogInverse b y) +
      -latticeFunctional (toricCartierDatum D w) (latticeBasisLogInverse b y)
  have hH : ConvexOn ℝ univ H := by
    have h1 : ConvexOn ℝ univ (f ∘ latticeBasisLogInverse b) := by
      simpa only [preimage_univ] using hf.comp_linearMap (latticeBasisLogInverse b)
    have h2 : ConvexOn ℝ univ
        (-(latticeFunctional (toricCartierDatum D w) ∘ₗ latticeBasisLogInverse b)) :=
      LinearMap.convexOn _ convex_univ
    exact h1.add h2
  have htp := plurisubharmonicOn_tropicalPullback_of_convexOn hH
  apply isThetaPSHOn_of_finite_single_chart (polytopeToricVertexChart γ hs w)
    (ρ := h.weight w)
  · intro p hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    rw [polytopeToricVertexChart_chart, originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs w a
  · exact (h.smooth w).contDiffOn
  · exact h.atlasForm_coeff_vertexChart w
  · have hset : ((ofFixedModel n (PolytopeToricVariety γ hs)).chart
          (polytopeToricVertexChart γ hs w)).target ∩
        ((ofFixedModel n (PolytopeToricVariety γ hs)).chart
          (polytopeToricVertexChart γ hs w)).symm ⁻¹' (polytopeToricBoundary γ hs)ᶜ =
        complexTorus n := by
      ext z
      rw [polytopeToric_chart_target, univ_inter, mem_preimage, polytopeToricVertexChart_chart]
      exact polytopeToricVertexChart_symm_mem_compl_iff γ hs w z
    rw [hset]
    intro z hz
    apply (htp z hz).congr
    filter_upwards [(isOpen_complexTorus n).mem_nhds hz] with y hy
    symm
    change h.offPotential f ((originalPolytopeNativeModelChart γ hs w).symm y) +
      (h.weight w y : EReal) = _
    rw [h.vertexChart_corrected_eq (h.offPotential_invariantValues f) w hy,
      h.profile_offPotential]
    simp only [tropicalPullback, H, b, EReal.coe_add]
  · intro p _
    exact ⟨_, rfl⟩

/-- For `F ≼ Supp_{P_D}`, the torus potential `Trop^*(F - F_θ)` is bounded above. -/
theorem exists_upper_bound_offPotential {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    ∃ C : ℝ, ∀ p, h.offPotential f p ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2
  obtain ⟨E, hE⟩ := h.exists_support_le_potential
  refine ⟨E + C, fun p => ?_⟩
  set x := polytopeToricLog γ hs p
  have hle : ((f x : ℝ) : EReal) ≤ ((h.potential x + E + C : ℝ) : EReal) := by
    calc ((f x : ℝ) : EReal)
        ≤ support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x +
            (C : EReal) := hC x
      _ ≤ ((h.potential x + E : ℝ) : EReal) + (C : EReal) := add_le_add (hE x) le_rfl
      _ = _ := by rw [← EReal.coe_add]
  have hle' : f x ≤ h.potential x + E + C := EReal.coe_le_coe_iff.mp hle
  change ((f x - h.potential x : ℝ) : EReal) ≤ ((E + C : ℝ) : EReal)
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Source `thm:toricpshbig`, map (2) → (1) (via `thm:GRexten`): existence and uniqueness
of the `θ`-psh extension of `Trop^*(F - F_θ)` across the toric boundary. -/
theorem existsUnique_extension {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    ∃! v : PolytopeToricVariety γ hs → EReal,
      (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm v ∧
        EqOn v (h.offPotential f) (polytopeToricBoundary γ hs)ᶜ := by
  obtain ⟨C, hC⟩ := h.exists_upper_bound_offPotential hf
  exact exists_unique_bounded_theta_analytic_extension
    (h.isThetaPSHOn_offPotential hf.1)
    (hasAnalyticChartEquations_polytopeToricBoundary γ hs)
    (interior_polytopeToricBoundary γ hs)
    (fun _ _ => ⟨univ, univ_mem, C, fun p _ _ => hC p⟩)

/-- The toric potential attached to `F ∈ 𝓟(N_ℝ, P_D)`. -/
def extension (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    PolytopeToricVariety γ hs → EReal :=
  Classical.choose (h.existsUnique_extension hf)

theorem extension_spec (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm (h.extension f hf) ∧
      EqOn (h.extension f hf) (h.offPotential f) (polytopeToricBoundary γ hs)ᶜ :=
  (Classical.choose_spec (h.existsUnique_extension hf)).1

theorem extension_unique (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D))
    (v : PolytopeToricVariety γ hs → EReal)
    (hv : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm v)
    (heq : EqOn v (h.offPotential f) (polytopeToricBoundary γ hs)ᶜ) :
    v = h.extension f hf :=
  (Classical.choose_spec (h.existsUnique_extension hf)).2 v ⟨hv, heq⟩

/-- Uniqueness of the extension gives its `T_c`-invariance. -/
theorem extension_invariant (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    PolytopeToricInvariant γ hs (h.extension f hf) := by
  intro a ha p
  have h1 := h.isThetaPSH_comp_action (h.extension_spec f hf).1 ha
  have h2 : EqOn (fun q => h.extension f hf (polytopeToricAction γ hs a q))
      (h.offPotential f) (polytopeToricBoundary γ hs)ᶜ := by
    intro q hq
    obtain ⟨b, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs q).mp hq
    change h.extension f hf (polytopeToricAction γ hs a (polytopeToricEmbedding γ hs b)) = _
    rw [polytopeToricAction_embedding,
      (h.extension_spec f hf).2 (polytopeToricEmbedding_mem_compl γ hs _),
      offPotential_embedding, offPotential_embedding, unitTorusLog_compact_mul ha]
  exact congrFun (h.extension_unique f hf _ h1 h2) p

theorem extension_mem (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    h.extension f hf ∈ h.PSHTor :=
  ⟨(h.extension_spec f hf).1, h.extension_invariant f hf⟩

/-- The profile of the extension of `F` is `F`. -/
theorem profile_extension (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)) :
    h.profile (h.extension f hf) = fun x => (f x : EReal) := by
  rw [← h.profile_offPotential f]
  funext x
  rw [profile, profile, (h.extension_spec f hf).2 (polytopeToricEmbedding_mem_compl γ hs _)]

/-- Every toric potential is the extension of its own profile. -/
theorem extension_realProfile {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.extension (h.realProfile u) (h.realProfile_mem hu).1 = u := by
  symm
  apply h.extension_unique _ _ u hu.1
  intro p hp
  obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
  rw [offPotential_embedding, hu.2.embedding_eq γ hs a]
  have hh := congrFun (h.realProfile_mem hu).2 (unitTorusLog a)
  rw [profile] at hh
  exact EReal.eq_coe_sub_of_add_coe_eq hh

/-- Source `thm:toricpshbig`, bijection (1) ↔ (2): `PSH_tor(X, θ) ≃ 𝓟(N_ℝ, P_D)`,
`φ ↦ F_φ`, with inverse `F ↦` the `θ`-psh extension of `Trop^*(F - F_θ)`. -/
def equivRealGrowth :
    {u // u ∈ h.PSHTor} ≃
      {f // f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)} where
  toFun u := ⟨h.realProfile u.val, (h.realProfile_mem u.property).1⟩
  invFun f := ⟨h.extension f.val f.property, h.extension_mem f.val f.property⟩
  left_inv u := Subtype.ext (h.extension_realProfile u.property)
  right_inv f := by
    apply Subtype.ext
    funext x
    change (h.profile (h.extension f.val f.property) x).toReal = _
    simp only [profile_extension, EReal.toReal_coe]

theorem equivRealGrowth_apply (u : {u // u ∈ h.PSHTor}) (x : EuclideanSpace ℝ (Fin n)) :
    ((h.equivRealGrowth u).val x : EReal) = h.profile u.val x :=
  (congrFun (h.realProfile_mem u.property).2 x).symm

/-- The inverse map restricts on the torus to `Trop^*(F - F_θ)`. -/
theorem equivRealGrowth_symm_embedding
    (f : {f // f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D)})
    (a : Fin n → ℂˣ) :
    ((h.equivRealGrowth).symm f).val (polytopeToricEmbedding γ hs a) =
      ((f.val (unitTorusLog a) - h.potential (unitTorusLog a) : ℝ) : EReal) := by
  change h.extension f.val f.property (polytopeToricEmbedding γ hs a) = _
  rw [(h.extension_spec f.val f.property).2 (polytopeToricEmbedding_mem_compl γ hs a),
    offPotential_embedding]

/-- Source `thm:toricpshbig`, bijection (1) ↔ (3): `PSH_tor(X, θ)` is in bijection with the
closed proper convex functions on `M_ℝ` which are `+∞` off `P_D`, via `φ ↦ G_φ = F_φ^*`.
(`P_D` is `n`-dimensional, in particular nonempty, since `D` is big.) -/
def equivClosedProper (hne : (toricDivisorPolytope D).Nonempty) :
    {u // u ∈ h.PSHTor} ≃ {g // g ∈ ClosedProperOnBody (toricDivisorPolytope D)} :=
  h.equivRealGrowth.trans
    (realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
      (isCompact_toricDivisorPolytope D) hne (convex_toricDivisorPolytope D))

/-- The third-class map is the Legendre transform `G_φ = F_φ^*`. -/
theorem equivClosedProper_apply (hne : (toricDivisorPolytope D).Nonempty)
    (u : {u // u ∈ h.PSHTor}) :
    (h.equivClosedProper hne u).val = h.legendre u.val := by
  change conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
    (fun x => ((h.realProfile u.val x : ℝ) : EReal)) = _
  rw [← (h.realProfile_mem u.property).2]
  rfl

/-- The inverse of the third-class map on the torus: `Trop^*(G^* - F_θ)`. -/
theorem equivClosedProper_symm_embedding (hne : (toricDivisorPolytope D).Nonempty)
    (g : {g // g ∈ ClosedProperOnBody (toricDivisorPolytope D)}) (a : Fin n → ℂˣ) :
    ((h.equivClosedProper hne).symm g).val (polytopeToricEmbedding γ hs a) =
      (((conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip g.val (unitTorusLog a)).toReal -
        h.potential (unitTorusLog a) : ℝ) : EReal) := by
  change ((h.equivRealGrowth).symm
    ((realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
      (isCompact_toricDivisorPolytope D) hne (convex_toricDivisorPolytope D)).symm g)).val
        (polytopeToricEmbedding γ hs a) = _
  rw [equivRealGrowth_symm_embedding, realGrowthClosedProperEquiv_symm_apply]

/-! ### Comparison -/

/-- Every toric potential is the bounded analytic filling of its torus values. -/
theorem eq_analyticExtension {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u) :
    u = analyticExtension (polytopeToricBoundary γ hs) u := by
  obtain ⟨C, hC⟩ := h.exists_upper_bound hu
  have hb : LocallyBoundedAboveOff (polytopeToricBoundary γ hs) u :=
    fun _ => ⟨univ, univ_mem, C, fun p _ _ => hC p⟩
  exact (hu.isThetaPSHOn (polytopeToricBoundary γ hs)ᶜ).analyticExtension_unique
    (hasAnalyticChartEquations_polytopeToricBoundary γ hs)
    (interior_polytopeToricBoundary γ hs) hb hu (fun _ _ => rfl)

/-- Additive comparisons on the torus extend to the boundary. -/
theorem le_add_of_le_off {u v : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u)
    (hv : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm v)
    (C : ℝ) (hle : ∀ p ∉ polytopeToricBoundary γ hs, u p ≤ v p + (C : EReal)) :
    ∀ p, u p ≤ v p + (C : EReal) := by
  have hfill : analyticExtension (polytopeToricBoundary γ hs) u ≤
      analyticExtension (polytopeToricBoundary γ hs) (fun p => v p + (C : EReal)) := by
    apply uscRegularization_mono
    intro p
    by_cases hp : p ∈ polytopeToricBoundary γ hs
    · simp [hp]
    · simpa only [if_neg hp] using hle p hp
  intro p
  calc
    u p = analyticExtension (polytopeToricBoundary γ hs) u p :=
      congrFun (h.eq_analyticExtension hu) p
    _ ≤ analyticExtension (polytopeToricBoundary γ hs) (fun q => v q + (C : EReal)) p := hfill p
    _ = analyticExtension (polytopeToricBoundary γ hs) v p + (C : EReal) :=
      analyticExtension_add_coe_apply (polytopeToricBoundary γ hs) v continuous_const.continuousAt
    _ = v p + (C : EReal) := by rw [← h.eq_analyticExtension hv]

/-- The same finite constant compares two toric potentials and their profiles. -/
theorem le_add_iff {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (C : ℝ) :
    (∀ p, u p ≤ v p + (C : EReal)) ↔ ∀ x, h.profile u x ≤ h.profile v x + (C : EReal) := by
  constructor
  · intro hle x
    rw [profile, profile, add_right_comm]
    exact add_le_add (hle _) le_rfl
  · intro hle
    apply h.le_add_of_le_off hu.1 hv.1 C
    intro p hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    rw [hu.2.embedding_eq γ hs a, hv.2.embedding_eq γ hs a]
    have hx := hle (unitTorusLog a)
    rw [profile, profile, add_right_comm (v _)] at hx
    exact (EReal.addLECancellable_coe _).add_le_add_iff_right.mp hx

/-- `φ ≤ ψ ⇔ F_φ ≤ F_ψ`. -/
theorem le_iff {u v : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    u ≤ v ↔ h.profile u ≤ h.profile v := by
  change (∀ p, u p ≤ v p) ↔ ∀ x, h.profile u x ≤ h.profile v x
  simpa only [EReal.coe_zero, add_zero] using h.le_add_iff hu hv 0

/-- `φ ≼ ψ ⇔ F_φ ≼ F_ψ`. -/
theorem singularityLE_iff {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    SGPT.PSH.SingularityLE u v ↔ SGPT.PSH.SingularityLE (h.profile u) (h.profile v) := by
  rw [SGPT.PSH.singularityLE_iff_exists_real, SGPT.PSH.singularityLE_iff_exists_real]
  exact exists_congr fun C => h.le_add_iff hu hv C

include hne in
/-- Biconjugation: `F_φ = G_φ^*`. -/
theorem conjugate_legendre {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.legendre u) = h.profile u :=
  (biconjugate_eq_convexClosure_of_isContPerfPair _
      (h.profile_mem_growthClass hne hu).1.1).trans
    (convexClosure_eq_self_of_isClosedConvex (h.isClosedConvex_profile hne hu))

include hne in
/-- `F_φ ≤ F_ψ ⇔ G_ψ ≤ G_φ`. -/
theorem profile_le_iff_legendre {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    h.profile u ≤ h.profile v ↔ h.legendre v ≤ h.legendre u := by
  constructor
  · intro hle y
    exact conjugate_antitone (innerₗ (EuclideanSpace ℝ (Fin n))) hle y
  · intro hle x
    have hh := conjugate_antitone (innerₗ (EuclideanSpace ℝ (Fin n))).flip hle x
    rwa [h.conjugate_legendre hne hu, h.conjugate_legendre hne hv] at hh

include hne in
/-- `F_φ ≼ F_ψ ⇔ G_ψ ≼ G_φ`. -/
theorem profile_singularityLE_iff_legendre {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    SGPT.PSH.SingularityLE (h.profile u) (h.profile v) ↔
      SGPT.PSH.SingularityLE (h.legendre v) (h.legendre u) := by
  constructor
  · exact conjugate_singularityLE (innerₗ (EuclideanSpace ℝ (Fin n)))
  · intro hle
    have hh := conjugate_singularityLE (innerₗ (EuclideanSpace ℝ (Fin n))).flip hle
    rwa [h.conjugate_legendre hne hu, h.conjugate_legendre hne hv] at hh

/-! ### Constants (source `prop:toricpluscstbig`) -/

theorem mem_PSHTor_add_const {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (C : ℝ) : (fun p => u p + (C : EReal)) ∈ h.PSHTor :=
  ⟨hu.1.add_const C, fun a ha p => by simp only [hu.2 a ha p]⟩

/-- Source `prop:toricpluscstbig`: `F_{φ+C} = F_φ + C`. -/
theorem profile_add_const (u : PolytopeToricVariety γ hs → EReal) (C : ℝ) :
    h.profile (fun p => u p + (C : EReal)) = fun x => h.profile u x + (C : EReal) := by
  funext x
  exact add_right_comm _ (C : EReal) _

/-- Source `prop:toricpluscstbig`: `G_{φ+C} = G_φ - C`. -/
theorem legendre_add_const (u : PolytopeToricVariety γ hs → EReal) (C : ℝ) :
    h.legendre (fun p => u p + (C : EReal)) = fun y => h.legendre u y - (C : EReal) := by
  funext y
  let B := innerₗ (EuclideanSpace ℝ (Fin n))
  let f := h.profile u
  have hcost (x : EuclideanSpace ℝ (Fin n)) :
      (B x y : EReal) - (f x + (C : EReal)) = ((B x y : EReal) - f x) - (C : EReal) := by
    simpa only [add_zero, zero_add, zero_sub, sub_eq_add_neg] using
      (EReal.add_sub_add_comm (a := (B x y : EReal)) (b := 0)
        (c := f x) (d := (C : EReal)) (.inr (EReal.coe_ne_top C))
        (.inr (EReal.coe_ne_bot C)))
  simp only [legendre, profile_add_const, conjugate]
  change (⨆ x, (B x y : EReal) - (f x + (C : EReal))) = (⨆ x, (B x y : EReal) - f x) - (C : EReal)
  simp_rw [hcost]
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
    SGPT.Foundations.Analysis.FirstPass.iSup_add_coe (fun x => (B x y : EReal) - f x) (-C)

end BigToricMetric

end SGPT.Toric
