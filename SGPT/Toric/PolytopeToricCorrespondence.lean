import SGPT.Toric.PolytopeToricVariety
import SGPT.Toric.ProjectiveToricModelEnvelope

/-!
# Toric `ω`-psh functions and convex functions on a Delzant toric manifold

Source `chapter_toric_ample.tex`:

* `thm:toricpsh`: canonical bijections between `PSH_tor(X, ω)`, the convex functions
  `F : N_ℝ → ℝ` with `F ≼ Supp_P` (`RealGrowthClass`), and the closed proper convex
  functions on `M_ℝ` which are `+∞` off `P` (`ClosedProperOnBody`);
* `prop:toricpshcomp`: the three orders (pointwise and singularity) agree;
* `prop:toricpluscst`: `F_{φ+C} = F_φ + C` and `G_{φ+C} = G_φ - C`.

Here `X = PolytopeToricVariety γ hs` is the toric manifold of an arbitrary Delzant
lattice polytope `P = conv(γ)` with its Guillemin Kähler form.  The forward map is the
profile `F_φ` of `polytopeToricProfile`; its inverse is the unique `ω`-psh extension
of `Trop^*(F - F_0)` across the toric boundary, constructed with the bounded
analytic extension theorem (source `thm:GRexten`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Finite additive cancellation in `EReal`. -/
theorem EReal.eq_coe_sub_of_add_coe_eq {a : EReal} {c r : ℝ}
    (h : a + (c : EReal) = (r : EReal)) : a = ((r - c : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => simp at h
  | top => simp at h
  | coe x =>
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_eq_coe_iff]
    linarith

variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-! ### From toric potentials to convex functions -/

/-- Source `thm:toricpsh` (forward map) and `lma:convextopsh`: the profile of a toric
`ω`-psh function is a finite convex function. -/
theorem polytopeToricProfile_real_convex {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u)
    (hi : PolytopeToricInvariant γ hs u) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ univ f ∧
      polytopeToricProfile γ hs u = fun x => (f x : EReal) := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  let w : latticePolytopeVertices γ := ⟨v, hv⟩
  let b := originalPolytopeNativeBasis γ hs w
  let c := originalPolytopeNativeModelChart γ hs w
  let H : EuclideanSpace ℝ (Fin n) → EReal := fun y =>
    polytopeToricProfile γ hs u (latticeBasisLogInverse b y) +
      ((-latticeFunctional w.val (latticeBasisLogInverse b y) : ℝ) : EReal)
  have hp := plurisubharmonicOn_polytopeToric_vertexChart γ hs hu w
  have heq : ∀ z ∈ complexTorus n,
      u (c.symm z) + (originalGuilleminGeometricNativeWeight γ hs w z : EReal) =
        tropicalPullback H z :=
    fun z hz => polytopeToric_vertexChart_corrected_eq γ hs
      (fun a => hi.embedding_eq γ hs a) w hz
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
  obtain ⟨h, hh, hH⟩ := exists_real_convex_of_pshOn_tropicalPullback hpsh
  refine ⟨fun x => h (latticeBasisLogMap b x) + latticeFunctional w.val x, ?_, ?_⟩
  · have h1 : ConvexOn ℝ univ (h ∘ latticeBasisLogMap b) := by
      simpa only [preimage_univ] using hh.comp_linearMap (latticeBasisLogMap b)
    exact h1.add ((latticeFunctional w.val).convexOn convex_univ)
  · funext x
    have hx := congrFun hH (latticeBasisLogMap b x)
    simp only [H, latticeBasisLogInverse_logMap] at hx
    rw [EReal.eq_coe_sub_of_add_coe_eq hx, sub_neg_eq_add]

/-- The profile of a toric potential has support growth: `F_φ ≼ Supp_P`. -/
theorem polytopeToricProfile_le_support {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u) :
    SGPT.PSH.SingularityLE (polytopeToricProfile γ hs u)
      (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ)) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_polytopeToricPSH γ hs hu
  obtain ⟨h1, _⟩ := (SGPT.PSH.singularityEquiv_iff _ _).mp
    (polytopeToricReference_singularityEquiv_support γ hs)
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h1
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨C + D, fun x => ?_⟩
  calc
    polytopeToricProfile γ hs u x ≤ (C : EReal) +
        (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ) x +
          (D : EReal)) := add_le_add (hC _) (hD x)
    _ = _ := by
      rw [add_comm (C : EReal), add_assoc, ← EReal.coe_add, add_comm D C]

/-- The real-valued profile `F_φ` of a toric potential. -/
def polytopeToricRealProfile (u : PolytopeToricVariety γ hs → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (polytopeToricProfile γ hs u x).toReal

/-- Source `thm:toricpsh`, map (1) → (2): `F_φ ∈ 𝓟(N_ℝ, P)`. -/
theorem polytopeToricRealProfile_mem {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricRealProfile γ hs u ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) ∧
      polytopeToricProfile γ hs u = fun x => (polytopeToricRealProfile γ hs u x : EReal) := by
  obtain ⟨f, hf, heq⟩ := polytopeToricProfile_real_convex γ hs hu.1 hu.2
  have hreal : polytopeToricRealProfile γ hs u = f := by
    funext x
    simp only [polytopeToricRealProfile, heq, EReal.toReal_coe]
  have hcoe : polytopeToricProfile γ hs u =
      fun x => (polytopeToricRealProfile γ hs u x : EReal) := by
    rw [hreal]; exact heq
  refine ⟨⟨by rw [hreal]; exact hf, ?_⟩, hcoe⟩
  rw [← hcoe]
  exact polytopeToricProfile_le_support γ hs hu.1

/-- The extended-valued profile lies in the growth class `𝓟(N_ℝ, P)`. -/
theorem polytopeToricProfile_mem_growthClass {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricProfile γ hs u ∈
      GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) := by
  have hmem := polytopeToricRealProfile_mem γ hs hu
  rw [hmem.2]
  exact ((realGrowthEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
    (isCompact_polytopeToricMomentPolytope γ) (nonempty_polytopeToricMomentPolytope γ))
      ⟨_, hmem.1⟩).property

/-- The profile of a toric potential is closed convex. -/
theorem isClosedConvex_polytopeToricProfile {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) : IsClosedConvex (polytopeToricProfile γ hs u) :=
  isClosedConvex_of_mem_growthClass _ (isCompact_polytopeToricMomentPolytope γ)
    (nonempty_polytopeToricMomentPolytope γ) (polytopeToricProfile_mem_growthClass γ hs hu)

/-! ### From convex functions to toric potentials -/

/-- A fixed reference vertex of `P`. -/
def polytopeToricBaseVertex : latticePolytopeVertices γ :=
  ⟨(nonempty_latticePolytopeVertices γ).some, (nonempty_latticePolytopeVertices γ).some_mem⟩

/-- The tropicalization map of the open torus of `X`, read in the base vertex chart. -/
def polytopeToricLog (p : PolytopeToricVariety γ hs) : EuclideanSpace ℝ (Fin n) :=
  latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ))
    (tropicalization (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ) p))

theorem polytopeToricLog_embedding (a : Fin n → ℂˣ) :
    polytopeToricLog γ hs (polytopeToricEmbedding γ hs a) = unitTorusLog a := by
  rw [polytopeToricLog, tropicalization_polytopeToricVertexChart_embedding,
    latticeBasisLogInverse_logMap]

/-- The torus potential `Trop^*(F - F_0)` attached to a convex function `F`.  Its values
on the toric boundary are irrelevant (only the extension across it is used). -/
def polytopeToricOffPotential (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : PolytopeToricVariety γ hs) : EReal :=
  ((f (polytopeToricLog γ hs p) - polytopeToricReference γ hs (polytopeToricLog γ hs p) : ℝ) :
    EReal)

theorem polytopeToricOffPotential_embedding (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin n → ℂˣ) :
    polytopeToricOffPotential γ hs f (polytopeToricEmbedding γ hs a) =
      ((f (unitTorusLog a) - polytopeToricReference γ hs (unitTorusLog a) : ℝ) : EReal) := by
  rw [polytopeToricOffPotential, polytopeToricLog_embedding]

theorem polytopeToricOffPotential_invariantValues (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin n → ℂˣ) :
    polytopeToricOffPotential γ hs f (polytopeToricEmbedding γ hs a) =
      polytopeToricOffPotential γ hs f
        (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a))) := by
  rw [polytopeToricOffPotential_embedding, polytopeToricOffPotential_embedding,
    unitTorusLog_positiveTorusPoint]

theorem polytopeToricProfile_offPotential (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    polytopeToricProfile γ hs (polytopeToricOffPotential γ hs f) = fun x => (f x : EReal) := by
  funext x
  rw [polytopeToricProfile, polytopeToricOffPotential_embedding, unitTorusLog_positiveTorusPoint,
    ← EReal.coe_add]
  congr 1
  ring

/-- `Trop^*(F - F_0)` is `ω`-psh on the open torus for every finite convex `F`. -/
theorem isThetaPSHOn_polytopeToricOffPotential {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ univ f) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSHOn (polytopeToricOmega γ hs)
      (polytopeToricOffPotential γ hs f) (polytopeToricBoundary γ hs)ᶜ := by
  let w := polytopeToricBaseVertex γ
  let b := originalPolytopeNativeBasis γ hs w
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    f (latticeBasisLogInverse b y) + -latticeFunctional w.val (latticeBasisLogInverse b y)
  have hH : ConvexOn ℝ univ H := by
    have h1 : ConvexOn ℝ univ (f ∘ latticeBasisLogInverse b) := by
      simpa only [preimage_univ] using hf.comp_linearMap (latticeBasisLogInverse b)
    have h2 : ConvexOn ℝ univ (-(latticeFunctional w.val ∘ₗ latticeBasisLogInverse b)) :=
      LinearMap.convexOn _ convex_univ
    exact h1.add h2
  have htp := plurisubharmonicOn_tropicalPullback_of_convexOn hH
  apply isThetaPSHOn_of_finite_single_chart (polytopeToricVertexChart γ hs w)
    (ρ := originalGuilleminGeometricNativeWeight γ hs w)
  · intro p hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    rw [polytopeToricVertexChart_chart, originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs w a
  · exact (contDiff_originalGuilleminGeometricNativeWeight γ hs w).contDiffOn
  · exact polytopeToricOmega_coeff_vertexChart γ hs w
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
    change polytopeToricOffPotential γ hs f ((originalPolytopeNativeModelChart γ hs w).symm y) +
      (originalGuilleminGeometricNativeWeight γ hs w y : EReal) = _
    rw [polytopeToric_vertexChart_corrected_eq γ hs
      (polytopeToricOffPotential_invariantValues γ hs f) w hy,
      polytopeToricProfile_offPotential]
    simp only [tropicalPullback, H, b, EReal.coe_add]
  · intro p _
    exact ⟨_, rfl⟩

/-- For `F ≼ Supp_P`, the torus potential `Trop^*(F - F_0)` is bounded above. -/
theorem exists_upper_bound_polytopeToricOffPotential {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    ∃ C : ℝ, ∀ p, polytopeToricOffPotential γ hs f p ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2
  obtain ⟨_, h2⟩ := (SGPT.PSH.singularityEquiv_iff _ _).mp
    (polytopeToricReference_singularityEquiv_support γ hs)
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h2
  refine ⟨D + C, fun p => ?_⟩
  set x := polytopeToricLog γ hs p
  have hle : ((f x : ℝ) : EReal) ≤ ((polytopeToricReference γ hs x + D + C : ℝ) : EReal) := by
    calc ((f x : ℝ) : EReal)
        ≤ support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ) x +
            (C : EReal) := hC x
      _ ≤ ((polytopeToricReference γ hs x : EReal) + (D : EReal)) + (C : EReal) :=
            add_le_add (hD x) le_rfl
      _ = _ := by rw [← EReal.coe_add, ← EReal.coe_add]
  have hle' : f x ≤ polytopeToricReference γ hs x + D + C := EReal.coe_le_coe_iff.mp hle
  change ((f x - polytopeToricReference γ hs x : ℝ) : EReal) ≤ ((D + C : ℝ) : EReal)
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Source `thm:toricpsh`, map (2) → (1) (via `thm:GRexten`): existence and uniqueness of
the `ω`-psh extension of `Trop^*(F - F_0)` across the toric boundary. -/
theorem existsUnique_polytopeToricExtension {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    ∃! v : PolytopeToricVariety γ hs → EReal,
      (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) v ∧
        EqOn v (polytopeToricOffPotential γ hs f) (polytopeToricBoundary γ hs)ᶜ := by
  obtain ⟨C, hC⟩ := exists_upper_bound_polytopeToricOffPotential γ hs hf
  exact exists_unique_bounded_theta_analytic_extension
    (isThetaPSHOn_polytopeToricOffPotential γ hs hf.1)
    (hasAnalyticChartEquations_polytopeToricBoundary γ hs)
    (interior_polytopeToricBoundary γ hs)
    (fun _ _ => ⟨univ, univ_mem, C, fun p _ _ => hC p⟩)

/-- The toric potential attached to `F ∈ 𝓟(N_ℝ, P)`. -/
def polytopeToricExtension (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    PolytopeToricVariety γ hs → EReal :=
  Classical.choose (existsUnique_polytopeToricExtension γ hs hf)

theorem polytopeToricExtension_spec (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs)
        (polytopeToricExtension γ hs f hf) ∧
      EqOn (polytopeToricExtension γ hs f hf) (polytopeToricOffPotential γ hs f)
        (polytopeToricBoundary γ hs)ᶜ :=
  (Classical.choose_spec (existsUnique_polytopeToricExtension γ hs hf)).1

theorem polytopeToricExtension_unique (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ))
    (v : PolytopeToricVariety γ hs → EReal)
    (hv : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) v)
    (heq : EqOn v (polytopeToricOffPotential γ hs f) (polytopeToricBoundary γ hs)ᶜ) :
    v = polytopeToricExtension γ hs f hf :=
  (Classical.choose_spec (existsUnique_polytopeToricExtension γ hs hf)).2 v ⟨hv, heq⟩

/-- Uniqueness of the extension gives its `T_c`-invariance. -/
theorem polytopeToricExtension_invariant (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    PolytopeToricInvariant γ hs (polytopeToricExtension γ hs f hf) := by
  intro a ha p
  have h1 := isThetaPSH_comp_polytopeToricAction γ hs (polytopeToricExtension_spec γ hs f hf).1 ha
  have h2 : EqOn (fun q => polytopeToricExtension γ hs f hf (polytopeToricAction γ hs a q))
      (polytopeToricOffPotential γ hs f) (polytopeToricBoundary γ hs)ᶜ := by
    intro q hq
    obtain ⟨b, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs q).mp hq
    change polytopeToricExtension γ hs f hf
      (polytopeToricAction γ hs a (polytopeToricEmbedding γ hs b)) = _
    rw [polytopeToricAction_embedding,
      (polytopeToricExtension_spec γ hs f hf).2 (polytopeToricEmbedding_mem_compl γ hs _),
      polytopeToricOffPotential_embedding, polytopeToricOffPotential_embedding,
      unitTorusLog_compact_mul ha]
  exact congrFun (polytopeToricExtension_unique γ hs f hf _ h1 h2) p

theorem polytopeToricExtension_mem (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    polytopeToricExtension γ hs f hf ∈ PolytopeToricPSH γ hs :=
  ⟨(polytopeToricExtension_spec γ hs f hf).1, polytopeToricExtension_invariant γ hs f hf⟩

/-- Source `eq:FvarphidefGdef` for the extension: its profile is `F`. -/
theorem polytopeToricProfile_extension (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ)) :
    polytopeToricProfile γ hs (polytopeToricExtension γ hs f hf) = fun x => (f x : EReal) := by
  rw [← polytopeToricProfile_offPotential γ hs f]
  funext x
  rw [polytopeToricProfile, polytopeToricProfile,
    (polytopeToricExtension_spec γ hs f hf).2 (polytopeToricEmbedding_mem_compl γ hs _)]

/-- Every toric potential is the extension of its own profile. -/
theorem polytopeToricExtension_realProfile {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricExtension γ hs (polytopeToricRealProfile γ hs u)
      (polytopeToricRealProfile_mem γ hs hu).1 = u := by
  symm
  apply polytopeToricExtension_unique γ hs _ _ u hu.1
  intro p hp
  obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
  rw [polytopeToricOffPotential_embedding, hu.2.embedding_eq γ hs a]
  have h := congrFun (polytopeToricRealProfile_mem γ hs hu).2 (unitTorusLog a)
  rw [polytopeToricProfile] at h
  exact EReal.eq_coe_sub_of_add_coe_eq h

/-- Source `thm:toricpsh`, bijection (1) ↔ (2): `PSH_tor(X, ω) ≃ 𝓟(N_ℝ, P)`, `φ ↦ F_φ`,
with inverse `F ↦` the `ω`-psh extension of `Trop^*(F - F_0)`. -/
def polytopeToricEquivRealGrowth :
    {u // u ∈ PolytopeToricPSH γ hs} ≃
      {f // f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n)))
        (polytopeToricMomentPolytope γ)} where
  toFun u := ⟨polytopeToricRealProfile γ hs u.val, (polytopeToricRealProfile_mem γ hs u.property).1⟩
  invFun f := ⟨polytopeToricExtension γ hs f.val f.property,
    polytopeToricExtension_mem γ hs f.val f.property⟩
  left_inv u := Subtype.ext (polytopeToricExtension_realProfile γ hs u.property)
  right_inv f := by
    apply Subtype.ext
    funext x
    change (polytopeToricProfile γ hs (polytopeToricExtension γ hs f.val f.property) x).toReal = _
    simp only [polytopeToricProfile_extension, EReal.toReal_coe]

theorem polytopeToricEquivRealGrowth_apply (u : {u // u ∈ PolytopeToricPSH γ hs})
    (x : EuclideanSpace ℝ (Fin n)) :
    ((polytopeToricEquivRealGrowth γ hs u).val x : EReal) = polytopeToricProfile γ hs u.val x :=
  (congrFun (polytopeToricRealProfile_mem γ hs u.property).2 x).symm

/-- The inverse map restricts on the torus to `Trop^*(F - F_0)`. -/
theorem polytopeToricEquivRealGrowth_symm_embedding
    (f : {f // f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n)))
      (polytopeToricMomentPolytope γ)}) (a : Fin n → ℂˣ) :
    ((polytopeToricEquivRealGrowth γ hs).symm f).val (polytopeToricEmbedding γ hs a) =
      ((f.val (unitTorusLog a) - polytopeToricReference γ hs (unitTorusLog a) : ℝ) : EReal) := by
  change polytopeToricExtension γ hs f.val f.property (polytopeToricEmbedding γ hs a) = _
  rw [(polytopeToricExtension_spec γ hs f.val f.property).2
    (polytopeToricEmbedding_mem_compl γ hs a), polytopeToricOffPotential_embedding]

/-- Source `thm:toricpsh`, bijection (1) ↔ (3): `PSH_tor(X, ω)` is in bijection with the
closed proper convex functions on `M_ℝ` which are `+∞` off `P`, via `φ ↦ G_φ = F_φ^*`. -/
def polytopeToricEquivClosedProper :
    {u // u ∈ PolytopeToricPSH γ hs} ≃
      {g // g ∈ ClosedProperOnBody (polytopeToricMomentPolytope γ)} :=
  (polytopeToricEquivRealGrowth γ hs).trans
    (realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
      (isCompact_polytopeToricMomentPolytope γ) (nonempty_polytopeToricMomentPolytope γ)
      (convex_polytopeToricMomentPolytope γ))

/-- The third-class map is the Legendre transform `G_φ = F_φ^*`. -/
theorem polytopeToricEquivClosedProper_apply (u : {u // u ∈ PolytopeToricPSH γ hs}) :
    (polytopeToricEquivClosedProper γ hs u).val = polytopeToricLegendre γ hs u.val := by
  change conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
    (fun x => ((polytopeToricRealProfile γ hs u.val x : ℝ) : EReal)) = _
  rw [← (polytopeToricRealProfile_mem γ hs u.property).2]
  rfl

/-- The inverse of the third-class map on the torus: `Trop^*(G^* - F_0)`. -/
theorem polytopeToricEquivClosedProper_symm_embedding
    (g : {g // g ∈ ClosedProperOnBody (polytopeToricMomentPolytope γ)}) (a : Fin n → ℂˣ) :
    ((polytopeToricEquivClosedProper γ hs).symm g).val (polytopeToricEmbedding γ hs a) =
      (((conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip g.val (unitTorusLog a)).toReal -
        polytopeToricReference γ hs (unitTorusLog a) : ℝ) : EReal) := by
  change ((polytopeToricEquivRealGrowth γ hs).symm
    ((realGrowthClosedProperEquiv (innerₗ (EuclideanSpace ℝ (Fin n)))
      (isCompact_polytopeToricMomentPolytope γ) (nonempty_polytopeToricMomentPolytope γ)
      (convex_polytopeToricMomentPolytope γ)).symm g)).val (polytopeToricEmbedding γ hs a) = _
  rw [polytopeToricEquivRealGrowth_symm_embedding, realGrowthClosedProperEquiv_symm_apply]

/-! ### Comparison (source `prop:toricpshcomp`) -/

/-- Every toric potential is the bounded analytic filling of its torus values. -/
theorem polytopeToricPSH_eq_analyticExtension {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u) :
    u = analyticExtension (polytopeToricBoundary γ hs) u := by
  obtain ⟨C, hC⟩ := exists_upper_bound_polytopeToricPSH γ hs hu
  have hb : LocallyBoundedAboveOff (polytopeToricBoundary γ hs) u :=
    fun _ => ⟨univ, univ_mem, C, fun p _ _ => hC p⟩
  exact (hu.isThetaPSHOn (polytopeToricBoundary γ hs)ᶜ).analyticExtension_unique
    (hasAnalyticChartEquations_polytopeToricBoundary γ hs)
    (interior_polytopeToricBoundary γ hs) hb hu (fun _ _ => rfl)

/-- Additive comparisons on the torus extend to the boundary. -/
theorem polytopeToricPSH_le_add_of_le_off {u v : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u)
    (hv : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) v)
    (C : ℝ) (h : ∀ p ∉ polytopeToricBoundary γ hs, u p ≤ v p + (C : EReal)) :
    ∀ p, u p ≤ v p + (C : EReal) := by
  have hfill : analyticExtension (polytopeToricBoundary γ hs) u ≤
      analyticExtension (polytopeToricBoundary γ hs) (fun p => v p + (C : EReal)) := by
    apply uscRegularization_mono
    intro p
    by_cases hp : p ∈ polytopeToricBoundary γ hs
    · simp [hp]
    · simpa only [if_neg hp] using h p hp
  intro p
  calc
    u p = analyticExtension (polytopeToricBoundary γ hs) u p :=
      congrFun (polytopeToricPSH_eq_analyticExtension γ hs hu) p
    _ ≤ analyticExtension (polytopeToricBoundary γ hs) (fun q => v q + (C : EReal)) p := hfill p
    _ = analyticExtension (polytopeToricBoundary γ hs) v p + (C : EReal) :=
      analyticExtension_add_coe_apply (polytopeToricBoundary γ hs) v continuous_const.continuousAt
    _ = v p + (C : EReal) := by rw [← polytopeToricPSH_eq_analyticExtension γ hs hv]

/-- The same finite constant compares two toric potentials and their profiles. -/
theorem polytopeToricPSH_le_add_iff {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) (C : ℝ) :
    (∀ p, u p ≤ v p + (C : EReal)) ↔
      ∀ x, polytopeToricProfile γ hs u x ≤ polytopeToricProfile γ hs v x + (C : EReal) := by
  constructor
  · intro h x
    rw [polytopeToricProfile, polytopeToricProfile, add_right_comm]
    exact add_le_add (h _) le_rfl
  · intro h
    apply polytopeToricPSH_le_add_of_le_off γ hs hu.1 hv.1 C
    intro p hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    rw [hu.2.embedding_eq γ hs a, hv.2.embedding_eq γ hs a]
    have hx := h (unitTorusLog a)
    rw [polytopeToricProfile, polytopeToricProfile, add_right_comm (v _)] at hx
    exact (EReal.addLECancellable_coe _).add_le_add_iff_right.mp hx

/-- Source `prop:toricpshcomp`, pointwise version of (1) ⇔ (2): `φ ≤ ψ ⇔ F_φ ≤ F_ψ`. -/
theorem polytopeToricPSH_le_iff {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) :
    u ≤ v ↔ polytopeToricProfile γ hs u ≤ polytopeToricProfile γ hs v := by
  change (∀ p, u p ≤ v p) ↔ ∀ x, polytopeToricProfile γ hs u x ≤ polytopeToricProfile γ hs v x
  simpa only [EReal.coe_zero, add_zero] using polytopeToricPSH_le_add_iff γ hs hu hv 0

/-- Source `prop:toricpshcomp`, (1) ⇔ (2): `φ ≼ ψ ⇔ F_φ ≼ F_ψ`. -/
theorem polytopeToricPSH_singularityLE_iff {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) :
    SGPT.PSH.SingularityLE u v ↔
      SGPT.PSH.SingularityLE (polytopeToricProfile γ hs u) (polytopeToricProfile γ hs v) := by
  rw [SGPT.PSH.singularityLE_iff_exists_real, SGPT.PSH.singularityLE_iff_exists_real]
  exact exists_congr fun C => polytopeToricPSH_le_add_iff γ hs hu hv C

/-- Biconjugation: `F_φ = G_φ^*`. -/
theorem conjugate_polytopeToricLegendre {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricLegendre γ hs u) =
      polytopeToricProfile γ hs u := by
  exact (biconjugate_eq_convexClosure_of_isContPerfPair _
      (polytopeToricProfile_mem_growthClass γ hs hu).1.1).trans
    (convexClosure_eq_self_of_isClosedConvex (isClosedConvex_polytopeToricProfile γ hs hu))

/-- Source `prop:toricpshcomp`, (2) ⇔ (3), pointwise: `F_φ ≤ F_ψ ⇔ G_ψ ≤ G_φ`. -/
theorem polytopeToricProfile_le_iff_legendre {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) :
    polytopeToricProfile γ hs u ≤ polytopeToricProfile γ hs v ↔
      polytopeToricLegendre γ hs v ≤ polytopeToricLegendre γ hs u := by
  constructor
  · intro h y
    exact conjugate_antitone (innerₗ (EuclideanSpace ℝ (Fin n))) h y
  · intro h x
    have hh := conjugate_antitone (innerₗ (EuclideanSpace ℝ (Fin n))).flip h x
    rwa [conjugate_polytopeToricLegendre γ hs hu, conjugate_polytopeToricLegendre γ hs hv] at hh

/-- Source `prop:toricpshcomp`, (2) ⇔ (3): `F_φ ≼ F_ψ ⇔ G_ψ ≼ G_φ`. -/
theorem polytopeToricProfile_singularityLE_iff_legendre {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) :
    SGPT.PSH.SingularityLE (polytopeToricProfile γ hs u) (polytopeToricProfile γ hs v) ↔
      SGPT.PSH.SingularityLE (polytopeToricLegendre γ hs v) (polytopeToricLegendre γ hs u) := by
  constructor
  · exact conjugate_singularityLE (innerₗ (EuclideanSpace ℝ (Fin n)))
  · intro h
    have hh := conjugate_singularityLE (innerₗ (EuclideanSpace ℝ (Fin n))).flip h
    rwa [conjugate_polytopeToricLegendre γ hs hu, conjugate_polytopeToricLegendre γ hs hv] at hh

/-- Source `prop:toricpshcomp` with `≤`: `φ ≤ ψ ⇔ G_ψ ≤ G_φ`. -/
theorem polytopeToricPSH_le_iff_legendre {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) :
    u ≤ v ↔ polytopeToricLegendre γ hs v ≤ polytopeToricLegendre γ hs u :=
  (polytopeToricPSH_le_iff γ hs hu hv).trans (polytopeToricProfile_le_iff_legendre γ hs hu hv)

/-- Source `prop:toricpshcomp` with `≼`: `φ ≼ ψ ⇔ G_ψ ≼ G_φ`. -/
theorem polytopeToricPSH_singularityLE_iff_legendre {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs) :
    SGPT.PSH.SingularityLE u v ↔
      SGPT.PSH.SingularityLE (polytopeToricLegendre γ hs v) (polytopeToricLegendre γ hs u) :=
  (polytopeToricPSH_singularityLE_iff γ hs hu hv).trans
    (polytopeToricProfile_singularityLE_iff_legendre γ hs hu hv)

/-! ### Constants (source `prop:toricpluscst`) -/

theorem mem_polytopeToricPSH_add_const {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (C : ℝ) :
    (fun p => u p + (C : EReal)) ∈ PolytopeToricPSH γ hs :=
  ⟨hu.1.add_const C, fun a ha p => by simp only [hu.2 a ha p]⟩

/-- Source `prop:toricpluscst`: `F_{φ+C} = F_φ + C`. -/
theorem polytopeToricProfile_add_const (u : PolytopeToricVariety γ hs → EReal) (C : ℝ) :
    polytopeToricProfile γ hs (fun p => u p + (C : EReal)) =
      fun x => polytopeToricProfile γ hs u x + (C : EReal) := by
  funext x
  exact add_right_comm _ (C : EReal) _

/-- Source `prop:toricpluscst`: `G_{φ+C} = G_φ - C`. -/
theorem polytopeToricLegendre_add_const (u : PolytopeToricVariety γ hs → EReal) (C : ℝ) :
    polytopeToricLegendre γ hs (fun p => u p + (C : EReal)) =
      fun y => polytopeToricLegendre γ hs u y - (C : EReal) := by
  funext y
  let B := innerₗ (EuclideanSpace ℝ (Fin n))
  let f := polytopeToricProfile γ hs u
  have hcost (x : EuclideanSpace ℝ (Fin n)) :
      (B x y : EReal) - (f x + (C : EReal)) = ((B x y : EReal) - f x) - (C : EReal) := by
    simpa only [add_zero, zero_add, zero_sub, sub_eq_add_neg] using
      (EReal.add_sub_add_comm (a := (B x y : EReal)) (b := 0)
        (c := f x) (d := (C : EReal)) (.inr (EReal.coe_ne_top C))
        (.inr (EReal.coe_ne_bot C)))
  simp only [polytopeToricLegendre, polytopeToricProfile_add_const, conjugate]
  change (⨆ x, (B x y : EReal) - (f x + (C : EReal))) = (⨆ x, (B x y : EReal) - f x) - (C : EReal)
  simp_rw [hcost]
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
    SGPT.Foundations.Analysis.FirstPass.iSup_add_coe (fun x => (B x y : EReal) - f x) (-C)

end SGPT.Toric
