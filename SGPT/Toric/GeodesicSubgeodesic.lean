import SGPT.Toric.GeodesicChart
import SGPT.Toric.PolytopeToricOperations
import SGPT.PSH.SourceSubgeodesicEndpoints
import SGPT.PSH.SourceSubgeodesicConvexity

/-!
# Toric subgeodesics and convex functions on `N_ℝ × (0,1)`

Source `chapter_toric_big.tex`, `prop:toricsubgeod`: for `φ₀, φ₁ ∈ PSH_tor(X, θ)` there is a
canonical bijection between

1. the `T_c`-invariant subgeodesics `(φ_t)_{t ∈ (0,1)}` from `φ₀` to `φ₁`, and
2. the convex functions `F : N_ℝ × (0,1) → ℝ` with `F_r → F_{φ₁}` (resp. `F_{φ₀}`) everywhere
   as `r → 1-` (resp. `r → 0+`), where `F_r = F(·, r)`;

namely `F(x, t) = F_{φ_t}(x)`.

Here `X = PolytopeToricVariety γ hs`, `θ = c_1(O(D), h)` for an arbitrary torus-invariant
divisor `D` and `T_c`-invariant metric `h` (`BigToricMetric`), and subgeodesics are the source
ones (`SourceSubgeodesicFrom`: the complexification on the strip `X × {0 < Re τ < 1}` is
`p₁^*θ`-psh and the slices converge in the global `L¹` topology of an arbitrary Kähler form
`ω`).  A family indexed by `(0,1)` is a function `Ioo 0 1 → X → EReal`; it is fed to the
real-time subgeodesic predicate through `ioo01Curve` (whose values off `(0,1)` are never read).
A function on `N_ℝ × (0,1)` is a function on the subtype; its convexity is `ConvexOn` of its
extension `stripFunction` on the convex set `N_ℝ × (0,1)`.

## Route

* (1) → (2): convexity is the chart computation `convexOn_profile_of_jointThetaPSH`.  For the
  boundary values we use `cor:subgeodboundary` (`source_subgeodesic_endpoints_whole`): the
  pointwise limits exist, are `≤` the endpoint and equal to it quasi-everywhere.  On the torus
  this gives a finite convex limit `≤ F_{φ₀}` (bounded below by the profile of the toric
  `θ`-psh slice infimum), equal to `F_{φ₀}` on a dense set (pluripolar sets are chart-null),
  hence everywhere by continuity.  This replaces the source's `L¹ ⇒ a.e. ⇒ thm:seqconv`
  argument.
* (2) → (1): `F_r ≤ (1-r) F_{φ₀} + r F_{φ₁}` (convexity and the limits), so `F_r ∈ 𝓟(N_ℝ, P_D)`
  and `φ_r` is the toric potential of `F_r` (`thm:toricpshbig`).  The complexification is
  `p₁^*θ`-psh by `plurisubharmonicOn_vertexChart_strip` (via `thm:GRexten` in each chart).  The
  `L¹` limits follow from dominated convergence in each chart (pointwise convergence on the
  torus, domination by the toric slice infimum and a uniform upper bound), instead of the
  source's `L¹`-compactness argument.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators

/-- A family indexed by `(0,1)`, read as a real-time curve (extended by `u` off `(0,1)`;
the subgeodesic predicate never reads those values). -/
def ioo01Curve {X : Type*} (c : Ioo (0 : ℝ) 1 → X → EReal) (u : X → EReal) (t : ℝ) : X → EReal :=
  if ht : t ∈ Ioo (0 : ℝ) 1 then c ⟨t, ht⟩ else u

theorem ioo01Curve_of_mem {X : Type*} (c : Ioo (0 : ℝ) 1 → X → EReal) (u : X → EReal) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : ioo01Curve c u t = c ⟨t, ht⟩ := dif_pos ht

/-- A function `F : N_ℝ × (0,1) → ℝ`, extended by `0` to `N_ℝ × ℝ` (only its values on the
convex set `N_ℝ × (0,1)` are used). -/
def stripFunction {E : Type*} (F : E × Ioo (0 : ℝ) 1 → ℝ) (p : E × ℝ) : ℝ :=
  if hp : p.2 ∈ Ioo (0 : ℝ) 1 then F (p.1, ⟨p.2, hp⟩) else 0

theorem stripFunction_of_mem {E : Type*} (F : E × Ioo (0 : ℝ) 1 → ℝ) (x : E) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : stripFunction F (x, t) = F (x, ⟨t, ht⟩) := dif_pos ht

/-- `ContinuousOn` of `Trop` on the torus. -/
theorem continuousOn_tropicalization_complexTorus {n : ℕ} :
    ContinuousOn (tropicalization (n := n)) (complexTorus n) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  exact continuousAt_const.mul
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr (hz i))).comp
      (f := fun z : ComplexModel n => ‖z i‖)
      (PiLp.continuous_apply 2 _ i).continuousAt.norm)

/-- Chord bound for a convex function on `E × (0,1)` with boundary limits:
`g(x, s) ≤ (1-s) g₀(x) + s g₁(x)`. -/
theorem le_chord_of_convexOn_strip {E : Type*} [AddCommGroup E] [Module ℝ E]
    {g : E × ℝ → ℝ} (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) {g₀ g₁ : E → ℝ} (x : E)
    (h₀ : Tendsto (fun r => g (x, r)) (𝓝[>] 0) (𝓝 (g₀ x)))
    (h₁ : Tendsto (fun r => g (x, r)) (𝓝[<] 1) (𝓝 (g₁ x))) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    g (x, s) ≤ (1 - s) * g₀ x + s * g₁ x := by
  -- the convexity inequality on the vertical line
  have hline : ∀ a b, 0 < a → a < s → s < b → b < 1 →
      g (x, s) ≤ ((b - s) * g (x, a) + (s - a) * g (x, b)) / (b - a) := by
    intro a b ha has hsb hb
    have hba : 0 < b - a := by linarith
    have hα : 0 ≤ (b - s) / (b - a) := div_nonneg (by linarith) hba.le
    have hβ : 0 ≤ (s - a) / (b - a) := div_nonneg (by linarith) hba.le
    have hαβ : (b - s) / (b - a) + (s - a) / (b - a) = 1 := by field_simp; ring
    have hxa : ((x, a) : E × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 := ⟨mem_univ _, ha, has.trans hs.2⟩
    have hxb : ((x, b) : E × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 := ⟨mem_univ _, hs.1.trans hsb, hb⟩
    have h := hg.2 hxa hxb hα hβ hαβ
    have hpt : ((b - s) / (b - a)) • ((x, a) : E × ℝ) + ((s - a) / (b - a)) • (x, b) = (x, s) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, ← add_smul]
        rw [show (b - s) / (b - a) + (s - a) / (b - a) = 1 by field_simp; ring, one_smul]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        field_simp; ring
    rw [hpt] at h
    simp only [smul_eq_mul] at h
    calc g (x, s) ≤ (b - s) / (b - a) * g (x, a) + (s - a) / (b - a) * g (x, b) := h
      _ = _ := by field_simp
  -- let `a → 0+`
  have hstep : ∀ b, s < b → b < 1 → g (x, s) ≤ ((b - s) * g₀ x + s * g (x, b)) / b := by
    intro b hsb hb
    have hb0 : 0 < b := hs.1.trans hsb
    have ht : Tendsto (fun a => ((b - s) * g (x, a) + (s - a) * g (x, b)) / (b - a))
        (𝓝[>] 0) (𝓝 (((b - s) * g₀ x + (s - 0) * g (x, b)) / (b - 0))) := by
      have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      apply Tendsto.div _ (tendsto_const_nhds.sub hid) (by simpa using hb0.ne')
      exact (tendsto_const_nhds.mul h₀).add ((tendsto_const_nhds.sub hid).mul tendsto_const_nhds)
    simp only [sub_zero] at ht
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsGT hs.1] with a ha
    exact hline a b ha.1 ha.2 hsb hb
  -- let `b → 1-`
  have ht : Tendsto (fun b => ((b - s) * g₀ x + s * g (x, b)) / b) (𝓝[<] 1)
      (𝓝 (((1 - s) * g₀ x + s * g₁ x) / 1)) := by
    have hid : Tendsto (fun b : ℝ => b) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    apply Tendsto.div _ hid one_ne_zero
    exact ((hid.sub tendsto_const_nhds).mul tendsto_const_nhds).add
      (tendsto_const_nhds.mul h₁)
  rw [div_one] at ht
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT hs.2] with b hb
  exact hstep b hb.1 hb.2

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The slice infimum of a `T_c`-invariant family is `T_c`-invariant. -/
theorem polytopeToricInvariant_sliceInfimum {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    (hinv : ∀ t ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve t)) :
    PolytopeToricInvariant γ hs (sourceSliceInfimum curve) := by
  intro a ha p
  simp only [sourceSliceInfimum]
  exact iInf_congr fun t => hinv t.1 t.2 a ha p

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))

/-! ### The two sets of the bijection -/

/-- Set (1) of `prop:toricsubgeod`: `(φ_t)_{t ∈ (0,1)}` is a `T_c`-invariant subgeodesic from
`u₀` to `u₁` (source `def:subgeod`, with the global `L¹` topology of the Kähler form `ω`). -/
def IsToricSubgeodesic (u₀ u₁ : PolytopeToricVariety γ hs → EReal)
    (c : Ioo (0 : ℝ) 1 → PolytopeToricVariety γ hs → EReal) : Prop :=
  SourceSubgeodesicFrom omega h.atlasForm (ioo01Curve c u₀) u₀ u₁ ∧
    ∀ t, PolytopeToricInvariant γ hs (c t)

/-- Set (2) of `prop:toricsubgeod`: `F : N_ℝ × (0,1) → ℝ` is convex and `F_r → F_{u₁}`
(resp. `F_{u₀}`) everywhere as `r → 1-` (resp. `r → 0+`). -/
def IsToricSubgeodesicProfile (u₀ u₁ : PolytopeToricVariety γ hs → EReal)
    (F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ) : Prop :=
  ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) (stripFunction F) ∧
    (∀ x, Tendsto (fun r => stripFunction F (x, r)) (𝓝[<] 1) (𝓝 (h.realProfile u₁ x))) ∧
    (∀ x, Tendsto (fun r => stripFunction F (x, r)) (𝓝[>] 0) (𝓝 (h.realProfile u₀ x)))

/-! ### Auxiliary facts on toric potentials -/

/-- The value of a toric potential at a torus point: `u(a) = F_u(Trop a) - F_θ(Trop a)`. -/
theorem apply_embedding_of_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (a : Fin n → ℂˣ) :
    u (polytopeToricEmbedding γ hs a) =
      ((h.realProfile u (unitTorusLog a) - h.potential (unitTorusLog a) : ℝ) : EReal) := by
  rw [hu.2.embedding_eq γ hs a]
  have hh := congrFun (h.realProfile_mem hu).2 (unitTorusLog a)
  rw [profile] at hh
  exact EReal.eq_coe_sub_of_add_coe_eq hh

/-- A `θ`-psh function bounded by `C` on the torus is bounded by `C` everywhere. -/
theorem le_of_le_off_boundary {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm u) {C : EReal}
    (hC : ∀ p ∉ polytopeToricBoundary γ hs, u p ≤ C) (p : PolytopeToricVariety γ hs) :
    u p ≤ C := by
  rw [h.eq_analyticExtension hu, analyticExtension_eq_neighborhood_sup]
  exact iInf₂_le_of_le univ univ_mem (iSup₂_le fun y hy => hC y hy.2)

/-! ### From subgeodesics to convex functions: boundary values -/

/-- The boundary-value argument of `prop:toricsubgeod`, (1) → (2), for one endpoint: the
profiles of a toric family converge everywhere to the profile of the endpoint `u` as soon as
the pointwise limit `Lim` exists, is `≤ u`, equal to `u` quasi-everywhere, and the family is
bounded below by a toric `θ`-psh function. -/
theorem tendsto_realProfile_of_limit {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    {u η Lim : PolytopeToricVariety γ hs → EReal} {l : Filter ℝ} [l.NeBot]
    (hl : ∀ᶠ t in l, t ∈ Ioo (0 : ℝ) 1)
    (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, curve t ∈ h.PSHTor) (hu : u ∈ h.PSHTor) (hη : η ∈ h.PSHTor)
    (hηle : ∀ t ∈ Ioo (0 : ℝ) 1, η ≤ curve t)
    (hlim : ∀ p, Tendsto (fun t => curve t p) l (𝓝 (Lim p))) (hle : Lim ≤ u)
    (hqe : SourceQuasiEverywhere (n := n) (fun p => Lim p = u p)) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t => h.realProfile (curve t) x) l (𝓝 (h.realProfile u x)) := by
  let P : EuclideanSpace ℝ (Fin n) → PolytopeToricVariety γ hs :=
    fun y => polytopeToricEmbedding γ hs (positiveTorusPoint y)
  -- the limit of the profiles, as an extended real
  have hprofTend (y : EuclideanSpace ℝ (Fin n)) : Tendsto (fun t => h.profile (curve t) y) l
      (𝓝 (Lim (P y) + (h.potential y : EReal))) := by
    have hc := EReal.continuousAt_add (p := (Lim (P y), (h.potential y : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    exact hc.tendsto.comp ((hlim (P y)).prodMk_nhds tendsto_const_nhds)
  have hlow (y : EuclideanSpace ℝ (Fin n)) : h.profile η y ≤ Lim (P y) + (h.potential y : EReal) := by
    apply add_le_add _ le_rfl
    exact ge_of_tendsto (hlim (P y)) (hl.mono fun t ht => hηle t ht (P y))
  have hup (y : EuclideanSpace ℝ (Fin n)) : Lim (P y) + (h.potential y : EReal) ≤ h.profile u y :=
    add_le_add (hle (P y)) le_rfl
  let r : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (Lim (P y) + (h.potential y : EReal)).toReal
  have hr (y : EuclideanSpace ℝ (Fin n)) : Lim (P y) + (h.potential y : EReal) = (r y : EReal) := by
    have h1 := hlow y
    have h2 := hup y
    rw [(h.realProfile_mem hη).2] at h1
    rw [(h.realProfile_mem hu).2] at h2
    refine (EReal.coe_toReal ?_ ?_).symm
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
  have hrTend (y : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun t => h.realProfile (curve t) y) l (𝓝 (r y)) := by
    apply EReal.tendsto_coe.mp
    rw [← hr y]
    apply (hprofTend y).congr'
    filter_upwards [hl] with t ht
    exact congrFun (h.realProfile_mem (hmem t ht)).2 y
  -- `r` is convex, continuous, `≤ F_u`, and `= F_u` on a dense set
  have hrconv : ConvexOn ℝ univ r := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    apply le_of_tendsto_of_tendsto (hrTend (a • y + b • z))
      (((hrTend y).const_smul a).add ((hrTend z).const_smul b))
    filter_upwards [hl] with t ht
    exact (h.realProfile_mem (hmem t ht)).1.1.2 (mem_univ y) (mem_univ z) ha hb hab
  have hrcont : Continuous r := continuousOn_univ.mp (hrconv.continuousOn isOpen_univ)
  have hucont : Continuous (h.realProfile u) :=
    continuousOn_univ.mp ((h.realProfile_mem hu).1.1.continuousOn isOpen_univ)
  have hdense : Dense {y | r y = h.realProfile u y} := by
    rw [dense_iff_inter_open]
    intro U hU hne
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    obtain ⟨x₀, hx₀⟩ := hne
    let w := polytopeToricBaseVertex γ
    let e : ComplexChart n (PolytopeToricVariety γ hs) := polytopeToricVertexChart γ hs w
    let b := originalPolytopeNativeBasis γ hs w
    let V : Set (ComplexModel n) :=
      complexTorus n ∩ tropicalization ⁻¹' (latticeBasisLogInverse b ⁻¹' U)
    have hVo : IsOpen V := continuousOn_tropicalization_complexTorus.isOpen_inter_preimage
      (isOpen_complexTorus n)
      (hU.preimage (LinearMap.continuous_of_finiteDimensional (latticeBasisLogInverse b)))
    have hVne : V.Nonempty := by
      refine ⟨expCoordinates (latticeBasisLogMap b x₀), expCoordinates_mem_complexTorus _, ?_⟩
      change latticeBasisLogInverse b (tropicalization (expCoordinates _)) ∈ U
      rw [tropicalization_expCoordinates, latticeBasisLogInverse_logMap]
      exact hx₀
    have hsub : V ⊆ pluripolarChartSet {p | ¬ (Lim p = u p)} e := by
      rintro z ⟨hz, hzU⟩
      have ht : z ∈ e.val.target := by
        change z ∈ (originalPolytopeNativeModelChart γ hs w).target
        rw [originalPolytopeNativeModelChart_target]; exact mem_univ z
      refine ⟨ht, ?_⟩
      obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs w hz
      have hza : originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a) = z := by
        rw [ha]; exact (originalPolytopeNativeModelChart γ hs w).right_inv ht
      have hlog : latticeBasisLogInverse b (tropicalization z) = unitTorusLog a := by
        rw [← hza, tropicalization_polytopeToricVertexChart_embedding,
          latticeBasisLogInverse_logMap]
      have hxU : unitTorusLog a ∈ U := by
        have := hzU; simp only [mem_preimage] at this; rwa [hlog] at this
      intro hEq
      change Lim (e.val.symm z) = u (e.val.symm z) at hEq
      change Lim ((originalPolytopeNativeModelChart γ hs w).symm z) =
        u ((originalPolytopeNativeModelChart γ hs w).symm z) at hEq
      rw [← ha] at hEq
      -- invariance of the limit and of `u`
      have hLimEq : Lim (polytopeToricEmbedding γ hs a) = Lim (P (unitTorusLog a)) := by
        apply tendsto_nhds_unique (hlim _)
        apply (hlim (P (unitTorusLog a))).congr'
        filter_upwards [hl] with t ht
        exact ((hmem t ht).2.embedding_eq γ hs a).symm
      rw [hLimEq, hu.2.embedding_eq γ hs a] at hEq
      have hG : r (unitTorusLog a) = h.realProfile u (unitTorusLog a) := by
        have h1 : ((r (unitTorusLog a) : ℝ) : EReal) = h.profile u (unitTorusLog a) := by
          rw [← hr, profile, hEq]
        rw [(h.realProfile_mem hu).2] at h1
        exact EReal.coe_eq_coe_iff.mp h1
      have : unitTorusLog a ∈ U ∩ {y | r y = h.realProfile u y} := ⟨hxU, hG⟩
      rw [hempty] at this
      exact this
    have h0 := ManifoldLocallyPluripolar.chart_measure_eq_zero
      ((sourceQuasiEverywhere_iff_native _).mp hqe) e volume
    exact (hVo.measure_pos volume hVne).ne' (measure_mono_null hsub h0)
  have hreq : r = h.realProfile u := Continuous.ext_on hdense hrcont hucont (fun y hy => hy)
  rw [← hreq]
  exact hrTend x

/-- `prop:toricsubgeod`, map (1) → (2): the profile function of a `T_c`-invariant subgeodesic is
in set (2). -/
theorem isToricSubgeodesicProfile_of_isToricSubgeodesic {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    {c : Ioo (0 : ℝ) 1 → PolytopeToricVariety γ hs → EReal}
    (hc : h.IsToricSubgeodesic omega u₀ u₁ c) :
    h.IsToricSubgeodesicProfile u₀ u₁ (fun p => h.realProfile (c p.2) p.1) := by
  set curve := ioo01Curve c u₀
  have hsub := hc.1
  have hcurve (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : curve t = c ⟨t, ht⟩ := ioo01Curve_of_mem c u₀ ht
  have hinv : ∀ t ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve t) := by
    intro t ht; rw [hcurve t ht]; exact hc.2 _
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, curve t ∈ h.PSHTor := fun t ht => ⟨hsub.2.2.1.1 t ht, hinv t ht⟩
  have hstrip (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      stripFunction (fun p : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 => h.realProfile (c p.2) p.1)
        (x, t) = h.realProfile (curve t) x := by
    rw [stripFunction_of_mem _ x ht, hcurve t ht]
  -- the slice infimum
  let η := sourceSliceInfimum curve
  have hη : η ∈ h.PSHTor := ⟨hsub.isThetaPSH_sliceInfimum, polytopeToricInvariant_sliceInfimum hinv⟩
  have hηle : ∀ t ∈ Ioo (0 : ℝ) 1, η ≤ curve t := fun t ht p =>
    iInf_le (fun s : Ioo (0 : ℝ) 1 => curve s.1 p) ⟨t, ht⟩
  obtain ⟨hlimL, hlimR, hleL, hleR, hqeL, hqeR⟩ := source_subgeodesic_endpoints_whole hsub
  refine ⟨?_, ?_, ?_⟩
  · -- convexity
    have hconv := h.convexOn_profile_of_jointThetaPSH (f := fun s x => h.realProfile (curve s) x)
      hsub.2.2.1.2 hinv (fun s hs => (h.realProfile_mem (hmem s hs)).2)
    refine ⟨hconv.1, ?_⟩
    rintro ⟨x, s⟩ hp ⟨y, s'⟩ hq a b ha hb hab
    have hpq := hconv.1 hp hq ha hb hab
    have := hconv.2 hp hq ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk] at hpq this ⊢
    rw [hstrip _ hp.2, hstrip _ hq.2, hstrip _ hpq.2]
    exact this
  · intro x
    apply (h.tendsto_realProfile_of_limit sourceRay_endpoint_filters.2 hmem hu₁ hη hηle hlimR hleR
      hqeR x).congr'
    filter_upwards [sourceRay_endpoint_filters.2] with t ht
    exact (hstrip x ht).symm
  · intro x
    apply (h.tendsto_realProfile_of_limit sourceRay_endpoint_filters.1 hmem hu₀ hη hηle hlimL hleL
      hqeL x).congr'
    filter_upwards [sourceRay_endpoint_filters.1] with t ht
    exact (hstrip x ht).symm

/-! ### From convex functions to subgeodesics -/

/-- The slice `F_r = F(·, r)` of a function on `N_ℝ × (0,1)`. -/
def stripSlice (F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ) (r : Ioo (0 : ℝ) 1) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => F (x, r)

/-- A uniform growth bound: `F_r ≤ Supp_{P_D} + C` for all `r ∈ (0,1)`. -/
theorem exists_stripSlice_le_support {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    {F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ} (hF : h.IsToricSubgeodesicProfile u₀ u₁ F) :
    ∃ C : ℝ, ∀ r x, ((stripSlice F r x : ℝ) : EReal) ≤
      support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x + (C : EReal) := by
  obtain ⟨C₀, hC₀⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp (h.realProfile_mem hu₀).1.2
  obtain ⟨C₁, hC₁⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp (h.realProfile_mem hu₁).1.2
  refine ⟨max C₀ C₁, fun r x => ?_⟩
  have hch := le_chord_of_convexOn_strip hF.1 x (hF.2.2 x) (hF.2.1 x) r.2
  rw [stripFunction_of_mem F x r.2] at hch
  have hr0 : 0 < (r : ℝ) := r.2.1
  have hr1 : (r : ℝ) < 1 := r.2.2
  change ((F (x, r) : ℝ) : EReal) ≤ _
  rcases le_total (h.realProfile u₀ x) (h.realProfile u₁ x) with hle | hle
  · have hF1 : F (x, r) ≤ h.realProfile u₁ x := by nlinarith
    calc ((F (x, r) : ℝ) : EReal) ≤ (h.realProfile u₁ x : EReal) := EReal.coe_le_coe_iff.mpr hF1
      _ ≤ _ := (hC₁ x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))
  · have hF0 : F (x, r) ≤ h.realProfile u₀ x := by nlinarith
    calc ((F (x, r) : ℝ) : EReal) ≤ (h.realProfile u₀ x : EReal) := EReal.coe_le_coe_iff.mpr hF0
      _ ≤ _ := (hC₀ x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))

/-- `F_r ∈ 𝓟(N_ℝ, P_D)` for every `r ∈ (0,1)`. -/
theorem stripSlice_mem {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    {F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ} (hF : h.IsToricSubgeodesicProfile u₀ u₁ F)
    (r : Ioo (0 : ℝ) 1) :
    stripSlice F r ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  refine ⟨⟨convex_univ, ?_⟩, ?_⟩
  · intro x _ y _ a b ha hb hab
    have hx : ((x, (r : ℝ)) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, r.2⟩
    have hy : ((y, (r : ℝ)) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, r.2⟩
    have := hF.1.2 hx hy ha hb hab
    have hr : a • (r : ℝ) + b • (r : ℝ) = r := by rw [← add_smul, hab, one_smul]
    simp only [Prod.smul_mk, Prod.mk_add_mk, hr] at this
    rw [stripFunction_of_mem F _ r.2, stripFunction_of_mem F _ r.2,
      stripFunction_of_mem F _ r.2] at this
    exact this
  · obtain ⟨C, hC⟩ := h.exists_stripSlice_le_support hu₀ hu₁ hF
    exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, hC r⟩

/-- `prop:toricsubgeod`, map (2) → (1): the family of toric potentials with profiles `F_r`. -/
def profileFamily {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    (F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ) (hF : h.IsToricSubgeodesicProfile u₀ u₁ F)
    (r : Ioo (0 : ℝ) 1) : PolytopeToricVariety γ hs → EReal :=
  h.extension (stripSlice F r) (h.stripSlice_mem hu₀ hu₁ hF r)

/-- `L¹` boundary values by dominated convergence in the charts: a toric family whose profiles
converge everywhere to the profile of `u`, bounded above uniformly and below by a toric
`θ`-psh function, converges to `u` in the chart-local `L¹` topology. -/
theorem manifoldL1LocallyTendsto_of_profile {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    {u η : PolytopeToricVariety γ hs → EReal} {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : ∀ᶠ t in l, t ∈ Ioo (0 : ℝ) 1)
    (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, curve t ∈ h.PSHTor) (hu : u ∈ h.PSHTor) (hη : η ∈ h.PSHTor)
    (hηle : ∀ t ∈ Ioo (0 : ℝ) 1, η ≤ curve t) (C : ℝ)
    (hC : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ p, curve t p ≤ (C : EReal))
    (hlim : ∀ x, Tendsto (fun t => h.realProfile (curve t) x) l (𝓝 (h.realProfile u x))) :
    ManifoldL1LocallyTendsto (n := n) curve l u := by
  intro e Kc hK _
  have htarget : e.val.target = univ := polytopeToric_chart_target γ hs e
  have hsymm : Continuous e.val.symm := by
    have := e.val.continuousOn_symm
    rw [htarget] at this
    exact continuousOn_univ.mp this
  have htor : ∀ z ∈ complexTorus n, ∃ a, e.val.symm z = polytopeToricEmbedding γ hs a := by
    obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
    intro z hz
    obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hz
    exact ⟨a, ha.symm⟩
  have hquasi {w : PolytopeToricVariety γ hs → EReal} (hw : w ∈ h.PSHTor) :
      IsGlobalQuasiPshPotential (n := n) w := by
    have hn := (isThetaPSH_iff_nativeThetaPotential h.atlasForm w).mp hw.1
    exact ⟨hn.1.quasiPlurisubharmonic, hn.2⟩
  let G : ℝ → ComplexModel n → ENNReal := fun t z =>
    canonicalERealAbsDiff (chartFunction (curve t) e z) (chartFunction u e z)
  let bnd : ComplexModel n → ℝ := fun z =>
    |C| + |(chartFunction η e z).toReal| + |(chartFunction u e z).toReal|
  have hmeas : ∀ᶠ t in l, Measurable (G t) := by
    filter_upwards [hl] with t ht
    exact ((hmem t ht).1.upperSemicontinuous.measurable.comp hsymm.measurable).canonicalERealAbsDiff
      (hu.1.upperSemicontinuous.measurable.comp hsymm.measurable)
  have hbound : ∀ᶠ t in l, ∀ᵐ z ∂(volume.restrict Kc), G t z ≤ ENNReal.ofReal (bnd z) := by
    filter_upwards [hl] with t ht
    filter_upwards [ae_restrict_of_ae ae_mem_complexTorus_volume] with z hz
    obtain ⟨a, ha⟩ := htor z hz
    have hA := h.apply_embedding_of_mem (hmem t ht) a
    have hB := h.apply_embedding_of_mem hu a
    have hM := h.apply_embedding_of_mem hη a
    have hle1 := hηle t ht (polytopeToricEmbedding γ hs a)
    have hle2 := hC t ht (polytopeToricEmbedding γ hs a)
    simp only [G, bnd, chartFunction, ha, hA, hB, hM, canonicalERealAbsDiff_coe_coe,
      EReal.toReal_coe] at hle1 hle2 ⊢
    have h1 := EReal.coe_le_coe_iff.mp hle1
    have h2 := EReal.coe_le_coe_iff.mp hle2
    apply ENNReal.ofReal_le_ofReal
    have := abs_sub (h.realProfile (curve t) (unitTorusLog a) - h.potential (unitTorusLog a))
      (h.realProfile u (unitTorusLog a) - h.potential (unitTorusLog a))
    have h3 : |h.realProfile (curve t) (unitTorusLog a) - h.potential (unitTorusLog a)| ≤
        |C| + |h.realProfile η (unitTorusLog a) - h.potential (unitTorusLog a)| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (h.realProfile η (unitTorusLog a) - h.potential (unitTorusLog a)),
          abs_nonneg C]
      · linarith [le_abs_self C, abs_nonneg (h.realProfile η (unitTorusLog a) -
          h.potential (unitTorusLog a))]
    linarith
  have hfin : ∫⁻ z, ENNReal.ofReal (bnd z) ∂(volume.restrict Kc) ≠ ⊤ := by
    have hKfin : volume Kc ≠ ⊤ := hK.measure_lt_top.ne
    have hiη : IntegrableOn (fun z => (chartFunction η e z).toReal) Kc volume := by
      have hl' := (hquasi hη).locallyIntegrableOn_chart_toReal e
      rw [htarget] at hl'
      exact (hl'.mono_set (subset_univ Kc)).integrableOn_isCompact hK
    have hiu : IntegrableOn (fun z => (chartFunction u e z).toReal) Kc volume := by
      have hl' := (hquasi hu).locallyIntegrableOn_chart_toReal e
      rw [htarget] at hl'
      exact (hl'.mono_set (subset_univ Kc)).integrableOn_isCompact hK
    have hint : Integrable bnd (volume.restrict Kc) :=
      ((integrableOn_const hKfin).add hiη.abs).add hiu.abs
    exact hint.lintegral_lt_top.ne
  have hpt : ∀ᵐ z ∂(volume.restrict Kc), Tendsto (fun t => G t z) l (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae ae_mem_complexTorus_volume] with z hz
    obtain ⟨a, ha⟩ := htor z hz
    have hlim' : Tendsto (fun t => ENNReal.ofReal |h.realProfile (curve t) (unitTorusLog a) -
        h.realProfile u (unitTorusLog a)|) l (𝓝 0) := by
      have := ((hlim (unitTorusLog a)).sub
        (tendsto_const_nhds (x := h.realProfile u (unitTorusLog a)))).abs
      rw [sub_self, abs_zero] at this
      have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp this
      rw [ENNReal.ofReal_zero] at h2
      exact h2
    apply hlim'.congr'
    filter_upwards [hl] with t ht
    simp only [G, chartFunction, ha, h.apply_embedding_of_mem (hmem t ht) a,
      h.apply_embedding_of_mem hu a, canonicalERealAbsDiff_coe_coe]
    congr 2
    ring
  have hdc := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict Kc)
    (fun z => ENNReal.ofReal (bnd z)) hmeas hbound hfin hpt
  change Tendsto (fun t => ∫⁻ z in Kc, G t z) l (𝓝 0)
  simp only [lintegral_zero] at hdc
  exact hdc

/-- `prop:toricsubgeod`, map (2) → (1): the family `φ_r` with profiles `F_r` is a
`T_c`-invariant subgeodesic from `u₀` to `u₁`. -/
theorem isToricSubgeodesic_profileFamily {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    {F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ} (hF : h.IsToricSubgeodesicProfile u₀ u₁ F) :
    h.IsToricSubgeodesic omega u₀ u₁ (h.profileFamily hu₀ hu₁ F hF) := by
  set c := h.profileFamily hu₀ hu₁ F hF
  set curve := ioo01Curve c u₀
  have hcurve (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : curve t = c ⟨t, ht⟩ := ioo01Curve_of_mem c u₀ ht
  have hcmem (r : Ioo (0 : ℝ) 1) : c r ∈ h.PSHTor :=
    h.extension_mem _ (h.stripSlice_mem hu₀ hu₁ hF r)
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, curve t ∈ h.PSHTor := fun t ht => by
    rw [hcurve t ht]; exact hcmem _
  have hprof : ∀ s ∈ Ioo (0 : ℝ) 1,
      h.profile (curve s) = fun x => ((stripFunction F (x, s) : ℝ) : EReal) := by
    intro s hs
    rw [hcurve s hs]
    funext x
    rw [stripFunction_of_mem F x hs]
    exact congrFun (h.profile_extension _ (h.stripSlice_mem hu₀ hu₁ hF ⟨s, hs⟩)) x
  have hrp : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ x, h.realProfile (curve s) x = stripFunction F (x, s) := by
    intro s hs x
    simp only [realProfile, hprof s hs, EReal.toReal_coe]
  -- uniform upper bound
  obtain ⟨C, hC⟩ := h.exists_stripSlice_le_support hu₀ hu₁ hF
  obtain ⟨E, hE⟩ := h.exists_support_le_potential
  have hbound : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ p, curve t p ≤ ((E + C : ℝ) : EReal) := by
    intro t ht
    apply h.le_of_le_off_boundary (hmem t ht).1
    intro p hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    rw [h.apply_embedding_of_mem (hmem t ht) a, hrp t ht, stripFunction_of_mem F _ ht]
    have h1 := (hC ⟨t, ht⟩ (unitTorusLog a)).trans (add_le_add (hE (unitTorusLog a)) le_rfl)
    rw [← EReal.coe_add] at h1
    have h2 := EReal.coe_le_coe_iff.mp h1
    exact EReal.coe_le_coe_iff.mpr (by
      change F (unitTorusLog a, ⟨t, ht⟩) ≤ h.potential (unitTorusLog a) + E + C at h2
      linarith)
  have hinv : ∀ s ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve s) :=
    fun s hs => (hmem s hs).2
  -- the native interior condition
  have hnat : IsSubgeodesicInterior (atlasClosedFormToNative h.atlasForm).val curve := by
    refine ⟨fun t ht => (isThetaPSH_iff_nativeThetaPotential _ _).mp (hmem t ht).1, ?_⟩
    intro e z _
    obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
    exact ⟨univ, h.weight v, mem_univ z, h.isSmoothLocalPotential_weight v,
      h.plurisubharmonicOn_vertexChart_strip (f := fun s x => stripFunction F (x, s)) hF.1
        (fun s hs => (hmem s hs).1) hinv hprof (E + C) hbound v⟩
  have hint : SourceSubgeodesicInterior h.atlasForm curve :=
    (sourceInterior_iff_native h.atlasForm curve).mpr hnat
  -- the slice infimum
  let η := sourceSliceInfimum curve
  have hη : η ∈ h.PSHTor :=
    ⟨(isThetaPSH_iff_nativeThetaPotential _ _).mpr
      (SGPT.Foundations.Analysis.Pending.SubgeodesicInfimumThetaPsh.isThetaPshPotential_sliceInfimum
        hnat), polytopeToricInvariant_sliceInfimum hinv⟩
  have hηle : ∀ t ∈ Ioo (0 : ℝ) 1, η ≤ curve t := fun t ht p =>
    iInf_le (fun s : Ioo (0 : ℝ) 1 => curve s.1 p) ⟨t, ht⟩
  have hslices : ∀ t ∈ Ioo (0 : ℝ) 1,
      (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm (curve t) :=
    fun t ht => (hmem t ht).1
  refine ⟨⟨hu₀.1, hu₁.1, hint, ?_, ?_⟩, fun r => hcmem r |>.2⟩
  · apply (sourceRayL1_iff_global omega hslices hu₀.1 sourceRay_endpoint_filters.1).mp
    apply h.manifoldL1LocallyTendsto_of_profile sourceRay_endpoint_filters.1 hmem hu₀ hη hηle
      (E + C) hbound
    intro x
    apply (hF.2.2 x).congr'
    filter_upwards [sourceRay_endpoint_filters.1] with t ht
    exact (hrp t ht x).symm
  · apply (sourceRayL1_iff_global omega hslices hu₁.1 sourceRay_endpoint_filters.2).mp
    apply h.manifoldL1LocallyTendsto_of_profile sourceRay_endpoint_filters.2 hmem hu₁ hη hηle
      (E + C) hbound
    intro x
    apply (hF.2.1 x).congr'
    filter_upwards [sourceRay_endpoint_filters.2] with t ht
    exact (hrp t ht x).symm

/-! ### The bijection -/

/-- Source `prop:toricsubgeod`: for `φ₀, φ₁ ∈ PSH_tor(X, θ)`, the canonical bijection between
the `T_c`-invariant subgeodesics `(φ_t)_{t ∈ (0,1)}` from `φ₀` to `φ₁` and the convex functions
`F : N_ℝ × (0,1) → ℝ` with `F_r → F_{φ₁}` as `r → 1-` and `F_r → F_{φ₀}` as `r → 0+`
everywhere, `F(x, t) = F_{φ_t}(x)`. -/
def toricSubgeodesicEquiv {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor) :
    {c // h.IsToricSubgeodesic omega u₀ u₁ c} ≃ {F // h.IsToricSubgeodesicProfile u₀ u₁ F} where
  toFun c := ⟨fun p => h.realProfile (c.1 p.2) p.1,
    h.isToricSubgeodesicProfile_of_isToricSubgeodesic omega hu₀ hu₁ c.2⟩
  invFun F := ⟨h.profileFamily hu₀ hu₁ F.1 F.2, h.isToricSubgeodesic_profileFamily omega hu₀ hu₁ F.2⟩
  left_inv c := by
    apply Subtype.ext
    funext r
    have hr : c.1 r ∈ h.PSHTor := by
      have hsub := c.2.1
      have := hsub.2.2.1.1 r.1 r.2
      rw [ioo01Curve_of_mem c.1 u₀ r.2] at this
      exact ⟨this, c.2.2 r⟩
    exact h.extension_realProfile hr
  right_inv F := by
    apply Subtype.ext
    funext p
    change (h.profile (h.extension (stripSlice F.1 p.2) (h.stripSlice_mem hu₀ hu₁ F.2 p.2))
      p.1).toReal = F.1 p
    rw [h.profile_extension]
    rfl

/-- The map (1) → (2) of `toricSubgeodesicEquiv` is `F(x, t) = F_{φ_t}(x)`. -/
theorem toricSubgeodesicEquiv_apply {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor) (c : {c // h.IsToricSubgeodesic omega u₀ u₁ c})
    (p : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1) :
    (h.toricSubgeodesicEquiv omega hu₀ hu₁ c).1 p = h.realProfile (c.1 p.2) p.1 := rfl

/-- The map (2) → (1) of `toricSubgeodesicEquiv` is `φ_t = Trop^*(F_t - F_θ)` on the torus. -/
theorem toricSubgeodesicEquiv_symm_embedding {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor) (F : {F // h.IsToricSubgeodesicProfile u₀ u₁ F})
    (r : Ioo (0 : ℝ) 1) (a : Fin n → ℂˣ) :
    ((h.toricSubgeodesicEquiv omega hu₀ hu₁).symm F).1 r (polytopeToricEmbedding γ hs a) =
      ((F.1 (unitTorusLog a, r) - h.potential (unitTorusLog a) : ℝ) : EReal) := by
  change h.extension (stripSlice F.1 r) (h.stripSlice_mem hu₀ hu₁ F.2 r)
    (polytopeToricEmbedding γ hs a) = _
  rw [(h.extension_spec _ _).2 (polytopeToricEmbedding_mem_compl γ hs a), offPotential_embedding]
  rfl

end BigToricMetric

end SGPT.Toric
