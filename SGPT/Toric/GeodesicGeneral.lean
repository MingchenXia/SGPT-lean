import SGPT.Toric.GeodesicSubgeodesic
import SGPT.Toric.GeodesicAction
import SGPT.Toric.BigToricOperations
import SGPT.Toric.BigToricNewtonBody
import SGPT.PSH.SourceGlobalPSubgeodesicExistence
import SGPT.PSH.SourcePerronConsumers
import SGPT.PSH.SourceGeodesicOrder

/-!
# Toric geodesics

Source `chapter_toric_big.tex`, `cor:toricgeodgeneral`: for
`φ₀, φ₁ ∈ PSH_tor(X, θ) ∩ PSH(X, θ)_{>0}`,

1. `φ₀ ∼_P φ₁` if and only if there is a subgeodesic from `φ₀` to `φ₁`;
2. in that case the geodesic `(φ_t)_{t ∈ (0,1)}` from `φ₀` to `φ₁` is toric and
   `G_{φ_t} = (1-t) G_{φ₀} + t G_{φ₁}` (`eq:Glinear`).

The geodesic is the source one (`SourceIsGeodesicFrom`: the Perron envelope of all
subgeodesics with endpoints below `φ₀`, `φ₁`).

## Route

(1) is `thm:geodexi` (`sourceSubgeodesic_exists_iff_sourcePEquivalent`).  For (2): the geodesic
is a subgeodesic (`thm:geodexi`), and `T_c` permutes the subgeodesics
(`sourceSubgeodesicFrom_comp_action`), so by maximality each `φ_t` is `T_c`-invariant ("the
geodesic is the upper envelope of toric subgeodesics").  By `prop:toricsubgeod` its profile
`F(x, t)` is convex on `N_ℝ × (0,1)` with boundary values `F_{φ₀}`, `F_{φ₁}`; the convexity
extended to the closed strip gives `G_{φ_t} ≥ (1-t) G_{φ₀} + t G_{φ₁}`.  Conversely
`H(x, t) = sup_{m ∈ Dom G_{φ₀} ∩ Dom G_{φ₁}} (⟨m, x⟩ - (1-t) G_{φ₀}(m) - t G_{φ₁}(m))` is
convex on `N_ℝ × [0,1]` and continuous in `t` at the ends; by `prop:toricsubgeod` it is the
profile of a toric subgeodesic with endpoints below `φ₀`, `φ₁` (the domain intersection is
nonempty since `G_{φ₀ ∧ φ₁} = G_{φ₀} ∨ G_{φ₁}` is proper, `prop:toricrooftopbig`), hence a Perron
competitor, which gives `G_{φ_t} ≤ H_t^* ≤ (1-t) G_{φ₀} + t G_{φ₁}`.  This is a direct version
of the source's argument through the minimal element of `cor:geodG`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators RealInnerProductSpace

/-! ### Two elementary lemmas -/

/-- Convexity on the closed strip: a convex function `g` on `ℝⁿ × (0,1)` with boundary
limits `g₀`, `g₁` satisfies `g((1-t) x₀ + t x₁, t) ≤ (1-t) g₀(x₀) + t g₁(x₁)`. -/
theorem le_of_convexOn_strip_closed {n : ℕ} {g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) {g₀ g₁ : EuclideanSpace ℝ (Fin n) → ℝ}
    (x₀ x₁ : EuclideanSpace ℝ (Fin n))
    (h₀ : Tendsto (fun r => g (x₀, r)) (𝓝[>] 0) (𝓝 (g₀ x₀)))
    (h₁ : Tendsto (fun r => g (x₁, r)) (𝓝[<] 1) (𝓝 (g₁ x₁))) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    g ((1 - t) • x₀ + t • x₁, t) ≤ (1 - t) * g₀ x₀ + t * g₁ x₁ := by
  have hopen : IsOpen (univ ×ˢ Ioo (0 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin n) × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hcont := hg.continuousOn hopen
  have hpt : ((1 - t) • x₀ + t • x₁, t) ∈ (univ ×ˢ Ioo (0 : ℝ) 1 :
      Set (EuclideanSpace ℝ (Fin n) × ℝ)) := ⟨mem_univ _, ht⟩
  -- the time `s(ε) = (1-t) ε + t (1-ε) → t`
  have hs : Tendsto (fun ε : ℝ => ((1 - t) • x₀ + t • x₁, (1 - t) * ε + t * (1 - ε)))
      (𝓝[>] 0) (𝓝 ((1 - t) • x₀ + t • x₁, t)) := by
    apply Tendsto.prodMk_nhds tendsto_const_nhds
    have : Tendsto (fun ε : ℝ => (1 - t) * ε + t * (1 - ε)) (𝓝 0) (𝓝 ((1 - t) * 0 + t * (1 - 0))) :=
      ((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_const.sub continuous_id))).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun ε : ℝ => g ((1 - t) • x₀ + t • x₁, (1 - t) * ε + t * (1 - ε)))
      (𝓝[>] 0) (𝓝 (g ((1 - t) • x₀ + t • x₁, t))) :=
    ((hcont _ hpt).continuousAt (hopen.mem_nhds hpt)).tendsto.comp hs
  have h1' : Tendsto (fun ε : ℝ => g (x₁, 1 - ε)) (𝓝[>] 0) (𝓝 (g₁ x₁)) := by
    apply h₁.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => 1 - ε) (𝓝 0) (𝓝 (1 - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 1 - ε < 1
      linarith [show (0 : ℝ) < ε from hε]
  have hR : Tendsto (fun ε : ℝ => (1 - t) * g (x₀, ε) + t * g (x₁, 1 - ε)) (𝓝[>] 0)
      (𝓝 ((1 - t) * g₀ x₀ + t * g₁ x₁)) :=
    (tendsto_const_nhds.mul h₀).add (tendsto_const_nhds.mul h1')
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
  have hxa : ((x₀, ε) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
    ⟨mem_univ _, hε.1, by linarith [hε.2]⟩
  have hxb : ((x₁, 1 - ε) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
    ⟨mem_univ _, by linarith [hε.2], by linarith [hε.1]⟩
  have := hg.2 hxa hxb (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this

/-- Approximation in `EReal`: if `s x + t y ≤ Γ` whenever `x < a` and `y < b` (`s, t > 0`,
`a, b ≠ ⊥`), then `s a + t b ≤ Γ`. -/
theorem EReal.combo_le_of_forall_lt {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {a b Γ : EReal}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (h : ∀ x y : ℝ, (x : EReal) < a → (y : EReal) < b → ((s * x + t * y : ℝ) : EReal) ≤ Γ) :
    (s : EReal) * a + (t : EReal) * b ≤ Γ := by
  apply EReal.add_le_of_forall_lt
  intro a' ha' b' hb'
  -- choose real witnesses below `a` and `b`
  have hsa : ∃ x : ℝ, (x : EReal) < a ∧ a' ≤ ((s * x : ℝ) : EReal) := by
    induction a' using EReal.rec with
    | bot => exact ⟨(EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr ha)).choose,
        ((EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr ha)).choose_spec).2, bot_le⟩
    | top => exact absurd ha' (not_lt.mpr le_top)
    | coe a'' =>
      refine ⟨a'' / s, ?_, le_of_eq (by rw [mul_div_cancel₀ _ hs.ne'])⟩
      induction a using EReal.rec with
      | bot => exact absurd rfl ha
      | top => exact EReal.coe_lt_top _
      | coe a₀ =>
        have h1 : (a'' : EReal) < ((s : ℝ) : EReal) * (a₀ : EReal) := ha'
        rw [← EReal.coe_mul, EReal.coe_lt_coe_iff] at h1
        exact EReal.coe_lt_coe_iff.mpr ((div_lt_iff₀' hs).mpr h1)
  have htb : ∃ y : ℝ, (y : EReal) < b ∧ b' ≤ ((t * y : ℝ) : EReal) := by
    induction b' using EReal.rec with
    | bot => exact ⟨(EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hb)).choose,
        ((EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hb)).choose_spec).2, bot_le⟩
    | top => exact absurd hb' (not_lt.mpr le_top)
    | coe b'' =>
      refine ⟨b'' / t, ?_, le_of_eq (by rw [mul_div_cancel₀ _ ht.ne'])⟩
      induction b using EReal.rec with
      | bot => exact absurd rfl hb
      | top => exact EReal.coe_lt_top _
      | coe b₀ =>
        have h1 : (b'' : EReal) < ((t : ℝ) : EReal) * (b₀ : EReal) := hb'
        rw [← EReal.coe_mul, EReal.coe_lt_coe_iff] at h1
        exact EReal.coe_lt_coe_iff.mpr ((div_lt_iff₀' ht).mpr h1)
  obtain ⟨x, hx, hxa⟩ := hsa
  obtain ⟨y, hy, hyb⟩ := htb
  calc a' + b' ≤ ((s * x : ℝ) : EReal) + ((t * y : ℝ) : EReal) := add_le_add hxa hyb
    _ = ((s * x + t * y : ℝ) : EReal) := by rw [EReal.coe_add]
    _ ≤ Γ := h x y hx hy

theorem EReal.coe_mul_ne_bot_of_pos {t : ℝ} (ht : 0 < t) {x : EReal} (hx : x ≠ ⊥) :
    (t : EReal) * x ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  | top => rw [EReal.coe_mul_top_of_pos ht]; exact top_ne_bot

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))

/-- The geodesic between toric potentials is toric. -/
theorem perronGeodesic_mem_PSHTor {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    (hg : SourceSubgeodesicFrom omega h.atlasForm (sourcePerronGeodesic omega h.atlasForm u₀ u₁)
      u₀ u₁) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    sourcePerronGeodesic omega h.atlasForm u₀ u₁ t ∈ h.PSHTor := by
  set g := sourcePerronGeodesic omega h.atlasForm u₀ u₁
  refine ⟨hg.2.2.1.1 t ht, ?_⟩
  have hle (a : Fin n → ℂˣ) (ha : IsCompactTorusElement a) (p : PolytopeToricVariety γ hs) :
      g t (polytopeToricAction γ hs a p) ≤ g t p := by
    have hsub := h.sourceSubgeodesicFrom_comp_action omega hg ha
    have he₀ : (fun p => u₀ (polytopeToricAction γ hs a p)) = u₀ := funext (hu₀.2 a ha)
    have he₁ : (fun p => u₁ (polytopeToricAction γ hs a p)) = u₁ := funext (hu₁.2 a ha)
    rw [he₀, he₁] at hsub
    have hcomp : (fun s p => g s (polytopeToricAction γ hs a p)) ∈
        sourcePerronCompetitors omega h.atlasForm u₀ u₁ :=
      ⟨u₀, u₁, hu₀.1, hu₁.1, le_rfl, le_rfl, hsub⟩
    exact sourcePerron_competitor_le hcomp t p
  intro a ha p
  apply le_antisymm (hle a ha p)
  have := hle a⁻¹ (isCompactTorusElement_inv ha) (polytopeToricAction γ hs a p)
  rwa [← polytopeToricAction_mul, inv_mul_cancel, polytopeToricAction_one] at this

/-- The value of the Legendre transform of a toric potential is never `-∞`. -/
theorem legendre_ne_bot {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (m : EuclideanSpace ℝ (Fin n)) : h.legendre u m ≠ ⊥ := by
  have h0 : ((⟪(0 : EuclideanSpace ℝ (Fin n)), m⟫ - h.realProfile u 0 : ℝ) : EReal) ≤
      h.legendre u m := by
    unfold legendre conjugate
    refine le_trans ?_ (le_iSup _ (0 : EuclideanSpace ℝ (Fin n)))
    rw [(h.realProfile_mem hu).2, innerₗ_apply_apply, EReal.coe_sub]
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h0

/-- `cor:toricgeodgeneral`, lower bound: `G_{φ_t} ≥ (1-t) G_{φ₀} + t G_{φ₁}`. -/
theorem combo_legendre_le_perronGeodesic {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    (hg : SourceSubgeodesicFrom omega h.atlasForm (sourcePerronGeodesic omega h.atlasForm u₀ u₁)
      u₀ u₁) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (m : EuclideanSpace ℝ (Fin n)) :
    ((1 - t : ℝ) : EReal) * h.legendre u₀ m + (t : EReal) * h.legendre u₁ m ≤
      h.legendre (sourcePerronGeodesic omega h.atlasForm u₀ u₁ t) m := by
  set g := sourcePerronGeodesic omega h.atlasForm u₀ u₁
  let c : Ioo (0 : ℝ) 1 → PolytopeToricVariety γ hs → EReal := fun r => g r
  have hmem (r : Ioo (0 : ℝ) 1) : c r ∈ h.PSHTor := h.perronGeodesic_mem_PSHTor omega hu₀ hu₁ hg r.2
  have hc : h.IsToricSubgeodesic omega u₀ u₁ c :=
    ⟨hg.congr_Ioo (fun s hs => (ioo01Curve_of_mem c u₀ hs).symm), fun r => (hmem r).2⟩
  obtain ⟨hconv, hlim₁, hlim₀⟩ := h.isToricSubgeodesicProfile_of_isToricSubgeodesic omega hu₀ hu₁ hc
  have hgt := hmem ⟨t, ht⟩
  apply EReal.combo_le_of_forall_lt (sub_pos.mpr ht.2) ht.1 (h.legendre_ne_bot hu₀ m)
    (h.legendre_ne_bot hu₁ m)
  intro x y hx hy
  unfold legendre conjugate at hx hy
  obtain ⟨x₀, hx₀⟩ := lt_iSup_iff.mp hx
  obtain ⟨x₁, hx₁⟩ := lt_iSup_iff.mp hy
  rw [(h.realProfile_mem hu₀).2, innerₗ_apply_apply, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hx₀
  rw [(h.realProfile_mem hu₁).2, innerₗ_apply_apply, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hx₁
  have hstrip := le_of_convexOn_strip_closed hconv x₀ x₁ (hlim₀ x₀) (hlim₁ x₁) ht
  rw [stripFunction_of_mem _ _ ht] at hstrip
  change h.realProfile (g t) ((1 - t) • x₀ + t • x₁) ≤ _ at hstrip
  unfold legendre conjugate
  refine le_trans ?_ (le_iSup _ ((1 - t) • x₀ + t • x₁))
  rw [(h.realProfile_mem hgt).2, innerₗ_apply_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1t : 0 < 1 - t := sub_pos.mpr ht.2
  nlinarith [ht.1]

/-- Fenchel–Young: `⟨m, x⟩ - G_u(m) ≤ F_u(x)`. -/
theorem inner_sub_legendre_le {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    {m : EuclideanSpace ℝ (Fin n)} (hm : h.legendre u m ≠ ⊤) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, m⟫ - (h.legendre u m).toReal ≤ h.realProfile u x := by
  have hne := h.nonempty_toricDivisorPolytope_of_mem hu
  have hF : conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip (h.legendre u) x =
      (h.realProfile u x : EReal) := by
    have := congrFun (h.conjugate_legendre hne hu) x
    rw [(h.realProfile_mem hu).2] at this
    exact this
  have h1 : ((⟪x, m⟫ - (h.legendre u m).toReal : ℝ) : EReal) ≤ (h.realProfile u x : EReal) := by
    rw [← hF]
    unfold conjugate
    refine le_trans ?_ (le_iSup _ m)
    rw [LinearMap.flip_apply, innerₗ_apply_apply, EReal.coe_sub,
      EReal.coe_toReal hm (h.legendre_ne_bot hu m)]
  exact EReal.coe_le_coe_iff.mp h1

/-! ### The comparison subgeodesic -/

section Comparison

variable {u₀ u₁ : PolytopeToricVariety γ hs → EReal}

/-- The common domain `Dom G_{φ₀} ∩ Dom G_{φ₁}`. -/
def commonDomain (u₀ u₁ : PolytopeToricVariety γ hs → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {m | h.legendre u₀ m ≠ ⊤ ∧ h.legendre u₁ m ≠ ⊤}

/-- The affine functions `ℓ_m(x, s) = ⟨m, x⟩ - (1-s) G₀(m) - s G₁(m)`. -/
def comboAffine (u₀ u₁ : PolytopeToricVariety γ hs → EReal) (m : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  ⟪x, m⟫ - (1 - s) * (h.legendre u₀ m).toReal - s * (h.legendre u₁ m).toReal

/-- `H(x, s) = sup_{m ∈ Dom G₀ ∩ Dom G₁} ℓ_m(x, s)`. -/
def comboProfile (u₀ u₁ : PolytopeToricVariety γ hs → EReal) (x : EuclideanSpace ℝ (Fin n))
    (s : ℝ) : ℝ :=
  ⨆ m : h.commonDomain u₀ u₁, h.comboAffine u₀ u₁ m x s

variable (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
include hu₀ hu₁

omit hu₁ in
theorem coe_toReal_legendre₀ {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ h.commonDomain u₀ u₁) :
    ((h.legendre u₀ m).toReal : EReal) = h.legendre u₀ m :=
  EReal.coe_toReal hm.1 (h.legendre_ne_bot hu₀ m)

omit hu₀ in
theorem coe_toReal_legendre₁ {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ h.commonDomain u₀ u₁) :
    ((h.legendre u₁ m).toReal : EReal) = h.legendre u₁ m :=
  EReal.coe_toReal hm.2 (h.legendre_ne_bot hu₁ m)

theorem comboAffine_le {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ h.commonDomain u₀ u₁)
    (x : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    h.comboAffine u₀ u₁ m x s ≤ (1 - s) * h.realProfile u₀ x + s * h.realProfile u₁ x := by
  have h0 := h.inner_sub_legendre_le hu₀ hm.1 x
  have h1 := h.inner_sub_legendre_le hu₁ hm.2 x
  unfold comboAffine
  nlinarith [hs.1, hs.2]

theorem bddAbove_comboAffine (x : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    BddAbove (range fun m : h.commonDomain u₀ u₁ => h.comboAffine u₀ u₁ m x s) :=
  ⟨_, by rintro _ ⟨m, rfl⟩; exact h.comboAffine_le hu₀ hu₁ m.2 x hs⟩

theorem comboAffine_le_comboProfile [Nonempty (h.commonDomain u₀ u₁)]
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∈ h.commonDomain u₀ u₁)
    (x : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    h.comboAffine u₀ u₁ m x s ≤ h.comboProfile u₀ u₁ x s :=
  le_ciSup (h.bddAbove_comboAffine hu₀ hu₁ x hs) ⟨m, hm⟩

theorem comboProfile_le [Nonempty (h.commonDomain u₀ u₁)] (x : EuclideanSpace ℝ (Fin n)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    h.comboProfile u₀ u₁ x s ≤ (1 - s) * h.realProfile u₀ x + s * h.realProfile u₁ x :=
  ciSup_le fun m => h.comboAffine_le hu₀ hu₁ m.2 x hs

/-- `H` is convex on `N_ℝ × [0,1]`. -/
theorem convexOn_comboProfile [Nonempty (h.commonDomain u₀ u₁)] :
    ConvexOn ℝ (univ ×ˢ Icc (0 : ℝ) 1)
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => h.comboProfile u₀ u₁ p.1 p.2) := by
  refine ⟨convex_univ.prod (convex_Icc 0 1), ?_⟩
  rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, s'⟩ ⟨-, hs'⟩ a b ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  apply ciSup_le
  intro m
  have h1 := h.comboAffine_le_comboProfile hu₀ hu₁ m.2 x hs
  have h2 := h.comboAffine_le_comboProfile hu₀ hu₁ m.2 y hs'
  have heq : h.comboAffine u₀ u₁ m (a • x + b • y) (a * s + b * s') =
      a * h.comboAffine u₀ u₁ m x s + b * h.comboAffine u₀ u₁ m y s' := by
    unfold comboAffine
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hb' : b = 1 - a := by linarith
    subst hb'
    ring
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

theorem comboProfile_le_chord [Nonempty (h.commonDomain u₀ u₁)] (x : EuclideanSpace ℝ (Fin n))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    h.comboProfile u₀ u₁ x s ≤
      (1 - s) * h.comboProfile u₀ u₁ x 0 + s * h.comboProfile u₀ u₁ x 1 := by
  have := (h.convexOn_comboProfile hu₀ hu₁).2 (x := (x, 0)) (y := (x, 1))
    ⟨mem_univ _, left_mem_Icc.mpr zero_le_one⟩ ⟨mem_univ _, right_mem_Icc.mpr zero_le_one⟩
    (sub_nonneg.mpr hs.2) hs.1 (by ring)
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, mul_one, zero_add,
    ← add_smul, sub_add_cancel, one_smul] using this

/-- Continuity of `H(x, ·)` at the end points of `[0,1]`. -/
theorem tendsto_comboProfile [Nonempty (h.commonDomain u₀ u₁)] (x : EuclideanSpace ℝ (Fin n))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) {l : Filter ℝ} (hl : l ≤ 𝓝 s₀)
    (hlI : ∀ᶠ s in l, s ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun s => h.comboProfile u₀ u₁ x s) l (𝓝 (h.comboProfile u₀ u₁ x s₀)) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    obtain ⟨m, hm⟩ := exists_lt_of_lt_ciSup hc
    have hcont : Tendsto (fun s => h.comboAffine u₀ u₁ m x s) l
        (𝓝 (h.comboAffine u₀ u₁ m x s₀)) := by
      apply Tendsto.mono_left _ hl
      unfold comboAffine
      exact ((continuous_const.sub (continuous_const.sub continuous_id |>.mul continuous_const)).sub
        (continuous_id.mul continuous_const)).tendsto s₀
    filter_upwards [hcont.eventually (lt_mem_nhds hm), hlI] with s hs hsI
    exact hs.trans_le (h.comboAffine_le_comboProfile hu₀ hu₁ m.2 x hsI)
  · intro c hc
    have hchord : Tendsto (fun s => (1 - s) * h.comboProfile u₀ u₁ x 0 +
        s * h.comboProfile u₀ u₁ x 1) l
        (𝓝 ((1 - s₀) * h.comboProfile u₀ u₁ x 0 + s₀ * h.comboProfile u₀ u₁ x 1)) := by
      apply Tendsto.mono_left _ hl
      exact (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)).tendsto s₀
    rcases hs₀.1.eq_or_lt with h0 | h0
    · subst h0
      simp only [sub_zero, one_mul, zero_mul, add_zero] at hchord
      filter_upwards [hchord.eventually (gt_mem_nhds hc), hlI] with s hs hsI
      exact (h.comboProfile_le_chord hu₀ hu₁ x hsI).trans_lt hs
    · rcases hs₀.2.eq_or_lt with h1 | h1
      · subst h1
        simp only [sub_self, zero_mul, one_mul, zero_add] at hchord
        filter_upwards [hchord.eventually (gt_mem_nhds hc), hlI] with s hs hsI
        exact (h.comboProfile_le_chord hu₀ hu₁ x hsI).trans_lt hs
      · -- interior points (not needed, but harmless): continuity of a convex function
        have hopen : IsOpen (univ ×ˢ Ioo (0 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin n) × ℝ)) :=
          isOpen_univ.prod isOpen_Ioo
        have hcv := ((h.convexOn_comboProfile hu₀ hu₁).subset
          (prod_mono subset_rfl Ioo_subset_Icc_self) (convex_univ.prod (convex_Ioo 0 1))).continuousOn
          hopen
        have hpt : ((x, s₀) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
          ⟨mem_univ _, h0, h1⟩
        have hca := ((hcv _ hpt).continuousAt (hopen.mem_nhds hpt)).tendsto.comp
          ((tendsto_const_nhds (x := x)).prodMk_nhds (tendsto_id (x := 𝓝 s₀)))
        exact (hca.mono_left hl).eventually (gt_mem_nhds hc)

/-- The endpoint profile `H(·, 0)`, in `𝓟(N_ℝ, P_D)`. -/
theorem comboProfile_endpoint_mem [Nonempty (h.commonDomain u₀ u₁)] {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun x => h.comboProfile u₀ u₁ x s) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  refine ⟨⟨convex_univ, ?_⟩, ?_⟩
  · intro x _ y _ a b ha hb hab
    have := (h.convexOn_comboProfile hu₀ hu₁).2 (x := (x, s)) (y := (y, s)) ⟨mem_univ _, hs⟩
      ⟨mem_univ _, hs⟩ ha hb hab
    have hs' : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hs'] using this
  · obtain ⟨C₀, hC₀⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp (h.realProfile_mem hu₀).1.2
    obtain ⟨C₁, hC₁⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp (h.realProfile_mem hu₁).1.2
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨max C₀ C₁, fun x => ?_⟩
    have hle := h.comboProfile_le hu₀ hu₁ x hs
    rcases le_total (h.realProfile u₀ x) (h.realProfile u₁ x) with h01 | h01
    · have : h.comboProfile u₀ u₁ x s ≤ h.realProfile u₁ x := by nlinarith [hs.1, hs.2]
      exact (EReal.coe_le_coe_iff.mpr this).trans
        ((hC₁ x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _))))
    · have : h.comboProfile u₀ u₁ x s ≤ h.realProfile u₀ x := by nlinarith [hs.1, hs.2]
      exact (EReal.coe_le_coe_iff.mpr this).trans
        ((hC₀ x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left _ _))))

end Comparison

/-- The common domain of `G_{φ₀}`, `G_{φ₁}` is nonempty as soon as there is a subgeodesic
(`G_{φ₀ ∧ φ₁} = G_{φ₀} ∨ G_{φ₁}` is proper). -/
theorem nonempty_commonDomain {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor) {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    (hsub : SourceSubgeodesicFrom omega h.atlasForm curve u₀ u₁) :
    (h.commonDomain u₀ u₁).Nonempty := by
  have hne := h.nonempty_toricDivisorPolytope_of_mem hu₀
  have hbot := hsub.thetaRooftop_ne_bot
  have hroof := h.mem_PSHTor_thetaRooftop hu₀ hu₁ hbot
  have hleg := h.legendre_thetaRooftop hne hu₀ hu₁ hbot
  obtain ⟨m, hm⟩ := (h.legendre_mem_closedProperOnBody hne hroof).1.2.1
  refine ⟨m, ?_, ?_⟩
  · have hm' : h.legendre (thetaRooftop h.atlasForm u₀ u₁) m < ⊤ := hm
    rw [hleg] at hm'
    exact (lt_of_le_of_lt (le_max_left _ _) hm').ne
  · have hm' : h.legendre (thetaRooftop h.atlasForm u₀ u₁) m < ⊤ := hm
    rw [hleg] at hm'
    exact (lt_of_le_of_lt (le_max_right _ _) hm').ne

/-- `cor:toricgeodgeneral`, upper bound: `G_{φ_t} ≤ (1-t) G_{φ₀} + t G_{φ₁}`. -/
theorem perronGeodesic_le_combo_legendre {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    (hg : SourceSubgeodesicFrom omega h.atlasForm (sourcePerronGeodesic omega h.atlasForm u₀ u₁)
      u₀ u₁) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (m : EuclideanSpace ℝ (Fin n)) :
    h.legendre (sourcePerronGeodesic omega h.atlasForm u₀ u₁ t) m ≤
      ((1 - t : ℝ) : EReal) * h.legendre u₀ m + (t : EReal) * h.legendre u₁ m := by
  set g := sourcePerronGeodesic omega h.atlasForm u₀ u₁
  have hDne := h.nonempty_commonDomain omega hu₀ hu₁ hg
  have : Nonempty (h.commonDomain u₀ u₁) := hDne.to_subtype
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  -- the endpoints of the comparison subgeodesic
  have hm₀ := h.comboProfile_endpoint_mem hu₀ hu₁ hI0
  have hm₁ := h.comboProfile_endpoint_mem hu₀ hu₁ hI1
  set ψ₀ := h.extension _ hm₀
  set ψ₁ := h.extension _ hm₁
  have hψ₀ : ψ₀ ∈ h.PSHTor := h.extension_mem _ hm₀
  have hψ₁ : ψ₁ ∈ h.PSHTor := h.extension_mem _ hm₁
  have hrp₀ : h.realProfile ψ₀ = fun x => h.comboProfile u₀ u₁ x 0 := by
    funext x; simp only [realProfile, ψ₀, h.profile_extension, EReal.toReal_coe]
  have hrp₁ : h.realProfile ψ₁ = fun x => h.comboProfile u₀ u₁ x 1 := by
    funext x; simp only [realProfile, ψ₁, h.profile_extension, EReal.toReal_coe]
  -- the profile in set (2)
  let F : EuclideanSpace ℝ (Fin n) × Ioo (0 : ℝ) 1 → ℝ := fun p => h.comboProfile u₀ u₁ p.1 p.2
  have hstrip : EqOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => h.comboProfile u₀ u₁ p.1 p.2)
      (stripFunction F) (univ ×ˢ Ioo (0 : ℝ) 1) := by
    rintro ⟨x, s⟩ ⟨-, hs⟩
    exact (stripFunction_of_mem F x hs).symm
  have hF : h.IsToricSubgeodesicProfile ψ₀ ψ₁ F := by
    refine ⟨((h.convexOn_comboProfile hu₀ hu₁).subset (prod_mono subset_rfl Ioo_subset_Icc_self)
      (convex_univ.prod (convex_Ioo 0 1))).congr hstrip, ?_, ?_⟩
    · intro x
      rw [hrp₁]
      apply (h.tendsto_comboProfile hu₀ hu₁ x hI1 nhdsWithin_le_nhds
        (by filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
            exact Ioo_subset_Icc_self hs)).congr'
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact (stripFunction_of_mem F x hs).symm
    · intro x
      rw [hrp₀]
      apply (h.tendsto_comboProfile hu₀ hu₁ x hI0 nhdsWithin_le_nhds
        (by filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
            exact Ioo_subset_Icc_self hs)).congr'
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact (stripFunction_of_mem F x hs).symm
  -- the comparison subgeodesic is a Perron competitor
  set c := h.profileFamily hψ₀ hψ₁ F hF
  have hc := h.isToricSubgeodesic_profileFamily omega hψ₀ hψ₁ hF
  have hψ₀le : ψ₀ ≤ u₀ := by
    apply (h.le_iff hψ₀ hu₀).mpr
    intro x
    rw [(h.realProfile_mem hψ₀).2, (h.realProfile_mem hu₀).2, hrp₀]
    apply EReal.coe_le_coe_iff.mpr
    simpa using h.comboProfile_le hu₀ hu₁ x hI0
  have hψ₁le : ψ₁ ≤ u₁ := by
    apply (h.le_iff hψ₁ hu₁).mpr
    intro x
    rw [(h.realProfile_mem hψ₁).2, (h.realProfile_mem hu₁).2, hrp₁]
    apply EReal.coe_le_coe_iff.mpr
    simpa using h.comboProfile_le hu₀ hu₁ x hI1
  have hcomp : ioo01Curve c ψ₀ ∈ sourcePerronCompetitors omega h.atlasForm u₀ u₁ :=
    ⟨ψ₀, ψ₁, hψ₀.1, hψ₁.1, hψ₀le, hψ₁le, hc.1⟩
  have hct := sourcePerron_competitor_le hcomp t
  rw [ioo01Curve_of_mem c ψ₀ ht] at hct
  have hcmem : c ⟨t, ht⟩ ∈ h.PSHTor := h.extension_mem _ (h.stripSlice_mem hψ₀ hψ₁ hF ⟨t, ht⟩)
  have hgt := h.perronGeodesic_mem_PSHTor omega hu₀ hu₁ hg ht
  have hprof := (h.le_iff hcmem hgt).mp hct
  have hcprof : h.profile (c ⟨t, ht⟩) = fun x => (h.comboProfile u₀ u₁ x t : EReal) := by
    funext x
    exact congrFun (h.profile_extension _ (h.stripSlice_mem hψ₀ hψ₁ hF ⟨t, ht⟩)) x
  rw [hcprof] at hprof
  -- conclude by Legendre duality
  have hconj : h.legendre (g t) m ≤
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun x => (h.comboProfile u₀ u₁ x t : EReal)) m :=
    conjugate_antitone _ hprof m
  refine hconj.trans ?_
  have h1t : 0 < 1 - t := sub_pos.mpr ht.2
  by_cases hm : m ∈ h.commonDomain u₀ u₁
  · rw [← h.coe_toReal_legendre₀ hu₀ hm, ← h.coe_toReal_legendre₁ hu₁ hm,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    unfold conjugate
    apply iSup_le
    intro x
    have hle := h.comboAffine_le_comboProfile hu₀ hu₁ hm x (Ioo_subset_Icc_self ht)
    rw [innerₗ_apply_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    unfold comboAffine at hle
    linarith
  · simp only [commonDomain, mem_ofPred_eq, not_and_or, not_not] at hm
    rcases hm with hm | hm
    · rw [hm, EReal.coe_mul_top_of_pos h1t,
        EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_pos ht.1 (h.legendre_ne_bot hu₁ m))]
      exact le_top
    · rw [hm, EReal.coe_mul_top_of_pos ht.1,
        EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot_of_pos h1t (h.legendre_ne_bot hu₀ m))]
      exact le_top

/-- Source `cor:toricgeodgeneral`.  Let `φ₀, φ₁ ∈ PSH_tor(X, θ)` have positive non-pluripolar
mass.  Then (1) `φ₀ ∼_P φ₁` iff there is a subgeodesic from `φ₀` to `φ₁`; and (2) if so, the
geodesic `(φ_t)_{t ∈ (0,1)}` from `φ₀` to `φ₁` is toric with
`G_{φ_t} = (1-t) G_{φ₀} + t G_{φ₁}` (`eq:Glinear`). -/
theorem toric_geodesic_general {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hu₀ : u₀ ∈ h.PSHTor) (hu₁ : u₁ ∈ h.PSHTor)
    (hpos₀ : 0 < sourcePotentialNonPluripolarMeasure h.atlasForm u₀ hu₀.1 univ)
    (hpos₁ : 0 < sourcePotentialNonPluripolarMeasure h.atlasForm u₁ hu₁.1 univ) :
    (GlobalPComparison.sourcePEquivalent (n := n) u₀ u₁ ↔
        ∃ curve, SourceSubgeodesicFrom omega h.atlasForm curve u₀ u₁) ∧
      (GlobalPComparison.sourcePEquivalent (n := n) u₀ u₁ →
        ∀ curve : ℝ → PolytopeToricVariety γ hs → EReal,
          SourceIsGeodesicFrom omega h.atlasForm curve u₀ u₁ →
            ∀ t ∈ Ioo (0 : ℝ) 1, curve t ∈ h.PSHTor ∧
              h.legendre (curve t) = fun m =>
                ((1 - t : ℝ) : EReal) * h.legendre u₀ m + (t : EReal) * h.legendre u₁ m) := by
  refine ⟨(sourceSubgeodesic_exists_iff_sourcePEquivalent omega hu₀.1 hu₁.1 hpos₀ hpos₁).symm, ?_⟩
  intro hP curve hcurve t ht
  have hg := sourcePerron_isSubgeodesicFrom_of_sourcePEquivalent omega hu₀.1 hu₁.1 hpos₀ hpos₁ hP
  rw [hcurve.2.2.2 t ht]
  refine ⟨h.perronGeodesic_mem_PSHTor omega hu₀ hu₁ hg ht, ?_⟩
  funext m
  exact le_antisymm (h.perronGeodesic_le_combo_legendre omega hu₀ hu₁ hg ht m)
    (h.combo_legendre_le_perronGeodesic omega hu₀ hu₁ hg ht m)

end BigToricMetric

end SGPT.Toric
