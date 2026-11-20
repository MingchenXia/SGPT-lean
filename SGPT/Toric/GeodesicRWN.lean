import SGPT.Toric.GeodesicRays
import SGPT.PSH.SourceRayLegendreTestCurve
import SGPT.Convex.IntrinsicSegment

/-!
# The toric Ross–Witt Nyström correspondence

Source `chapter_toric_big.tex`, `cor:RWN_toric`: let `ℓ ∈ R_tor(X, θ; φ)` and let `g` be the
function of `cor:geod_tor_char` (`toricRayEquiv`).  Then `ℓ^*_max = -inf_{M_ℝ} g`, and for
`τ < -inf g` the Legendre transform `ℓ^*_τ = inf_{t > 0} (ℓ_t - t τ)` is toric with
`G_{ℓ^*_τ} = G_φ` on `{g ≤ -τ}` and `+∞` elsewhere; in particular `Δ(θ, ℓ^*_τ) = {g ≤ -τ}`.

`ℓ^*` is the source test curve of the ray (`sourceRayLegendreTestCurve`, `lma:LegendsRtoTC`),
whose cut-off `ℓ^*_max` is `sup_X ℓ_1` and whose potentials are `sourcePositiveRayInverse`.

## Route

As in the source: `F_{ℓ^*_τ} = inf_t (F_{ℓ_t} - t τ)` on the torus, so
`G_{ℓ^*_τ} = sup_{t > 0} (G_{ℓ_t} + t τ) = G_φ + sup_{t > 0} t (g + τ)`.  The identity
`ℓ^*_max = -inf g` is proved by comparing with the general facts that `ℓ^*_τ` is `θ`-psh for
`τ ≤ ℓ^*_max` and `≡ -∞` for `τ > ℓ^*_max`: a properness argument gives `inf g ≤ -ℓ^*_max`, and a
lower bound of `ℓ^*_τ` on the torus (from one point of the relative interior of `Dom g` with
`g < -τ`) gives the converse.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators RealInnerProductSpace

/-! ### Extended-real helpers -/

/-- Adding a real constant is an order automorphism of `EReal`. -/
def EReal.addCoeOrderIso (c : ℝ) : EReal ≃o EReal where
  toFun x := x + c
  invFun x := x + ((-c : ℝ) : EReal)
  left_inv x := by
    change x + c + ((-c : ℝ) : EReal) = x
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  right_inv x := by
    change x + ((-c : ℝ) : EReal) + c = x
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  map_rel_iff' {x y} := by
    change x + c ≤ y + c ↔ x ≤ y
    constructor
    · intro hxy
      have := add_le_add hxy (le_refl ((-c : ℝ) : EReal))
      rwa [add_assoc, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero,
        add_zero] at this
    · intro hxy; exact add_le_add hxy le_rfl

theorem EReal.iInf_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i) + (c : EReal) = ⨅ i, (f i + c) :=
  (EReal.addCoeOrderIso c).map_iInf f

theorem EReal.iSup_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨆ i, f i) + (c : EReal) = ⨆ i, (f i + c) :=
  (EReal.addCoeOrderIso c).map_iSup f

/-- `sup_{t > 0} (A + t γ + t τ) = A` if `γ ≤ -τ` and `+∞` otherwise. -/
theorem EReal.iSup_ray {A γ : EReal} (hA : A ≠ ⊥) (hγ : γ ≠ ⊥) (τ : ℝ) :
    (⨆ t : Ioi (0 : ℝ), (A + (t.1 : EReal) * γ + ((t.1 * τ : ℝ) : EReal))) =
      if γ ≤ ((-τ : ℝ) : EReal) then A else ⊤ := by
  have hne (t : Ioi (0 : ℝ)) : (t.1 : EReal) * γ ≠ ⊥ := EReal.coe_mul_ne_bot_of_pos t.2 hγ
  have h1 : (1 : ℝ) ∈ Ioi (0 : ℝ) := mem_Ioi.mpr one_pos
  by_cases hAt : A = ⊤
  · subst hAt
    rw [ite_self]
    apply eq_top_iff.mpr
    refine le_trans ?_ (le_iSup _ ⟨1, h1⟩)
    rw [EReal.top_add_of_ne_bot (hne _), EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, A = a := ⟨A.toReal, (EReal.coe_toReal hAt hA).symm⟩
  by_cases hγt : γ = ⊤
  · subst hγt
    rw [if_neg (by simp)]
    apply eq_top_iff.mpr
    refine le_trans ?_ (le_iSup _ ⟨1, h1⟩)
    rw [EReal.coe_mul_top_of_pos one_pos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _),
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
  obtain ⟨c, rfl⟩ : ∃ c : ℝ, γ = c := ⟨γ.toReal, (EReal.coe_toReal hγt hγ).symm⟩
  have hterm (t : Ioi (0 : ℝ)) :
      (a : EReal) + (t.1 : EReal) * (c : EReal) + ((t.1 * τ : ℝ) : EReal) =
        ((a + t.1 * (c + τ) : ℝ) : EReal) := by
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]; congr 1; ring
  simp only [hterm]
  by_cases hc : c ≤ -τ
  · rw [if_pos (EReal.coe_le_coe_iff.mpr hc)]
    apply le_antisymm
    · refine iSup_le fun t => EReal.coe_le_coe_iff.mpr ?_
      have ht : (0 : ℝ) < t.1 := t.2
      have : t.1 * (c + τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith)
      linarith
    · have ht : Tendsto (fun t : ℝ => ((a + t * (c + τ) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (a : EReal)) := by
        apply EReal.tendsto_coe.mpr
        have : Tendsto (fun t : ℝ => a + t * (c + τ)) (𝓝 0) (𝓝 (a + 0 * (c + τ))) :=
          (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      apply le_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin] with t htpos
      exact le_iSup (fun s : Ioi (0 : ℝ) => ((a + s.1 * (c + τ) : ℝ) : EReal)) ⟨t, htpos⟩
  · rw [if_neg (by rw [EReal.coe_le_coe_iff]; exact hc)]
    push Not at hc
    have hpos : 0 < c + τ := by linarith
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro R
    have hT : 0 < (|R - a| + 1) / (c + τ) := by positivity
    refine lt_of_lt_of_le ?_ (le_iSup _ (⟨(|R - a| + 1) / (c + τ), hT⟩ : Ioi (0 : ℝ)))
    apply EReal.coe_lt_coe_iff.mpr
    have : (|R - a| + 1) / (c + τ) * (c + τ) = |R - a| + 1 := by field_simp
    change R < a + (|R - a| + 1) / (c + τ) * (c + τ)
    rw [this]
    linarith [le_abs_self (R - a)]

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))
variable {φ : PolytopeToricVariety γ hs → EReal} (hφt : φ ∈ h.PSHTor)
  (hφ : SourceModelPotential h.atlasForm φ) (ℓ : {ℓ // ℓ ∈ h.toricRays omega φ hφ})

/-- A point of `ri Dom g` with `g < μ`, as soon as `inf g < μ`. -/
theorem exists_mem_intrinsicInterior_lt {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : IsProper g)
    {μ : ℝ} (hμ : (⨅ m, g m) < (μ : EReal)) :
    ∃ m₀ ∈ intrinsicInterior ℝ (effectiveDomain g), g m₀ < (μ : EReal) := by
  obtain ⟨m₁, hm₁⟩ := iInf_lt_iff.mp hμ
  have hm₁D : m₁ ∈ effectiveDomain g := hm₁.trans (EReal.coe_lt_top _)
  have hC := convex_effectiveDomain hg.1
  obtain ⟨m', hm'⟩ := hg.2.1.intrinsicInterior hC
  have hm'D : m' ∈ effectiveDomain g := intrinsicInterior_subset hm'
  have hcv := convexOn_toReal_effectiveDomain hg
  set c₁ := (g m₁).toReal
  set c' := (g m').toReal
  have hg₁ : g m₁ = (c₁ : EReal) := (EReal.coe_toReal hm₁D.ne (hg.2.2 m₁)).symm
  have hc₁ : c₁ < μ := by rw [hg₁] at hm₁; exact EReal.coe_lt_coe_iff.mp hm₁
  set a := min (1 / 2) ((μ - c₁) / (2 * (|c' - c₁| + 1)))
  have ha : 0 < a := lt_min (by norm_num) (by apply div_pos <;> [linarith; positivity])
  have ha1 : a ≤ 1 / 2 := min_le_left _ _
  have ha2 : a ≤ (μ - c₁) / (2 * (|c' - c₁| + 1)) := min_le_right _ _
  have hmem := combo_mem_intrinsicInterior hC hm' hm₁D ha (by linarith : 0 ≤ 1 - a)
    (by ring : a + (1 - a) = 1)
  refine ⟨_, hmem, ?_⟩
  have hD := intrinsicInterior_subset hmem
  have hval := hcv.2 hm'D hm₁D ha.le (by linarith : 0 ≤ 1 - a) (by ring)
  simp only [smul_eq_mul] at hval
  rw [← EReal.coe_toReal (ne_of_lt hD) (hg.2.2 _), EReal.coe_lt_coe_iff]
  have hbound : a * (c' - c₁) < μ - c₁ := by
    have h1 : a * (c' - c₁) ≤ a * |c' - c₁| := mul_le_mul_of_nonneg_left (le_abs_self _) ha.le
    have h2 : a * |c' - c₁| ≤ (μ - c₁) / (2 * (|c' - c₁| + 1)) * (|c' - c₁| + 1) :=
      mul_le_mul ha2 (by linarith) (abs_nonneg _) (by apply div_nonneg <;> [linarith; positivity])
    have h3 : (μ - c₁) / (2 * (|c' - c₁| + 1)) * (|c' - c₁| + 1) = (μ - c₁) / 2 := by
      field_simp
    linarith
  change (g (a • m' + (1 - a) • m₁)).toReal < μ
  linarith

omit hφt in
theorem rayExt_mem_PSHTor (t : ℝ) : sourceRayExtension ℓ.1 t ∈ h.PSHTor := ℓ.2.2 _

omit hφt in
theorem mem_sourceGeodesicRays_of_toricRays :
    ℓ.1 ∈ sourceGeodesicRays omega h.atlasForm φ hφ := ℓ.property.1

theorem rayLegendre_mem_class :
    (h.toricRayEquiv omega hφt hφ ℓ).1 ∈ h.rayLegendreClass φ :=
  (h.toricRayEquiv omega hφt hφ ℓ).2

/-- `G_{ℓ_t} = G_φ + t g` for `t > 0`, with `ℓ_t` read through the real-time extension. -/
theorem legendre_rayExt_pos {t : ℝ} (ht : 0 < t) (m : EuclideanSpace ℝ (Fin n)) :
    h.legendre (sourceRayExtension ℓ.1 t) m =
      h.legendre φ m + (t : EReal) * (h.toricRayEquiv omega hφt hφ ℓ).1 m :=
  congrFun (h.legendre_rayExt_eq_rayLegendre omega hφt hφ ℓ.2 ht) m

omit hφt in
/-- `ℓ^*_τ` is `T_c`-invariant. -/
theorem invariant_positiveRayInverse (τ : ℝ) :
    PolytopeToricInvariant γ hs (sourcePositiveRayInverse ℓ.1 τ) := by
  intro a ha p
  simp only [sourcePositiveRayInverse]
  exact iInf_congr fun t => congrArg (· - ((t.1 * τ : ℝ) : EReal))
    ((ℓ.2.2 ⟨max t.1 0, mem_Ici.mpr (le_max_right _ _)⟩).2 a ha p)

omit hφt in
/-- `F_{ℓ^*_τ} = inf_{t > 0} (F_{ℓ_t} - t τ)`. -/
theorem profile_positiveRayInverse (τ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    h.profile (sourcePositiveRayInverse ℓ.1 τ) x =
      ⨅ t : Ioi (0 : ℝ), (h.profile (sourceRayExtension ℓ.1 t.1) x - ((t.1 * τ : ℝ) : EReal)) := by
  unfold profile sourcePositiveRayInverse
  rw [EReal.iInf_add_coe]
  apply iInf_congr
  intro t
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]

omit hφt in
/-- `G_{ℓ^*_τ} = sup_{t > 0} (G_{ℓ_t} + t τ)`. -/
theorem legendre_positiveRayInverse (τ : ℝ) (m : EuclideanSpace ℝ (Fin n)) :
    h.legendre (sourcePositiveRayInverse ℓ.1 τ) m =
      ⨆ t : Ioi (0 : ℝ), (h.legendre (sourceRayExtension ℓ.1 t.1) m + ((t.1 * τ : ℝ) : EReal)) := by
  have hprof : h.profile (sourcePositiveRayInverse ℓ.1 τ) = fun x => ⨅ t : Ioi (0 : ℝ),
      (((h.realProfile (sourceRayExtension ℓ.1 t.1) x - t.1 * τ : ℝ) : EReal)) := by
    funext x
    rw [h.profile_positiveRayInverse omega hφ ℓ τ x]
    apply iInf_congr
    intro t
    rw [(h.realProfile_mem (h.rayExt_mem_PSHTor omega hφ ℓ t.1)).2, EReal.coe_sub]
  unfold legendre
  rw [hprof, conjugate_iInf]
  simp only [convexSup]
  apply iSup_congr
  intro t
  unfold conjugate
  rw [EReal.iSup_add_coe]
  apply iSup_congr
  intro x
  rw [(h.realProfile_mem (h.rayExt_mem_PSHTor omega hφ ℓ t.1)).2]
  dsimp only
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
  congr 1; ring

/-- `G_{ℓ^*_τ}(m) = G_φ(m)` if `g(m) ≤ -τ`, and `+∞` otherwise. -/
theorem legendre_positiveRayInverse_eq (τ : ℝ) (m : EuclideanSpace ℝ (Fin n)) :
    h.legendre (sourcePositiveRayInverse ℓ.1 τ) m =
      if (h.toricRayEquiv omega hφt hφ ℓ).1 m ≤ ((-τ : ℝ) : EReal) then h.legendre φ m else ⊤ := by
  rw [h.legendre_positiveRayInverse omega hφ ℓ τ m]
  rw [iSup_congr fun t : Ioi (0 : ℝ) => by rw [h.legendre_rayExt_pos omega hφt hφ ℓ t.2 m]]
  exact EReal.iSup_ray (h.legendre_ne_bot hφt m)
    ((h.rayLegendre_mem_class omega hφt hφ ℓ).1.2.2 m) τ

/-- `ℓ^*_max = -inf g`. -/
theorem rayLegendreCutoff_eq :
    ((sourceRayLegendreCutoff omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ) : ℝ) : EReal) =
      -(⨅ m, (h.toricRayEquiv omega hφt hφ ℓ).1 m) := by
  set g := (h.toricRayEquiv omega hφt hφ ℓ).1
  set c := sourceRayLegendreCutoff omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)
  have hg := h.rayLegendre_mem_class omega hφt hφ ℓ
  apply le_antisymm
  · -- `ℓ^*_c` is toric, so its Legendre transform is proper
    have hmem : sourcePositiveRayInverse ℓ.1 c ∈ h.PSHTor :=
      ⟨sourceRayLegendre_inverse_thetaPSH omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ) le_rfl,
        h.invariant_positiveRayInverse omega hφ ℓ c⟩
    obtain ⟨m, hm⟩ := (h.legendre_isProper hmem).2.1
    have hm' : h.legendre (sourcePositiveRayInverse ℓ.1 c) m < ⊤ := hm
    rw [h.legendre_positiveRayInverse_eq omega hφt hφ ℓ c m] at hm'
    have hgm : g m ≤ ((-c : ℝ) : EReal) := by
      by_contra hcon
      rw [if_neg hcon] at hm'
      exact lt_irrefl _ hm'
    have := (iInf_le g m).trans hgm
    rw [EReal.coe_neg] at this
    exact EReal.le_neg_of_le_neg this
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨τ, hcτ, hτ⟩ := EReal.exists_between_coe_real hcon
    have hcτ' : c < τ := EReal.coe_lt_coe_iff.mp hcτ
    have hinf : (⨅ m, g m) < ((-τ : ℝ) : EReal) := by
      rw [EReal.coe_neg]; exact EReal.lt_neg_comm.mp hτ
    obtain ⟨m₀, hm₀, hgm₀⟩ := exists_mem_intrinsicInterior_lt hg.1 hinf
    have hm₀φ : m₀ ∈ effectiveDomain (h.legendre φ) := by
      rw [h.intrinsicInterior_dom_eq hφt hg] at hm₀; exact intrinsicInterior_subset hm₀
    have hbot := sourceRayLegendre_inverse_bot_above omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ) hcτ'
    -- a finite lower bound at the torus point `e^{0}`
    set p := polytopeToricEmbedding γ hs (positiveTorusPoint 0)
    have hlow : (((-(h.legendre φ m₀).toReal - h.potential 0) : ℝ) : EReal) ≤
        sourcePositiveRayInverse ℓ.1 τ p := by
      apply le_iInf
      intro t
      have hmt := ℓ.2.2 ⟨max t.1 0, mem_Ici.mpr (le_max_right _ _)⟩
      have hval := h.apply_embedding_of_mem hmt (positiveTorusPoint 0)
      rw [unitTorusLog_positiveTorusPoint] at hval
      change _ ≤ sourceRayExtension ℓ.1 t.1 p - _
      change _ ≤ ℓ.1 ⟨max t.1 0, mem_Ici.mpr (le_max_right _ _)⟩ p - _
      rw [hval, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have hGt : h.legendre (sourceRayExtension ℓ.1 t.1) m₀ =
          h.legendre φ m₀ + (t.1 : EReal) * g m₀ := h.legendre_rayExt_pos omega hφt hφ ℓ t.2 m₀
      have hgm₀' : g m₀ < ((-τ : ℝ) : EReal) := hgm₀
      have hgfin : g m₀ ≠ ⊤ := (hgm₀'.trans (EReal.coe_lt_top _)).ne
      obtain ⟨gv, hgv⟩ : ∃ a : ℝ, g m₀ = a := ⟨_, (EReal.coe_toReal hgfin (hg.1.2.2 m₀)).symm⟩
      obtain ⟨Φ, hΦ⟩ : ∃ a : ℝ, h.legendre φ m₀ = a :=
        ⟨_, (EReal.coe_toReal (ne_of_lt hm₀φ) (h.legendre_ne_bot hφt m₀)).symm⟩
      rw [hgv, hΦ, ← EReal.coe_mul, ← EReal.coe_add] at hGt
      have hGfin : h.legendre (sourceRayExtension ℓ.1 t.1) m₀ ≠ ⊤ := by
        rw [hGt]; exact EReal.coe_ne_top _
      have hFY := h.inner_sub_legendre_le (h.rayExt_mem_PSHTor omega hφ ℓ t.1) hGfin 0
      rw [inner_zero_left, hGt, EReal.toReal_coe] at hFY
      change 0 - (Φ + t.1 * gv) ≤
        h.realProfile (ℓ.1 ⟨max t.1 0, mem_Ici.mpr (le_max_right _ _)⟩) 0 at hFY
      have hgτ : gv < -τ := by rw [hgv] at hgm₀'; exact EReal.coe_lt_coe_iff.mp hgm₀'
      rw [hΦ, EReal.toReal_coe]
      have ht : (0 : ℝ) < t.1 := t.2
      have hneg : t.1 * (gv + τ) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
      linarith
    rw [hbot] at hlow
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hlow)

/-- Source `cor:RWN_toric`.  Let `ℓ ∈ R_tor(X, θ; φ)`, `g` its function in `cor:geod_tor_char`,
and `ℓ^*` its Legendre transform test curve (`lma:LegendsRtoTC`).  Then `ℓ^*_max = -inf g`, and
for every `τ < ℓ^*_max = -inf g`, `ℓ^*_τ` is toric, `G_{ℓ^*_τ} = G_φ` on `{g ≤ -τ}` and `+∞`
elsewhere, and `Δ(θ, ℓ^*_τ) = {g ≤ -τ}`. -/
theorem toric_ray_test_curve :
    (((sourceRayLegendreTestCurve omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)).max : ℝ) : EReal) =
        -(⨅ m, (h.toricRayEquiv omega hφt hφ ℓ).1 m) ∧
      ∀ τ : Iio (sourceRayLegendreTestCurve omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)).max,
        (sourceRayLegendreTestCurve omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)).potential τ ∈ h.PSHTor ∧
        h.legendre ((sourceRayLegendreTestCurve omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)).potential τ) = (fun m =>
          if (h.toricRayEquiv omega hφt hφ ℓ).1 m ≤ ((-τ.1 : ℝ) : EReal) then h.legendre φ m
          else ⊤) ∧
        h.newtonBody ((sourceRayLegendreTestCurve omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)).potential τ) =
          {m | (h.toricRayEquiv omega hφt hφ ℓ).1 m ≤ ((-τ.1 : ℝ) : EReal)} := by
  refine ⟨h.rayLegendreCutoff_eq omega hφt hφ ℓ, ?_⟩
  intro τ
  set g := (h.toricRayEquiv omega hφt hφ ℓ).1
  have hg := h.rayLegendre_mem_class omega hφt hφ ℓ
  have hpot : (sourceRayLegendreTestCurve omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ)).potential τ =
      sourcePositiveRayInverse ℓ.1 τ.1 := rfl
  rw [hpot]
  have hτ : τ.1 < sourceRayLegendreCutoff omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ) := τ.2
  have hmem : sourcePositiveRayInverse ℓ.1 τ.1 ∈ h.PSHTor :=
    ⟨sourceRayLegendre_inverse_thetaPSH omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ) hτ.le,
      h.invariant_positiveRayInverse omega hφ ℓ τ.1⟩
  have hleg : h.legendre (sourcePositiveRayInverse ℓ.1 τ.1) = fun m =>
      if g m ≤ ((-τ.1 : ℝ) : EReal) then h.legendre φ m else ⊤ :=
    funext (h.legendre_positiveRayInverse_eq omega hφt hφ ℓ τ.1)
  refine ⟨hmem, hleg, ?_⟩
  -- the Newton body
  rw [h.newtonBody_eq_closure_dom hmem, hleg]
  have hdom : effectiveDomain (fun m => if g m ≤ ((-τ.1 : ℝ) : EReal) then h.legendre φ m else ⊤) =
      {m | g m ≤ ((-τ.1 : ℝ) : EReal)} ∩ effectiveDomain (h.legendre φ) := by
    ext m
    simp only [effectiveDomain, mem_ofPred_eq, mem_inter_iff]
    split_ifs with hm
    · exact ⟨fun h' => ⟨hm, h'⟩, fun h' => h'.2⟩
    · exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h'.1 hm⟩
  rw [hdom]
  have hclosed : IsClosed {m | g m ≤ ((-τ.1 : ℝ) : EReal)} := hg.2.1.isClosed_preimage _
  apply le_antisymm (closure_minimal inter_subset_left hclosed)
  -- density, through a relative-interior point with `g < -τ`
  intro m hm
  have hinf : (⨅ m, g m) < ((-τ.1 : ℝ) : EReal) := by
    have h1 := h.rayLegendreCutoff_eq omega hφt hφ ℓ
    have h2 : ((τ.1 : ℝ) : EReal) < ((sourceRayLegendreCutoff omega (h.mem_sourceGeodesicRays_of_toricRays omega hφ ℓ) : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr hτ
    rw [h1] at h2
    rw [EReal.coe_neg]; exact EReal.lt_neg_comm.mp h2
  obtain ⟨m₀, hm₀, hgm₀⟩ := exists_mem_intrinsicInterior_lt hg.1 hinf
  have hC := convex_effectiveDomain hg.1.1
  have hmD : m ∈ effectiveDomain g := lt_of_le_of_lt hm (EReal.coe_lt_top _)
  have hm₀D : m₀ ∈ effectiveDomain g := intrinsicInterior_subset hm₀
  have hcv := convexOn_toReal_effectiveDomain hg.1
  have hpath : Tendsto (fun a : ℝ => a • m₀ + (1 - a) • m) (𝓝[>] 0) (𝓝 m) := by
    have hc : Continuous (fun a : ℝ => a • m₀ + (1 - a) • m) :=
      (continuous_id.smul continuous_const).add
        ((continuous_const.sub continuous_id).smul continuous_const)
    have : Tendsto (fun a : ℝ => a • m₀ + (1 - a) • m) (𝓝 0) (𝓝 ((0 : ℝ) • m₀ + ((1 : ℝ) - 0) • m)) :=
      hc.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hpath
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha
  have h1a : (0 : ℝ) ≤ 1 - a := by linarith [ha.2]
  have hri := combo_mem_intrinsicInterior hC hm₀ hmD ha.1 h1a (by ring)
  refine ⟨?_, ?_⟩
  · -- `g ≤ -τ` along the segment
    have hD : (a • m₀ + (1 - a) • m) ∈ effectiveDomain g := intrinsicInterior_subset hri
    have hval : (g (a • m₀ + (1 - a) • m)).toReal ≤ a * (g m₀).toReal + (1 - a) * (g m).toReal := by
      have := hcv.2 hm₀D hmD ha.1.le h1a (by ring)
      simpa only [smul_eq_mul] using this
    obtain ⟨z, hz⟩ : ∃ z : ℝ, g (a • m₀ + (1 - a) • m) = z :=
      ⟨_, (EReal.coe_toReal (ne_of_lt hD) (hg.1.2.2 _)).symm⟩
    obtain ⟨u₀, hu₀⟩ : ∃ z : ℝ, g m₀ = z := ⟨_, (EReal.coe_toReal hm₀D.ne (hg.1.2.2 m₀)).symm⟩
    obtain ⟨u, hu⟩ : ∃ z : ℝ, g m = z := ⟨_, (EReal.coe_toReal hmD.ne (hg.1.2.2 m)).symm⟩
    have hgm₀' : g m₀ < ((-τ.1 : ℝ) : EReal) := hgm₀
    have hm' : g m ≤ ((-τ.1 : ℝ) : EReal) := hm
    rw [hu₀, EReal.coe_lt_coe_iff] at hgm₀'
    rw [hu, EReal.coe_le_coe_iff] at hm'
    rw [hz, hu₀, hu, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe] at hval
    change g (a • m₀ + (1 - a) • m) ≤ _
    rw [hz, EReal.coe_le_coe_iff]
    nlinarith [ha.1, ha.2]
  · rw [h.intrinsicInterior_dom_eq hφt hg] at hri
    exact intrinsicInterior_subset hri

end BigToricMetric

end SGPT.Toric
