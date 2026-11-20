import SGPT.LineBundle.FiltrationSectionPotentials
import SGPT.LineBundle.FeketeLimsup
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Continuity and superadditivity of the section potentials of a filtration

Source `ex:RWN` (chapter *Test curves*): for a filtration `𝓕` of `R(X, L)` and a smooth
Hermitian metric `h` on `L`,
`Γ^{𝓕,k}_τ = usc sup {log |s|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}`, and the book observes

`Γ^{𝓕,k+k'}_τ ≥ Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_τ`,

whence (`eq:limkGammaFk`, current revision) `limsup_k k⁻¹ Γ^{𝓕,k}_τ(x) = sup_k k⁻¹ Γ^{𝓕,k}_τ(x)`
at every point, with a genuine limit wherever `Γ^{𝓕,k}_τ(x) > -∞` for all large `k`.

The upper semicontinuous regularization in the definition of `Γ^{𝓕,k}_τ` does not commute with
sums in general. Here it is not needed: the raw supremum is already continuous. Indeed, the
sections `s ∈ 𝓕^{kτ}_k` with `sup_X |s|²_{h^k} ≤ 1` form a compact subset of the
finite-dimensional space `H⁰(X, L^k)` (the sup norm is a norm on `H⁰(X, L^k)` because a nonzero
section of a line bundle on an integral scheme does not vanish identically), and
`(s, x) ↦ log |s(x)|²_{h^k}` is jointly continuous (it is Lipschitz in `s`, uniformly in `x`, for
the seminorms `s ↦ |s(x)|_{h^k}`). A supremum of a jointly continuous function over a compact set
is continuous.

## Main results

* `SectionFiltration.continuous_rawSectionPotential`: the raw supremum is continuous.
* `SectionFiltration.sectionPotential_eq_raw`: `Γ^{𝓕,k}_τ` equals the raw supremum (no
  regularization is needed).
* `SectionFiltration.sectionPotential_add_le`: `Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_τ ≤ Γ^{𝓕,k+k'}_τ`.
* `SectionFiltration.limsup_sectionPotential_div_eq_iSup`: the revised `eq:limkGammaFk`,
  `limsup_k k⁻¹ Γ^{𝓕,k}_τ(x) = sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ(x)`.
* `SectionFiltration.tendsto_sectionPotential_div_iSup`: if `Γ^{𝓕,k}_τ(x) > -∞` for all
  `k ≥ k₀ > 0`, the limit exists and equals the supremum.
* `EReal.tendsto_div_iSup_of_superadditive_of_eventually_ne_bot`: Fekete's lemma for
  superadditive `[-∞, ∞)`-valued sequences that are finite from some index on (no linear lower
  bound needed).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology NNReal

section Fekete

/-- A superadditive `[-∞, ∞)`-valued sequence whose positive-index terms are finite from
`k₀ > 0` on admits a linear lower bound `-C k ≤ a k` at every positive index with `a k ≠ ⊥`. -/
theorem EReal.exists_linear_lower_bound_of_superadditive (a : ℕ → EReal)
    (hsuper : ∀ m k : ℕ, 0 < m → 0 < k → a m + a k ≤ a (m + k))
    (htop : ∀ k : ℕ, 0 < k → a k ≠ ⊤) (k₀ : ℕ) (hk₀ : 0 < k₀)
    (hfin : ∀ k : ℕ, k₀ ≤ k → a k ≠ ⊥) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 0 < k → a k ≠ ⊥ → (((-C) * k : ℝ) : EReal) ≤ a k := by
  classical
  -- a bound for the finitely many terms of index `< 2 k₀`
  let c₀ : ℝ := ∑ k ∈ Finset.range (2 * k₀), |(a k).toReal|
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hsmall : ∀ k : ℕ, 0 < k → k < 2 * k₀ → a k ≠ ⊥ → ((-c₀ : ℝ) : EReal) ≤ a k := by
    intro k hk hlt hbot
    have hak : a k = ((a k).toReal : EReal) := (EReal.coe_toReal (htop k hk) hbot).symm
    rw [hak, EReal.coe_le_coe_iff]
    have h1 : |(a k).toReal| ≤ c₀ :=
      Finset.single_le_sum (f := fun k => |(a k).toReal|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.mpr hlt)
    linarith [neg_abs_le (a k).toReal]
  refine ⟨c₀, hc₀, fun k hk hbot => ?_⟩
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hlt : k < 2 * k₀
  · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hsmall k hk hlt hbot)
    nlinarith
  · rw [not_lt] at hlt
    -- `k = q k₀ + r` with `k₀ ≤ r < 2 k₀`
    set q := (k - k₀) / k₀ with hq
    set r := k₀ + (k - k₀) % k₀ with hr
    have hkqr : k = q * k₀ + r := by
      have := Nat.div_add_mod (k - k₀) k₀
      rw [hq, hr]
      have hle : k₀ ≤ k := by omega
      calc k = (k - k₀) + k₀ := by omega
        _ = (k₀ * ((k - k₀) / k₀) + (k - k₀) % k₀) + k₀ := by rw [this]
        _ = (k - k₀) / k₀ * k₀ + (k₀ + (k - k₀) % k₀) := by ring
    have hr0 : 0 < r := by omega
    have hrlt : r < 2 * k₀ := by
      have := Nat.mod_lt (k - k₀) hk₀
      omega
    have hrfin : a r ≠ ⊥ := hfin r (by omega)
    have hk₀fin : a k₀ ≠ ⊥ := hfin k₀ le_rfl
    set α : ℝ := (a k₀).toReal with hα
    have hαeq : a k₀ = (α : EReal) := (EReal.coe_toReal (htop k₀ hk₀) hk₀fin).symm
    have hαlow : -c₀ ≤ α := by
      have := hsmall k₀ hk₀ (by omega) hk₀fin
      rw [hαeq, EReal.coe_le_coe_iff] at this
      exact this
    have hrlow := hsmall r hr0 hrlt hrfin
    have hit := EReal.superadditive_iterate hsuper hk₀ hαeq hr0 q
    rw [← hkqr] at hit
    have hqle : (q : ℝ) + 1 ≤ k := by
      have : q + 1 ≤ k := by
        have h1 : q ≤ k - k₀ := Nat.div_le_self _ _
        omega
      exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    calc (((-c₀) * k : ℝ) : EReal) ≤ (((q : ℝ) * α + -c₀ : ℝ) : EReal) := by
          rw [EReal.coe_le_coe_iff]
          nlinarith
      _ = (((q : ℝ) * α : ℝ) : EReal) + ((-c₀ : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ (((q : ℝ) * α : ℝ) : EReal) + a r := add_le_add le_rfl hrlow
      _ ≤ a k := hit

/-- **Fekete's lemma without a lower bound.** A superadditive `[-∞, ∞)`-valued sequence whose
terms are finite from some positive index `k₀` on satisfies
`a k / k → sup_{k > 0} a k / k`. -/
theorem EReal.tendsto_div_iSup_of_superadditive_of_eventually_ne_bot (a : ℕ → EReal)
    (hsuper : ∀ m k : ℕ, 0 < m → 0 < k → a m + a k ≤ a (m + k))
    (hup : ∀ k : ℕ, 0 < k → a k ≤ 0) (k₀ : ℕ) (hk₀ : 0 < k₀)
    (hfin : ∀ k : ℕ, k₀ ≤ k → a k ≠ ⊥) :
    Tendsto (fun k : ℕ => a k / ((k : ℝ) : EReal)) atTop
      (𝓝 (⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal))) := by
  have htop : ∀ k : ℕ, 0 < k → a k ≠ ⊤ := fun k hk =>
    ne_top_of_le_ne_top EReal.zero_ne_top (hup k hk)
  obtain ⟨C, hC0, hC⟩ :=
    EReal.exists_linear_lower_bound_of_superadditive a hsuper htop k₀ hk₀ hfin
  refine EReal.tendsto_div_iSup_of_superadditive a C k₀ hsuper (fun k hk => ?_) hC hfin hk₀
  refine (hup k hk).trans (EReal.coe_nonneg.mpr ?_)
  positivity

end Fekete

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance misc2PointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance misc2PointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance misc2PointManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

namespace Misc2RWN

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- The coordinate of a section of `L^k` at `p` in the frame chosen at `p`. -/
def pointCoeff (k : ℕ) (p : SchemeComplexPoint f) (s : SectionSpace f L k) : ℂ :=
  schemeOpenRegularFunction f n E (schemePointFrameOpen f p a)
    (((schemePointFrame f p a).tensorPower k).coefficients (𝟙 _)
      ((bundleTensorPower L k).val.map (homOfLE le_top).op s)) p

theorem sectionNormSq_eq_pointCoeff (k : ℕ) (s : SectionSpace f L k)
    (p : SchemeComplexPoint f) :
    H.sectionNormSq a k s p = Complex.normSq (pointCoeff (n := n) (E := E) a k p s) *
      H.frameNormSq (schemePointFrame f p a) p ^ k :=
  H.sectionNormSq_frame a (schemePointFrame f p a) k s p (schemePointFrame_mem f p a)

theorem pointCoeff_add (k : ℕ) (p : SchemeComplexPoint f) (s t : SectionSpace f L k) :
    pointCoeff (n := n) (E := E) a k p (s + t) =
      pointCoeff (n := n) (E := E) a k p s + pointCoeff (n := n) (E := E) a k p t := by
  unfold pointCoeff
  have h1 : ((bundleTensorPower L k).val.map (homOfLE (le_top :
      schemePointFrameOpen f p a ≤ ⊤)).op (s + t : SectionSpace f L k)) =
      (bundleTensorPower L k).val.map (homOfLE le_top).op s +
        (bundleTensorPower L k).val.map (homOfLE le_top).op t :=
    map_add _ _ _
  rw [h1, map_add]
  exact schemeOpenRegularFunction_add f n E _ _ _ (schemePointFrame_mem f p a)


theorem sqrt_normSq_mul (z : ℂ) {w : ℝ} :
    Real.sqrt (Complex.normSq z * w) = ‖z‖ * Real.sqrt w := by
  rw [Real.sqrt_mul (Complex.normSq_nonneg z), ← Complex.norm_def]

/-- `s ↦ |s(p)|_{h^k}` as a seminorm on `H⁰(X, L^k)`. -/
def pointSeminorm (k : ℕ) (p : SchemeComplexPoint f) : Seminorm ℂ (SectionSpace f L k) :=
  Seminorm.of (fun s => Real.sqrt (H.sectionNormSq a k s p))
    (fun s t => by
      simp only [sectionNormSq_eq_pointCoeff H a k _ p, pointCoeff_add, sqrt_normSq_mul]
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _))
    (fun c s => by
      simp only [H.sectionNormSq_smul a k c s p, sqrt_normSq_mul])

theorem pointSeminorm_apply (k : ℕ) (p : SchemeComplexPoint f) (s : SectionSpace f L k) :
    pointSeminorm H a k p s = Real.sqrt (H.sectionNormSq a k s p) := rfl

theorem pointSeminorm_sq (k : ℕ) (p : SchemeComplexPoint f) (s : SectionSpace f L k) :
    pointSeminorm H a k p s ^ 2 = H.sectionNormSq a k s p :=
  Real.sq_sqrt (H.sectionNormSq_nonneg a k s p)

theorem continuous_pointSeminorm (k : ℕ) (s : SectionSpace f L k) :
    Continuous fun p => pointSeminorm H a k p s := by
  let := E.isSeparated
  let := E.quasiCompact
  exact Real.continuous_sqrt.comp
    (ProductTestForms.ChartSmooth.continuous (H.sectionNormSq_chartSmooth a k s))

theorem exists_pointSeminorm_le (k : ℕ) (s : SectionSpace f L k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, pointSeminorm H a k p s ≤ M := by
  obtain ⟨M, _, hle⟩ := H.exists_sectionNormSq_le a k s
  exact ⟨Real.sqrt M, Real.sqrt_nonneg _, fun p => Real.sqrt_le_sqrt (hle p)⟩

variable (E) in
/-- A basis of the finite-dimensional space `H⁰(X, L^k)`. -/
def sectionBasis (k : ℕ) :
    Module.Basis (Fin (Module.finrank ℂ (SectionSpace f L k))) ℂ (SectionSpace f L k) :=
  haveI := SectionSpace.finiteDimensional f E a k
  Module.finBasis ℂ (SectionSpace f L k)

variable (E) in
/-- Coordinates on `H⁰(X, L^k)`. -/
def coordEquiv (k : ℕ) :
    (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) ≃ₗ[ℂ] SectionSpace f L k :=
  (sectionBasis E a k).equivFun.symm

/-- The seminorms `c ↦ |s_c(p)|_{h^k}`, `s_c = ∑ cᵢ eᵢ`, are Lipschitz in the coordinates,
uniformly in `p`. -/
theorem exists_lipschitzWith_pointSeminorm_coord (k : ℕ) :
    ∃ K : ℝ≥0, ∀ p : SchemeComplexPoint f, LipschitzWith K
      fun c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ =>
        pointSeminorm H a k p (coordEquiv E a k c) := by
  classical
  have hM : ∀ i : Fin (Module.finrank ℂ (SectionSpace f L k)), ∃ M : ℝ, 0 ≤ M ∧
      ∀ p, pointSeminorm H a k p (sectionBasis E a k i) ≤ M :=
    fun i => exists_pointSeminorm_le H a k (sectionBasis E a k i)
  choose M hM0 hMle using hM
  have hK0 : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  refine ⟨Real.toNNReal (∑ i, M i), fun p => ?_⟩
  refine LipschitzWith.of_dist_le_mul fun c c' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK0]
  have hsum : coordEquiv E a k (c - c') = ∑ i, (c - c') i • sectionBasis E a k i := by
    simp only [coordEquiv, Module.Basis.equivFun_symm_apply]
  calc |pointSeminorm H a k p (coordEquiv E a k c) -
        pointSeminorm H a k p (coordEquiv E a k c')|
      ≤ pointSeminorm H a k p (coordEquiv E a k c - coordEquiv E a k c') :=
        abs_sub_map_le_sub (pointSeminorm H a k p) _ _
    _ = pointSeminorm H a k p (∑ i, (c - c') i • sectionBasis E a k i) := by
        rw [← map_sub, hsum]
    _ ≤ ∑ i, pointSeminorm H a k p ((c - c') i • sectionBasis E a k i) :=
        Finset.le_sum_of_subadditive (pointSeminorm H a k p) (map_zero _).le
          (map_add_le_add _) _ _
    _ = ∑ i, ‖(c - c') i‖ * pointSeminorm H a k p (sectionBasis E a k i) := by
        simp only [map_smul_eq_mul]
    _ ≤ ∑ i, ‖c - c'‖ * M i := Finset.sum_le_sum fun i _ =>
        mul_le_mul (norm_le_pi_norm _ i) (hMle i p) (apply_nonneg _ _) (norm_nonneg _)
    _ = (∑ i, M i) * ‖c - c'‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- `(c, p) ↦ |s_c(p)|_{h^k}`, `s_c = ∑ cᵢ eᵢ`, is jointly continuous. -/
theorem continuous_pointSeminorm_coord (k : ℕ) :
    Continuous fun z : (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) ×
        SchemeComplexPoint f => pointSeminorm H a k z.2 (coordEquiv E a k z.1) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_pointSeminorm_coord H a k
  have ha : ∀ c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ,
      Continuous fun p => pointSeminorm H a k p (coordEquiv E a k c) :=
    fun c => continuous_pointSeminorm H a k _
  exact continuous_prod_of_continuous_lipschitzWith
    (fun z : (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) × SchemeComplexPoint f =>
      pointSeminorm H a k z.2 (coordEquiv E a k z.1)) K ha hK

/-- The same, with the factors swapped. -/
theorem continuous_pointSeminorm_coord_swap (k : ℕ) :
    Continuous fun z : SchemeComplexPoint f ×
        (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) =>
          pointSeminorm H a k z.1 (coordEquiv E a k z.2) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_pointSeminorm_coord H a k
  have ha : ∀ c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ,
      Continuous fun p => pointSeminorm H a k p (coordEquiv E a k c) :=
    fun c => continuous_pointSeminorm H a k _
  exact continuous_prod_of_continuous_lipschitzWith'
    (fun z : SchemeComplexPoint f × (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) =>
      pointSeminorm H a k z.1 (coordEquiv E a k z.2)) K hK ha

/-- `(p, c) ↦ log |s_c(p)|²_{h^k}` is jointly continuous. -/
theorem continuous_sectionLogNormSq_coord_swap (k : ℕ) :
    Continuous fun z : SchemeComplexPoint f ×
        (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) =>
          H.sectionLogNormSq a k (coordEquiv E a k z.2) z.1 := by
  have h2 : Continuous fun z : SchemeComplexPoint f ×
      (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) =>
        H.sectionNormSq a k (coordEquiv E a k z.2) z.1 := by
    simp only [← pointSeminorm_sq H a k]
    exact (continuous_pointSeminorm_coord_swap H a k).pow 2
  exact ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp h2)

end Misc2RWN


namespace SectionFiltration

open Misc2RWN

variable {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]

/-- In coordinates, the sections `s ∈ 𝓕^{kτ}_k` with `sup_X |s|²_{h^k} ≤ 1` form a compact set
(the sup norm is a norm on `H⁰(X, L^k)`). -/
theorem isCompact_coord_normalizedSections [Nonempty (SchemeComplexPoint f)]
    (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L) (k : ℕ) (τ : ℝ) :
    IsCompact (coordEquiv E a k ⁻¹' F.normalizedSections H k τ) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hQ := continuous_pointSeminorm_coord H a k
  have hcp : ∀ c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ,
      Continuous fun p => pointSeminorm H a k p (coordEquiv E a k c) :=
    fun c => continuous_pointSeminorm H a k _
  have hcc : ∀ p : SchemeComplexPoint f,
      Continuous fun c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ =>
        pointSeminorm H a k p (coordEquiv E a k c) :=
    fun p => (Classical.choose_spec (exists_lipschitzWith_pointSeminorm_coord H a k) p).continuous
  -- closedness
  have hclosed : IsClosed (coordEquiv E a k ⁻¹' F.normalizedSections H k τ) := by
    have h1 : IsClosed ((((F.piece ((k : ℝ) * τ) k).comap
        (coordEquiv E a k).toLinearMap : Submodule ℂ _) : Set
          (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ))) :=
      Submodule.closed_of_finiteDimensional _
    have h2 : IsClosed (⋂ p : SchemeComplexPoint f,
        {c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ |
          H.sectionNormSq a k (coordEquiv E a k c) p ≤ 1}) := by
      refine isClosed_iInter fun p => isClosed_le ?_ continuous_const
      simp only [← pointSeminorm_sq H a k p]
      exact (hcc p).pow 2
    have heq : coordEquiv E a k ⁻¹' F.normalizedSections H k τ =
        (((F.piece ((k : ℝ) * τ) k).comap (coordEquiv E a k).toLinearMap : Submodule ℂ _) :
          Set (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ)) ∩
        ⋂ p : SchemeComplexPoint f,
          {c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ |
            H.sectionNormSq a k (coordEquiv E a k c) p ≤ 1} := by
      ext c
      simp only [normalizedSections, mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_iInter,
        SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [heq]
    exact h1.inter h2
  -- the sup norm `P c = sup_X |s_c|_{h^k}`
  let P : (Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) → ℝ := fun c =>
    sSup ((fun p => pointSeminorm H a k p (coordEquiv E a k c)) '' univ)
  have hP : Continuous P :=
    isCompact_univ.continuous_sSup (f := fun c p => pointSeminorm H a k p (coordEquiv E a k c))
      (by exact hQ)
  have hleP : ∀ c p, pointSeminorm H a k p (coordEquiv E a k c) ≤ P c := fun c p =>
    le_csSup (isCompact_univ.image (hcp c)).bddAbove (mem_image_of_mem _ (mem_univ p))
  have hPle : ∀ c (r : ℝ), (∀ p, pointSeminorm H a k p (coordEquiv E a k c) ≤ r) → P c ≤ r :=
    fun c r h => csSup_le (univ_nonempty.image _) (by rintro _ ⟨p, _, rfl⟩; exact h p)
  have hPpos : ∀ c, c ≠ 0 → 0 < P c := by
    intro c hc
    have hΦ : coordEquiv E a k c ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hc
    obtain ⟨p, _, hp⟩ := H.exists_sectionNormSq_ne_zero_of_isOpen a k (coordEquiv E a k c) hΦ
      univ isOpen_univ univ_nonempty
    have : 0 < pointSeminorm H a k p (coordEquiv E a k c) :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne (H.sectionNormSq_nonneg a k _ p) (Ne.symm hp))
    exact this.trans_le (hleP c p)
  -- normalization onto the unit sphere
  have hunit : ∀ c : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ, c ≠ 0 →
      ((‖c‖⁻¹ : ℝ) : ℂ) • c ∈ Metric.sphere (0 : Fin (Module.finrank ℂ
        (SectionSpace f L k)) → ℂ) 1 := by
    intro c hc
    have hnc : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnc), inv_mul_cancel₀ hnc.ne']
  have hR : ∃ R : ℝ, ∀ c ∈ coordEquiv E a k ⁻¹' F.normalizedSections H k τ, ‖c‖ ≤ R := by
    by_cases hS : (Metric.sphere (0 : Fin (Module.finrank ℂ (SectionSpace f L k)) → ℂ) 1).Nonempty
    · obtain ⟨c₀, hc₀, hmin⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ
        (SectionSpace f L k)) → ℂ) 1).exists_isMinOn hS hP.continuousOn
      have hc₀ne : c₀ ≠ 0 := by
        intro h
        rw [h, mem_sphere_zero_iff_norm, norm_zero] at hc₀
        exact zero_ne_one hc₀
      have hm := hPpos c₀ hc₀ne
      refine ⟨(P c₀)⁻¹, fun c hc => ?_⟩
      by_cases hc0 : c = 0
      · rw [hc0, norm_zero]
        exact (inv_pos.mpr hm).le
      · have hnc : 0 < ‖c‖ := norm_pos_iff.mpr hc0
        have hqu : ∀ p, pointSeminorm H a k p (coordEquiv E a k (((‖c‖⁻¹ : ℝ) : ℂ) • c)) ≤
            ‖c‖⁻¹ := by
          intro p
          rw [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hnc)]
          have h1 : pointSeminorm H a k p (coordEquiv E a k c) ≤ 1 :=
            (Real.sqrt_le_sqrt (hc.2 p)).trans_eq Real.sqrt_one
          calc ‖c‖⁻¹ * pointSeminorm H a k p (coordEquiv E a k c) ≤ ‖c‖⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hnc.le)
            _ = ‖c‖⁻¹ := mul_one _
        have hle : P c₀ ≤ ‖c‖⁻¹ :=
          (isMinOn_iff.mp hmin _ (hunit c hc0)).trans (hPle _ _ hqu)
        exact (le_inv_comm₀ hm hnc).mp hle
    · refine ⟨0, fun c _ => ?_⟩
      by_contra hlt
      have hc0 : c ≠ 0 := by
        intro h
        rw [h, norm_zero] at hlt
        exact hlt le_rfl
      exact hS ⟨_, hunit c hc0⟩
  obtain ⟨R, hR⟩ := hR
  exact Metric.isCompact_of_isClosed_isBounded hclosed (isBounded_iff_forall_norm_le.mpr ⟨R, hR⟩)

/-- The raw supremum `x ↦ sup {log |s(x)|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}` is
continuous (source `ex:RWN`). -/
theorem continuous_rawSectionPotential (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) (k : ℕ) (τ : ℝ) :
    Continuous fun x => ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x := by
  rcases isEmpty_or_nonempty (SchemeComplexPoint f) with hX | hX
  · exact continuous_of_discreteTopology
  have hK := F.isCompact_coord_normalizedSections H k τ
  have hG := continuous_sectionLogNormSq_coord_swap H a k
  have heq : (fun x => ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x) =
      fun x => sSup ((fun c => H.sectionLogNormSq a k (coordEquiv E a k c) x) ''
        (coordEquiv E a k ⁻¹' F.normalizedSections H k τ)) := by
    funext x
    apply le_antisymm
    · refine iSup_le fun s => le_sSup ⟨(coordEquiv E a k).symm s.1, ?_, ?_⟩
      · change coordEquiv E a k ((coordEquiv E a k).symm s.1) ∈ F.normalizedSections H k τ
        rw [LinearEquiv.apply_symm_apply]
        exact s.2
      · change H.sectionLogNormSq a k (coordEquiv E a k ((coordEquiv E a k).symm s.1)) x = _
        rw [LinearEquiv.apply_symm_apply]
    · refine sSup_le ?_
      rintro _ ⟨c, hc, rfl⟩
      exact le_iSup (fun s : F.normalizedSections H k τ => H.sectionLogNormSq a k s.1 x)
        ⟨coordEquiv E a k c, hc⟩
  rw [heq]
  exact hK.continuous_sSup
    (f := fun x c => H.sectionLogNormSq a k (coordEquiv E a k c) x)
    hG

/-- Source `ex:RWN`: `Γ^{𝓕,k}_τ` is the raw supremum itself; the upper semicontinuous
regularization does not change it. -/
theorem sectionPotential_eq_raw (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (k : ℕ) (τ : ℝ) :
    F.sectionPotential H k τ =
      fun x => ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x :=
  uscRegularization_eq (F.continuous_rawSectionPotential H k τ).upperSemicontinuous

/-- Source `ex:RWN`: `Γ^{𝓕,k}_τ` is continuous (as a `[-∞, 0]`-valued function). -/
theorem continuous_sectionPotential (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) (k : ℕ) (τ : ℝ) :
    Continuous (F.sectionPotential H k τ) := by
  rw [F.sectionPotential_eq_raw H k τ]
  exact F.continuous_rawSectionPotential H k τ

/-- **Source `ex:RWN`, superadditivity**:
`Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_τ ≤ Γ^{𝓕,k+k'}_τ` for all `k, k' ∈ ℕ` and `τ ∈ ℝ`. -/
theorem sectionPotential_add_le (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (k k' : ℕ) (τ : ℝ) (x : SchemeComplexPoint f) :
    F.sectionPotential H k τ x + F.sectionPotential H k' τ x ≤
      F.sectionPotential H (k + k') τ x := by
  rw [F.sectionPotential_eq_raw H k τ, F.sectionPotential_eq_raw H k' τ,
    F.sectionPotential_eq_raw H (k + k') τ]
  refine EReal.add_le_of_forall_lt fun u hu v hv => ?_
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hu
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hv
  have hmem : SectionSpace.mul f a k k' s.1 t.1 ∈ F.normalizedSections H (k + k') τ := by
    refine ⟨?_, fun p => ?_⟩
    · have h := F.mul_mem _ _ k k' s.1 t.1 s.2.1 t.2.1
      have he : ((k + k' : ℕ) : ℝ) * τ = (k : ℝ) * τ + (k' : ℝ) * τ := by
        push_cast
        ring
      rw [he]
      exact h
    · rw [SectionSpace.mul_apply]
      erw [H.sectionNormSq_mul a k k' s.1 t.1 p]
      exact mul_le_one₀ (s.2.2 p) (H.sectionNormSq_nonneg a k' t.1 p) (t.2.2 p)
  calc u + v ≤ H.sectionLogNormSq a k s.1 x + H.sectionLogNormSq a k' t.1 x :=
        add_le_add hs.le ht.le
    _ = H.sectionLogNormSq a (k + k') (SectionSpace.mul f a k k' s.1 t.1) x :=
        (congrFun (H.sectionLogNormSq_mul a k k' s.1 t.1) x).symm
    _ ≤ ⨆ r : F.normalizedSections H (k + k') τ, H.sectionLogNormSq a (k + k') r.1 x :=
        le_iSup (fun r : F.normalizedSections H (k + k') τ =>
          H.sectionLogNormSq a (k + k') r.1 x) ⟨SectionSpace.mul f a k k' s.1 t.1, hmem⟩

/-- **Source `ex:RWN`, `eq:limkGammaFk` (current revision)**: at every point `x` (and for every
`τ`), `limsup_k k⁻¹ Γ^{𝓕,k}_τ(x) = sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ(x)`. -/
theorem limsup_sectionPotential_div_eq_iSup (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) (τ : ℝ) (x : SchemeComplexPoint f) :
    limsup (fun k : ℕ => F.sectionPotential H k τ x / ((k : ℝ) : EReal)) atTop =
      ⨆ (k : ℕ) (_ : 0 < k), F.sectionPotential H k τ x / ((k : ℝ) : EReal) :=
  EReal.limsup_div_eq_iSup_of_superadditive _
    (fun m k _ _ => F.sectionPotential_add_le H m k τ x)
    (fun k _ => ne_top_of_le_ne_top EReal.zero_ne_top (F.sectionPotential_le_zero H k τ x))

/-- **Source `ex:RWN`, `eq:limkGammaFk` (current revision), the limit clause**: if
`Γ^{𝓕,k}_τ(x) > -∞` for all `k ≥ k₀` (some `k₀ > 0`), then `k⁻¹ Γ^{𝓕,k}_τ(x)` converges to
`sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ(x)`. -/
theorem tendsto_sectionPotential_div_iSup (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) (τ : ℝ) (x : SchemeComplexPoint f) (k₀ : ℕ)
    (hk₀ : 0 < k₀) (hfin : ∀ k : ℕ, k₀ ≤ k → F.sectionPotential H k τ x ≠ ⊥) :
    Tendsto (fun k : ℕ => F.sectionPotential H k τ x / ((k : ℝ) : EReal)) atTop
      (𝓝 (⨆ (k : ℕ) (_ : 0 < k), F.sectionPotential H k τ x / ((k : ℝ) : EReal))) :=
  EReal.tendsto_div_iSup_of_superadditive_of_eventually_ne_bot _
    (fun m k _ _ => F.sectionPotential_add_le H m k τ x)
    (fun k _ => F.sectionPotential_le_zero H k τ x) k₀ hk₀ hfin

end SectionFiltration

end SGPT.LineBundle
