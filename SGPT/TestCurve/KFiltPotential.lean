import SGPT.TestCurve.KFiltRing
import SGPT.TestCurve.RWNObstacleIGood

/-!
# The test curve of a filtration, for an abstract metered section ring

Source `ex:RWN` (chapter *Test curves*). Blueprint `claude-k-filt`, nodes `claude-k-filt:metric`,
`claude-k-filt:potentials`, `claude-k-filt:obstacle`.

The construction of `ex:RWN` uses the section ring `R(X, L)` only through:

* the finite-dimensional graded pieces `S k = H⁰(X, L^k)` and their product;
* the pointwise squared norms `|s|²_{h^k}` of a smooth metric `h` (homogeneous, subadditive
  square roots, multiplicative, continuous, not identically zero on a nonzero section);
* Lelong–Poincaré, `log |s|²_{h^k} ∈ PSH(X, kθ)`, `θ = c₁(L, h)`, for `s ≠ 0`, `k > 0`;
* the analytic singularities of `log |s|²_{h^k}`.

`SectionMetric` packages these data on a complex manifold `X` (in the sense of
SGPT.Foundations.Analysis). For a filtration `𝓕` (`GradedFiltration`) we define, exactly as in the
book, `Γ^{𝓕,k}_τ = usc sup {log |s|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}`,
the obstacle `usc sup_{k>0} k⁻¹Γ^{𝓕,k}_τ` and `Γ^𝓕_τ = P_θ[obstacle]`, and port the proofs of
the projective formalization (`SGPT.LineBundle.SectionFiltration.*`, lanes MISC2/RWN) to this
interface. The analytic section ring of a compact Kähler manifold is an instance
(`SGPT.TestCurve.KFilt.analyticSectionMetric`).

## Main results

* `GradedFiltration.isThetaPshPotential_sectionPotential`: `Γ^{𝓕,k}_τ ∈ PSH(X, kθ)` for
  `kτ ≤ τ_k(𝓕)`, `k > 0`; `sectionPotential_le_zero`.
* `GradedFiltration.sectionPotential_eq_raw`, `continuous_sectionPotential`: no regularization
  is needed (compactness of the normalized sections).
* `GradedFiltration.sectionPotential_add_le`: `Γ^{𝓕,k+k'}_τ ≥ Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_τ`;
  `limsup_sectionPotential_div_eq_iSup`, `tendsto_sectionPotential_div_iSup`
  (`eq:limkGammaFk`).
* `GradedFiltration.testCurvePotential_anti`, `testCurvePotential_isThetaPshPotential`,
  `obstacle_concave`, `testCurvePotential_concave`.
* `GradedFiltration.obstacle_iGood`: the obstacle is `𝓘`-good (`prop:Igoodsup`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open Filter Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.RWN
open scoped Topology NNReal

/-- Metric data on a graded section ring `⊕_k S k` over a complex manifold `X`: the pointwise
squared norms `|s|²_{h^k}` of a smooth Hermitian metric `h` and its curvature form
`θ = c₁(L, h)`, with the properties used in source `ex:RWN`. -/
structure SectionMetric (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (S : ℕ → Type) [∀ k, AddCommGroup (S k)] [∀ k, Module ℂ (S k)]
    (mul : ∀ k k' : ℕ, S k → S k' → S (k + k')) where
  /-- The curvature form `θ = c₁(L, h)`. -/
  θ : ClosedRealOneOneForm n X
  /-- The squared norm `x ↦ |s(x)|²_{h^k}` of a section `s ∈ S k`. -/
  normSq : ∀ k : ℕ, S k → X → ℝ
  normSq_nonneg : ∀ (k : ℕ) (s : S k) (x : X), 0 ≤ normSq k s x
  normSq_smul : ∀ (k : ℕ) (c : ℂ) (s : S k) (x : X),
    normSq k (c • s) x = Complex.normSq c * normSq k s x
  sqrt_normSq_add_le : ∀ (k : ℕ) (s t : S k) (x : X),
    Real.sqrt (normSq k (s + t) x) ≤ Real.sqrt (normSq k s x) + Real.sqrt (normSq k t x)
  normSq_mul : ∀ (k k' : ℕ) (s : S k) (t : S k') (x : X),
    normSq (k + k') (mul k k' s t) x = normSq k s x * normSq k' t x
  continuous_normSq : ∀ (k : ℕ) (s : S k), Continuous (normSq k s)
  exists_normSq_ne_zero : ∀ (k : ℕ) (s : S k), s ≠ 0 → ∃ x, normSq k s x ≠ 0
  mul_ne_zero : ∀ (k k' : ℕ) (s : S k) (t : S k'), s ≠ 0 → t ≠ 0 → mul k k' s t ≠ 0
  /-- Lelong–Poincaré: `log |s|²_{h^k} ∈ PSH(X, kθ)` for `s ≠ 0`, `k > 0`. -/
  isThetaPsh : ∀ (k : ℕ), 0 < k → ∀ s : S k, s ≠ 0 →
    IsThetaPshPotential ((k : ℝ) • θ).val fun x => ENNReal.log (ENNReal.ofReal (normSq k s x))
  /-- `log |s|²_{h^k}` has analytic singularities for `s ≠ 0`. -/
  analyticType : ∀ (k : ℕ) (s : S k), s ≠ 0 →
    QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n)
      fun x => ENNReal.log (ENNReal.ofReal (normSq k s x))

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
variable {S : ℕ → Type} [∀ k, AddCommGroup (S k)] [∀ k, Module ℂ (S k)]
  {mul : ∀ k k' : ℕ, S k → S k' → S (k + k')}

namespace SectionMetric

variable (D : SectionMetric n X S mul)

/-- `log |s|²_{h^k}` (with `log 0 = -∞`). -/
def logNormSq (k : ℕ) (s : S k) (x : X) : EReal :=
  ENNReal.log (ENNReal.ofReal (D.normSq k s x))

theorem normSq_zero (k : ℕ) (x : X) : D.normSq k 0 x = 0 := by
  have h := D.normSq_smul k 0 0 x
  rwa [zero_smul, map_zero, zero_mul] at h

theorem logNormSq_zero (k : ℕ) (x : X) : D.logNormSq k 0 x = ⊥ := by
  simp [logNormSq, D.normSq_zero]

theorem logNormSq_mul (k k' : ℕ) (s : S k) (t : S k') (x : X) :
    D.logNormSq (k + k') (mul k k' s t) x = D.logNormSq k s x + D.logNormSq k' t x := by
  unfold logNormSq
  rw [D.normSq_mul, ENNReal.ofReal_mul (D.normSq_nonneg k s x), ENNReal.log_mul_add]

/-- `log |c s|²_{h^k} = log |c|² + log |s|²_{h^k}` for `c ≠ 0`. -/
theorem logNormSq_smul (k : ℕ) {c : ℂ} (hc : c ≠ 0) (s : S k) (x : X) :
    D.logNormSq k (c • s) x = ((Real.log (Complex.normSq c) : ℝ) : EReal) + D.logNormSq k s x := by
  unfold logNormSq
  rw [D.normSq_smul k c s x, ENNReal.ofReal_mul (Complex.normSq_nonneg c),
    ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Complex.normSq_pos.mpr hc)]

/-- On a compact manifold every `|s|²_{h^k}` is bounded. -/
theorem exists_normSq_le [CompactSpace X] (k : ℕ) (s : S k) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, D.normSq k s x ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_range (D.continuous_normSq k s)).bddAbove
  exact ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun p => (hM ⟨p, rfl⟩).trans (le_max_left _ _)⟩

/-- Every nonzero section has a nonzero multiple `c s` with `|c s|²_{h^k} ≤ 1`. -/
theorem exists_normalized [CompactSpace X] (k : ℕ) (s : S k) (hs : s ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ c • s ≠ 0 ∧ ∀ x, D.normSq k (c • s) x ≤ 1 := by
  obtain ⟨M, hM, hle⟩ := D.exists_normSq_le k s
  refine ⟨((Real.sqrt M)⁻¹ : ℝ), ?_, ?_, fun p => ?_⟩
  · exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hM)).ne'
  · exact smul_ne_zero (by exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hM)).ne') hs
  · rw [D.normSq_smul k, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hM.le]
    rw [inv_mul_le_iff₀ hM, mul_one]
    exact hle p

/-- The normalized section potential `k⁻¹ log |s|²_{h^k}` is `θ`-psh for `s ≠ 0`, `k > 0`. -/
theorem isThetaPsh_normalized {k : ℕ} (hk : 0 < k) {s : S k} (hs : s ≠ 0) :
    IsThetaPshPotential D.θ.val fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * D.logNormSq k s x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := RestrictedApproximantComparison.isThetaPshPotential_smul (D.isThetaPsh k hk s hs)
    (inv_pos.mpr hkR)
  simp only [smul_smul, inv_mul_cancel₀ hkR.ne', one_smul] at h
  exact h

/-! #### Pointwise seminorms and coordinates -/

theorem sqrt_normSq_mul (z : ℂ) {w : ℝ} :
    Real.sqrt (Complex.normSq z * w) = ‖z‖ * Real.sqrt w := by
  rw [Real.sqrt_mul (Complex.normSq_nonneg z), ← Complex.norm_def]

/-- `s ↦ |s(x)|_{h^k}` as a seminorm on `S k`. -/
def pointSeminorm (k : ℕ) (x : X) : Seminorm ℂ (S k) :=
  Seminorm.of (fun s => Real.sqrt (D.normSq k s x)) (fun s t => D.sqrt_normSq_add_le k s t x)
    (fun c s => by simp only [D.normSq_smul k c s x, sqrt_normSq_mul])

theorem pointSeminorm_sq (k : ℕ) (x : X) (s : S k) :
    D.pointSeminorm k x s ^ 2 = D.normSq k s x :=
  Real.sq_sqrt (D.normSq_nonneg k s x)

theorem continuous_pointSeminorm (k : ℕ) (s : S k) : Continuous fun x => D.pointSeminorm k x s :=
  Real.continuous_sqrt.comp (D.continuous_normSq k s)

theorem exists_pointSeminorm_le [CompactSpace X] (k : ℕ) (s : S k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, D.pointSeminorm k x s ≤ M := by
  obtain ⟨M, _, hle⟩ := D.exists_normSq_le k s
  exact ⟨Real.sqrt M, Real.sqrt_nonneg _, fun p => Real.sqrt_le_sqrt (hle p)⟩

variable [∀ k, FiniteDimensional ℂ (S k)]

/-- Coordinates on the finite-dimensional space `S k`. -/
def coordEquiv (k : ℕ) : (Fin (Module.finrank ℂ (S k)) → ℂ) ≃ₗ[ℂ] S k :=
  (Module.finBasis ℂ (S k)).equivFun.symm

/-- The seminorms `c ↦ |s_c(x)|_{h^k}` are Lipschitz in the coordinates, uniformly in `x`. -/
theorem exists_lipschitzWith_pointSeminorm_coord [CompactSpace X] (k : ℕ) :
    ∃ K : ℝ≥0, ∀ x : X, LipschitzWith K
      fun c : Fin (Module.finrank ℂ (S k)) → ℂ => D.pointSeminorm k x (coordEquiv k c) := by
  classical
  have hM : ∀ i : Fin (Module.finrank ℂ (S k)), ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, D.pointSeminorm k x (Module.finBasis ℂ (S k) i) ≤ M :=
    fun i => D.exists_pointSeminorm_le k _
  choose M hM0 hMle using hM
  have hK0 : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  refine ⟨Real.toNNReal (∑ i, M i), fun p => ?_⟩
  refine LipschitzWith.of_dist_le_mul fun c c' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK0]
  have hsum : coordEquiv k (c - c') = ∑ i, (c - c') i • Module.finBasis ℂ (S k) i := by
    simp only [coordEquiv, Module.Basis.equivFun_symm_apply]
  calc |D.pointSeminorm k p (coordEquiv k c) - D.pointSeminorm k p (coordEquiv k c')|
      ≤ D.pointSeminorm k p (coordEquiv k c - coordEquiv k c') :=
        abs_sub_map_le_sub (D.pointSeminorm k p) _ _
    _ = D.pointSeminorm k p (∑ i, (c - c') i • Module.finBasis ℂ (S k) i) := by
        rw [← map_sub, hsum]
    _ ≤ ∑ i, D.pointSeminorm k p ((c - c') i • Module.finBasis ℂ (S k) i) :=
        Finset.le_sum_of_subadditive (D.pointSeminorm k p) (map_zero _).le
          (map_add_le_add _) _ _
    _ = ∑ i, ‖(c - c') i‖ * D.pointSeminorm k p (Module.finBasis ℂ (S k) i) := by
        simp only [map_smul_eq_mul]
    _ ≤ ∑ i, ‖c - c'‖ * M i := Finset.sum_le_sum fun i _ =>
        mul_le_mul (norm_le_pi_norm _ i) (hMle i p) (apply_nonneg _ _) (norm_nonneg _)
    _ = (∑ i, M i) * ‖c - c'‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- `(x, c) ↦ |s_c(x)|_{h^k}` is jointly continuous. -/
theorem continuous_pointSeminorm_coord_swap [CompactSpace X] (k : ℕ) :
    Continuous fun z : X × (Fin (Module.finrank ℂ (S k)) → ℂ) =>
      D.pointSeminorm k z.1 (coordEquiv k z.2) := by
  obtain ⟨K, hK⟩ := D.exists_lipschitzWith_pointSeminorm_coord k
  exact continuous_prod_of_continuous_lipschitzWith'
    (fun z : X × (Fin (Module.finrank ℂ (S k)) → ℂ) => D.pointSeminorm k z.1 (coordEquiv k z.2))
    K hK (fun c => D.continuous_pointSeminorm k (coordEquiv k c))

/-- `(x, c) ↦ log |s_c(x)|²_{h^k}` is jointly continuous. -/
theorem continuous_logNormSq_coord_swap [CompactSpace X] (k : ℕ) :
    Continuous fun z : X × (Fin (Module.finrank ℂ (S k)) → ℂ) =>
      D.logNormSq k (coordEquiv k z.2) z.1 := by
  have h2 : Continuous fun z : X × (Fin (Module.finrank ℂ (S k)) → ℂ) =>
      D.normSq k (coordEquiv k z.2) z.1 := by
    simp only [← D.pointSeminorm_sq k]
    exact (D.continuous_pointSeminorm_coord_swap k).pow 2
  exact ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp h2)

end SectionMetric

/-! ### The section potentials `Γ^{𝓕,k}_τ` -/

namespace GradedFiltration

variable (F : GradedFiltration mul) (D : SectionMetric n X S mul)

/-- The sections `s ∈ 𝓕^{kτ}_k` with `|s|²_{h^k} ≤ 1` (source `ex:RWN`). -/
def normalizedSections (k : ℕ) (τ : ℝ) : Set (S k) :=
  {s | s ∈ F.piece ((k : ℝ) * τ) k ∧ ∀ x, D.normSq k s x ≤ 1}

/-- Source `ex:RWN`:
`Γ^{𝓕,k}_τ = usc sup {log |s|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}`. -/
def sectionPotential (k : ℕ) (τ : ℝ) : X → EReal :=
  SGPT.PSH.uscSup fun s : F.normalizedSections D k τ => D.logNormSq k s.1

/-- `Γ^{𝓕,k}_τ ≤ 0`. -/
theorem sectionPotential_le_zero (k : ℕ) (τ : ℝ) : F.sectionPotential D k τ ≤ 0 := by
  have h : (fun x => ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x) ≤
      fun _ => (0 : EReal) := fun x => iSup_le fun s => by
    change ENNReal.log (ENNReal.ofReal (D.normSq k s.1 x)) ≤ 0
    rw [ENNReal.log_le_zero_iff]
    exact ENNReal.ofReal_le_one.mpr (s.2.2 x)
  intro x
  have := uscRegularization_mono h x
  rwa [uscRegularization_const] at this

variable [CompactSpace X] [∀ k, FiniteDimensional ℂ (S k)]

/-- **Source `ex:RWN`**: `Γ^{𝓕,k}_τ ∈ PSH(X, kθ)` whenever `kτ ≤ τ_k(𝓕)` and `k > 0`. -/
theorem isThetaPshPotential_sectionPotential {k : ℕ} (hk : 0 < k) {τ : ℝ}
    (hτ : (((k : ℝ) * τ : ℝ) : EReal) ≤ F.jump k) :
    IsThetaPshPotential ((k : ℝ) • D.θ).val (F.sectionPotential D k τ) := by
  have hne : F.piece ((k : ℝ) * τ) k ≠ ⊥ := (F.piece_ne_bot_iff _).mpr hτ
  obtain ⟨s₀, hs₀, hs₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, _, hc0, hcle⟩ := D.exists_normalized k s₀ hs₀0
  let J := {s : F.normalizedSections D k τ // s.1 ≠ 0}
  have hJ : Nonempty J :=
    ⟨⟨⟨c • s₀, (F.piece ((k : ℝ) * τ) k).smul_mem c hs₀, hcle⟩, hc0⟩⟩
  have hsup : (fun x => ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x) =
      fun x => ⨆ j : J, D.logNormSq k j.1.1 x := by
    funext x
    apply le_antisymm
    · refine iSup_le fun s => ?_
      by_cases h0 : s.1 = 0
      · rw [h0, D.logNormSq_zero]
        exact bot_le
      · exact le_iSup_of_le (⟨s, h0⟩ : J) le_rfl
    · exact iSup_le fun j => le_iSup_of_le j.1 le_rfl
  change IsThetaPshPotential _ (uscRegularization fun x =>
    ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x)
  rw [hsup]
  refine SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    (fun j : J => D.isThetaPsh k hk j.1.1 j.2) (C := 0) ?_
  intro j x
  change ENNReal.log (ENNReal.ofReal (D.normSq k j.1.1 x)) ≤ ((0 : ℝ) : EReal)
  rw [EReal.coe_zero, ENNReal.log_le_zero_iff]
  exact ENNReal.ofReal_le_one.mpr (j.1.2.2 x)

open SectionMetric in
/-- In coordinates, the normalized sections form a compact set (the sup norm is a norm). -/
theorem isCompact_coord_normalizedSections [Nonempty X] (k : ℕ) (τ : ℝ) :
    IsCompact (coordEquiv k ⁻¹' F.normalizedSections D k τ) := by
  have hQ := D.continuous_pointSeminorm_coord_swap k
  have hcp : ∀ c : Fin (Module.finrank ℂ (S k)) → ℂ,
      Continuous fun p => D.pointSeminorm k p (coordEquiv k c) :=
    fun c => D.continuous_pointSeminorm k _
  have hcc : ∀ p : X, Continuous fun c : Fin (Module.finrank ℂ (S k)) → ℂ =>
      D.pointSeminorm k p (coordEquiv k c) :=
    fun p => (Classical.choose_spec (D.exists_lipschitzWith_pointSeminorm_coord k) p).continuous
  have hclosed : IsClosed (coordEquiv k ⁻¹' F.normalizedSections D k τ) := by
    have h1 : IsClosed ((((F.piece ((k : ℝ) * τ) k).comap
        (coordEquiv (S := S) k).toLinearMap : Submodule ℂ _) : Set
          (Fin (Module.finrank ℂ (S k)) → ℂ))) :=
      Submodule.closed_of_finiteDimensional _
    have h2 : IsClosed (⋂ p : X, {c : Fin (Module.finrank ℂ (S k)) → ℂ |
          D.normSq k (coordEquiv k c) p ≤ 1}) := by
      refine isClosed_iInter fun p => isClosed_le ?_ continuous_const
      simp only [← D.pointSeminorm_sq k p]
      exact (hcc p).pow 2
    have heq : coordEquiv k ⁻¹' F.normalizedSections D k τ =
        (((F.piece ((k : ℝ) * τ) k).comap (coordEquiv (S := S) k).toLinearMap :
          Submodule ℂ _) : Set (Fin (Module.finrank ℂ (S k)) → ℂ)) ∩
        ⋂ p : X, {c : Fin (Module.finrank ℂ (S k)) → ℂ |
            D.normSq k (coordEquiv k c) p ≤ 1} := by
      ext c
      simp only [normalizedSections, mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_iInter,
        SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [heq]
    exact h1.inter h2
  let P : (Fin (Module.finrank ℂ (S k)) → ℂ) → ℝ := fun c =>
    sSup ((fun p => D.pointSeminorm k p (coordEquiv k c)) '' univ)
  have hP : Continuous P :=
    isCompact_univ.continuous_sSup (f := fun c p => D.pointSeminorm k p (coordEquiv k c))
      (by exact (hQ.comp continuous_swap))
  have hleP : ∀ c p, D.pointSeminorm k p (coordEquiv k c) ≤ P c := fun c p =>
    le_csSup (isCompact_univ.image (hcp c)).bddAbove (mem_image_of_mem _ (mem_univ p))
  have hPle : ∀ c (r : ℝ), (∀ p, D.pointSeminorm k p (coordEquiv k c) ≤ r) → P c ≤ r :=
    fun c r h => csSup_le (univ_nonempty.image _) (by rintro _ ⟨p, _, rfl⟩; exact h p)
  have hPpos : ∀ c, c ≠ 0 → 0 < P c := by
    intro c hc
    have hΦ : coordEquiv k c ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hc
    obtain ⟨p, hp⟩ := D.exists_normSq_ne_zero k (coordEquiv k c) hΦ
    have : 0 < D.pointSeminorm k p (coordEquiv k c) :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne (D.normSq_nonneg k _ p) (Ne.symm hp))
    exact this.trans_le (hleP c p)
  have hunit : ∀ c : Fin (Module.finrank ℂ (S k)) → ℂ, c ≠ 0 →
      ((‖c‖⁻¹ : ℝ) : ℂ) • c ∈ Metric.sphere (0 : Fin (Module.finrank ℂ (S k)) → ℂ) 1 := by
    intro c hc
    have hnc : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnc), inv_mul_cancel₀ hnc.ne']
  have hR : ∃ R : ℝ, ∀ c ∈ coordEquiv k ⁻¹' F.normalizedSections D k τ, ‖c‖ ≤ R := by
    by_cases hS : (Metric.sphere (0 : Fin (Module.finrank ℂ (S k)) → ℂ) 1).Nonempty
    · obtain ⟨c₀, hc₀, hmin⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ (S k)) → ℂ)
        1).exists_isMinOn hS hP.continuousOn
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
        have hqu : ∀ p, D.pointSeminorm k p (coordEquiv k (((‖c‖⁻¹ : ℝ) : ℂ) • c)) ≤
            ‖c‖⁻¹ := by
          intro p
          rw [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hnc)]
          have h1 : D.pointSeminorm k p (coordEquiv k c) ≤ 1 :=
            (Real.sqrt_le_sqrt (hc.2 p)).trans_eq Real.sqrt_one
          calc ‖c‖⁻¹ * D.pointSeminorm k p (coordEquiv k c) ≤ ‖c‖⁻¹ * 1 :=
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

open SectionMetric in
/-- The raw supremum `x ↦ sup {log |s(x)|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}` is
continuous. -/
theorem continuous_rawSectionPotential (k : ℕ) (τ : ℝ) :
    Continuous fun x => ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact continuous_of_discreteTopology
  have hK := F.isCompact_coord_normalizedSections D k τ
  have hG := D.continuous_logNormSq_coord_swap k
  have heq : (fun x => ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x) =
      fun x => sSup ((fun c => D.logNormSq k (coordEquiv k c) x) ''
        (coordEquiv k ⁻¹' F.normalizedSections D k τ)) := by
    funext x
    apply le_antisymm
    · refine iSup_le fun s => le_sSup ⟨(coordEquiv k).symm s.1, ?_, ?_⟩
      · change coordEquiv k ((coordEquiv k).symm s.1) ∈ F.normalizedSections D k τ
        rw [LinearEquiv.apply_symm_apply]
        exact s.2
      · change D.logNormSq k (coordEquiv k ((coordEquiv k).symm s.1)) x = _
        rw [LinearEquiv.apply_symm_apply]
    · refine sSup_le ?_
      rintro _ ⟨c, hc, rfl⟩
      exact le_iSup (fun s : F.normalizedSections D k τ => D.logNormSq k s.1 x)
        ⟨coordEquiv k c, hc⟩
  rw [heq]
  exact hK.continuous_sSup (f := fun x c => D.logNormSq k (coordEquiv k c) x) hG

/-- Source `ex:RWN`: `Γ^{𝓕,k}_τ` is the raw supremum (no regularization is needed). -/
theorem sectionPotential_eq_raw (k : ℕ) (τ : ℝ) :
    F.sectionPotential D k τ = fun x => ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x :=
  uscRegularization_eq (F.continuous_rawSectionPotential D k τ).upperSemicontinuous

/-- Source `ex:RWN`: `Γ^{𝓕,k}_τ` is continuous (as a `[-∞, 0]`-valued function). -/
theorem continuous_sectionPotential (k : ℕ) (τ : ℝ) : Continuous (F.sectionPotential D k τ) := by
  rw [F.sectionPotential_eq_raw D k τ]
  exact F.continuous_rawSectionPotential D k τ

/-- Superadditivity across levels:
`Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_{τ'} ≤ Γ^{𝓕,k+k'}_{(kτ+k'τ')/(k+k')}` (products of sections). -/
theorem sectionPotential_add_le_mix (k k' : ℕ) (hkk : 0 < k + k') (τ τ' : ℝ) (x : X) :
    F.sectionPotential D k τ x + F.sectionPotential D k' τ' x ≤
      F.sectionPotential D (k + k') (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) x := by
  rw [F.sectionPotential_eq_raw D k τ, F.sectionPotential_eq_raw D k' τ',
    F.sectionPotential_eq_raw D (k + k')]
  refine EReal.add_le_of_forall_lt fun u hu v hv => ?_
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hu
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hv
  have hmem : mul k k' s.1 t.1 ∈
      F.normalizedSections D (k + k') (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) := by
    refine ⟨?_, fun p => ?_⟩
    · have h := F.mul_mem _ _ k k' s.1 t.1 s.2.1 t.2.1
      have he : ((k + k' : ℕ) : ℝ) * (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) =
          (k : ℝ) * τ + (k' : ℝ) * τ' := by
        have : (0 : ℝ) < ((k + k' : ℕ) : ℝ) := by exact_mod_cast hkk
        push_cast at this ⊢
        field_simp
      rw [he]
      exact h
    · rw [D.normSq_mul]
      exact mul_le_one₀ (s.2.2 p) (D.normSq_nonneg k' t.1 p) (t.2.2 p)
  calc u + v ≤ D.logNormSq k s.1 x + D.logNormSq k' t.1 x := add_le_add hs.le ht.le
    _ = D.logNormSq (k + k') (mul k k' s.1 t.1) x := (D.logNormSq_mul k k' s.1 t.1 x).symm
    _ ≤ _ := le_iSup (fun r : F.normalizedSections D (k + k')
          (((k : ℝ) * τ + (k' : ℝ) * τ') / ((k : ℝ) + k')) =>
            D.logNormSq (k + k') r.1 x) ⟨mul k k' s.1 t.1, hmem⟩

/-- **Source `ex:RWN`, superadditivity**: `Γ^{𝓕,k}_τ + Γ^{𝓕,k'}_τ ≤ Γ^{𝓕,k+k'}_τ` for all
`k, k'` and `τ`. -/
theorem sectionPotential_add_le (k k' : ℕ) (τ : ℝ) (x : X) :
    F.sectionPotential D k τ x + F.sectionPotential D k' τ x ≤
      F.sectionPotential D (k + k') τ x := by
  rw [F.sectionPotential_eq_raw D k τ, F.sectionPotential_eq_raw D k' τ,
    F.sectionPotential_eq_raw D (k + k') τ]
  refine EReal.add_le_of_forall_lt fun u hu v hv => ?_
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hu
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hv
  have hmem : mul k k' s.1 t.1 ∈ F.normalizedSections D (k + k') τ := by
    refine ⟨?_, fun p => ?_⟩
    · have h := F.mul_mem _ _ k k' s.1 t.1 s.2.1 t.2.1
      have he : ((k + k' : ℕ) : ℝ) * τ = (k : ℝ) * τ + (k' : ℝ) * τ := by
        push_cast
        ring
      rw [he]
      exact h
    · rw [D.normSq_mul]
      exact mul_le_one₀ (s.2.2 p) (D.normSq_nonneg k' t.1 p) (t.2.2 p)
  calc u + v ≤ D.logNormSq k s.1 x + D.logNormSq k' t.1 x := add_le_add hs.le ht.le
    _ = D.logNormSq (k + k') (mul k k' s.1 t.1) x := (D.logNormSq_mul k k' s.1 t.1 x).symm
    _ ≤ _ := le_iSup (fun r : F.normalizedSections D (k + k') τ => D.logNormSq (k + k') r.1 x)
          ⟨mul k k' s.1 t.1, hmem⟩

/-- **Source `ex:RWN`, `eq:limkGammaFk`**: at every point `x` and every `τ`,
`limsup_k k⁻¹ Γ^{𝓕,k}_τ(x) = sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ(x)`. -/
theorem limsup_sectionPotential_div_eq_iSup (τ : ℝ) (x : X) :
    limsup (fun k : ℕ => F.sectionPotential D k τ x / ((k : ℝ) : EReal)) atTop =
      ⨆ (k : ℕ) (_ : 0 < k), F.sectionPotential D k τ x / ((k : ℝ) : EReal) :=
  SGPT.LineBundle.EReal.limsup_div_eq_iSup_of_superadditive _
    (fun m k _ _ => F.sectionPotential_add_le D m k τ x)
    (fun k _ => ne_top_of_le_ne_top EReal.zero_ne_top (F.sectionPotential_le_zero D k τ x))

/-- **Source `ex:RWN`, `eq:limkGammaFk`, the limit clause**: if `Γ^{𝓕,k}_τ(x) > -∞` for all
`k ≥ k₀ > 0`, then `k⁻¹ Γ^{𝓕,k}_τ(x)` converges to `sup_{k > 0} k⁻¹ Γ^{𝓕,k}_τ(x)`. -/
theorem tendsto_sectionPotential_div_iSup (τ : ℝ) (x : X) (k₀ : ℕ) (hk₀ : 0 < k₀)
    (hfin : ∀ k : ℕ, k₀ ≤ k → F.sectionPotential D k τ x ≠ ⊥) :
    Tendsto (fun k : ℕ => F.sectionPotential D k τ x / ((k : ℝ) : EReal)) atTop
      (𝓝 (⨆ (k : ℕ) (_ : 0 < k), F.sectionPotential D k τ x / ((k : ℝ) : EReal))) :=
  SGPT.LineBundle.EReal.tendsto_div_iSup_of_superadditive_of_eventually_ne_bot _
    (fun m k _ _ => F.sectionPotential_add_le D m k τ x)
    (fun k _ => F.sectionPotential_le_zero D k τ x) k₀ hk₀ hfin

end GradedFiltration

end SGPT.TestCurve.KFilt
