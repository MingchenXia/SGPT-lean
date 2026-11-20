import SGPT.TestCurve.TestConfigFiltration
import SGPT.TestCurve.TestConfigL2Sections
import SGPT.LineBundle.IntersectionAmple

/-!
# The Phong–Sturm ray of a filtration (`rmk:PhongSturm`)

Source `rmk:PhongSturm` (chapter *Test curves*): *"Suppose that `L` is ample and `𝓕` is the
filtration induced by a smooth test configuration `(𝓧, 𝓛)` of `(X, L)`. Then the geodesic ray
`Γ^{𝓕*}` is exactly the Phong–Sturm geodesic ray associated with `(𝓧, 𝓛)`. See [RWN14, §9]."*

## The Phong–Sturm ray ([RWN14, §9])

Fix `φ ∈ 𝓗(L)` (a smooth metric `h = e^{-φ}` with `θ = dd^c φ > 0`), the `L²` products
`(·, ·)_{kφ}` of `μ = (dd^c φ)^n`, and for every `k` an orthonormal basis `(s_i)` of
`H⁰(X, L^k)` adapted to the filtration, `𝓕^λ H⁰(X, L^k) = span {s_i : λ_i ≥ λ}`
(`SGPT.TestCurve.TestConfig.AdaptedONBasis`). Ross–Witt Nyström define

`Φ_k(t) = k⁻¹ log ∑_i e^{t λ_i} |s_i|²_{h^k}`, and the Phong–Sturm ray
`Φ(t) = lim*_{k → ∞} sup_{l ≥ k} Φ_l(t) = usc limsup_k Φ_k(t)`;

for the filtration of a test configuration the `λ_i` are the weights of the `ℂ^*`-action and
`(s_i)` is the basis of Phong–Sturm [PS07, Lemma 7]. [RWN14, Theorem 9.2] states
`Φ(t) = (φ^𝓕)^_t`, the Legendre transform of the test curve of `𝓕`.

## Formal setting

The scheme-side setting of `ex:RWN` (`SGPT.LineBundle.SectionFiltration`, `TestConfFiltrationRay`):
`X` an integral smooth projective complex scheme, `L` with atlas `a`, smooth metric `H`
(`θ = c₁(L, h)`), `μ` a finite Borel measure on `X^{an}` charging nonempty open sets
(`(dd^c φ)^n` in [RWN14, §9]; the construction is stated for every such `μ`).

## Main definitions

* `filtL2 H a μ F k`: the pieces `𝓕^λ_k` as subspaces of the `L²` space of degree `k`.
* `PSBases H a μ F`: a choice of adapted orthonormal bases in every positive degree;
  `exists_psBases`: such choices exist.
* `psSum`, `psApprox`: `∑_i e^{t λ_i} |s_i|²_{h^k}` and `Φ_k(t)`.
* `phongSturmRay`: the Phong–Sturm ray `Φ(t)` of [RWN14, §9, (9.1)].
* `obstacleLegendre`, `filtrationLegendre`: the Legendre transforms
  `usc sup_{τ < τ(𝓕)} (ψ_τ + tτ)` of the obstacle `ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ` and
  `Γ^{𝓕*}_t = usc sup_{τ < τ(𝓕)} (Γ^𝓕_τ + tτ)` of the test curve `Γ^𝓕_τ = P_θ[ψ_τ]` of `ex:RWN`.
* `PhongSturmClaim`, `PhongSturmRemarkStatement`: the faithful statement of `rmk:PhongSturm`.

## Main results

* `sectionNormSq_le_bessel`: pointwise Bessel inequality
  `|s(p)|² ≤ ‖s‖²_{L²} ∑_{λ_i ≥ c} |s_i(p)|²` for `s ∈ 𝓕^c_k`.
* `rawObstacle_add_le_limsup_psApprox`, **`obstacleLegendre_le_phongSturmRay`**: the lower bound
  `usc sup_τ (ψ_τ + tτ) ≤ Φ(t)` of [RWN14, proof of Theorem 9.2] (for every filtration).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TestConfig

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology ComplexConjugate

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance tcPSTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcPSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance tcPSManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance tcPSMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcPSBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)
  (μ : Measure (SchemeComplexPoint f)) (F : SectionFiltration f a)

/-! ### The filtration in the `L²` spaces -/

/-- The piece `𝓕^λ_k` as a subspace of `H⁰(X, L^k)` with its `L²` structure. -/
def filtL2 (k : ℕ) (μ' : ℝ) : Submodule ℂ (L2Sections H a μ k) := F.piece μ' k

variable [IsIntegral X] [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

theorem isLeftContFiltration_filtL2 {k : ℕ} (hk : 0 < k) :
    IsLeftContFiltration (filtL2 H a μ F k) := by
  refine ⟨fun _ _ h => F.antitone_piece k h, fun μ' x hx => ?_, ?_⟩
  · change x ∈ F.piece μ' k
    rw [F.leftContinuous μ' k]
    exact Submodule.mem_iInf _ |>.mpr fun μ'' => Submodule.mem_iInf _ |>.mpr fun h => hx μ'' h
  · refine ⟨(F.bound : ℝ) * k, ?_⟩
    exact F.piece_bound_eq_bot hk

omit [IsIntegral X] [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] in
theorem filtL2_exhaustive {k : ℕ} (hk : 0 < k) : ∃ μ', filtL2 H a μ F k μ' = ⊤ :=
  ⟨-((F.bound : ℝ) * k), F.piece_neg_bound_eq_top hk⟩

instance finiteDimensional_l2Sections (k : ℕ) : FiniteDimensional ℂ (L2Sections H a μ k) :=
  SectionSpace.finiteDimensional f E a k

/-- A choice of orthonormal bases adapted to `𝓕` in every positive degree `j + 1`. -/
abbrev PSBases : Type 1 := ∀ j : ℕ, AdaptedONBasis (filtL2 H a μ F (j + 1))

theorem exists_psBases : Nonempty (PSBases H a μ F) :=
  ⟨fun j => (exists_adaptedONBasis _ (isLeftContFiltration_filtL2 H a μ F (Nat.succ_pos j))
    (filtL2_exhaustive H a μ F (Nat.succ_pos j))).some⟩

/-! ### Approximants and the Phong–Sturm ray -/

variable {H a μ F}

/-- `∑_i e^{t λ_i} |s_i|²_{h^k}` for an adapted orthonormal basis `(s_i, λ_i)` of degree `k`. -/
def psSum {k : ℕ} (B : AdaptedONBasis (filtL2 H a μ F k)) (t : ℝ) (p : SchemeComplexPoint f) :
    ℝ :=
  ∑ i, Real.exp (t * B.weight i) *
    H.sectionNormSq a k ((L2Sections.equiv k).symm (B.basis i)) p

theorem psSum_nonneg {k : ℕ} (B : AdaptedONBasis (filtL2 H a μ F k)) (t : ℝ)
    (p : SchemeComplexPoint f) : 0 ≤ psSum B t p :=
  Finset.sum_nonneg fun _i _ => mul_nonneg (Real.exp_pos _).le (H.sectionNormSq_nonneg a k _ p)

/-- The approximant `Φ_k(t) = k⁻¹ log ∑_i e^{t λ_i} |s_i|²_{h^k}` of [RWN14, §9]. -/
def psApprox {k : ℕ} (B : AdaptedONBasis (filtL2 H a μ F k)) (t : ℝ)
    (p : SchemeComplexPoint f) : EReal :=
  ENNReal.log (ENNReal.ofReal (psSum B t p)) / ((k : ℝ) : EReal)

/-- **The Phong–Sturm ray** ([RWN14, §9, (9.1)]):
`Φ(t) = lim*_{k → ∞} sup_{l ≥ k} Φ_l(t)`, the upper semicontinuous regularization of
`limsup_k Φ_k(t)`. -/
def phongSturmRay (Bs : PSBases H a μ F) (t : ℝ) : SchemeComplexPoint f → EReal :=
  uscRegularization fun p => limsup (fun j : ℕ => psApprox (Bs j) t p) atTop

/-- The Legendre transform `usc sup_{τ < τ(𝓕)} (ψ_τ + tτ)` of the obstacle
`ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ` of `ex:RWN` (this is the Legendre transform of the test curve
`φ^𝓕` of [RWN14, Lemma 7.4]). -/
def obstacleLegendre (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L) (t : ℝ) :
    SchemeComplexPoint f → EReal :=
  uscRegularization fun p => ⨆ τ : {τ : ℝ // (τ : EReal) < F.slope},
    F.obstacle H τ.1 p + ((t * τ.1 : ℝ) : EReal)

/-- The geodesic ray `Γ^{𝓕*}_t = usc sup_{τ < τ(𝓕)} (Γ^𝓕_τ + tτ)` of `ex:RWN`, the Legendre
transform of the family `Γ^𝓕_τ = P_θ[ψ_τ]` (`SectionFiltration.testCurvePotential`). -/
def filtrationLegendre (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (t : ℝ) : SchemeComplexPoint f → EReal :=
  uscRegularization fun p => ⨆ τ : {τ : ℝ // (τ : EReal) < F.slope},
    F.testCurvePotential H τ.1 p + ((t * τ.1 : ℝ) : EReal)

/-! ### The pointwise Bessel inequality -/

/-- If `s` lies in the span of the `s_i`, `i ∈ T`, of an orthonormal basis, its coefficients
outside `T` vanish. -/
theorem inner_eq_zero_of_mem_span {k : ℕ} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (L2Sections H a μ k)) (T : Set ι) {s : L2Sections H a μ k}
    (hs : s ∈ Submodule.span ℂ (b '' T)) {i : ι} (hi : i ∉ T) : inner ℂ (b i) s = 0 := by
  refine Submodule.span_induction (p := fun x _ => inner ℂ (b i) x = 0) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨j, hj, rfl⟩
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    exact b.orthonormal.2 hij
  · exact inner_zero_right _
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [inner_smul_right, hx, mul_zero]

/-- **Pointwise Bessel inequality**: for `s` in the span of `s_i`, `i ∈ T`,
`|s(p)|²_{h^k} ≤ ‖s‖²_{L²} ∑_{i ∈ T} |s_i(p)|²_{h^k}`. -/
theorem sectionNormSq_le_bessel {k : ℕ} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (L2Sections H a μ k)) (T : Finset ι) {s : L2Sections H a μ k}
    (hs : s ∈ Submodule.span ℂ (b '' (T : Set ι))) (p : SchemeComplexPoint f) :
    H.sectionNormSq a k ((L2Sections.equiv k).symm s) p ≤
      ‖s‖ ^ 2 * ∑ i ∈ T, H.sectionNormSq a k ((L2Sections.equiv k).symm (b i)) p := by
  classical
  set ev : L2Sections H a μ k →ₗ[ℂ] ℂ := (evalAt (n := n) (E := E) a k p).comp
    (L2Sections.equiv (H := H) (a := a) (μ := μ) k).symm.toLinearMap with hev
  set W := frameWeight H a k p
  have hW : 0 < W := frameWeight_pos H a k p
  have hnorm : ∀ x : L2Sections H a μ k,
      H.sectionNormSq a k ((L2Sections.equiv k).symm x) p = Complex.normSq (ev x) * W :=
    fun x => sectionNormSq_eq_evalAt H a k _ p
  -- expansion of `s` on the basis, restricted to `T`
  have hexp : s = ∑ i ∈ T, inner ℂ (b i) s • b i := by
    conv_lhs => rw [← b.sum_repr' s]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [inner_eq_zero_of_mem_span b (T : Set ι) hs (by simpa using hi), zero_smul]
  have hevs : ev s = ∑ i ∈ T, inner ℂ (b i) s * ev (b i) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  -- Cauchy–Schwarz
  have hcs : Complex.normSq (ev s) ≤
      (∑ i ∈ T, ‖inner ℂ (b i) s‖ ^ 2) * ∑ i ∈ T, Complex.normSq (ev (b i)) := by
    rw [Complex.normSq_eq_norm_sq, hevs]
    have h1 : ‖∑ i ∈ T, inner ℂ (b i) s * ev (b i)‖ ≤
        ∑ i ∈ T, ‖inner ℂ (b i) s‖ * ‖ev (b i)‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq T (fun i => ‖inner ℂ (b i) s‖)
      (fun i => ‖ev (b i)‖)
    calc ‖∑ i ∈ T, inner ℂ (b i) s * ev (b i)‖ ^ 2
        ≤ (∑ i ∈ T, ‖inner ℂ (b i) s‖ * ‖ev (b i)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ i ∈ T, ‖inner ℂ (b i) s‖ ^ 2) * ∑ i ∈ T, ‖ev (b i)‖ ^ 2 := h2
      _ = _ := by simp_rw [Complex.normSq_eq_norm_sq]
  -- Parseval
  have hpar : ∑ i ∈ T, ‖inner ℂ (b i) s‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right s]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      fun i _ _ => sq_nonneg _
  rw [hnorm s]
  have hsum : ∑ i ∈ T, H.sectionNormSq a k ((L2Sections.equiv k).symm (b i)) p =
      (∑ i ∈ T, Complex.normSq (ev (b i))) * W := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hnorm (b i)
  rw [hsum]
  have hS : 0 ≤ ∑ i ∈ T, Complex.normSq (ev (b i)) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  calc Complex.normSq (ev s) * W
      ≤ ((∑ i ∈ T, ‖inner ℂ (b i) s‖ ^ 2) * ∑ i ∈ T, Complex.normSq (ev (b i))) * W :=
        mul_le_mul_of_nonneg_right hcs hW.le
    _ ≤ (‖s‖ ^ 2 * ∑ i ∈ T, Complex.normSq (ev (b i))) * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpar hS) hW.le
    _ = ‖s‖ ^ 2 * ((∑ i ∈ T, Complex.normSq (ev (b i))) * W) := by ring

/-! ### The lower bound `ψ^*_t ≤ Φ(t)` -/

/-- A normalized section `s ∈ 𝓕^{kτ}_k`, `|s|² ≤ 1`, satisfies
`|s(p)|² ≤ μ(X) e^{-tkτ} ∑_i e^{t λ_i} |s_i(p)|²` for `t ≥ 0`. -/
theorem sectionNormSq_le_psSum {k : ℕ} (B : AdaptedONBasis (filtL2 H a μ F k)) {t : ℝ}
    (ht : 0 ≤ t) {τ : ℝ} {s : SectionSpace f L k} (hs : s ∈ F.normalizedSections H k τ)
    (p : SchemeComplexPoint f) :
    H.sectionNormSq a k s p ≤
      (μ univ).toReal * Real.exp (-(t * (k * τ))) * psSum B t p := by
  classical
  set T : Finset B.ι := Finset.univ.filter fun i => (k : ℝ) * τ ≤ B.weight i with hT
  have hmem : (L2Sections.equiv (H := H) (a := a) (μ := μ) k s) ∈
      Submodule.span ℂ (B.basis '' (T : Set B.ι)) := by
    have h := hs.1
    change (L2Sections.equiv (H := H) (a := a) (μ := μ) k s) ∈ filtL2 H a μ F k ((k : ℝ) * τ)
      at h
    rw [B.adapted] at h
    convert h using 3
    · rfl
    · rw [hT, Finset.coe_filter]
      simp
  have hb := sectionNormSq_le_bessel B.basis T hmem p
  have hn : ‖L2Sections.equiv (H := H) (a := a) (μ := μ) k s‖ ^ 2 ≤ 1 * (μ univ).toReal :=
    L2Sections.norm_sq_le k _ fun q => hs.2 q
  have hsum : ∑ i ∈ T, H.sectionNormSq a k ((L2Sections.equiv k).symm (B.basis i)) p ≤
      Real.exp (-(t * (k * τ))) * psSum B t p := by
    rw [psSum, Finset.mul_sum]
    refine (Finset.sum_le_sum fun i hi => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) fun i _ _ =>
        mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le
          (H.sectionNormSq_nonneg a k _ p)))
    have hw : (k : ℝ) * τ ≤ B.weight i := (Finset.mem_filter.mp hi).2
    have h1 : 1 ≤ Real.exp (-(t * (k * τ))) * Real.exp (t * B.weight i) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have h0 := H.sectionNormSq_nonneg a k ((L2Sections.equiv k).symm (B.basis i)) p
    nlinarith
  have hs' : (L2Sections.equiv k).symm (L2Sections.equiv (H := H) (a := a) (μ := μ) k s) = s :=
    rfl
  rw [hs'] at hb
  have hμ : 0 ≤ (μ univ).toReal := ENNReal.toReal_nonneg
  have hsum0 : 0 ≤ ∑ i ∈ T, H.sectionNormSq a k ((L2Sections.equiv k).symm (B.basis i)) p :=
    Finset.sum_nonneg fun i _ => H.sectionNormSq_nonneg a k _ p
  calc H.sectionNormSq a k s p
      ≤ ‖L2Sections.equiv (H := H) (a := a) (μ := μ) k s‖ ^ 2 *
          ∑ i ∈ T, H.sectionNormSq a k ((L2Sections.equiv k).symm (B.basis i)) p := hb
    _ ≤ (μ univ).toReal *
          ∑ i ∈ T, H.sectionNormSq a k ((L2Sections.equiv k).symm (B.basis i)) p :=
        mul_le_mul_of_nonneg_right (by linarith) hsum0
    _ ≤ (μ univ).toReal * (Real.exp (-(t * (k * τ))) * psSum B t p) :=
        mul_le_mul_of_nonneg_left hsum hμ
    _ = _ := by ring

omit [IsIntegral X] [CompactSpace (SchemeComplexPoint f)] in
theorem measure_univ_toReal_pos : 0 < (μ univ).toReal := by
  refine ENNReal.toReal_pos ?_ (measure_ne_top μ univ)
  exact (isOpen_univ.measure_pos μ univ_nonempty).ne'

/-- The section potential `Γ^{𝓕,k}_τ` is bounded by `log μ(X) - tkτ + log ∑_i e^{t λ_i} |s_i|²`. -/
theorem sectionPotential_le_log_psSum {k : ℕ} (B : AdaptedONBasis (filtL2 H a μ F k)) {t : ℝ}
    (ht : 0 ≤ t) (τ : ℝ) (p : SchemeComplexPoint f) :
    F.sectionPotential H k τ p ≤
      ((Real.log (μ univ).toReal - t * (k * τ) : ℝ) : EReal) +
        ENNReal.log (ENNReal.ofReal (psSum B t p)) := by
  rw [F.sectionPotential_eq_raw H k τ]
  refine iSup_le fun s => ?_
  have h := sectionNormSq_le_psSum B ht s.2 p
  have hμ := measure_univ_toReal_pos (μ := μ)
  change ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k s.1 p)) ≤ _
  calc ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k s.1 p))
      ≤ ENNReal.log (ENNReal.ofReal
          ((μ univ).toReal * Real.exp (-(t * (k * τ))) * psSum B t p)) :=
        ENNReal.log_le_log (ENNReal.ofReal_le_ofReal h)
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hμ.le (Real.exp_pos _).le),
        ENNReal.ofReal_mul hμ.le, ENNReal.log_mul_add, ENNReal.log_mul_add,
        ENNReal.log_ofReal_of_pos hμ, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
        ← EReal.coe_add]
      ring_nf

/-- For every degree, `k⁻¹ Γ^{𝓕,k}_τ + (tτ - k⁻¹ log μ(X)) ≤ Φ_k(t)`. -/
theorem normalizedPotential_add_le_psApprox {k : ℕ} (hk : 0 < k)
    (B : AdaptedONBasis (filtL2 H a μ F k)) {t : ℝ} (ht : 0 ≤ t) (τ : ℝ)
    (p : SchemeComplexPoint f) :
    F.normalizedPotential H k τ p + ((t * τ - Real.log (μ univ).toReal / k : ℝ) : EReal) ≤
      psApprox B t p := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h := sectionPotential_le_log_psSum (F := F) B ht τ p
  have hdiv := EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hkpos.le) h
  rw [EReal.add_div_of_nonneg_right (EReal.coe_nonneg.mpr hkpos.le), ← EReal.coe_div] at hdiv
  change F.sectionPotential H k τ p / ((k : ℝ) : EReal) +
      ((t * τ - Real.log (μ univ).toReal / k : ℝ) : EReal) ≤ psApprox B t p
  set c : ℝ := (Real.log (μ univ).toReal - t * (k * τ)) / k with hc
  have hc' : (t * τ - Real.log (μ univ).toReal / k : ℝ) = -c := by
    rw [hc]
    field_simp
    ring
  rw [hc']
  calc F.sectionPotential H k τ p / ((k : ℝ) : EReal) + ((-c : ℝ) : EReal)
      ≤ ((c : ℝ) : EReal) + ENNReal.log (ENNReal.ofReal (psSum B t p)) / ((k : ℝ) : EReal) +
          ((-c : ℝ) : EReal) := add_le_add_left hdiv _
    _ = ENNReal.log (ENNReal.ofReal (psSum B t p)) / ((k : ℝ) : EReal) := by
        rw [add_comm ((c : ℝ) : EReal), add_assoc, ← EReal.coe_add, add_neg_cancel,
          EReal.coe_zero, add_zero]
    _ = psApprox B t p := rfl

/-- **The raw lower bound** ([RWN14, proof of Theorem 9.2]):
`sup_k k⁻¹ Γ^{𝓕,k}_τ(p) + tτ ≤ limsup_k Φ_k(t)(p)` for `t ≥ 0`. -/
theorem rawObstacle_add_le_limsup_psApprox (Bs : PSBases H a μ F) {t : ℝ} (ht : 0 ≤ t)
    (τ : ℝ) (p : SchemeComplexPoint f) :
    F.rawObstacle H τ p + ((t * τ : ℝ) : EReal) ≤
      limsup (fun j : ℕ => psApprox (Bs j) t p) atTop := by
  -- `sup_k = limsup_k` (`eq:limkGammaFk`), shifted to degrees `j + 1`
  have hraw : F.rawObstacle H τ p =
      limsup (fun j : ℕ => F.normalizedPotential H (j + 1) τ p) atTop := by
    have h1 := F.limsup_sectionPotential_div_eq_iSup H τ p
    have h2 : limsup (fun j : ℕ => F.normalizedPotential H (j + 1) τ p) atTop =
        limsup (fun k : ℕ => F.sectionPotential H k τ p / ((k : ℝ) : EReal)) atTop :=
      Filter.limsup_nat_add (fun k : ℕ => F.sectionPotential H k τ p / ((k : ℝ) : EReal)) 1
    rw [h2, h1]
    rfl
  -- the errors `(j + 1)⁻¹ log μ(X)` tend to zero
  set v : ℕ → ℝ := fun j => t * τ - Real.log (μ univ).toReal / ((j + 1 : ℕ) : ℝ) with hv
  have h0 : Tendsto (fun j : ℕ => Real.log (μ univ).toReal / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (Real.log (μ univ).toReal)
    rw [mul_zero] at h
    refine h.congr fun j => ?_
    push_cast
    ring
  have hvlim : Tendsto v atTop (𝓝 (t * τ)) := by
    have := (tendsto_const_nhds (x := t * τ)).sub h0
    rw [sub_zero] at this
    exact this
  have hvlim' : Tendsto (fun j => ((v j : ℝ) : EReal)) atTop (𝓝 ((t * τ : ℝ) : EReal)) :=
    (EReal.continuous_coe_iff.mpr continuous_id).continuousAt.tendsto.comp hvlim
  have hliminf : liminf (fun j => ((v j : ℝ) : EReal)) atTop = ((t * τ : ℝ) : EReal) :=
    hvlim'.liminf_eq
  rw [hraw, ← hliminf]
  refine EReal.le_limsup_add.trans (Filter.limsup_le_limsup (Eventually.of_forall fun j => ?_))
  exact normalizedPotential_add_le_psApprox (Nat.succ_pos j) (Bs j) ht τ p

/-- **Lower bound of `rmk:PhongSturm`** ([RWN14, Theorem 9.2, second half]): for every filtration
`𝓕` (no ampleness needed), every choice of adapted bases and `t ≥ 0`,
`ψ^*_t = usc sup_{τ < τ(𝓕)} (ψ_τ + tτ) ≤ Φ(t)`, where `ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ` is the
obstacle of `ex:RWN`. -/
theorem obstacleLegendre_le_phongSturmRay (Bs : PSBases H a μ F) {t : ℝ} (ht : 0 ≤ t) :
    obstacleLegendre F H t ≤ phongSturmRay Bs t := by
  refine uscRegularization_le (upperSemicontinuous_uscRegularization _) fun p => ?_
  refine iSup_le fun τ => ?_
  have h1 : F.obstacle H τ.1 p + ((t * τ.1 : ℝ) : EReal) =
      uscRegularization (fun q => F.rawObstacle H τ.1 q + ((t * τ.1 : ℝ) : EReal)) p := by
    rw [uscRegularization_add_coe_const]
    rfl
  rw [h1]
  exact uscRegularization_mono (fun q => rawObstacle_add_le_limsup_psApprox Bs ht τ.1 q) p

/-! ### The upper bound `Φ(t) ≤ ψ^*_t` -/

variable (H a μ) in
/-- The **Bernstein–Markov property** of `μ` with respect to `h` ([RWN14, §7]): for every `ε > 0`
there is `C_ε` with `sup_X |s|²_{h^k} ≤ C_ε e^{εk} ‖s‖²_{L²}` for all `k` and
`s ∈ H⁰(X, L^k)`. -/
def IsBernsteinMarkov : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (s : SectionSpace f L k) (q : SchemeComplexPoint f),
    H.sectionNormSq a k s q ≤ C * Real.exp (ε * k) * ∫ x, H.sectionNormSq a k s x ∂μ

omit [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] in
/-- For `τ ≤ τ(𝓕)` (the endpoint included), `ψ_τ + tτ ≤ ψ^*_t`. -/
theorem obstacle_add_le_obstacleLegendre {t : ℝ} (ht : 0 ≤ t) {τ : ℝ} (hτ : (τ : EReal) ≤ F.slope)
    (p : SchemeComplexPoint f) :
    F.obstacle H τ p + ((t * τ : ℝ) : EReal) ≤ obstacleLegendre F H t p := by
  have hlt : ∀ τ' : ℝ, (τ' : EReal) < F.slope →
      F.obstacle H τ' p + ((t * τ' : ℝ) : EReal) ≤ obstacleLegendre F H t p := by
    intro τ' hτ'
    refine le_trans ?_ (le_uscRegularization _ p)
    exact le_iSup (fun τ'' : {τ : ℝ // (τ : EReal) < F.slope} =>
      F.obstacle H τ''.1 p + ((t * τ''.1 : ℝ) : EReal)) ⟨τ', hτ'⟩
  rcases hτ.lt_or_eq with hτ | hτ
  · exact hlt τ hτ
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  -- `ψ_τ ≤ z - tτ + tδ` for every `δ > 0`
  have hδ : ∀ δ : ℝ, 0 < δ → F.obstacle H τ p ≤ ((z - t * τ + t * δ : ℝ) : EReal) := by
    intro δ hδ
    have h1 : ((τ - δ : ℝ) : EReal) < F.slope := by
      rw [← hτ]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    have h2 := (hlt (τ - δ) h1).trans_lt hz
    have h3 : F.obstacle H τ p ≤ F.obstacle H (τ - δ) p := F.obstacle_anti H (by linarith) p
    have h4 : F.obstacle H (τ - δ) p < ((z - t * (τ - δ) : ℝ) : EReal) := by
      rcases eq_bot_or_bot_lt (F.obstacle H (τ - δ) p) with hb | hb
      · rw [hb]; exact EReal.bot_lt_coe _
      have hne : F.obstacle H (τ - δ) p ≠ ⊤ := fun ht' => by
        rw [ht', EReal.top_add_coe] at h2; exact not_top_lt h2
      lift F.obstacle H (τ - δ) p to ℝ using ⟨hne, hb.ne'⟩ with x
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h2
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    exact h3.trans (h4.le.trans (EReal.coe_le_coe_iff.mpr (by ring_nf; linarith)))
  have hle : F.obstacle H τ p ≤ ((z - t * τ : ℝ) : EReal) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hc1' : z - t * τ < c := EReal.coe_lt_coe_iff.mp hc1
    have := hδ ((c - (z - t * τ)) / (t + 1)) (div_pos (by linarith) (by linarith))
    have hlt' : z - t * τ + t * ((c - (z - t * τ)) / (t + 1)) < c := by
      have hfrac : t * ((c - (z - t * τ)) / (t + 1)) < c - (z - t * τ) := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    exact absurd (this.trans_lt (EReal.coe_lt_coe_iff.mpr hlt')) (not_lt.mpr hc2.le)
  calc F.obstacle H τ p + ((t * τ : ℝ) : EReal) ≤ ((z - t * τ : ℝ) : EReal) + ((t * τ : ℝ) : EReal) :=
        add_le_add hle le_rfl
    _ = (z : EReal) := by rw [← EReal.coe_add]; ring_nf

/-- One adapted basis vector: if `ψ^*_t(p) < r`, then `e^{t λ_i} |s_i(p)|² ≤ C e^{εk} e^{kr}`. -/
theorem exp_mul_sectionNormSq_le {k : ℕ} (hk : 0 < k) (B : AdaptedONBasis (filtL2 H a μ F k))
    {ε C : ℝ} (hC : 0 < C)
    (hBM : ∀ (s : SectionSpace f L k) (q : SchemeComplexPoint f),
      H.sectionNormSq a k s q ≤ C * Real.exp (ε * k) * ∫ x, H.sectionNormSq a k s x ∂μ)
    {t : ℝ} (ht : 0 ≤ t) {p : SchemeComplexPoint f} {r : ℝ}
    (hr : obstacleLegendre F H t p < r) (i : B.ι) :
    Real.exp (t * B.weight i) * H.sectionNormSq a k ((L2Sections.equiv k).symm (B.basis i)) p ≤
      C * Real.exp (ε * k) * Real.exp (k * r) := by
  set b : SectionSpace f L k := (L2Sections.equiv k).symm (B.basis i) with hbdef
  set y := H.sectionNormSq a k b p with hy
  have hD : 0 < C * Real.exp (ε * k) := mul_pos hC (Real.exp_pos _)
  rcases (H.sectionNormSq_nonneg a k b p).eq_or_lt with hy0 | hy0
  · rw [hy, ← hy0, mul_zero]; positivity
  set D := C * Real.exp (ε * k) with hDdef
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- `∫ |b|² = ‖s_i‖² = 1`
  have hint : ∫ x, H.sectionNormSq a k b x ∂μ = 1 := by
    have h1 := L2Sections.norm_sq_eq (H := H) (a := a) (μ := μ) k (B.basis i)
    rw [B.basis.orthonormal.1 i, one_pow] at h1
    exact h1.symm
  -- the normalized section
  set c : ℂ := (((Real.sqrt D)⁻¹ : ℝ) : ℂ) with hc
  have hnc : Complex.normSq c = D⁻¹ := by
    rw [hc, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hD.le]
  set s : SectionSpace f L k := c • b with hsdef
  have hsnorm : ∀ q, H.sectionNormSq a k s q = D⁻¹ * H.sectionNormSq a k b q := fun q => by
    rw [hsdef, H.sectionNormSq_smul a k c b q, hnc]
  have hbmem : b ∈ F.piece (B.weight i) k := by
    change B.basis i ∈ filtL2 H a μ F k (B.weight i)
    rw [B.adapted]
    exact Submodule.subset_span ⟨i, show B.weight i ≤ B.weight i from le_refl _, rfl⟩
  have hsmem : s ∈ F.normalizedSections H k (B.weight i / k) := by
    refine ⟨?_, fun q => ?_⟩
    · rw [mul_div_cancel₀ _ hkpos.ne']
      exact Submodule.smul_mem _ c hbmem
    · rw [hsnorm]
      have := hBM b q
      rw [hint, mul_one] at this
      calc D⁻¹ * H.sectionNormSq a k b q ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left this
            (inv_nonneg.mpr hD.le)
        _ = 1 := inv_mul_cancel₀ hD.ne'
  -- the slope bound `λ_i / k ≤ τ(𝓕)`
  have hslope : ((B.weight i / k : ℝ) : EReal) ≤ F.slope := by
    have hne : F.piece (B.weight i) k ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.mem_bot] at hbmem
      have h1 := B.basis.orthonormal.1 i
      have : B.basis i = 0 := hbmem
      rw [this, norm_zero] at h1
      exact zero_ne_one h1
    have h1 := F.le_jump hne
    have h2 : F.jump k / ((k : ℝ) : EReal) ≤ F.slope :=
      le_iSup₂ (f := fun (k : ℕ) (_ : 0 < k) => F.jump k / ((k : ℝ) : EReal)) k hk
    rw [EReal.coe_div]
    exact (EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hkpos.le) h1).trans h2
  -- `k⁻¹ log |s(p)|² ≤ ψ_{λ_i/k}(p)`
  have hlog : ((Real.log (D⁻¹ * y) / k : ℝ) : EReal) ≤ F.obstacle H (B.weight i / k) p := by
    have hsp : H.sectionLogNormSq a k s p ≤ F.sectionPotential H k (B.weight i / k) p := by
      rw [F.sectionPotential_eq_raw H k]
      exact le_iSup (fun s' : F.normalizedSections H k (B.weight i / k) =>
        H.sectionLogNormSq a k s'.1 p) ⟨s, hsmem⟩
    have hval : H.sectionLogNormSq a k s p = ((Real.log (D⁻¹ * y) : ℝ) : EReal) := by
      change ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k s p)) = _
      rw [hsnorm, ENNReal.log_ofReal_of_pos (mul_pos (inv_pos.mpr hD) hy0)]
    rw [hval] at hsp
    have h1 := EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hkpos.le) hsp
    rw [← EReal.coe_div] at h1
    refine h1.trans ?_
    refine le_trans ?_ (le_uscRegularization _ p)
    exact le_iSup₂ (f := fun (k' : ℕ) (_ : 0 < k') => F.normalizedPotential H k'
      (B.weight i / k) p) k hk
  have hmain := ((add_le_add hlog le_rfl).trans
    (obstacle_add_le_obstacleLegendre (F := F) (H := H) ht hslope p)).trans_lt hr
  rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at hmain
  -- back to real numbers
  have hlt : Real.log (D⁻¹ * y) + t * B.weight i < k * r := by
    have h2 : Real.log (D⁻¹ * y) / k + t * (B.weight i / k) =
        (Real.log (D⁻¹ * y) + t * B.weight i) / k := by ring
    rw [h2, div_lt_iff₀ hkpos] at hmain
    linarith
  have hexp := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_add, Real.exp_log (mul_pos (inv_pos.mpr hD) hy0)] at hexp
  have : D⁻¹ * (y * Real.exp (t * B.weight i)) < Real.exp (k * r) := by linarith
  rw [inv_mul_lt_iff₀ hD] at this
  linarith

/-- The approximant bound: if `ψ^*_t(p) < r`, then
`Φ_k(t)(p) ≤ k⁻¹ (log N_k + log C) + ε + r`, `N_k = dim H⁰(X, L^k)`. -/
theorem psApprox_le {k : ℕ} (hk : 0 < k) (B : AdaptedONBasis (filtL2 H a μ F k))
    {ε C : ℝ} (hC : 0 < C)
    (hBM : ∀ (s : SectionSpace f L k) (q : SchemeComplexPoint f),
      H.sectionNormSq a k s q ≤ C * Real.exp (ε * k) * ∫ x, H.sectionNormSq a k s x ∂μ)
    {t : ℝ} (ht : 0 ≤ t) {p : SchemeComplexPoint f} {r : ℝ}
    (hr : obstacleLegendre F H t p < r) :
    psApprox B t p ≤ (((Real.log (Fintype.card B.ι) + Real.log C) / k + ε + r : ℝ) : EReal) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsum : psSum B t p ≤ Fintype.card B.ι * (C * Real.exp (ε * k) * Real.exp (k * r)) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset B.ι) _ _
      fun i _ => exp_mul_sectionNormSq_le hk B hC hBM ht hr i
    rw [nsmul_eq_mul] at this
    exact this
  rcases (psSum_nonneg B t p).eq_or_lt with h0 | h0
  · rw [psApprox, ← h0, ENNReal.ofReal_zero, ENNReal.log_zero, EReal.bot_div_of_pos_ne_top
      (EReal.coe_pos.mpr hkpos) (EReal.coe_ne_top _)]
    exact bot_le
  have hcard : 0 < (Fintype.card B.ι : ℝ) := by
    by_contra hc
    push Not at hc
    have hc0 : (Fintype.card B.ι : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg _)
    rw [hc0, zero_mul] at hsum
    linarith
  rw [psApprox, ENNReal.log_ofReal_of_pos h0, ← EReal.coe_div, EReal.coe_le_coe_iff,
    div_le_iff₀ hkpos]
  have hlog := Real.log_le_log h0 hsum
  rw [Real.log_mul hcard.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hC.ne' (by positivity), Real.log_exp, Real.log_exp] at hlog
  have : ((Real.log (Fintype.card B.ι) + Real.log C) / k + ε + r) * k =
      Real.log (Fintype.card B.ι) + Real.log C + ε * k + k * r := by
    field_simp
  rw [this]
  linarith

/-- **Upper bound of [RWN14, Theorem 9.2]**: if `μ` has the Bernstein–Markov property and
`k⁻¹ log dim H⁰(X, L^k) → 0`, then `Φ(t) ≤ ψ^*_t` for `t ≥ 0`. -/
theorem phongSturmRay_le_obstacleLegendre (hBM : IsBernsteinMarkov H a μ)
    (hN : Tendsto (fun k : ℕ => Real.log (Module.finrank ℂ (SectionSpace f L k)) / k) atTop
      (𝓝 0))
    (Bs : PSBases H a μ F) {t : ℝ} (ht : 0 ≤ t) :
    phongSturmRay Bs t ≤ obstacleLegendre F H t := by
  refine uscRegularization_le (upperSemicontinuous_uscRegularization _) fun p => ?_
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hz
  have hrz : r < z := EReal.coe_lt_coe_iff.mp hr2
  set ε := (z - r) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨C, hC, hBMC⟩ := hBM ε hεpos
  -- the error terms tend to zero
  have hcardeq : ∀ j : ℕ, (Fintype.card (Bs j).ι : ℝ) =
      Module.finrank ℂ (SectionSpace f L (j + 1)) := fun j => by
    rw [← Module.finrank_eq_card_basis (Bs j).basis.toBasis]
    rfl
  have herr : Tendsto (fun j : ℕ => (Real.log (Fintype.card (Bs j).ι) + Real.log C) /
      ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => Real.log (Module.finrank ℂ (SectionSpace f L (j + 1))) /
        ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr hN
    have h2 : Tendsto (fun j : ℕ => Real.log C / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log C)
      rw [mul_zero] at h
      refine h.congr fun j => ?_
      push_cast
      ring
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr fun j => ?_
    rw [hcardeq, add_div]
  have hev : ∀ᶠ j : ℕ in atTop, (Real.log (Fintype.card (Bs j).ι) + Real.log C) /
      ((j + 1 : ℕ) : ℝ) < ε := herr.eventually (gt_mem_nhds hεpos)
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with j hj
  refine (psApprox_le (Nat.succ_pos j) (Bs j) hC (fun s q => hBMC (j + 1) s q) ht hr1).trans ?_
  refine EReal.coe_le_coe_iff.mpr ?_
  rw [hε] at hj ⊢
  linarith

/-- **[RWN14, Theorem 9.2] in the normalization of `ex:RWN`**: for every filtration `𝓕`, every
choice of adapted orthonormal bases and `t ≥ 0`, if `μ` has the Bernstein–Markov property and
`k⁻¹ log dim H⁰(X, L^k) → 0`, the Phong–Sturm ray is the Legendre transform of the obstacle:
`Φ(t) = usc sup_{τ < τ(𝓕)} (ψ_τ + tτ)`, `ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ`. -/
theorem phongSturmRay_eq_obstacleLegendre (hBM : IsBernsteinMarkov H a μ)
    (hN : Tendsto (fun k : ℕ => Real.log (Module.finrank ℂ (SectionSpace f L k)) / k) atTop
      (𝓝 0))
    (Bs : PSBases H a μ F) {t : ℝ} (ht : 0 ≤ t) :
    phongSturmRay Bs t = obstacleLegendre F H t :=
  le_antisymm (phongSturmRay_le_obstacleLegendre hBM hN Bs ht)
    (obstacleLegendre_le_phongSturmRay Bs ht)

/-! ### The statement of `rmk:PhongSturm` and its reduction -/

variable (F H μ) in
/-- The claim of `rmk:PhongSturm` for one filtration `𝓕` and one measure `μ`: for every choice
of adapted orthonormal bases, the geodesic ray `Γ^{𝓕*}` is the Phong–Sturm ray,
`Γ^{𝓕*}_t = Φ(t)` for all `t > 0`. -/
def PhongSturmClaim : Prop :=
  ∀ (Bs : PSBases H a μ F) (t : ℝ), 0 < t → filtrationLegendre F H t = phongSturmRay Bs t

variable (F H) in
/-- The part of the claim not covered by [RWN14, Theorem 9.2]: the Legendre transforms of
`ψ_τ` and of `Γ^𝓕_τ = P_θ[ψ_τ]` agree. For `L` ample it follows from
`P_θ[ψ_τ] = ψ_τ`, `τ < τ(𝓕)` ([RWN14, Proposition 7.11], Skoda division; see the footnote to
`ex:RWN`). -/
def LegendrePEnvelopeClause : Prop :=
  ∀ t : ℝ, 0 < t → filtrationLegendre F H t = obstacleLegendre F H t

variable (F H) in
/-- [RWN14, Proposition 7.11] in the notation of `ex:RWN`: `P_θ[ψ_τ] = ψ_τ` for `τ < τ(𝓕)`. -/
def RWNSkodaClause : Prop :=
  ∀ τ : ℝ, (τ : EReal) < F.slope → F.testCurvePotential H τ = F.obstacle H τ

omit [IsIntegral X] [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] in
theorem legendrePEnvelopeClause_of_skoda (h : RWNSkodaClause H F) : LegendrePEnvelopeClause H F := by
  intro t _
  unfold filtrationLegendre obstacleLegendre
  congr 1
  funext p
  congr 1
  funext τ
  rw [h τ.1 τ.2]

/-- **`rmk:PhongSturm` from its two analytic inputs**: under the Bernstein–Markov property and
`k⁻¹ log dim H⁰(X, L^k) → 0`, the claim of `rmk:PhongSturm` for `𝓕` is equivalent to
`LegendrePEnvelopeClause` (and follows from [RWN14, Proposition 7.11]). -/
theorem phongSturmClaim_iff (hBM : IsBernsteinMarkov H a μ)
    (hN : Tendsto (fun k : ℕ => Real.log (Module.finrank ℂ (SectionSpace f L k)) / k) atTop
      (𝓝 0)) :
    PhongSturmClaim H μ F ↔ LegendrePEnvelopeClause H F := by
  constructor
  · intro h t ht
    obtain ⟨Bs⟩ := exists_psBases H a μ F
    rw [h Bs t ht, phongSturmRay_eq_obstacleLegendre hBM hN Bs ht.le]
  · intro h Bs t ht
    rw [h t ht, phongSturmRay_eq_obstacleLegendre hBM hN Bs ht.le]

theorem phongSturmClaim_of_skoda (hBM : IsBernsteinMarkov H a μ)
    (hN : Tendsto (fun k : ℕ => Real.log (Module.finrank ℂ (SectionSpace f L k)) / k) atTop
      (𝓝 0)) (hS : RWNSkodaClause H F) : PhongSturmClaim H μ F :=
  (phongSturmClaim_iff hBM hN).mpr (legendrePEnvelopeClause_of_skoda hS)

/-! ### Ample line bundles and the statement of `rmk:PhongSturm` -/

omit [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] in
include n a in
/-- For an ample line bundle `k⁻¹ log dim H⁰(X, L^k) → 0` (asymptotic Riemann–Roch,
`AmplePolarization.tendsto_h0_selfIntersection`). -/
theorem tendsto_log_h0_div_of_ample (P : AmplePolarization f L) :
    Tendsto (fun k : ℕ => Real.log (Module.finrank ℂ (SectionSpace f L k)) / k) atTop (𝓝 0) := by
  have hRR := P.tendsto_h0_selfIntersection n a
  set c := max (P.selfIntersection n) 0 + 1 with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith [le_max_right (P.selfIntersection n) 0]
  have hev : ∀ᶠ k : ℕ in atTop, (Nat.factorial n : ℝ) * (h0 f L k : ℝ) / (k : ℝ) ^ n ≤ c :=
    hRR.eventually (ge_mem_nhds (by rw [hc]; linarith [le_max_left (P.selfIntersection n) 0]))
  -- the upper bound `(log c + n log k) / k`
  have hupper : Tendsto (fun k : ℕ => (Real.log c + n * Real.log k) / k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => Real.log c / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun k : ℕ => Real.log k / (k : ℝ)) atTop (𝓝 0) := by
      have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
      refine this.congr fun k => ?_
      simp
    have := h1.add (h2.const_mul (n : ℝ))
    rw [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Eventually.of_forall fun k => div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    refine div_le_div_of_nonneg_right ?_ hkpos.le
    have hfact : (1 : ℝ) ≤ (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hh0 : (h0 f L k : ℝ) ≤ c * (k : ℝ) ^ n := by
      rw [div_le_iff₀ (by positivity)] at hk
      nlinarith [Nat.cast_nonneg (α := ℝ) (h0 f L k), pow_pos hkpos n]
    change Real.log (h0 f L k : ℝ) ≤ _
    rcases Nat.eq_zero_or_pos (h0 f L k) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      exact add_nonneg (Real.log_nonneg hc1) (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_natCast_nonneg _))
    · have hpos : (0 : ℝ) < h0 f L k := by exact_mod_cast h
      calc Real.log (h0 f L k : ℝ) ≤ Real.log (c * (k : ℝ) ^ n) := Real.log_le_log hpos hh0
        _ = Real.log c + n * Real.log k := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]

variable (H a μ) in
/-- **Source `rmk:PhongSturm`** for `(X, L, h, μ)`: for every ample test configuration
`(𝓧, 𝓛)` of `(X, L)` — encoded, by [BHJ17, Prop. 2.15], by its finitely generated normalized
`ℤ`-filtration `G` of `R(X, L)`, inducing the filtration `𝓕 = G.fgFiltration` — the geodesic
ray `Γ^{𝓕*}` is the Phong–Sturm ray: `Γ^{𝓕*}_t = Φ(t)` for all `t > 0` and every choice of
adapted orthonormal bases. In [RWN14, §9], `h` has positive curvature and `μ = (dd^c φ)^n`. -/
def PhongSturmRemark : Prop :=
  ∀ (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤),
    PhongSturmClaim H μ (G.fgFiltration hG h0)

/-- **`rmk:PhongSturm` from [RWN14, Proposition 7.11]**: for `L` ample and `μ` with the
Bernstein–Markov property, `rmk:PhongSturm` holds as soon as `P_θ[ψ_τ] = ψ_τ` for `τ < τ(𝓕)`
(the Skoda-division step of [RWN14, Prop. 7.11]; footnote to `ex:RWN`). -/
theorem phongSturmRemark_of_skoda (P : AmplePolarization f L) (hBM : IsBernsteinMarkov H a μ)
    (hS : ∀ (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤),
      RWNSkodaClause H (G.fgFiltration hG h0)) :
    PhongSturmRemark H a μ := fun G hG h0 =>
  phongSturmClaim_of_skoda hBM (tendsto_log_h0_div_of_ample (n := n) (a := a) P) (hS G hG h0)

/-- **[RWN14, Theorem 9.2] for test configurations**: for `L` ample and `μ` Bernstein–Markov,
the Phong–Sturm ray of an ample test configuration is the Legendre transform of the obstacle
`ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ`. -/
theorem phongSturmRay_eq_obstacleLegendre_of_ample (P : AmplePolarization f L)
    (hBM : IsBernsteinMarkov H a μ) (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤) (Bs : PSBases H a μ (G.fgFiltration hG h0)) {t : ℝ} (ht : 0 ≤ t) :
    phongSturmRay Bs t = obstacleLegendre (G.fgFiltration hG h0) H t :=
  phongSturmRay_eq_obstacleLegendre hBM (tendsto_log_h0_div_of_ample (n := n) (a := a) P) Bs ht

end SGPT.TestCurve.TestConfig
