import SGPT.TestCurve.TestConfigAdaptedBasis
import SGPT.TestCurve.TestConfFiltrationRay

/-!
# The `L²` scalar product on `H⁰(X, L^k)`

Infrastructure for `rmk:PhongSturm` (chapter *Test curves*), following Ross–Witt Nyström
[RWN14, §7, §9]: a smooth Hermitian metric `h = e^{-φ}` on `L` and a finite measure `μ` on `X`
give the `L²` scalar product

`(s, t)_{kφ} = ∫_X ⟨s, t⟩_{h^k} dμ`

on `H⁰(X, L^k)`. In [RWN14, §9] `μ = (dd^c φ)^n`; here `μ` is any finite Borel measure charging
every nonempty open set (this contains the Monge–Ampère volume form of a Kähler form and every
smooth volume form).

## Formal setting

As in `SGPT.LineBundle.SectionFiltration`: `X` is an integral smooth projective complex scheme
with analytic space `X^{an} = SchemeComplexPoint f`, `L` a line bundle with atlas `a` and smooth
metric `H`. The pointwise Hermitian product `⟨s(p), t(p)⟩_{h^k}` is
`conj (s_α(p)) t_α(p) |e_α|²_{h^k}(p)` in the frame `e_α` chosen at `p`
(`SGPT.LineBundle.Misc2RWN.pointCoeff`); it is continuous in `p` by polarization.

## Main definitions

* `evalAt a k p : H⁰(X, L^k) →ₗ[ℂ] ℂ`: the coefficient at `p` in the frame chosen at `p`.
* `pointInner H a k p s t = ⟨s(p), t(p)⟩_{h^k}`.
* `l2Core H a μ k`: the `L²` scalar product as an `InnerProductSpace.Core`.
* `L2Sections H a μ k`: `H⁰(X, L^k)` with this inner product space structure.

## Main results

* `pointInner_self`: `⟨s(p), s(p)⟩_{h^k} = |s(p)|²_{h^k}`.
* `continuous_pointInner`: `p ↦ ⟨s(p), t(p)⟩_{h^k}` is continuous.
* `l2Core.definite`: the `L²` product is positive definite (a nonzero section does not vanish
  on the nonempty open set where it is nonzero, which has positive measure).
* `l2_inner_self_eq`, `l2_norm_sq_le`: `‖s‖² = ∫ |s|²_{h^k} dμ ≤ μ(X) sup_X |s|²_{h^k}`.
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

local instance tcL2Topology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcL2Charts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance tcL2Manifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance tcL2Measurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcL2Borel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-! ### Pointwise Hermitian product -/

/-- The frame coefficient of `c • s` is `c` times that of `s`. -/
theorem pointCoeff_smul (k : ℕ) (p : SchemeComplexPoint f) (c : ℂ) (s : SectionSpace f L k) :
    Misc2RWN.pointCoeff (n := n) (E := E) a k p (c • s) =
      c * Misc2RWN.pointCoeff (n := n) (E := E) a k p s := by
  let := E.isSeparated
  let := E.quasiCompact
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  have hco : (α.tensorPower k).coefficients (𝟙 U)
      ((bundleTensorPower L k).val.map (homOfLE le_top).op (c • s : SectionSpace f L k)) =
      X.sheaf.obj.map (homOfLE (le_top : U ≤ ⊤)).op (schemeGlobalConstants f c) *
        (α.tensorPower k).coefficients (𝟙 U)
          ((bundleTensorPower L k).val.map (homOfLE le_top).op s) := by
    have h := (bundleTensorPower L k).val.map_smul (homOfLE (le_top : U ≤ ⊤)).op
      (schemeGlobalConstants f c) s
    exact (congrArg ((α.tensorPower k).coefficients (𝟙 _)) h).trans
      (((α.tensorPower k).coefficients (𝟙 _)).map_smul _ _)
  unfold Misc2RWN.pointCoeff
  change schemeOpenRegularFunction f n E U ((α.tensorPower k).coefficients (𝟙 U)
      ((bundleTensorPower L k).val.map (homOfLE le_top).op (c • s : SectionSpace f L k))) p = _
  rw [hco, schemeOpenRegularFunction_mul f n E U _ _ hp]
  beta_reduce
  congr 1
  rw [schemeOpenRegularFunction_apply f n E U _ p hp]
  have hg := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤))
    (schemeComplexPointImage f p) hp (schemeGlobalConstants f c)
  erw [hg]
  exact schemeNativeStalkGerm_eval_const f n p c

/-- The coefficient of a section at `p` in the frame chosen at `p`, as a linear form. -/
def evalAt (k : ℕ) (p : SchemeComplexPoint f) : SectionSpace f L k →ₗ[ℂ] ℂ where
  toFun s := Misc2RWN.pointCoeff (n := n) (E := E) a k p s
  map_add' s t := Misc2RWN.pointCoeff_add a k p s t
  map_smul' c s := pointCoeff_smul a k p c s

/-- The weight `|e_α|²_{h^k}(p)` of the frame chosen at `p`. -/
def frameWeight (k : ℕ) (p : SchemeComplexPoint f) : ℝ :=
  H.frameNormSq (schemePointFrame f p a) p ^ k

theorem frameWeight_pos (k : ℕ) (p : SchemeComplexPoint f) : 0 < frameWeight H a k p :=
  pow_pos (H.positive _ p (schemePointFrame_mem f p a)) k

theorem sectionNormSq_eq_evalAt (k : ℕ) (s : SectionSpace f L k) (p : SchemeComplexPoint f) :
    H.sectionNormSq a k s p =
      Complex.normSq (evalAt (n := n) (E := E) a k p s) * frameWeight H a k p :=
  Misc2RWN.sectionNormSq_eq_pointCoeff H a k s p

/-- The pointwise Hermitian product `⟨s(p), t(p)⟩_{h^k}` (conjugate-linear in `s`). -/
def pointInner (k : ℕ) (p : SchemeComplexPoint f) (s t : SectionSpace f L k) : ℂ :=
  conj (evalAt (n := n) (E := E) a k p s) * evalAt (n := n) (E := E) a k p t *
    (frameWeight H a k p : ℂ)

theorem pointInner_self (k : ℕ) (p : SchemeComplexPoint f) (s : SectionSpace f L k) :
    pointInner H a k p s s = (H.sectionNormSq a k s p : ℂ) := by
  rw [sectionNormSq_eq_evalAt, pointInner, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]

/-- Polarization: the pointwise Hermitian product is a combination of pointwise squared norms. -/
theorem pointInner_polarization (k : ℕ) (p : SchemeComplexPoint f) (s t : SectionSpace f L k) :
    4 * pointInner H a k p s t =
      ((H.sectionNormSq a k (s + t) p : ℂ) - (H.sectionNormSq a k (s - t) p : ℂ)) +
        Complex.I * ((H.sectionNormSq a k (s - Complex.I • t) p : ℂ) -
          (H.sectionNormSq a k (s + Complex.I • t) p : ℂ)) := by
  simp only [← pointInner_self, pointInner, map_add, map_sub, map_smul, smul_eq_mul, map_mul,
    Complex.conj_I]
  set x := evalAt (n := n) (E := E) a k p s
  set y := evalAt (n := n) (E := E) a k p t
  set W : ℂ := (frameWeight H a k p : ℂ)
  linear_combination (2 * conj x * y * W - 2 * conj y * x * W) * Complex.I_sq

theorem conj_pointInner (k : ℕ) (p : SchemeComplexPoint f) (s t : SectionSpace f L k) :
    conj (pointInner H a k p t s) = pointInner H a k p s t := by
  simp only [pointInner, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem pointInner_add_left (k : ℕ) (p : SchemeComplexPoint f) (s s' t : SectionSpace f L k) :
    pointInner H a k p (s + s') t = pointInner H a k p s t + pointInner H a k p s' t := by
  simp only [pointInner, map_add]
  ring

theorem pointInner_smul_left (k : ℕ) (p : SchemeComplexPoint f) (c : ℂ)
    (s t : SectionSpace f L k) :
    pointInner H a k p (c • s) t = conj c * pointInner H a k p s t := by
  simp only [pointInner, map_smul, smul_eq_mul, map_mul]
  ring

theorem continuous_sectionNormSq (k : ℕ) (s : SectionSpace f L k) :
    Continuous fun p => H.sectionNormSq a k s p := by
  let := E.isSeparated
  let := E.quasiCompact
  exact ProductTestForms.ChartSmooth.continuous (H.sectionNormSq_chartSmooth a k s)

theorem continuous_pointInner (k : ℕ) (s t : SectionSpace f L k) :
    Continuous fun p => pointInner H a k p s t := by
  have h4 : (fun p => pointInner H a k p s t) = fun p => (1 / 4 : ℂ) *
      (((H.sectionNormSq a k (s + t) p : ℂ) - (H.sectionNormSq a k (s - t) p : ℂ)) +
        Complex.I * ((H.sectionNormSq a k (s - Complex.I • t) p : ℂ) -
          (H.sectionNormSq a k (s + Complex.I • t) p : ℂ))) := by
    funext p
    rw [← pointInner_polarization]
    ring
  rw [h4]
  have hc : ∀ u : SectionSpace f L k, Continuous fun p => (H.sectionNormSq a k u p : ℂ) :=
    fun u => Complex.continuous_ofReal.comp (continuous_sectionNormSq H a k u)
  exact continuous_const.mul (((hc _).sub (hc _)).add (continuous_const.mul ((hc _).sub (hc _))))

/-! ### The `L²` product -/

variable (μ : Measure (SchemeComplexPoint f))

theorem integrable_pointInner [CompactSpace (SchemeComplexPoint f)] [IsFiniteMeasure μ] (k : ℕ)
    (s t : SectionSpace f L k) : Integrable (fun p => pointInner H a k p s t) μ := by
  have hc := continuous_pointInner H a k s t
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable μ

theorem integrable_sectionNormSq [CompactSpace (SchemeComplexPoint f)] [IsFiniteMeasure μ]
    (k : ℕ) (s : SectionSpace f L k) : Integrable (fun p => H.sectionNormSq a k s p) μ := by
  have hc := continuous_sectionNormSq H a k s
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable μ

/-- The `L²` scalar product `(s, t)_{kφ} = ∫_X ⟨s, t⟩_{h^k} dμ` ([RWN14, §7]). -/
def l2Inner (k : ℕ) (s t : SectionSpace f L k) : ℂ := ∫ p, pointInner H a k p s t ∂μ

theorem l2Inner_self (k : ℕ) (s : SectionSpace f L k) :
    l2Inner H a μ k s s = ((∫ p, H.sectionNormSq a k s p ∂μ : ℝ) : ℂ) := by
  unfold l2Inner
  simp_rw [pointInner_self]
  exact integral_ofReal

/-- `H⁰(X, L^k)`, to be equipped with the `L²` inner product space structure of `(h, μ)`. -/
@[nolint unusedArguments]
def L2Sections (_H : SchemeLineBundleMetric f n E L) (_a : LineBundleAtlas L)
    (_μ : Measure (SchemeComplexPoint f)) (k : ℕ) : Type :=
  SectionSpace f L k

variable [IsIntegral X] [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
  [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- The `L²` scalar product is positive definite. -/
theorem l2Inner_definite (k : ℕ) (s : SectionSpace f L k) (h : l2Inner H a μ k s s = 0) :
    s = 0 := by
  rw [l2Inner_self, Complex.ofReal_eq_zero] at h
  have hnn : 0 ≤ᵐ[μ] fun p => H.sectionNormSq a k s p :=
    Filter.Eventually.of_forall fun p => H.sectionNormSq_nonneg a k s p
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_sectionNormSq H a μ k s)).mp h
  have hzero : ∀ p, H.sectionNormSq a k s p = 0 := by
    intro p
    have := (continuous_sectionNormSq H a k s).ae_eq_iff_eq μ continuous_const |>.mp hae
    exact congrFun this p
  by_contra hs
  obtain ⟨q, -, hq⟩ := H.exists_sectionNormSq_ne_zero_of_isOpen a k s hs univ isOpen_univ
    univ_nonempty
  exact hq (hzero q)

/-- The `L²` scalar product as an inner product space core. -/
@[instance_reducible]
def l2Core (k : ℕ) : InnerProductSpace.Core ℂ (SectionSpace f L k) where
  inner s t := l2Inner H a μ k s t
  conj_inner_symm s t := by
    unfold l2Inner
    rw [← integral_conj]
    simp_rw [conj_pointInner]
  re_inner_nonneg s := by
    rw [l2Inner_self, RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun p => H.sectionNormSq_nonneg a k s p
  add_left s s' t := by
    change l2Inner H a μ k (s + s') t = l2Inner H a μ k s t + l2Inner H a μ k s' t
    unfold l2Inner
    simp_rw [pointInner_add_left]
    exact integral_add (integrable_pointInner H a μ k s t) (integrable_pointInner H a μ k s' t)
  smul_left s t c := by
    change l2Inner H a μ k (c • s) t = conj c * l2Inner H a μ k s t
    unfold l2Inner
    simp_rw [pointInner_smul_left]
    exact integral_const_mul _ _
  definite s h := l2Inner_definite H a μ k s h

namespace L2Sections

variable {H a μ} (k : ℕ)

instance : AddCommGroup (L2Sections H a μ k) := inferInstanceAs (AddCommGroup (SectionSpace f L k))

instance : Module ℂ (L2Sections H a μ k) := inferInstanceAs (Module ℂ (SectionSpace f L k))

/-- The identification with `H⁰(X, L^k)`. -/
def equiv : SectionSpace f L k ≃ₗ[ℂ] L2Sections H a μ k := LinearEquiv.refl ℂ _

instance instCore : InnerProductSpace.Core ℂ (L2Sections H a μ k) := l2Core H a μ k

instance instNormedAddCommGroup : NormedAddCommGroup (L2Sections H a μ k) :=
  (instCore (H := H) (a := a) (μ := μ) k).toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace ℂ (L2Sections H a μ k) :=
  InnerProductSpace.ofCore (instCore (H := H) (a := a) (μ := μ) k).toCore

theorem inner_def (s t : L2Sections H a μ k) :
    inner ℂ s t = l2Inner H a μ k (equiv k |>.symm s) (equiv k |>.symm t) := rfl

/-- `‖s‖² = ∫_X |s|²_{h^k} dμ`. -/
theorem norm_sq_eq (s : L2Sections H a μ k) :
    ‖s‖ ^ 2 = ∫ p, H.sectionNormSq a k ((equiv k).symm s) p ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, inner_def, l2Inner_self, RCLike.re_to_complex, Complex.ofReal_re]

/-- `‖s‖² ≤ μ(X) · sup_X |s|²_{h^k}`. -/
theorem norm_sq_le (s : L2Sections H a μ k) {M : ℝ}
    (hM : ∀ p, H.sectionNormSq a k ((equiv k).symm s) p ≤ M) :
    ‖s‖ ^ 2 ≤ M * (μ univ).toReal := by
  rw [norm_sq_eq]
  calc ∫ p, H.sectionNormSq a k ((equiv k).symm s) p ∂μ ≤ ∫ _p, M ∂μ :=
        integral_mono (integrable_sectionNormSq H a μ k _) (integrable_const M) hM
    _ = M * (μ univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_comm, Measure.real]

end L2Sections

end SGPT.TestCurve.TestConfig
