import SGPT.TestCurve.SkodaIncMain

/-!
# Unitary gauges for the sections of `L^m` and of its analytification

Blueprint `claude-global-skoda.tex`, node `global-skoda:gauge`.

Let `(L, h)` be a metrized algebraic line bundle on `X` and `(L, h)^an` its analytification
(`SGPT.NAPotential.GAGAMult.schemeHermitianLineBundle`). At every point `x` the fibres of
`L^m` and of `((L, h)^an)^{⊗ m}` are identified with `ℂ` through the `h`-unit vector of the
preferred atlas frame at `x`. In these unitary gauges

* an analytic vector `u` of `((L, h)^an)^{⊗ m}_x` becomes `fibreGauge m x u ∈ ℂ`, with
  `‖u‖ = |fibreGauge m x u|` and coefficient `frameCoef(α, x)^m · fibreGauge m x u` in every
  algebraic frame `α` (`twCoef_eq_fibreGauge`);
* an algebraic section `σ ∈ H⁰(X, L^m)` becomes `sectionGauge m x σ ∈ ℂ`, with
  `|σ|²_{h^m}(x) = |sectionGauge m x σ|²`, coefficient `frameCoef(α, x)^m · sectionGauge m x σ`
  in every algebraic frame (`sectionFrameCoefficient_eq_sectionGauge`), and
  `sectionGauge (m + l) x (σ τ) = sectionGauge m x σ · sectionGauge l x τ`;
* `s = σ^an` gives `fibreGauge m x (s x) = sectionGauge m x σ`.

So all pointwise identities between sections in different degrees become identities between
complex numbers; this is how the global division theorem compares the algebraic section
`σ - ∑ wⱼ tⱼ` with the analytic error of the `∂̄`-correction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open SGPT.TestCurve.TestConfig MeasureTheory Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.GAGAMult SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance globalSkodaGaugeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalSkodaGaugeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-! ### Algebraic sections -/

/-- The value at `p` of the coefficient of `σ` in the frame `α^{⊗ m}`. -/
theorem sectionFrameCoefficient_def {U : X.Opens} (α : LocalBundleFrame L U) (m : ℕ)
    (σ : SectionSpace f L m) :
    sectionFrameCoefficient f n E α m σ = schemeOpenRegularFunction f n E U (algCoef α m σ) :=
  rfl

theorem schemeOpenRegularFunction_pow (U : X.Opens) (r : Γ(X, U)) (k : ℕ)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U (r ^ k) p = schemeOpenRegularFunction f n E U r p ^ k := by
  simp only [schemeOpenRegularFunction, dif_pos hp, map_pow]

/-- **Change of algebraic frame for the coefficients of a section**:
`c_β(σ) = g_{αβ}^m c_α(σ)`. -/
theorem sectionFrameCoefficient_transition {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) (m : ℕ) (σ : SectionSpace f L m) {p : SchemeComplexPoint f}
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    sectionFrameCoefficient f n E β m σ p =
      schemeFrameTransition f n E α β p ^ m * sectionFrameCoefficient f n E α m σ p := by
  have hp : schemeComplexPointImage f p ∈ U ⊓ V := ⟨hpU, hpV⟩
  set g : Γ(X, U ⊓ V) :=
    (localBundleFrameTransition α β (homOfLE inf_le_left) (homOfLE inf_le_right)).val with hg
  have h : (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (algCoef β m σ) :
      Γ(X, U ⊓ V)) =
      g ^ m * X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (algCoef α m σ) :=
    LocalBundleFrame.global_coefficients_transition α β
      (homOfLE inf_le_left : U ⊓ V ⟶ U) (homOfLE inf_le_right : U ⊓ V ⟶ V) m σ
  have h' : schemeOpenRegularFunction f n E (U ⊓ V)
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (algCoef β m σ)) p =
      schemeFrameTransition f n E α β p ^ m * schemeOpenRegularFunction f n E (U ⊓ V)
        (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (algCoef α m σ)) p := by
    rw [h, schemeOpenRegularFunction_mul f n E _ _ _ hp]
    beta_reduce
    rw [schemeOpenRegularFunction_pow _ _ _ hp]
    rfl
  have hV := schemeOpenRegularFunction_restrict f n E (U ⊓ V) V inf_le_right (algCoef β m σ) hp
  have hU := schemeOpenRegularFunction_restrict f n E (U ⊓ V) U inf_le_left (algCoef α m σ) hp
  change schemeOpenRegularFunction f n E V (algCoef β m σ) p =
    schemeFrameTransition f n E α β p ^ m * schemeOpenRegularFunction f n E U (algCoef α m σ) p
  rw [← hV, ← hU]
  exact h'

section Gauge

variable [IsSeparated f] [QuasiCompact f]

local instance globalSkodaGaugeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The frame chosen at `p` and its index. -/
abbrev ptFrame (p : SchemeComplexPoint f) : LocalBundleFrame L (schemePointFrameOpen f p a) :=
  schemePointFrame f p a

/-- **The unitary gauge of an algebraic section**: `σ(p) = sectionGauge m p σ · u_p^{⊗ m}`,
`u_p` the `h`-unit vector of the preferred frame at `p`. -/
def sectionGauge (m : ℕ) (p : SchemeComplexPoint f) : SectionSpace f L m →ₗ[ℂ] ℂ :=
  ((frameCoef f n E a H (ptFrame a p) p ^ m)⁻¹) • evalAt (n := n) (E := E) a m p

omit [IsSeparated f] [QuasiCompact f] in
theorem evalAt_eq_sectionFrameCoefficient (m : ℕ) (p : SchemeComplexPoint f)
    (σ : SectionSpace f L m) :
    evalAt (n := n) (E := E) a m p σ = sectionFrameCoefficient f n E (ptFrame a p) m σ p :=
  rfl

omit [IsSeparated f] [QuasiCompact f] in
/-- In every algebraic frame `α`, the coefficient of `σ` is `frameCoef(α, p)^m` times its
gauge. -/
theorem sectionFrameCoefficient_eq_sectionGauge {U : X.Opens} (α : LocalBundleFrame L U)
    (m : ℕ) (σ : SectionSpace f L m) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    sectionFrameCoefficient f n E α m σ p =
      frameCoef f n E a H α p ^ m * sectionGauge H a m p σ := by
  have h0 : schemeComplexPointImage f p ∈ schemePointFrameOpen f p a := schemePointFrame_mem f p a
  have hne : frameCoef f n E a H (ptFrame a p) p ≠ 0 :=
    frameCoef_ne_zero f n E a H _ h0
  rw [sectionFrameCoefficient_transition (ptFrame a p) α m σ h0 hp,
    frameCoef_transition f n E a H (ptFrame a p) α h0 hp, sectionGauge, LinearMap.smul_apply,
    smul_eq_mul, evalAt_eq_sectionFrameCoefficient, mul_pow, mul_assoc,
    ← mul_assoc (frameCoef f n E a H (ptFrame a p) p ^ m), mul_inv_cancel₀ (pow_ne_zero _ hne),
    one_mul]

omit [IsSeparated f] [QuasiCompact f] in
/-- `|σ|²_{h^m}(p) = |sectionGauge m p σ|²`. -/
theorem sectionNormSq_eq_sectionGauge (m : ℕ) (σ : SectionSpace f L m)
    (p : SchemeComplexPoint f) :
    H.sectionNormSq a m σ p = ‖sectionGauge H a m p σ‖ ^ 2 := by
  have h0 : schemeComplexPointImage f p ∈ schemePointFrameOpen f p a := schemePointFrame_mem f p a
  have h1 := normSq_frameCoef_mul f n E a H (ptFrame a p) h0
  rw [H.sectionNormSq_frame a (ptFrame a p) m σ p h0]
  change Complex.normSq (sectionFrameCoefficient f n E (ptFrame a p) m σ p) * _ = _
  rw [sectionFrameCoefficient_eq_sectionGauge H a (ptFrame a p) m σ h0, Complex.normSq_mul,
    map_pow, ← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (frameCoef f n E a H (ptFrame a p) p) ^ m *
        Complex.normSq (sectionGauge H a m p σ) * H.frameNormSq (ptFrame a p) p ^ m
      = (Complex.normSq (frameCoef f n E a H (ptFrame a p) p) *
          H.frameNormSq (ptFrame a p) p) ^ m * Complex.normSq (sectionGauge H a m p σ) := by ring
    _ = _ := by rw [h1, one_pow, one_mul]

omit [IsSeparated f] [QuasiCompact f] in
/-- The gauge is multiplicative. -/
theorem sectionGauge_mul (m l : ℕ) (p : SchemeComplexPoint f) (σ : SectionSpace f L m)
    (τ : SectionSpace f L l) :
    sectionGauge H a (m + l) p (SectionSpace.mul f a m l σ τ) =
      sectionGauge H a m p σ * sectionGauge H a l p τ := by
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  have hne : frameCoef f n E a H (a.frame i) p ≠ 0 := frameCoef_ne_zero f n E a H _ hi
  have hm : (atlasPowerGlobalCoefficients a (m + l) i (SectionSpace.mul f a m l σ τ) :
      Γ(X, a.opens i)) = (atlasPowerGlobalCoefficients a m i σ : Γ(X, a.opens i)) *
        atlasPowerGlobalCoefficients a l i τ :=
    SectionSpace.coefficients_mul f a m l i σ τ
  have h : schemeOpenRegularFunction f n E (a.opens i)
      (atlasPowerGlobalCoefficients a (m + l) i (SectionSpace.mul f a m l σ τ)) p =
      schemeOpenRegularFunction f n E (a.opens i) (atlasPowerGlobalCoefficients a m i σ) p *
        schemeOpenRegularFunction f n E (a.opens i) (atlasPowerGlobalCoefficients a l i τ) p := by
    rw [hm, schemeOpenRegularFunction_mul f n E _ _ _ hi]
  have e1 := sectionFrameCoefficient_eq_sectionGauge H a (a.frame i) (m + l)
    (SectionSpace.mul f a m l σ τ) hi
  have e2 := sectionFrameCoefficient_eq_sectionGauge H a (a.frame i) m σ hi
  have e3 := sectionFrameCoefficient_eq_sectionGauge H a (a.frame i) l τ hi
  change schemeOpenRegularFunction f n E (a.opens i) (atlasPowerGlobalCoefficients a (m + l) i
    (SectionSpace.mul f a m l σ τ)) p = _ at e1
  change schemeOpenRegularFunction f n E (a.opens i) (atlasPowerGlobalCoefficients a m i σ) p =
    _ at e2
  change schemeOpenRegularFunction f n E (a.opens i) (atlasPowerGlobalCoefficients a l i τ) p =
    _ at e3
  rw [e1, e2, e3, pow_add] at h
  have hpow : frameCoef f n E a H (a.frame i) p ^ m * frameCoef f n E a H (a.frame i) p ^ l ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hne) (pow_ne_zero _ hne)
  have h2 : frameCoef f n E a H (a.frame i) p ^ m * frameCoef f n E a H (a.frame i) p ^ l *
      sectionGauge H a (m + l) p (SectionSpace.mul f a m l σ τ) =
      frameCoef f n E a H (a.frame i) p ^ m * frameCoef f n E a H (a.frame i) p ^ l *
        (sectionGauge H a m p σ * sectionGauge H a l p τ) := by
    rw [h]; ring
  exact mul_left_cancel₀ hpow h2

/-! ### Analytic vectors -/

/-- The coefficient of a vector of `((L, h)^an)^{⊗ m}` in the frame `α^{⊗ m}`. -/
abbrev twCoef {U : X.Opens} (α : LocalBundleFrame L U) (m : ℕ) (p : SchemeComplexPoint f) :
    (twistedPower (schemeHermitianLineBundle f n E a H) unit m).Fiber p →L[ℂ] ℂ :=
  (twistedFrame f n E a H α m).val.continuousLinearMapAt ℂ p

/-- The coordinate change between the frames `α` and `β` of `(L, h)^an`. -/
theorem schemeHermitian_coordChange_one {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) {p : SchemeComplexPoint f}
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    ((schemeHermitianAtlasFrame f n E a H α).val.coordChangeL ℂ
      (schemeHermitianAtlasFrame f n E a H β).val p) 1 =
      frameCoef f n E a H β p * (frameCoef f n E a H α p)⁻¹ := by
  change ((schemeHermitianTrivialization f n E a H α).coordChangeL ℂ
    (schemeHermitianTrivialization f n E a H β) p) 1 = _
  rw [Trivialization.coordChangeL_apply _ _ ⟨hpU, hpV⟩, schemeHermitianTrivialization_symm f n E a H
    α hpU, schemeHermitianTrivialization_apply, mul_one]

theorem unit_coordChange_one (p : SchemeComplexPoint f) :
    ((unitAtlasFrame (n := n) (M := SchemeComplexPoint f)).val.coordChangeL ℂ
      unitAtlasFrame.val p) 1 = 1 := by
  change ((Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ).coordChangeL ℂ
    (Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ) p) 1 = 1
  rw [Bundle.Trivial.trivialization.coordChangeL]
  rfl

/-- **Change of algebraic frame for analytic vectors**:
`frameCoef(α)^m · c_β(u) = frameCoef(β)^m · c_α(u)`. -/
theorem twCoef_transition {U V : X.Opens} (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (m : ℕ) {p : SchemeComplexPoint f} (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V)
    (u : (twistedPower (schemeHermitianLineBundle f n E a H) unit m).Fiber p) :
    frameCoef f n E a H α p ^ m * twCoef H a β m p u =
      frameCoef f n E a H β p ^ m * twCoef H a α m p u := by
  set eα := (twistedFrame f n E a H α m).val
  set eβ := (twistedFrame f n E a H β m).val
  have hα : p ∈ eα.baseSet := mem_twistedFrame_baseSet f n E a H α m hpU
  have hβ : p ∈ eβ.baseSet := mem_twistedFrame_baseSet f n E a H β m hpV
  have hc : twCoef H a β m p u = (eα.coordChangeL ℂ eβ p) 1 * twCoef H a α m p u := by
    change eβ.continuousLinearMapAt ℂ p u = _ * eα.continuousLinearMapAt ℂ p u
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) eβ hβ,
      Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) eα hα]
    have h1 : (eα.coordChangeL ℂ eβ p) ((eα ⟨p, u⟩).2) = (eβ ⟨p, u⟩).2 := by
      rw [Trivialization.coordChangeL_apply eα eβ ⟨hα, hβ⟩, eα.symm_apply_apply_mk hα u]
    rw [← h1]
    calc (eα.coordChangeL ℂ eβ p) ((eα ⟨p, u⟩).2)
        = (eα.coordChangeL ℂ eβ p) ((eα ⟨p, u⟩).2 • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
      _ = _ := by rw [map_smul, smul_eq_mul, mul_comm]
  have htr := twistedPower_frame_transition (schemeHermitianAtlasFrame f n E a H α)
    (schemeHermitianAtlasFrame f n E a H β) unitAtlasFrame unitAtlasFrame
    (x := p) hpU hpV (Set.mem_univ p) (Set.mem_univ p) m
  have hne : frameCoef f n E a H α p ≠ 0 := frameCoef_ne_zero f n E a H α hpU
  change (eα.coordChangeL ℂ eβ p) 1 = _ at htr
  rw [hc, htr, schemeHermitian_coordChange_one H a α β hpU hpV, unit_coordChange_one, mul_one,
    mul_pow, inv_pow]
  field_simp

/-- The preferred atlas frame at `p`. -/
abbrev prefAtlasFrame (p : SchemeComplexPoint f) :
    LocalBundleFrame L (a.opens (prefIndex f n E a p)) :=
  a.frame (prefIndex f n E a p)

/-- **The unitary gauge of an analytic vector**. -/
def fibreGauge (m : ℕ) (p : SchemeComplexPoint f) :
    (twistedPower (schemeHermitianLineBundle f n E a H) unit m).Fiber p →ₗ[ℂ] ℂ :=
  ((frameCoef f n E a H (prefAtlasFrame (n := n) (E := E) a p) p ^ m)⁻¹) •
    (twCoef H a (prefAtlasFrame (n := n) (E := E) a p) m p).toLinearMap

/-- In every algebraic frame `α`, the coefficient of `u` is `frameCoef(α, p)^m` times its
gauge. -/
theorem twCoef_eq_fibreGauge {U : X.Opens} (α : LocalBundleFrame L U) (m : ℕ)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U)
    (u : (twistedPower (schemeHermitianLineBundle f n E a H) unit m).Fiber p) :
    twCoef H a α m p u = frameCoef f n E a H α p ^ m * fibreGauge H a m p u := by
  have h0 : schemeComplexPointImage f p ∈ a.opens (prefIndex f n E a p) := mem_prefIndex f n E a p
  have hne : frameCoef f n E a H (prefAtlasFrame (n := n) (E := E) a p) p ≠ 0 :=
    frameCoef_ne_zero f n E a H _ h0
  have h := twCoef_transition H a (prefAtlasFrame (n := n) (E := E) a p) α m h0 hp u
  rw [fibreGauge, LinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
  have hpow : frameCoef f n E a H (prefAtlasFrame (n := n) (E := E) a p) p ^ m ≠ 0 :=
    pow_ne_zero _ hne
  field_simp
  linear_combination h

/-- `‖u‖ = |fibreGauge m p u|`. -/
theorem norm_eq_fibreGauge (m : ℕ) (p : SchemeComplexPoint f)
    (u : (twistedPower (schemeHermitianLineBundle f n E a H) unit m).Fiber p) :
    ‖u‖ = ‖fibreGauge H a m p u‖ := by
  have h0 : schemeComplexPointImage f p ∈ a.opens (prefIndex f n E a p) := mem_prefIndex f n E a p
  set α := prefAtlasFrame (n := n) (E := E) a p
  set e := (twistedFrame f n E a H α m).val
  have he : p ∈ e.baseSet := mem_twistedFrame_baseSet f n E a H α m h0
  have hn := SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame e he u
  have hfr : ‖e.symm p 1‖ = ‖(schemeHermitianAtlasFrame f n E a H α).val.symm p 1‖ ^ m := by
    have := twistedPower_frame_norm (schemeHermitianAtlasFrame f n E a H α) unitAtlasFrame
      (x := p) h0 (Set.mem_univ p) m
    rw [SGPT.TestCurve.SkodaRWN.norm_unitAtlasFrame_symm_eq_one, mul_one] at this
    exact this
  have hsq := schemeHermitianAtlasFrame_norm_sq f n E a H α h0
  have h1 := normSq_frameCoef_mul f n E a H α h0
  have hprod : ‖frameCoef f n E a H α p‖ * ‖(schemeHermitianAtlasFrame f n E a H α).val.symm p 1‖
      = 1 := by
    have hsq' : (‖frameCoef f n E a H α p‖ *
        ‖(schemeHermitianAtlasFrame f n E a H α).val.symm p 1‖) ^ 2 = 1 := by
      rw [mul_pow, hsq, ← Complex.normSq_eq_norm_sq, h1]
    have hnn : 0 ≤ ‖frameCoef f n E a H α p‖ *
        ‖(schemeHermitianAtlasFrame f n E a H α).val.symm p 1‖ := by positivity
    nlinarith [sq_nonneg (‖frameCoef f n E a H α p‖ *
      ‖(schemeHermitianAtlasFrame f n E a H α).val.symm p 1‖ - 1)]
  have hc := twCoef_eq_fibreGauge H a α m h0 u
  change ‖u‖ = _
  rw [hn, hfr]
  change ‖twCoef H a α m p u‖ * _ = _
  rw [hc, norm_mul, norm_pow, mul_comm (‖frameCoef f n E a H α p‖ ^ m), mul_assoc, ← mul_pow,
    hprod, one_pow, mul_one]

/-- The gauge of the frame vector `α^{⊗ k}(p)` is `frameCoef(α, p)^{-k}`. -/
theorem fibreGauge_frame {U : X.Opens} (α : LocalBundleFrame L U) (k : ℕ)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    fibreGauge H a k p ((twistedFrame f n E a H α k).val.symm p 1) =
      (frameCoef f n E a H α p ^ k)⁻¹ := by
  have he : p ∈ (twistedFrame f n E a H α k).val.baseSet :=
    mem_twistedFrame_baseSet f n E a H α k hp
  have h1 : twCoef H a α k p ((twistedFrame f n E a H α k).val.symm p 1) = 1 :=
    SGPT.PSH.GlobalL2.trivialization_coef_frame (twistedFrame f n E a H α k).val he
  have hc := h1.symm.trans (twCoef_eq_fibreGauge H a α k hp
    ((twistedFrame f n E a H α k).val.symm p 1))
  have hne : frameCoef f n E a H α p ^ k ≠ 0 := pow_ne_zero _ (frameCoef_ne_zero f n E a H α hp)
  exact eq_inv_of_mul_eq_one_right hc.symm

/-- `s = σ^an` gives `fibreGauge m p (s p) = sectionGauge m p σ`. -/
theorem fibreGauge_of_isAnalytificationOf {m : ℕ}
    {s : twistedSections (schemeHermitianLineBundle f n E a H) unit m} {σ : SectionSpace f L m}
    (hσ : IsAnalytificationOf f n E a H s σ) (p : SchemeComplexPoint f) :
    fibreGauge H a m p (s p) = sectionGauge H a m p σ := by
  have h0 : schemeComplexPointImage f p ∈ a.opens (prefIndex f n E a p) := mem_prefIndex f n E a p
  have hs := hσ (prefIndex f n E a p) p h0
  have hc := twCoef_eq_fibreGauge H a (prefAtlasFrame (n := n) (E := E) a p) m h0 (s p)
  have hg := sectionFrameCoefficient_eq_sectionGauge H a (prefAtlasFrame (n := n) (E := E) a p)
    m σ h0
  rw [sectionFrameCoefficient_def] at hg
  change twCoef H a (prefAtlasFrame (n := n) (E := E) a p) m p (s p) = _ at hs
  rw [hs, hg] at hc
  exact (mul_left_cancel₀ (pow_ne_zero _ (frameCoef_ne_zero f n E a H _ h0)) hc).symm

end Gauge

end SGPT.TestCurve.GlobalSkoda
