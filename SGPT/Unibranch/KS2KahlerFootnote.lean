import SGPT.Unibranch.KS2DominatesPSH

/-!
# The Kähler form of the footnote of `def:traceop`

Source: footnote of `def:traceop` (`chapter_trace.tex`): "We can find a closed smooth real
`(1,1)`-form `θ` on `X` such that `φ ∈ PSH(X, θ)`. Then there is a Kähler form such that
`ω + θ + ddᶜ φ_j ≥ 0` for all `j ≥ 1`. Take a Kähler form `ω̃` on `Ỹ` so that
`ω̃ ≥ (θ + ω)|_Ỹ` and `ψ ∈ PSH(Ỹ, ω̃)`."

Here `ψ ∈ QPSH(Ỹ)` is a given quasi-psh function on the normalization, i.e. `ψ ∈ PSH(Ỹ, η)` for
some smooth form `η` on `Ỹ` (`def:unibranch:L105`). We prove the existence of `ω̃` with ALL
the properties the footnote asks for:

* `SpaceForm.smul`: scalar multiples of forms on complex spaces;
* `exists_kahler_dominating_two`: for every closed real `(1,1)`-form `θ` on `X` and every form `η`
  on `Ỹ` with local `ddᶜ`-potentials, there is a Kähler form `ω̃ = λ ((B ω)|_Ỹ + ddᶜ Ρ)` on `Ỹ`
  with `ω̃ ≥ θ|_Ỹ` and `ω̃ ≥ η`;
* **`exists_kahler_footnote`**: for `θ` on `X` and `ψ ∈ PSH(Ỹ, η)`, there is a Kähler form `ω̃` on
  `Ỹ` with `ω̃ ≥ θ|_Ỹ`, `PSH(Ỹ, θ|_Ỹ) ⊆ PSH(Ỹ, ω̃)` and `ψ ∈ PSH(Ỹ, ω̃)` (apply it to `θ + ω` for
  the footnote's `ω̃ ≥ (θ + ω)|_Ỹ`; then also `φ_j|_Ỹ ∈ PSH(Ỹ, ω̃)`).

Blueprint: `blueprint/src/KS2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.PositivityPerturbation

namespace SGPT.Unibranch

namespace LocalEmbedding

variable {X : SourceReducedComplexSpace}

theorem VanishesOn.smul {e : LocalEmbedding X} {k : ℕ} {W : Set (ComplexModel e.dim)}
    {v : AmbientForm e.dim k} (h : e.VanishesOn W v) (c : ℝ) : e.VanishesOn W (c • v) := by
  intro m D g hD hd hm z hz
  rw [pullbackForm_smul, Pi.smul_apply, h m D g hD hd hm z hz, smul_zero]

end LocalEmbedding

namespace SpaceForm

variable {X : SourceReducedComplexSpace} {k : ℕ}

/-- The scalar multiple `c θ` of a smooth form on a complex space. -/
def smul (c : ℝ) (θ : SpaceForm X k) : SpaceForm X k where
  ι := θ.ι
  chart := θ.chart
  covers := θ.covers
  rep i := c • θ.rep i
  smooth i := (θ.smooth i).const_smul c
  compatible i j W G hG := by
    have h := (θ.compatible i j W G hG).smul c
    refine h.congr fun z _ => ?_
    rw [pullbackForm_smul, smul_sub]

theorem RestrictsTo.smul {θ : SpaceForm X k} {e : LocalEmbedding X} {v : AmbientForm e.dim k}
    (h : θ.RestrictsTo e v) (c : ℝ) : (θ.smul c).RestrictsTo e (c • v) := by
  intro i W G hG
  have h' := (h i W G hG).smul c
  refine h'.congr fun z _ => ?_
  change c • (v z - pullbackForm G (θ.rep i) z) = c • v z - pullbackForm G (c • θ.rep i) z
  rw [pullbackForm_smul, Pi.smul_apply, smul_sub]

end SpaceForm

namespace KS2NormalizationKahler

open KSNormalizedSubvariety

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {C : Set M} {hC : IsComplexAnalyticSubset (n := n) C}

/-- Closed `(1,1)` ambient forms are stable under `λ v - w`. -/
theorem closed_oneOne_smul_sub {N : ℕ} {U : Set (ComplexModel N)} (hU : IsOpen U)
    {v w : AmbientForm N 2} (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U)
    (hvcl : ∀ z ∈ U, extDeriv v z = 0) (hwcl : ∀ z ∈ U, extDeriv w z = 0)
    (hv11 : ∀ z ∈ U, IsOneOne (v z)) (hw11 : ∀ z ∈ U, IsOneOne (w z)) (c : ℝ)
    {z : ComplexModel N} (hz : z ∈ U) :
    extDeriv (c • v - w) z = 0 ∧ IsOneOne ((c • v - w) z) := by
  have hvd : DifferentiableAt ℝ (c • v) z :=
    ((hv.const_smul c).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ (-w) z :=
    (hw.neg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  refine ⟨?_, fun a b => ?_⟩
  · rw [sub_eq_add_neg, extDeriv_add hvd hwd, extDeriv_smul, hvcl z hz, smul_zero, zero_add]
    have : extDeriv (-w) z = -extDeriv w z := by
      have hneg : (-w) = (-1 : ℝ) • w := by
        funext z'
        exact (neg_one_smul ℝ (w z')).symm
      rw [hneg, extDeriv_smul, neg_one_smul]
    rw [this, hwcl z hz, neg_zero]
  · simp only [Pi.sub_apply, Pi.smul_apply, ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.smul_apply]
    rw [hv11 z hz a b, hw11 z hz a b]

/-- The facts on one Kähler chart of `kahlerForm D ω B` (`exists_uniform_kahlerChart`), for a
constant `B ≥ B₀ + K` where `-θ + K ω` is semipositive: the representative
`v = P^*(B ω) + ddᶜ R` is smooth, closed, `(1,1)`, strictly positive, and dominates the
representative `w = P^*θ` of `θ|_Ỹ`. -/
theorem kahlerChart_facts (D : WindowData C hC) (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {K B₀ B : ℝ} (hK : 0 < K)
    (hsemi : (-θ + K • omega.form).val.IsSemipositive) (hB : B₀ + K ≤ B)
    {e : LocalEmbedding (normalization C hC)} {x : M} {P : ComplexModel e.dim → ComplexModel n}
    {R : ComplexModel e.dim → ℝ} (hP : ContDiffOn ℂ ∞ P e.ambient)
    (hmaps : MapsTo P e.ambient (complexChartAt (n := n) x).val.target)
    (hfac : ∀ c : e.carrier, ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
      b.val.val = P c.val.val ∧
      (LocalEmbedding.ofChart C hC x).toPoint b =
        (normalizationMap C hC).hom.left.base (e.toPoint c))
    (hR : ContDiffOn ℝ ∞ R e.ambient)
    (hReq : ∀ c : e.carrier, R c.val.val = D.potential (e.toPoint c))
    (hpos : ∀ B' : ℝ, B₀ ≤ B' → ∀ z ∈ e.ambient,
      IsStrictlyPositive (smoothDDC R z +
        B' • pullbackForm P (omega.form.val.coeff (complexChartAt (n := n) x)) z)) :
    let v := pullbackForm P ((B • omega.form).val.coeff (complexChartAt (n := n) x)) + smoothDDC R
    let w := pullbackForm P (θ.val.coeff (complexChartAt (n := n) x))
    ContDiffOn ℝ ∞ v e.ambient ∧ ContDiffOn ℝ ∞ w e.ambient ∧
    (kahlerForm D omega B).RestrictsTo e v ∧ (restrictForm C hC θ.val).RestrictsTo e w ∧
    (∀ z ∈ e.ambient, extDeriv v z = 0) ∧ (∀ z ∈ e.ambient, extDeriv w z = 0) ∧
    (∀ z ∈ e.ambient, IsOneOne (v z)) ∧ (∀ z ∈ e.ambient, IsOneOne (w z)) ∧
    (∀ z ∈ e.ambient, IsStrictlyPositive (v z)) ∧
    (∀ z ∈ e.ambient, ∀ u, w z ![u, Complex.I • u] ≤ v z ![u, Complex.I • u]) := by
  intro v w
  let φ := complexChartAt (n := n) x
  obtain ⟨hθres, hθsmooth, hres⟩ := kahlerForm_restrictsTo D omega B hP hmaps hfac hR hReq θ.val
  have hPr := hP.restrict_scalars ℝ
  have hvs : ContDiffOn ℝ ∞ v e.ambient :=
    (SmoothRealForm.contDiffOn_compContinuousLinearMap
      (((B • omega.form).val.smooth _).comp hPr hmaps)
      (hPr.fderiv_of_isOpen e.ambient.isOpen (by simp))).add
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn e.ambient.isOpen hR)
  have hwmul : (B • omega.form).val.coeff φ = B • omega.form.val.coeff φ := by
    funext z
    exact ClosedRealOneOneForm.coeff_smul B omega.form _ z
  have hB₀ : B₀ ≤ B := by linarith
  refine ⟨hvs, hθsmooth, hres, hθres, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact KS2LeviEstimate.extDeriv_pullback_add_ddc e.ambient.isOpen φ.val.open_target hP hmaps
      ((B • omega.form).val.smooth _) (fun z' hz' => (B • omega.form).property.1 _ z' hz') hR hz
  · intro z hz
    exact KS2DominatesPSH.extDeriv_pullbackForm_eq_zero e.ambient.isOpen φ.val.open_target hP
      hmaps (θ.val.smooth _) (fun z' hz' => θ.property.1 _ z' hz') hz
  · intro z hz
    exact KS2LeviEstimate.isOneOne_pullback_add_ddc e.ambient.isOpen hP hmaps
      (fun z' hz' => (B • omega.form).property.2 _ z' hz') hR hz
  · intro z hz
    exact KS2DominatesPSH.isOneOne_pullbackForm e.ambient.isOpen hP hmaps
      (fun z' hz' => θ.property.2 _ z' hz') hz
  · intro z hz
    have h := hpos B hB₀ z hz
    change IsStrictlyPositive ((pullbackForm P ((B • omega.form).val.coeff φ) + smoothDDC R) z)
    rw [hwmul, pullbackForm_smul]
    simpa only [Pi.add_apply, Pi.smul_apply, add_comm] using h
  · intro z hz u
    have hPz : DifferentiableAt ℂ P z :=
      (hP.differentiableOn (by simp)).differentiableAt (e.ambient.isOpen.mem_nhds hz)
    have h0 := quad_nonneg_of_isStrictlyPositive (hpos B₀ le_rfl z hz) u
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      pullbackForm_apply_complexLine hPz] at h0
    have hs := hsemi φ (P z) (hmaps hz) (fderiv ℝ P z u)
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at hs
    change pullbackForm P (θ.val.coeff φ) z ![u, Complex.I • u] ≤
      (pullbackForm P ((B • omega.form).val.coeff φ) + smoothDDC R) z ![u, Complex.I • u]
    rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, pullbackForm_apply_complexLine hPz,
      pullbackForm_apply_complexLine hPz, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hωnn : 0 ≤ omega.form.val.coeff φ (P z)
        ![fderiv ℝ P z u, Complex.I • fderiv ℝ P z u] :=
      quad_nonneg_of_isStrictlyPositive ((omega.isKahler.1 φ (P z) (hmaps hz)).2) _
    have hBK : B₀ + K ≤ B := hB
    nlinarith [mul_nonneg (sub_nonneg.mpr hBK) hωnn]

/-- **A Kähler form on `Ỹ` dominating a form of `X` and a form of `Ỹ`.** For every closed real
`(1,1)`-form `θ` on `X` and every form `η` on `Ỹ` which has local smooth `ddᶜ`-potentials, there is
a Kähler form `ω̃` on `Ỹ` with `ω̃ ≥ θ|_Ỹ` and `ω̃ ≥ η`. -/
theorem exists_kahler_dominating_two [CompactSpace M] (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (η : SpaceForm (normalization C hC) 2)
    (hη : ∀ y : (normalization C hC).obj.left, ∃ e : LocalEmbedding (normalization C hC),
      y ∈ range e.toPoint ∧ ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        η.RestrictsTo e (smoothDDC g)) :
    ∃ omt : SpaceForm (normalization C hC) 2, omt.IsKahler ∧
      omt.Dominates (restrictForm C hC θ.val) ∧ omt.Dominates η := by
  classical
  have hcpt : CompactSpace (normalization C hC).obj.left := normalization_compactSpace C hC
  obtain ⟨D⟩ := windowData_nonempty C hC
  obtain ⟨B₀, hB₀, hchart⟩ := exists_uniform_kahlerChart D omega
  obtain ⟨K, hK, hsemi⟩ := Pending.KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  set B : ℝ := B₀ + K with hBdef
  -- local data: a Kähler chart shrunk to an open set where `λ v - ddᶜ(g ∘ T)` is positive
  have hlocal : ∀ y : (normalization C hC).obj.left,
      ∃ (e : LocalEmbedding (normalization C hC)) (x : M)
        (P : ComplexModel e.dim → ComplexModel n) (R : ComplexModel e.dim → ℝ)
        (gη : ComplexModel e.dim → ℝ) (L : ℝ),
        y ∈ range e.toPoint ∧ ContDiffOn ℂ ∞ P e.ambient ∧
        MapsTo P e.ambient (complexChartAt (n := n) x).val.target ∧
        (∀ c : e.carrier, ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
          b.val.val = P c.val.val ∧
          (LocalEmbedding.ofChart C hC x).toPoint b =
            (normalizationMap C hC).hom.left.base (e.toPoint c)) ∧
        ContDiffOn ℝ ∞ R e.ambient ∧
        (∀ c : e.carrier, R c.val.val = D.potential (e.toPoint c)) ∧
        (∀ B' : ℝ, B₀ ≤ B' → ∀ z ∈ e.ambient,
          IsStrictlyPositive (smoothDDC R z +
            B' • pullbackForm P (omega.form.val.coeff (complexChartAt (n := n) x)) z)) ∧
        ContDiffOn ℝ ∞ gη e.ambient ∧ η.RestrictsTo e (smoothDDC gη) ∧
        ∀ L' : ℝ, L ≤ L' → ∀ z ∈ e.ambient,
          IsStrictlyPositive (-smoothDDC gη z + L' •
            (pullbackForm P ((B • omega.form).val.coeff (complexChartAt (n := n) x)) +
              smoothDDC R) z) := by
    intro y
    obtain ⟨e, x, P, R, ⟨c₀, hc₀⟩, hP, hmaps, hfac, hR, hReq, hpos⟩ := hchart y
    obtain ⟨e', ⟨c', hc'⟩, g', hg', hres'⟩ := hη y
    obtain ⟨W, hW, hc₀W, hWe, T, hT, hTmaps, hTfac⟩ :=
      e.exists_contDiff_transition e' c₀ ⟨c', hc'.trans hc₀.symm⟩
    obtain ⟨hvs, -, -, -, -, -, -, -, hvpos, -⟩ :=
      kahlerChart_facts D omega θ hK hsemi (le_of_eq hBdef.symm) hP hmaps hfac hR hReq hpos
    let v := pullbackForm P ((B • omega.form).val.coeff (complexChartAt (n := n) x)) +
      smoothDDC R
    let gη : ComplexModel e.dim → ℝ := fun z => g' (T z)
    have hgη : ContDiffOn ℝ ∞ gη W := hg'.comp (hT.restrict_scalars ℝ) hTmaps
    have hacont : ContinuousOn (fun z => -smoothDDC gη z) W :=
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn hW hgη).continuousOn.neg
    have hbcont : ContinuousOn v W := (hvs.mono hWe).continuousOn
    obtain ⟨L, -, U, hU, hc₀U, hUW, hL⟩ :=
      Pending.UniformTubePositivity.exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_familyOn
        hW hacont hbcont (fun z hz u => quad_nonneg_of_isStrictlyPositive (hvpos z (hWe hz)) u)
        (isCompact_singleton (x := c₀.val.val)) (singleton_subset_iff.mpr hc₀W) (by
          intro z hz u hu hnull
          exact absurd hnull (hvpos z (hWe (by rw [mem_singleton_iff.mp hz]; exact hc₀W)) u hu).ne')
    let U' : Opens (ComplexModel e.dim) := ⟨U, hU⟩
    have hU'e : U' ≤ e.ambient := fun z hz => hWe (hUW hz)
    have hUW' : (U' : Set (ComplexModel e.dim)) ⊆ W := hUW
    refine ⟨e.restrict U' hU'e, x, P, R, gη, L, ⟨⟨⟨c₀.val.val, hc₀U (mem_singleton _)⟩,
      c₀.property⟩, hc₀⟩, hP.mono hU'e, fun z hz => hmaps (hU'e hz),
      fun c => hfac ⟨Opens.inclusion hU'e c.val, c.property⟩, hR.mono hU'e,
      fun c => hReq ⟨Opens.inclusion hU'e c.val, c.property⟩,
      fun B' hB' z hz => hpos B' hB' z (hU'e hz), hgη.mono hUW', ?_, ?_⟩
    · -- `η = ddᶜ (g' ∘ T)` on the shrunk chart
      have hTe : DifferentiableOn ℂ T (U' : Set (ComplexModel e.dim)) :=
        (hT.differentiableOn (by simp)).mono hUW'
      have h1 := hres'.of_lift (e.restrict U' hU'e) hTe fun c =>
        hTfac ⟨Opens.inclusion hU'e c.val, c.property⟩ (hUW' c.val.property)
      refine SpaceForm.restrictsTo_congr h1 fun z hz => ?_
      exact (HolomorphicDDC.smoothDDC_comp U'.isOpen e'.ambient.isOpen (hT.mono hUW') hg'
        (fun z' hz' => hTmaps (hUW' hz')) hz).symm
    · intro L' hL' z hz
      exact hL L' hL' z hz
  choose e x P R gη L hy hP hmaps hfac hR hReq hpos hgη hηres hL using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => range (e y).toPoint)
    (fun y => (e y).isOpen_range_toPoint) (fun y _ => mem_iUnion.mpr ⟨y, hy y⟩)
  set lam : ℝ := 1 + ∑ y ∈ t, |L y| with hlamdef
  have hlam1 : 1 ≤ lam := by
    have : 0 ≤ ∑ y ∈ t, |L y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hlamL : ∀ y ∈ t, L y ≤ lam := by
    intro y hyt
    have h1 : |L y| ≤ ∑ y ∈ t, |L y| :=
      Finset.single_le_sum (f := fun y => |L y|) (fun _ _ => abs_nonneg _) hyt
    linarith [le_abs_self (L y)]
  -- the chart data at any point
  have hpt : ∀ y' : (normalization C hC).obj.left, ∃ y ∈ t, y' ∈ range (e y).toPoint :=
    fun y' => by simpa using ht (mem_univ y')
  refine ⟨(kahlerForm D omega B).smul lam, ?_, ?_, ?_⟩
  · intro y'
    obtain ⟨y, -, hy'⟩ := hpt y'
    obtain ⟨hvs, -, hres, -, hvcl, -, hv11, -, hvpos, -⟩ :=
      kahlerChart_facts D omega θ hK hsemi (le_of_eq hBdef.symm) (hP y) (hmaps y) (hfac y)
        (hR y) (hReq y) (hpos y)
    let V := pullbackForm (P y) ((B • omega.form).val.coeff (complexChartAt (n := n) (x y))) +
      smoothDDC (R y)
    refine ⟨e y, hy', lam • V, hvs.const_smul lam, fun z hz => ?_, fun z hz => ⟨?_, ?_⟩,
      hres.smul lam⟩
    · have h0 : extDeriv (lam • V) z = 0 := by rw [extDeriv_smul, hvcl z hz, smul_zero]
      exact h0
    · intro a b
      change lam • V z ![Complex.I • a, Complex.I • b] = lam • V z ![a, b]
      rw [hv11 z hz a b]
    · intro u hu
      change 0 < lam • V z ![u, Complex.I • u]
      rw [smul_eq_mul]
      exact mul_pos (by linarith) (hvpos z hz u hu)
  · intro y'
    obtain ⟨y, -, hy'⟩ := hpt y'
    obtain ⟨hvs, hws, hres, hθres, hvcl, hwcl, hv11, hw11, hvpos, hwv⟩ :=
      kahlerChart_facts D omega θ hK hsemi (le_of_eq hBdef.symm) (hP y) (hmaps y) (hfac y)
        (hR y) (hReq y) (hpos y)
    refine ⟨e y, hy', _, _, hvs.const_smul lam, hws, hres.smul lam, hθres, fun z hz => ?_⟩
    refine ⟨(closed_oneOne_smul_sub (e y).ambient.isOpen hvs hws hvcl hwcl hv11 hw11 lam
      hz).1, (closed_oneOne_smul_sub (e y).ambient.isOpen hvs hws hvcl hwcl hv11 hw11 lam hz).2,
      fun u => ?_⟩
    have h1 := hwv z hz u
    have h2 := quad_nonneg_of_isStrictlyPositive (hvpos z hz) u
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    nlinarith
  · intro y'
    obtain ⟨y, hyt, hy'⟩ := hpt y'
    obtain ⟨hvs, -, hres, -, hvcl, -, hv11, -, -, -⟩ :=
      kahlerChart_facts D omega θ hK hsemi (le_of_eq hBdef.symm) (hP y) (hmaps y) (hfac y)
        (hR y) (hReq y) (hpos y)
    have hgs := Pending.LogWeightFactorization.smoothDDC_contDiffOn (e y).ambient.isOpen (hgη y)
    have hgcl : ∀ z ∈ (e y).ambient, extDeriv (smoothDDC (gη y)) z = 0 := fun z hz =>
      extDeriv_extDeriv_apply
        ((smoothDc_contDiffOn (e y).ambient.isOpen (hgη y)).contDiffAt
          ((e y).ambient.isOpen.mem_nhds hz))
        (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hg11 : ∀ z ∈ (e y).ambient, IsOneOne (smoothDDC (gη y) z) := fun z hz a b =>
      MongeAmpere.smoothDDC_isOneOne (((hgη y).contDiffAt ((e y).ambient.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a b
    refine ⟨e y, hy', _, _, hvs.const_smul lam, hgs, hres.smul lam, hηres y, fun z hz => ?_⟩
    refine ⟨(closed_oneOne_smul_sub (e y).ambient.isOpen hvs hgs hvcl hgcl hv11 hg11 lam
      hz).1, (closed_oneOne_smul_sub (e y).ambient.isOpen hvs hgs hvcl hgcl hv11 hg11 lam
      hz).2, fun u => ?_⟩
    have h := quad_nonneg_of_isStrictlyPositive (hL y lam (hlamL y hyt) z hz) u
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    linarith

/-- **The footnote of `def:traceop`.** Let `θ` be a closed real `(1,1)`-form on the compact Kähler
manifold `X` and `ψ ∈ PSH(Ỹ, η)` a quasi-psh function on the normalization `Ỹ`. There is a Kähler
form `ω̃` on `Ỹ` with `ω̃ ≥ θ|_Ỹ`, `PSH(Ỹ, θ|_Ỹ) ⊆ PSH(Ỹ, ω̃)` and `ψ ∈ PSH(Ỹ, ω̃)`. (The footnote
applies it to `θ + ω`.) -/
theorem exists_kahler_footnote [CompactSpace M] (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (η : SpaceForm (normalization C hC) 2)
    {ψ : (normalization C hC).obj.left → EReal}
    (hψ : (normalization C hC).IsThetaPSH η ψ) :
    ∃ omt : SpaceForm (normalization C hC) 2, omt.IsKahler ∧
      omt.Dominates (restrictForm C hC θ.val) ∧
      (∀ φ : (normalization C hC).obj.left → EReal,
        (normalization C hC).IsThetaPSH (restrictForm C hC θ.val) φ →
          (normalization C hC).IsThetaPSH omt φ) ∧
      (normalization C hC).IsThetaPSH omt ψ := by
  obtain ⟨omt, hK, hθ, hη⟩ := exists_kahler_dominating_two C hC omega θ η (fun y => by
    obtain ⟨e, hy, -, g, hg, hres, -⟩ := hψ y
    exact ⟨e, hy, g, hg, hres⟩)
  have hX := normalization_isUnibranch C hC
  exact ⟨omt, hK, hθ, fun φ hφ => hφ.of_dominates_of_isUnibranch hθ hX,
    hψ.of_dominates_of_isUnibranch hη hX⟩

end KS2NormalizationKahler

end SGPT.Unibranch

end
