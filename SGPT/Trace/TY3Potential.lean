import SGPT.Trace.TY3Holomorphic
import SGPT.Unibranch.KS2KahlerFootnote

/-!
# Quasi-psh functions on the normalization read on resolutions

Source: `chapter_trace.tex`, `def:traceop` (trace operators are elements `ψ ∈ QPSH(Ỹ)`, and the
footnote takes a Kähler form `ω̃` on `Ỹ` with `ψ ∈ PSH(Ỹ, ω̃)`), Appendix B
(`appendix_unibranch.tex`): `def:unibranch:L105` (`QPSH` of a complex space), `cor:PSH`.

Lane TY2 proved `isTrace_iff_footnoteCondition` only for `ψ ∈ PSH(Ỹ, θ'|_Ỹ)` with `θ'` a form on
`X`: the trace predicate `TildeY.IsTrace` reads `ψ` on EVERY resolution `ν : V → Ỹ`, and for a
general `ψ ∈ QPSH(Ỹ)` it was not known that the readings `ψ ∘ ν` are quasi-psh on `V`. This file
proves it.

* `SourceReducedComplexSpace.IsThetaPSH.add_smooth_of_local`: if `ω = θ + ddᶜ f` locally (`f`
  smooth on the complex space, with local smooth ambient extensions `R`), then
  `φ ∈ PSH(X, ω)` gives `φ + f ∈ PSH(X, θ)`.
* `TY3KahlerPotential.exists_kahlerForm_smul_dominates`: the Kähler form of lane KS2 can be taken
  of the explicit shape `ω̃ = λ ((B ω)|_Ỹ + ddᶜ Ρ)` (`KS2NormalizationKahler.kahlerForm`) and
  dominating any given form `η` with local `ddᶜ`-potentials (the construction of
  `KS2NormalizationKahler.exists_kahler_dominating_two`, with the shape of `ω̃` kept).
* `TY3KahlerPotential.exists_add_isThetaPSH_restrictForm`: **every `ψ ∈ QPSH(Ỹ)` is, up to a
  smooth function, `θ'|_Ỹ`-psh for a form `θ'` on `X`**: `ψ ∈ PSH(Ỹ, η)` gives
  `ψ ∈ PSH(Ỹ, ω̃)` (`ω̃ ≥ η`, unibranch), and `ψ + λ Ρ ∈ PSH(Ỹ, (λ B ω)|_Ỹ)`.
* `Normalization.isThetaPshPotential_comp_of_isQPSH`: **for every `ψ ∈ QPSH(Ỹ)` and every
  resolution `ν : V → Ỹ`, `ψ ∘ ν` is quasi-psh on `V`**: `(ψ + ρ) ∘ ν ∈ PSH(V, ι^*θ')` (forward
  `cor:PSH`, `corPSHForward_all`), `ρ ∘ ν` is smooth (`TY3Holomorphic.chartSmooth_comp_ν`), hence
  `ψ ∘ ν ∈ PSH(V, ι^*θ' + ddᶜ(ρ ∘ ν))`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory Metric
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.PositivityPerturbation

namespace SGPT.Unibranch

namespace SourceReducedComplexSpace

/-- **Adding a smooth function.** Let `θ`, `ω` be smooth forms on a complex space and `f` a
function on it such that, locally, `θ` restricts to an ambient form `w`, `f` extends to a smooth
ambient `R` and `ω` restricts to `w + ddᶜ R` (i.e. `ω = θ + ddᶜ f`). Then every `ω`-psh `φ` whose
finite locus is dense gives the `θ`-psh function `φ + f`. -/
theorem IsThetaPSH.add_smooth_of_local {X : SourceReducedComplexSpace} {θ om : SpaceForm X 2}
    {f : X.obj.left → ℝ}
    (hloc : ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      ∃ (w : AmbientForm e.dim 2) (R : ComplexModel e.dim → ℝ),
        ContDiffOn ℝ ∞ w e.ambient ∧ ContDiffOn ℝ ∞ R e.ambient ∧ θ.RestrictsTo e w ∧
        om.RestrictsTo e (w + smoothDDC R) ∧ ∀ c : e.carrier, R c.val.val = f (e.toPoint c))
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH om φ) (hd : Dense {x | φ x ≠ ⊥}) :
    X.IsThetaPSH θ (fun x => φ x + (f x : EReal)) := by
  intro x
  obtain ⟨e₁, ⟨c₁, hc₁⟩, -, g₁, hg₁, res₁, psh₁⟩ := hφ x
  obtain ⟨e₂, ⟨c₂, hc₂⟩, w, R, -, hR, resw, resom, hReq⟩ := hloc x
  obtain ⟨W, hW, hc₁W, hWe₁, T, hT, hTmaps, hTfac⟩ :=
    e₁.exists_contDiff_transition e₂ c₁ ⟨c₂, hc₂.trans hc₁.symm⟩
  have hTr := hT.restrict_scalars ℝ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW c₁.val.val hc₁W
  let B : Opens (ComplexModel e₁.dim) := ⟨ball c₁.val.val r, isOpen_ball⟩
  have hBW : (B : Set (ComplexModel e₁.dim)) ⊆ W := hball
  have hB : B ≤ e₁.ambient := fun z hz => hWe₁ (hBW hz)
  let e := e₁.restrict B hB
  have hRT : ContDiffOn ℝ ∞ (fun z => R (T z)) W := hR.comp hTr hTmaps
  let g : ComplexModel e₁.dim → ℝ := fun z => g₁ z - R (T z)
  have hg : ContDiffOn ℝ ∞ g B := (hg₁.mono fun z hz => hB hz).sub (hRT.mono hBW)
  have hfac : ∀ c : e.carrier, ∃ b : e₂.carrier,
      b.val.val = T c.val.val ∧ e₂.toPoint b = e.toPoint c := fun c =>
    hTfac ⟨Opens.inclusion hB c.val, c.property⟩ (hBW c.val.property)
  refine ⟨e, ⟨⟨⟨c₁.val.val, mem_ball_self hr⟩, c₁.property⟩, hc₁⟩,
    (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr), g, hg, ?_, ?_⟩
  · -- `θ = (ddᶜ g)|_V`
    have hTe : DifferentiableOn ℂ T (B : Set (ComplexModel e₁.dim)) :=
      (hT.differentiableOn (by simp)).mono hBW
    have hwe := resw.of_lift e hTe hfac
    have home := resom.of_lift e hTe hfac
    have hge := res₁.restrict B hB
    have htr : e.IsTransition e (e.ambient : Set (ComplexModel e.dim)) id :=
      ⟨e.ambient.isOpen, subset_rfl, differentiableOn_id, fun z hz => hz,
        fun y _ => ⟨y, rfl, rfl⟩⟩
    have hvan := hge.vanishesOn_sub home htr
    refine hwe.of_vanishesOn_sub (hvan.congr fun z hz => ?_)
    rw [pullbackForm_id]
    have hzW : z ∈ W := hBW hz
    have hsub := smoothDDC_sub B.isOpen (hg₁.mono fun y hy => hB hy) (hRT.mono hBW) hz
    have hcomp : pullbackForm T (smoothDDC R) z = smoothDDC (fun y => R (T y)) z :=
      (HolomorphicDDC.smoothDDC_comp hW e₂.ambient.isOpen hT hR hTmaps hzW).symm
    simp only [Pi.sub_apply]
    change smoothDDC g₁ z - pullbackForm T (w + smoothDDC R) z =
      smoothDDC (fun y => g₁ y - R (T y)) z - pullbackForm T w z
    rw [hsub, pullbackForm_add, Pi.add_apply, hcomp]
    abel
  · -- `g + (φ + f) = g₁ + φ` on `V`, which is psh
    let f₁ : e₁.carrier → EReal := fun c => (g₁ c.val.val : EReal) + φ (e₁.toPoint c)
    have hcar : ∀ c : e.carrier,
        (⟨id c.val.val, hB c.val.property⟩ : e₁.ambient) ∈ e₁.carrier := fun c => c.property
    let F := analyticModelMorphism e.analytic e₁.analytic id contDiffOn_id
      (fun z hz => hB hz) hcar
    have hF : ∀ c : e.carrier, f₁ (F.hom.left.base c) =
        (g₁ c.val.val : EReal) + φ (e.toPoint c) := fun c => rfl
    have hdens : Dense {c : e.carrier | φ (e.toPoint c) ≠ ⊥} :=
      hd.preimage e.isOpenEmbedding_toPoint.isOpenMap
    have hdF : Dense {c : (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).obj.left |
        f₁ (F.hom.left.base c) ≠ ⊥} := by
      refine hdens.mono fun c hc => ?_
      change f₁ (F.hom.left.base c) ≠ ⊥
      rw [hF c]
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hc⟩
    have hloc' := locallyAmbientPSH_pullback_of_dense_finite psh₁.2 F hdF
    have hfun : (fun c : e.carrier => (g c.val.val : EReal) +
        (φ (e.toPoint c) + (f (e.toPoint c) : EReal))) =
        fun c : e.carrier => f₁ (F.hom.left.base c) := by
      funext c
      rw [hF c]
      obtain ⟨b, hb, hbc⟩ := hfac c
      have hRf : R (T c.val.val) = f (e.toPoint c) := by rw [← hb, hReq b, hbc]
      change ((g₁ c.val.val - R (T c.val.val) : ℝ) : EReal) +
        (φ (e.toPoint c) + (f (e.toPoint c) : EReal)) = (g₁ c.val.val : EReal) + φ (e.toPoint c)
      rw [hRf, add_comm (φ (e.toPoint c)), ← add_assoc, ← EReal.coe_add, sub_add_cancel]
    show (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsPSH
      (fun c : e.carrier => (g c.val.val : EReal) + (φ (e.toPoint c) + (f (e.toPoint c) : EReal)))
    rw [hfun]
    exact ⟨componentNondegenerate_model_of_dense_finite hdF, hloc'⟩

end SourceReducedComplexSpace

namespace TY3KahlerPotential

open KSNormalizedSubvariety KS2NormalizationKahler

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The Kähler form of the footnote, with its shape.** For every form `η` on `Ỹ` with local
smooth `ddᶜ`-potentials there are window data `D` and constants `B`, `λ > 0` such that
`ω̃ = λ ((B ω)|_Ỹ + ddᶜ Ρ)` dominates `η` (the construction of
`KS2NormalizationKahler.exists_kahler_dominating_two`). -/
theorem exists_kahlerForm_smul_dominates [CompactSpace M] (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (omega : KahlerBackground n M)
    (η : SpaceForm (normalization C hC) 2)
    (hη : ∀ y : (normalization C hC).obj.left, ∃ e : LocalEmbedding (normalization C hC),
      y ∈ range e.toPoint ∧ ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        η.RestrictsTo e (smoothDDC g)) :
    ∃ (D : WindowData C hC) (B lam : ℝ), 0 < lam ∧
      ((kahlerForm D omega B).smul lam).Dominates η := by
  classical
  have hcpt : CompactSpace (normalization C hC).obj.left := normalization_compactSpace C hC
  obtain ⟨D⟩ := windowData_nonempty C hC
  obtain ⟨B₀, hB₀, hchart⟩ := exists_uniform_kahlerChart D omega
  let θ : ClosedRealOneOneForm n M := 0
  obtain ⟨K, hK, hsemi⟩ := Pending.KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  set B : ℝ := B₀ + K with hBdef
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
    · have hTe : DifferentiableOn ℂ T (U' : Set (ComplexModel e.dim)) :=
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
  have hpt : ∀ y' : (normalization C hC).obj.left, ∃ y ∈ t, y' ∈ range (e y).toPoint :=
    fun y' => by simpa using ht (mem_univ y')
  refine ⟨D, B, lam, by linarith, ?_⟩
  intro y'
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

/-- **Every quasi-psh function on `Ỹ` is, up to a smooth function, `θ'|_Ỹ`-psh for a closed real
`(1,1)`-form `θ'` on `X`.** If `ψ ∈ PSH(Ỹ, η)` for some smooth form `η` on `Ỹ`, there are `θ'` on
`X` and a smooth `ρ` on `Ỹ` with `ψ + ρ ∈ PSH(Ỹ, θ'|_Ỹ)` (`θ' = λ B ω`, `ρ = λ Ρ`). -/
theorem exists_add_isThetaPSH_restrictForm [CompactSpace M] (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (omega : KahlerBackground n M)
    {η : SpaceForm (normalization C hC) 2} {ψ : (normalization C hC).obj.left → EReal}
    (hψ : (normalization C hC).IsThetaPSH η ψ) :
    ∃ (θ' : ClosedRealOneOneForm n M) (ρ : (normalization C hC).obj.left → ℝ),
      (normalization C hC).IsSmoothFunction ρ ∧
      (normalization C hC).IsThetaPSH (restrictForm C hC θ'.val)
        (fun y => ψ y + (ρ y : EReal)) := by
  obtain ⟨D, B, lam, -, hdom⟩ := exists_kahlerForm_smul_dominates C hC omega η (fun y => by
    obtain ⟨e, hy, -, g, hg, hres, -⟩ := hψ y
    exact ⟨e, hy, g, hg, hres⟩)
  have hX := normalization_isUnibranch C hC
  have hψ' := hψ.of_dominates_of_isUnibranch hdom hX
  have hd := hψ'.dense_finite_of_isUnibranch hX
  refine ⟨lam • (B • omega.form), fun y => lam • D.potential y, ?_, ?_⟩
  · intro y
    obtain ⟨e, hy, g, hg, hgeq⟩ := potential_isSmoothFunction D omega y
    refine ⟨e, hy, fun z => lam • g z, hg.const_smul lam, fun c => ?_⟩
    show lam • g c.val.val = lam • D.potential (e.toPoint c)
    rw [hgeq c]
  · refine hψ'.add_smooth_of_local ?_ hd
    intro y
    obtain ⟨e, x, P, R, -, hy, hP, hmaps, hfac, hR, hReq, -⟩ := exists_kahlerChart D omega y
    obtain ⟨hθres, hθsmooth, hres⟩ :=
      kahlerForm_restrictsTo D omega B hP hmaps hfac hR hReq (lam • (B • omega.form)).val
    refine ⟨e, hy, _, fun z => lam • R z, hθsmooth, hR.const_smul lam, hθres, ?_,
      fun c => by simp only [hReq c]⟩
    refine SpaceForm.restrictsTo_congr (hres.smul lam) fun z hz => ?_
    have h1 : (lam • (B • omega.form)).val.coeff (complexChartAt (n := n) x) =
        lam • (B • omega.form).val.coeff (complexChartAt (n := n) x) := by
      funext w
      rfl
    have h2 := smoothDDC_smul e.ambient.isOpen hR lam hz
    rw [h1, pullbackForm_smul]
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [h2, smul_add]

end TY3KahlerPotential

end SGPT.Unibranch

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Normalization

/-- **The readings of quasi-psh functions on `Ỹ` are quasi-psh.** For every `ψ ∈ QPSH(Ỹ)` and
every resolution `ν : V → Ỹ` of the normalization, `ψ ∘ ν` is `σ`-psh on `V` for a closed real
`(1,1)`-form `σ` on `V` (`σ = ι^*θ' + ddᶜ(ρ ∘ ν)` with `ψ + ρ ∈ PSH(Ỹ, θ'|_Ỹ)`). -/
theorem isThetaPshPotential_comp_of_isQPSH (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X)
    {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).IsQPSH ψ) (N : (normalizationTildeY omega Y).Resolution) :
    ∃ σ : ClosedRealOneOneForm Y.dim N.R.V, IsThetaPshPotential σ.val (ψ ∘ N.ν) := by
  obtain ⟨η, -, -, hη⟩ := hψ
  obtain ⟨θ', ρ, hρ, hψρ⟩ :=
    TY3KahlerPotential.exists_add_isThetaPSH_restrictForm Y.carrier Y.analytic omega hη
  have h1 : IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ').val
      (fun v => ψ (N.ν v) + (ρ (N.ν v) : EReal)) :=
    corPSHForward_all omega Y N θ' (fun y => ψ y + (ρ y : EReal)) hψρ
  have hs := chartSmooth_comp_ν omega Y N hρ
  refine ⟨ClosedRealOneOneForm.pullback N.R.contMDiff θ' +
    ddcClosedForm (fun v => ρ (N.ν v)) hs, ?_⟩
  have h2 := thetaPshPotential_sub_smooth (η := (ClosedRealOneOneForm.pullback N.R.contMDiff θ' +
    ddcClosedForm (fun v => ρ (N.ν v)) hs).val) hs (fun e z _ => by
      rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]) h1
  convert h2 using 1
  funext v
  exact (EReal.add_sub_cancel_right).symm

end Normalization

end SGPT.Trace.TY
