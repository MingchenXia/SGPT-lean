import SGPT.Unibranch.KS2NormalizationKahler
import SGPT.Unibranch.ComplexSpacePSHDensePullback
import SGPT.Unibranch.ComplexSpaceModelComponents
import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import SGPT.Unibranch.ComplexSpaceUnibranchPSHDensity

/-!
# Domination of forms and `θ`-psh functions on complex spaces

Source: footnote of `def:traceop` (`chapter_trace.tex`): "Take a Kähler form `ω̃` on `Ỹ` so that
`ω̃ ≥ (θ + ω)|_Ỹ` and `ψ ∈ PSH(Ỹ, ω̃)`". The inequality is used through its consequence
`PSH(Ỹ, (θ + ω)|_Ỹ) ⊆ PSH(Ỹ, ω̃)`: the restrictions `φ_j|_Ỹ ∈ PSH(Ỹ, (θ + ω)|_Ỹ)` of the
quasi-equisingular approximants are `ω̃`-psh, so that `d_{S, ω̃}` applies to them.

* `IsThetaPSH.of_dominates`: on a complex space, if `ω ≥ θ` (`SpaceForm.Dominates`: `ω - θ` is
  locally the restriction of a smooth closed semipositive real `(1,1)`-form), every `θ`-psh
  function (`def:unibranch:L105`) with dense finite locus is `ω`-psh. Proof: in the local
  embedding of the `θ`-psh datum `θ = (ddᶜ g)|_V`, the pull-back of the semipositive ambient form
  representing `ω - θ` has a smooth psh potential `h` on a ball (local `ddᶜ`-lemma), and
  `ω = (ddᶜ (g + h))|_V`, `(g + h) + φ` is psh on `V` (sum of a psh function and the restriction
  of a smooth psh function).
* `IsThetaPSH.of_dominates_of_isUnibranch`: on a unibranch space (e.g. the normalization `Ỹ`)
  the density hypothesis is automatic.
* `exists_kahler_dominating_psh`: for every closed real `(1,1)`-form `θ` on `X` there is a Kähler
  form `ω̃` on `Ỹ` with `ω̃ ≥ θ|_Ỹ` and `PSH(Ỹ, θ|_Ỹ) ⊆ PSH(Ỹ, ω̃)`.

Blueprint: `blueprint/src/KS2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

namespace SGPT.Unibranch

namespace KS2DominatesPSH

private theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

/-- A smooth function with nonnegative Levi form on an open set is plurisubharmonic there. -/
theorem plurisubharmonicOn_of_contDiffOn_levi_nonneg {N : ℕ} {U : Set (ComplexModel N)}
    (hU : IsOpen U) {u : ComplexModel N → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hL : ∀ z ∈ U, ∀ v : ComplexModel N, 0 ≤ leviForm u z v) :
    PlurisubharmonicOn (fun z => (u z : EReal)) U := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hU hu hx
  have hmem : {y | u y = g y} ∩ U ∈ 𝓝 x := inter_mem heq (hU.mem_nhds hx)
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hmem
  have heqV : EqOn u g V := fun y hy => (hVsub hy).1
  have hlevi : ∀ y ∈ V, ∀ v : ComplexModel N, 0 ≤ leviForm g y v := by
    intro y hy v
    have hloc : u =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with t ht
      exact heqV ht
    have hH : iteratedFDeriv ℝ 2 u y = iteratedFDeriv ℝ 2 g y :=
      (hloc.iteratedFDeriv ℝ 2).eq_of_nhds
    have : leviForm g y v = leviForm u y v := by
      simp only [leviForm, realHessian, hH]
    rw [this]
    exact hL y (hVsub hy).2 v
  have hpshg : PlurisubharmonicOn (fun y => (g y : EReal)) V :=
    plurisubharmonicOn_of_levi_nonneg (hg.of_le two_le_infty) hV hlevi
  apply (hpshg x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  rw [heqV hy]

/-- The pull-back of a closed ambient form along a holomorphic map is closed. -/
theorem extDeriv_pullbackForm_eq_zero {N n : ℕ} {T : Set (ComplexModel N)} (hT : IsOpen T)
    {O : Set (ComplexModel n)} (hO : IsOpen O) {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {w : AmbientForm n 2}
    (hw : ContDiffOn ℝ ∞ w O) (hwcl : ∀ x ∈ O, extDeriv w x = 0) {z : ComplexModel N}
    (hz : z ∈ T) : extDeriv (pullbackForm P w) z = 0 := by
  have hPr := hP.restrict_scalars ℝ
  have hdiff : DifferentiableAt ℝ w (P z) :=
    (hw.contDiffAt (hO.mem_nhds (hPO hz))).differentiableAt (by simp)
  have hnat := extDeriv_pullback hdiff (hPr.contDiffAt (hT.mem_nhds hz))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change extDeriv (fun x => (w (P x)).compContinuousLinearMap (fderiv ℝ P x)) z = 0
  rw [hnat, hwcl _ (hPO hz)]
  ext v
  rfl

/-- The pull-back of a `(1,1)` ambient form along a holomorphic map is of type `(1,1)`. -/
theorem isOneOne_pullbackForm {N n : ℕ} {T : Set (ComplexModel N)} (hT : IsOpen T)
    {O : Set (ComplexModel n)} {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {w : AmbientForm n 2}
    (hw11 : ∀ x ∈ O, IsOneOne (w x)) {z : ComplexModel N} (hz : z ∈ T) :
    IsOneOne (pullbackForm P w z) := by
  intro a b
  have hd : DifferentiableAt ℂ P z :=
    (hP.differentiableOn (by simp)).differentiableAt (hT.mem_nhds hz)
  have hlin (v : ComplexModel N) :
      fderiv ℝ P z (Complex.I • v) = Complex.I • fderiv ℝ P z v := by
    rw [hd.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ P z).map_smul Complex.I v
  change w (P z) ((fderiv ℝ P z) ∘ ![Complex.I • a, Complex.I • b]) =
    w (P z) ((fderiv ℝ P z) ∘ ![a, b])
  have hvec : ((fderiv ℝ P z) ∘ ![Complex.I • a, Complex.I • b]) =
      ![Complex.I • fderiv ℝ P z a, Complex.I • fderiv ℝ P z b] := by
    funext i
    fin_cases i <;> simp [hlin]
  have hvec' : ((fderiv ℝ P z) ∘ ![a, b]) = ![fderiv ℝ P z a, fderiv ℝ P z b] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, hvec']
  exact hw11 (P z) (hPO hz) (fderiv ℝ P z a) (fderiv ℝ P z b)

end KS2DominatesPSH

namespace LocalEmbedding

variable {X : SourceReducedComplexSpace}

theorem VanishesOn.congr {e : LocalEmbedding X} {k : ℕ} {W : Set (ComplexModel e.dim)}
    {v v' : AmbientForm e.dim k} (h : e.VanishesOn W v) (heq : ∀ z ∈ W, v z = v' z) :
    e.VanishesOn W v' := by
  intro m D g hD hd hm z hz
  have h0 := h m D g hD hd hm z hz
  change (v' (g z)).compContinuousLinearMap (fderiv ℝ g z) = 0
  rw [← heq (g z) (hm z hz).1]
  exact h0

theorem VanishesOn.mono {e : LocalEmbedding X} {k : ℕ} {W W' : Set (ComplexModel e.dim)}
    {v : AmbientForm e.dim k} (h : e.VanishesOn W v) (hW : W' ⊆ W) : e.VanishesOn W' v := by
  intro m D g hD hd hm z hz
  exact h m D g hD hd (fun y hy => ⟨hW (hm y hy).1, (hm y hy).2⟩) z hz

theorem VanishesOn.add {e : LocalEmbedding X} {k : ℕ} {W : Set (ComplexModel e.dim)}
    {v v' : AmbientForm e.dim k} (h : e.VanishesOn W v) (h' : e.VanishesOn W v') :
    e.VanishesOn W (v + v') := by
  intro m D g hD hd hm z hz
  rw [pullbackForm_add, Pi.add_apply, h m D g hD hd hm z hz, h' m D g hD hd hm z hz, add_zero]

end LocalEmbedding

namespace SpaceForm

variable {X : SourceReducedComplexSpace} {k : ℕ}

/-- Changing an ambient representative by a form vanishing on `X` preserves restriction. -/
theorem RestrictsTo.of_vanishesOn_sub {θ : SpaceForm X k} {e : LocalEmbedding X}
    {v v' : AmbientForm e.dim k} (hv : θ.RestrictsTo e v)
    (hvan : e.VanishesOn e.ambient (v' - v)) : θ.RestrictsTo e v' := by
  intro i W G hG
  have h1 := hv i W G hG
  have h2 := (hvan.mono hG.2.1).add h1
  refine h2.congr fun z _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  abel

end SpaceForm

namespace SourceReducedComplexSpace

/-- On a model space, adding the restriction of an ambient disc-psh real function preserves the
local ambient plurisubharmonicity at points of the closure of the finite locus. -/
theorem isLocallyAmbientPSHAt_add_of_discPshOn {N : ℕ} {U : Opens (ComplexModel N)}
    {C : Set U} {hC : IsComplexAnalyticSubset (n := N) C} {f : C → EReal}
    (hf : ∀ x, (sourceReducedComplexSpaceModel U C hC).IsLocallyAmbientPSHAt f x)
    {h : ComplexModel N → ℝ} (hh : DiscPshOn (fun z => (h z : EReal)) U) {c : C}
    (hc : c ∈ closure {y : C | f y ≠ ⊥}) :
    (sourceReducedComplexSpaceModel U C hC).IsLocallyAmbientPSHAt
      (fun y : C => f y + (h y.val.val : EReal)) c := by
  obtain ⟨W, hW, hcW, hWU, ψ, hψ, hfψ⟩ := exists_ambient hf (LocalEmbedding.model U C hC) c
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW c.val.val hcW
  let T : Opens (ComplexModel N) := ⟨ball c.val.val r, isOpen_ball⟩
  have hTU : T ≤ U := fun z hz => hWU (hball hz)
  let b := (LocalEmbedding.model U C hC).restrict T hTU
  have hbpt : ∀ a : b.carrier, b.toPoint a = ⟨Opens.inclusion hTU a.val, a.property⟩ :=
    fun _ => rfl
  have hcb : c ∈ range b.toPoint := ⟨⟨⟨c.val.val, mem_ball_self hr⟩, c.property⟩, rfl⟩
  obtain ⟨z, ⟨q, hq⟩, hzfin⟩ :=
    (_root_.mem_closure_iff.mp hc) (range b.toPoint) b.isOpen_range_toPoint hcb
  have hval : ∀ a : b.carrier, f (b.toPoint a) = ψ a.val.val := fun a =>
    hfψ ⟨Opens.inclusion hTU a.val, a.property⟩ (hball a.val.property)
  refine ⟨b, hcb, (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr),
    fun w => ψ w + (h w : EReal), ⟨?_, q.val.val, q.val.property, ?_⟩, ?_⟩
  · exact (hψ.mono hball).add (hh.mono fun w hw => hTU hw)
  · have hq' : f (b.toPoint q) ≠ ⊥ := by rw [hq]; exact hzfin
    rw [hval q] at hq'
    exact EReal.add_ne_bot_iff.mpr ⟨hq', EReal.coe_ne_bot _⟩
  · intro a
    exact congrArg (· + ((h a.val.val : ℝ) : EReal)) (hval a)

/-- **`θ`-psh functions are `ω`-psh when `ω ≥ θ`.** On a complex space, if `ω - θ` is locally the
restriction of a smooth closed semipositive real `(1,1)`-form (`SpaceForm.Dominates`), every
`θ`-psh function (`def:unibranch:L105`) whose finite locus is dense is `ω`-psh. -/
theorem IsThetaPSH.of_dominates {X : SourceReducedComplexSpace} {θ om : SpaceForm X 2}
    (hdom : om.Dominates θ) {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ)
    (hd : Dense {x | φ x ≠ ⊥}) : X.IsThetaPSH om φ := by
  intro x
  obtain ⟨e₁, ⟨c₁, hc₁⟩, -, g₁, hg₁, res₁, psh₁⟩ := hφ x
  obtain ⟨e₂, ⟨c₂, hc₂⟩, v, w, hv, hw, resv, resw, hpt⟩ := hdom x
  obtain ⟨W, hW, hc₁W, hWe₁, T, hT, hTmaps, hTfac⟩ :=
    e₁.exists_contDiff_transition e₂ c₁ ⟨c₂, hc₂.trans hc₁.symm⟩
  -- the pulled-back form representing `ω - θ`
  let η : AmbientForm e₁.dim 2 := pullbackForm T (v - w)
  have hTr := hT.restrict_scalars ℝ
  have hηs : ContDiffOn ℝ ∞ η W :=
    SmoothRealForm.contDiffOn_compContinuousLinearMap ((hv.sub hw).comp hTr hTmaps)
      (hTr.fderiv_of_isOpen hW (by simp))
  have hηcl : ∀ z ∈ W, extDeriv η z = 0 := fun z hz =>
    KS2DominatesPSH.extDeriv_pullbackForm_eq_zero hW e₂.ambient.isOpen hT hTmaps (hv.sub hw)
      (fun y hy => (hpt y hy).1) hz
  have hη11 : ∀ z ∈ W, IsOneOne (η z) := fun z hz =>
    KS2DominatesPSH.isOneOne_pullbackForm hW hT hTmaps (fun y hy => (hpt y hy).2.1) hz
  obtain ⟨W', ρ, hc₁W', hW', hW'W, hρ, hρeq⟩ :=
    Pending.LocalPotentials.exists_smooth_local_ddc_potential hW η hηs hηcl hη11 hc₁W
  -- `ρ` is plurisubharmonic: its Levi form is `π · η(u, iu) ≥ 0`
  have hρlevi : ∀ z ∈ W', ∀ u : ComplexModel e₁.dim, 0 ≤ leviForm ρ z u := by
    intro z hz u
    have hTz : DifferentiableAt ℂ T z :=
      (hT.differentiableOn (by simp)).differentiableAt (hW.mem_nhds (hW'W hz))
    have h2 : ContDiffAt ℝ 2 ρ z :=
      (hρ.contDiffAt (hW'.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hq := smoothDDC_complexDiagonal_eq_leviForm h2 u
    rw [hρeq hz] at hq
    have hηq : η z ![u, Complex.I • u] =
        (v - w) (T z) ![fderiv ℝ T z u, Complex.I • fderiv ℝ T z u] :=
      pullbackForm_apply_complexLine hTz (v - w) u
    have hle := (hpt (T z) (hTmaps (hW'W hz))).2.2 (fderiv ℝ T z u)
    have hnn : 0 ≤ η z ![u, Complex.I • u] := by
      rw [hηq, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
      linarith
    rw [hq] at hnn
    exact (div_nonneg_iff.mp hnn).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr Real.pi_pos))
  have hρpsh : DiscPshOn (fun z => (ρ z : EReal)) W' :=
    (KS2DominatesPSH.plurisubharmonicOn_of_contDiffOn_levi_nonneg hW' hρ hρlevi).discPshOn
  -- a ball around the base point
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW' c₁.val.val hc₁W'
  let B : Opens (ComplexModel e₁.dim) := ⟨ball c₁.val.val r, isOpen_ball⟩
  have hBW' : (B : Set (ComplexModel e₁.dim)) ⊆ W' := hball
  have hBW : (B : Set (ComplexModel e₁.dim)) ⊆ W := fun z hz => hW'W (hBW' hz)
  have hB : B ≤ e₁.ambient := fun z hz => hWe₁ (hBW hz)
  let e := e₁.restrict B hB
  have hept : ∀ c : e.carrier, e.toPoint c = e₁.toPoint ⟨Opens.inclusion hB c.val, c.property⟩ :=
    fun _ => rfl
  let g : ComplexModel e₁.dim → ℝ := fun z => g₁ z + ρ z
  have hg : ContDiffOn ℝ ∞ g B := (hg₁.mono fun z hz => hB hz).add (hρ.mono hBW')
  refine ⟨e, ⟨⟨⟨c₁.val.val, mem_ball_self hr⟩, c₁.property⟩, hc₁⟩,
    (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr), g, hg, ?_, ?_⟩
  · -- `ω = (ddᶜ g)|_V`
    have hTe : DifferentiableOn ℂ T (B : Set (ComplexModel e₁.dim)) :=
      (hT.differentiableOn (by simp)).mono hBW
    have hfac : ∀ c : e.carrier, ∃ b : e₂.carrier,
        b.val.val = T c.val.val ∧ e₂.toPoint b = e.toPoint c := fun c =>
      hTfac ⟨Opens.inclusion hB c.val, c.property⟩ (hBW c.val.property)
    have hve := resv.of_lift e hTe hfac
    have hwe := resw.of_lift e hTe hfac
    have hge := res₁.restrict B hB
    have htr : e.IsTransition e (e.ambient : Set (ComplexModel e.dim)) id :=
      ⟨e.ambient.isOpen, subset_rfl, differentiableOn_id, fun z hz => hz,
        fun y _ => ⟨y, rfl, rfl⟩⟩
    have hvan := hge.vanishesOn_sub hwe htr
    refine hve.of_vanishesOn_sub (hvan.congr fun z hz => ?_)
    rw [pullbackForm_id]
    have hadd := smoothDDC_add B.isOpen (hg₁.mono fun y hy => hB hy) (hρ.mono hBW') hz
    simp only [Pi.sub_apply]
    change smoothDDC g₁ z - pullbackForm T w z = smoothDDC (fun y => g₁ y + ρ y) z - _
    rw [hadd, hρeq (hBW' hz)]
    simp only [η, pullbackForm_sub, Pi.sub_apply]
    exact (show ∀ A Bw Cv : (ComplexModel e₁.dim) [⋀^Fin 2]→L[ℝ] ℝ,
      A - Bw = A + (Cv - Bw) - Cv from fun A Bw Cv => by abel) _ _ _
  · -- `g + φ` is psh on the local model
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
    have hloc := locallyAmbientPSH_pullback_of_dense_finite psh₁.2 F hdF
    have hfun : (fun c : e.carrier => (g c.val.val : EReal) + φ (e.toPoint c)) =
        fun c : e.carrier => f₁ (F.hom.left.base c) + (ρ c.val.val : EReal) := by
      funext c
      rw [hF c]
      change ((g₁ c.val.val + ρ c.val.val : ℝ) : EReal) + φ (e.toPoint c) = _
      rw [EReal.coe_add, add_right_comm]
    rw [hfun]
    refine ⟨componentNondegenerate_model_of_dense_finite ?_, fun c => ?_⟩
    · refine hdF.mono fun c hc => ?_
      exact EReal.add_ne_bot_iff.mpr ⟨hc, EReal.coe_ne_bot _⟩
    · exact isLocallyAmbientPSHAt_add_of_discPshOn hloc (hρpsh.mono hBW') (hdF c)

/-- On a unibranch space the density hypothesis is automatic: `PSH(X, θ) ⊆ PSH(X, ω)` when
`ω ≥ θ`. -/
theorem IsThetaPSH.of_dominates_of_isUnibranch {X : SourceReducedComplexSpace}
    {θ om : SpaceForm X 2} (hdom : om.Dominates θ) (hX : X.IsUnibranch)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) : X.IsThetaPSH om φ :=
  hφ.of_dominates hdom (hφ.dense_finite_of_isUnibranch hX)

end SourceReducedComplexSpace

namespace KS2NormalizationKahler

open KSNormalizedSubvariety

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)

/-- **The footnote of `def:traceop`, as used.** For every closed real `(1,1)`-form `θ` on the
compact Kähler manifold `X` there is a Kähler form `ω̃` on the normalization `Ỹ` with
`ω̃ ≥ θ|_Ỹ`, and then `PSH(Ỹ, θ|_Ỹ) ⊆ PSH(Ỹ, ω̃)`. (Apply it to `θ + ω` for the footnote's
`ω̃ ≥ (θ + ω)|_Ỹ`.) -/
theorem exists_kahler_dominating_psh [CompactSpace M] (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ omt : SpaceForm (normalization C hC) 2, omt.IsKahler ∧
      omt.Dominates (restrictForm C hC θ.val) ∧
      ∀ φ : (normalization C hC).obj.left → EReal,
        (normalization C hC).IsThetaPSH (restrictForm C hC θ.val) φ →
          (normalization C hC).IsThetaPSH omt φ := by
  obtain ⟨omt, hK, hdom⟩ := exists_kahler_dominating C hC omega θ
  exact ⟨omt, hK, hdom, fun φ hφ =>
    hφ.of_dominates_of_isUnibranch hdom (normalization_isUnibranch C hC)⟩

end KS2NormalizationKahler

end SGPT.Unibranch

end
