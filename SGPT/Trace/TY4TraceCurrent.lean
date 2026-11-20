import SGPT.Trace.TY4CurrentEquality
import SGPT.Trace.TY3TraceCurrent
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain

/-!
# `rmk:tracecurrent`: closed positive currents on `Ỹ`, their classes, and `Tr^β_Y(T)`

Source: `chapter_trace.tex`, `rmk:tracecurrent`: "As in `rmk:qpshtocurrents`, the trace operator
could also be applied to closed positive `(1,1)`-currents on `X`. If `T ∈ 𝒵₊(X, α)` for some
pseudo-effective class `α` on `X` and `β ∈ H^{1,1}(Ỹ, ℝ)`, then we write `Tr^β_Y(T)` for any (if
exists) closed positive `(1,1)`-current in `β` representing `Tr_Y(T)` when `ν(T, Y) = 0`."

Lanes TY/TY2/TY3 handled closed positive currents on the normalization `Ỹ` through presentations
`θ̃ + dd^c ψ`. Here the currents become objects, following Eyssidieux–Guedj–Zeriahi (J. AMS 2009,
§5.2, Definitions 5.7–5.8; see `TY4CurrentEquality`): two presentations are the same current
when their local potentials differ by pluriharmonic functions (`SpaceForm.SameCurrent`).

* `Normalization.dense_ne_bot`: a quasi-psh function on `Ỹ` is finite on a dense set (read on a
  resolution, where it is quasi-psh, `TY3`).
* `Normalization.sameCurrent_iff`: `θ̃₁ + dd^c ψ₁ = θ̃₂ + dd^c ψ₂` iff `θ̃₂ = θ̃₁ + dd^c f` and
  `ψ₁ = ψ₂ + f` for a SMOOTH function `f` on `Ỹ` (the potentials of two presentations of the same
  current differ by a smooth function: presentation-independence).
* `Normalization.sameCurrent_iff_re_and_weak`: the three readings of equality of currents (EGZ
  conditions (i) and (ii), and the probe version) agree on `Ỹ`;
  `exists_chartSmooth_of_sameCurrent`: equal currents have equal pull-backs to every resolution.
* `Normalization.Current omega Y` (`𝒵₊(Ỹ)`): presentations modulo `SameCurrent` (an equivalence
  relation, `currentSetoid`); `Current.cls : 𝒵₊(Ỹ) → H^{1,1}(Ỹ, ℝ)`, the class of a current, is
  well defined (`cls_mk`).
* `Current.RepresentsTrace S Tc`: `S` represents `Tr_Y(Tc)` (a potential of `S` is a trace operator
  of a potential of `Tc`), well defined: it holds for one presentation iff for every presentation
  (`representsTrace_mk`; presentations of the same current have `P`-equivalent potentials,
  `pEquivalent_of_sameCurrent`).
* `Current.IsTr Tc β S` (**`S` is a `Tr^β_Y(Tc)`**): `S ∈ β` and `S` represents `Tr_Y(Tc)`;
  `isTr_mk_iff` identifies it with the presentation-level `TildeY.IsTraceCurrentIn` of lane TY2,
  `IsTr.sourceGenericLelong_eq_zero` (it forces `ν(Tc, Y) = 0`), `IsTr.pEquivalent` (all of them
  have `𝓘`-good `P`-equivalent potentials), `exists_isTr` (existence in `{(θ + ω)|_Ỹ}`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace}

/-- Smooth functions on a complex space are continuous. -/
theorem IsSmoothFunction.continuous {f : X.obj.left → ℝ} (hf : X.IsSmoothFunction f) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, ⟨c, rfl⟩, g, hg, heq⟩ := hf x
  refine e.isOpenEmbedding_toPoint.continuousAt_iff.mp ?_
  have hcomp : f ∘ e.toPoint = fun c' : e.carrier => g c'.val.val := funext fun c' => (heq c').symm
  rw [hcomp]
  have hval : Continuous fun c' : e.carrier => c'.val.val :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ContinuousAt.comp (f := fun c' : e.carrier => c'.val.val) (x := c)
    (hg.continuousOn.continuousAt (e.ambient.isOpen.mem_nhds c.val.property)) hval.continuousAt

end SGPT.Unibranch.SourceReducedComplexSpace

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.PSH.BookCurrent SGPT.Trace.TraceCurrent

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X]

namespace TildeY

variable {Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X}

/-- **A presented closed positive `(1,1)`-current on `Ỹ`**: `θ̃ + dd^c ψ` with `θ̃` a smooth closed
real `(1,1)`-form on `Ỹ` (`def:unibranch:L105`) and `ψ ∈ PSH(Ỹ, θ̃)`. -/
structure CurrentPresentation (T : TildeY Y) where
  /-- The smooth closed real `(1,1)`-form `θ̃`. -/
  form : SpaceForm T.space 2
  /-- The potential `ψ`. -/
  pot : T.space.obj.left → EReal
  closed : PD.IsLocallyClosedOneOne form
  psh : T.space.IsThetaPSH form pot

end TildeY

namespace Normalization

variable (omega : KahlerBackground (m + 1) X) (Y : ClosedIrreducibleAnalyticSubvariety (m + 1) X)

/-- **Quasi-psh functions on `Ỹ` are finite on a dense set**: on any resolution `ν : V → Ỹ` the
reading is quasi-psh (`TY3`), hence finite on a dense set, and `ν` is continuous and onto. -/
theorem dense_ne_bot {ψ : (normalizationTildeY omega Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omega Y).IsQPSH ψ) :
    Dense {y : (normalizationTildeY omega Y).space.obj.left | ψ y ≠ ⊥} := by
  obtain ⟨N⟩ := (normalizationTildeY omega Y).nonempty_resolution
  obtain ⟨σ, hσ⟩ := isThetaPshPotential_comp_of_isQPSH omega Y hψ N
  have hV : Dense {v : N.R.V | ψ (N.ν v) ≠ ⊥} := by
    refine dense_iff_inter_open.mpr fun U hU ⟨v, hv⟩ => ?_
    obtain ⟨w, hwU, hw⟩ := hσ.2 v U hU hv
    exact ⟨w, hwU, hw⟩
  refine (N.surjective.denseRange.dense_image N.continuous hV).mono ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hv

theorem CurrentPresentation.dense (p : TildeY.CurrentPresentation (normalizationTildeY omega Y)) :
    Dense {y : (normalizationTildeY omega Y).space.obj.left | p.pot y ≠ ⊥} :=
  dense_ne_bot omega Y ⟨p.form, p.closed.isClosed, p.closed.isOneOne, p.psh⟩

/-- **Presentations of the same current on `Ỹ`** (`TY4CurrentEquality`, EGZ): `θ̃₁ + dd^c ψ₁ =
θ̃₂ + dd^c ψ₂` iff there is a SMOOTH function `f` on `Ỹ` with `θ̃₂ = θ̃₁ + dd^c f` and
`ψ₁ = ψ₂ + f`. -/
theorem sameCurrent_iff (p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)) :
    SpaceForm.SameCurrent p.form p.pot q.form q.pot ↔
      ∃ (f : (normalizationTildeY omega Y).space.obj.left → ℝ)
        (hf : (normalizationTildeY omega Y).space.IsSmoothFunction f),
        SpaceForm.SameForm (p.form.add (SpaceForm.ddcOf f hf)) q.form ∧
          ∀ y, p.pot y = q.pot y + (f y : EReal) := by
  constructor
  · intro h
    exact h.exists_smooth (CurrentPresentation.dense omega Y p) p.psh.ne_top
  · rintro ⟨f, hf, hS, hψ⟩
    exact SpaceForm.sameCurrent_of_eq_add p.psh hf hS hψ

/-- **The three readings of "the same current" agree on `Ỹ`**: local potentials differing by the
real part of a holomorphic function on `Ỹ` (EGZ (i), `SameCurrentRe`), by the restriction of an
ambient pluriharmonic function (EGZ (ii), `SameCurrent`), or by a smooth function with
`dd^c = 0` on `Ỹ` (`SameCurrentWeak`). -/
theorem sameCurrent_iff_re_and_weak (p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)) :
    (SpaceForm.SameCurrentRe p.form p.pot q.form q.pot ↔
        SpaceForm.SameCurrent p.form p.pot q.form q.pot) ∧
      (SpaceForm.SameCurrentWeak p.form p.pot q.form q.pot ↔
        SpaceForm.SameCurrent p.form p.pot q.form q.pot) := by
  refine ⟨⟨fun h => h.sameCurrent, fun h => ?_⟩, ⟨fun h => ?_, fun h => h.weak⟩⟩
  · obtain ⟨f, hf, hS, hψ⟩ := (sameCurrent_iff omega Y p q).mp h
    exact SpaceForm.sameCurrentRe_of_eq_add p.psh hf hS hψ
  · obtain ⟨f, hf, hS, hψ⟩ :=
      h.exists_smooth (CurrentPresentation.dense omega Y p) p.psh.ne_top
    exact SpaceForm.sameCurrent_of_eq_add p.psh hf hS hψ

/-- **Pull-back to resolutions**: if `θ̃₁ + dd^c ψ₁ = θ̃₂ + dd^c ψ₂` on `Ỹ`, then on every resolution
`ν : V → Ỹ` the readings of the potentials differ by a smooth function on `V` (so the pulled-back
currents agree as well). -/
theorem exists_chartSmooth_of_sameCurrent
    {p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)}
    (h : SpaceForm.SameCurrent p.form p.pot q.form q.pot)
    (N : (normalizationTildeY omega Y).Resolution) :
    ∃ g : N.R.V → ℝ, ChartSmooth (n := Y.dim) g ∧
      ∀ v, p.pot (N.ν v) = q.pot (N.ν v) + (g v : EReal) := by
  obtain ⟨f, hf, -, hψ⟩ := (sameCurrent_iff omega Y p q).mp h
  exact ⟨fun v => f (N.ν v), chartSmooth_comp_ν omega Y N hf, fun v => hψ (N.ν v)⟩

/-- **Equality of currents on `Ỹ`** is an equivalence relation on presentations. -/
def currentSetoid : Setoid (TildeY.CurrentPresentation (normalizationTildeY omega Y)) where
  r p q := SpaceForm.SameCurrent p.form p.pot q.form q.pot
  iseqv := ⟨fun p => SpaceForm.SameCurrent.refl p.psh, fun h => h.symm,
    fun {p q _} h₁ h₂ => SpaceForm.SameCurrent.trans p.psh (CurrentPresentation.dense omega Y p)
      p.psh.ne_top (CurrentPresentation.dense omega Y q) q.psh.ne_top h₁ h₂⟩

/-- **`𝒵₊(Ỹ)`: closed positive `(1,1)`-currents on `Ỹ`** (with local potentials, EGZ Def. 5.8):
presentations `θ̃ + dd^c ψ` modulo equality of currents. -/
def Current : Type 1 := Quotient (currentSetoid omega Y)

variable {omega Y}

/-- **The class of a presentation does not depend on the presentation of the current.** -/
theorem ofForm_eq_of_sameCurrent {p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)}
    (h : SpaceForm.SameCurrent p.form p.pot q.form q.pot) :
    H11.ofForm ⟨p.form, p.closed⟩ = H11.ofForm ⟨q.form, q.closed⟩ :=
  SpaceForm.SameCurrent.ofForm_eq (θ₁ := ⟨p.form, p.closed⟩) (θ₂ := ⟨q.form, q.closed⟩) h
    (CurrentPresentation.dense omega Y p) p.psh.ne_top

namespace Current

/-- The current `θ̃ + dd^c ψ`. -/
def mk (p : TildeY.CurrentPresentation (normalizationTildeY omega Y)) : Current omega Y :=
  Quotient.mk (currentSetoid omega Y) p

theorem mk_eq_mk_iff {p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)} :
    mk p = mk q ↔ SpaceForm.SameCurrent p.form p.pot q.form q.pot :=
  Quotient.eq

theorem mk_surjective : Function.Surjective (mk (omega := omega) (Y := Y)) :=
  Quotient.mk_surjective

/-- **The class `{S} ∈ H^{1,1}(Ỹ, ℝ)` of a closed positive current on `Ỹ`**: the class of the form
of any presentation (well defined, `ofForm_eq_of_sameCurrent`). -/
def cls (S : Current omega Y) : H11 (normalizationTildeY omega Y).space :=
  Quotient.lift (s := currentSetoid omega Y) (fun p => H11.ofForm ⟨p.form, p.closed⟩)
    (fun _ _ h => ofForm_eq_of_sameCurrent h) S

@[simp] theorem cls_mk (p : TildeY.CurrentPresentation (normalizationTildeY omega Y)) :
    (mk p).cls = H11.ofForm ⟨p.form, p.closed⟩ := rfl

end Current

/-- **Presentations of the same current have `P`-equivalent potentials**: the potentials differ
by a smooth, hence bounded, function on `Ỹ` (`sameCurrent_iff`), and so do their readings on
every resolution. -/
theorem pEquivalent_of_sameCurrent {p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)}
    (h : SpaceForm.SameCurrent p.form p.pot q.form q.pot) :
    (normalizationTildeY omega Y).PEquivalent p.pot q.pot := by
  obtain ⟨f, hf, -, hψ⟩ := (sameCurrent_iff omega Y p q).mp h
  have hp : (normalizationTildeY omega Y).IsQPSH p.pot :=
    ⟨p.form, p.closed.isClosed, p.closed.isOneOne, p.psh⟩
  have hq : (normalizationTildeY omega Y).IsQPSH q.pot :=
    ⟨q.form, q.closed.isClosed, q.closed.isOneOne, q.psh⟩
  have key : ∀ N : (normalizationTildeY omega Y).Resolution,
      SingularGlobalPOrder.SourcePOrder (n := Y.dim) (p.pot ∘ N.ν) (q.pot ∘ N.ν) ∧
        SingularGlobalPOrder.SourcePOrder (n := Y.dim) (q.pot ∘ N.ν) (p.pot ∘ N.ν) := by
    intro N
    obtain ⟨σp, hσp⟩ := isThetaPshPotential_comp_of_isQPSH omega Y hp N
    obtain ⟨σq, hσq⟩ := isThetaPshPotential_comp_of_isQPSH omega Y hq N
    have hcont : Continuous fun v => f (N.ν v) := hf.continuous.comp N.continuous
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ v, |f (N.ν v)| ≤ C := by
      obtain ⟨v₀, -, hv₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
        (continuous_abs.comp hcont).continuousOn
      exact ⟨_, fun v => hv₀ (mem_univ v)⟩
    refine ⟨GlobalQuasiPshPositivePDomain.sourcePOrder_of_moreSingularOn_globalQuasiPsh
        N.R.kahler hσp.quasiPshPotential hσq.quasiPshPotential ⟨C, fun v _ => ?_⟩,
      GlobalQuasiPshPositivePDomain.sourcePOrder_of_moreSingularOn_globalQuasiPsh
        N.R.kahler hσq.quasiPshPotential hσp.quasiPshPotential ⟨C, fun v _ => ?_⟩⟩
    · change p.pot (N.ν v) ≤ q.pot (N.ν v) + (C : EReal)
      rw [hψ]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_trans (le_abs_self _) (hC v)))
    · change q.pot (N.ν v) ≤ p.pot (N.ν v) + (C : EReal)
      rw [hψ, add_assoc, ← EReal.coe_add]
      have h0 : (0 : ℝ) ≤ f (N.ν v) + C := by
        have := neg_abs_le (f (N.ν v))
        linarith [hC v]
      calc q.pot (N.ν v) = q.pot (N.ν v) + ((0 : ℝ) : EReal) := by
            rw [EReal.coe_zero, add_zero]
        _ ≤ q.pot (N.ν v) + ((f (N.ν v) + C : ℝ) : EReal) :=
            add_le_add le_rfl (EReal.coe_le_coe_iff.mpr h0)
  exact ⟨fun N => (key N).1, fun N => (key N).2⟩

/-- **Whether a presentation represents `Tr_Y(Tc)` only depends on the current.** -/
theorem isTrace_iff_of_sameCurrent {p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)}
    (h : SpaceForm.SameCurrent p.form p.pot q.form q.pot) (φ : X → EReal) :
    (normalizationTildeY omega Y).IsTrace φ p.pot ↔
      (normalizationTildeY omega Y).IsTrace φ q.pot := by
  have hP := pEquivalent_of_sameCurrent h
  constructor
  · intro hp
    exact IsTrace.of_pEquivalent omega Y hp
      ⟨q.form, q.closed.isClosed, q.closed.isOneOne, q.psh⟩ hP
  · intro hq
    exact IsTrace.of_pEquivalent omega Y hq
      ⟨p.form, p.closed.isClosed, p.closed.isOneOne, p.psh⟩ ⟨hP.2, hP.1⟩

namespace Current

/-- **`S` represents `Tr_Y(Tc)`**: a potential of `S` (that of any presentation, well defined by
`isTrace_iff_of_sameCurrent`) is a trace operator of the potential of `Tc ∈ 𝒵₊(X)`. -/
def RepresentsTrace (S : Current omega Y) (Tc : ClosedPositiveCurrent m X) : Prop :=
  Quotient.lift (s := currentSetoid omega Y)
    (fun p => (normalizationTildeY omega Y).IsTrace (presentationPotential Tc) p.pot)
    (fun _ _ h => propext (isTrace_iff_of_sameCurrent h _)) S

@[simp] theorem representsTrace_mk (p : TildeY.CurrentPresentation (normalizationTildeY omega Y))
    (Tc : ClosedPositiveCurrent m X) :
    (mk p).RepresentsTrace Tc ↔
      (normalizationTildeY omega Y).IsTrace (presentationPotential Tc) p.pot := Iff.rfl

/-- **Source `rmk:tracecurrent`: `S` is a `Tr^β_Y(Tc)`**: the closed positive `(1,1)`-current `S`
on `Ỹ` lies in the class `β ∈ H^{1,1}(Ỹ, ℝ)` and represents `Tr_Y(Tc)`. -/
def IsTr (Tc : ClosedPositiveCurrent m X) (β : H11 (normalizationTildeY omega Y).space)
    (S : Current omega Y) : Prop :=
  S.cls = β ∧ S.RepresentsTrace Tc

/-- **`Tr^β_Y(Tc)` on currents is the presentation-level notion of lane TY2**: for every
presentation `θ̃ + dd^c ψ` of `S`, `S` is a `Tr^β_Y(Tc)` iff `TildeY.IsTraceCurrentIn Tc β θ̃ ψ`. -/
theorem isTr_mk_iff (Tc : ClosedPositiveCurrent m X) (β : H11 (normalizationTildeY omega Y).space)
    (p : TildeY.CurrentPresentation (normalizationTildeY omega Y)) :
    IsTr Tc β (mk p) ↔ (normalizationTildeY omega Y).IsTraceCurrentIn Tc β p.form p.pot := by
  constructor
  · rintro ⟨hβ, hT⟩
    exact ⟨p.closed, hβ, p.psh, hT⟩
  · rintro ⟨hθ, hβ, -, hT⟩
    exact ⟨hβ, hT⟩

/-- A `Tr^β_Y(Tc)` exists only when `ν(Tc, Y) = 0`. -/
theorem IsTr.sourceGenericLelong_eq_zero {Tc : ClosedPositiveCurrent m X}
    {β : H11 (normalizationTildeY omega Y).space} {S : Current omega Y} (h : IsTr Tc β S) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0 := by
  obtain ⟨p, rfl⟩ := mk_surjective S
  exact ((isTr_mk_iff Tc β p).mp h).sourceGenericLelong_eq_zero

/-- **Any two currents representing `Tr_Y(Tc)`** (in any classes) have `𝓘`-good `P`-equivalent
potentials (for all presentations). -/
theorem IsTr.pEquivalent {Tc : ClosedPositiveCurrent m X}
    {β₁ β₂ : H11 (normalizationTildeY omega Y).space}
    {p q : TildeY.CurrentPresentation (normalizationTildeY omega Y)}
    (h₁ : IsTr Tc β₁ (mk p)) (h₂ : IsTr Tc β₂ (mk q)) :
    (normalizationTildeY omega Y).IGood p.pot ∧ (normalizationTildeY omega Y).IGood q.pot ∧
      (normalizationTildeY omega Y).PEquivalent p.pot q.pot :=
  ((isTr_mk_iff Tc β₁ p).mp h₁).pEquivalent ((isTr_mk_iff Tc β₂ q).mp h₂)

/-- **The currents `Tr^β_Y(Tc)`**: given one, `S'` is a `Tr^β_Y(Tc)` iff `{S'} = β` and the
potentials of `S` and `S'` are `P`-equivalent. -/
theorem isTr_iff {Tc : ClosedPositiveCurrent m X} {β : H11 (normalizationTildeY omega Y).space}
    {p : TildeY.CurrentPresentation (normalizationTildeY omega Y)} (h : IsTr Tc β (mk p))
    (q : TildeY.CurrentPresentation (normalizationTildeY omega Y)) :
    IsTr Tc β (mk q) ↔ (mk q).cls = β ∧ (normalizationTildeY omega Y).PEquivalent p.pot q.pot := by
  rw [isTr_mk_iff, isTraceCurrentIn_iff omega Y ((isTr_mk_iff Tc β p).mp h)]
  constructor
  · rintro ⟨hθ, hβ, -, hP⟩
    exact ⟨hβ, hP⟩
  · rintro ⟨hβ, hP⟩
    exact ⟨q.closed, hβ, q.psh, hP⟩

/-- **Existence**: if `ν(Tc, Y) = 0` and `Tc = θ + dd^c φ`, then for every Kähler form `ω` on `X`
there is a closed positive current on `Ỹ` which is a `Tr^β_Y(Tc)` for `β = {(θ + ω)|_Ỹ}`. -/
theorem exists_isTr (Tc : ClosedPositiveCurrent m X) {θ : ClosedRealOneOneForm (m + 1) X}
    {φ : X → EReal} (hp : IsPresentation Tc θ φ) (om : KahlerBackground (m + 1) X)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) X).sourceGenericLelong
      (presentationPotential Tc) Y.carrier = 0) :
    ∃ S : Current omega Y, IsTr Tc
      (H11.ofForm ⟨_, restrict_isLocallyClosedOneOne omega Y (θ + om.form)⟩) S := by
  obtain ⟨ψ, hθ, hβ, hψ, hT⟩ := exists_isTraceCurrentIn omega Y Tc hp om hν
  exact ⟨mk ⟨_, ψ, hθ, hψ⟩, hβ, hT⟩

end Current

end Normalization

end SGPT.Trace.TY
