import SGPT.NPP.Capacity2Comparison
import SGPT.PSH.SourceQuasiContinuity
import SGPT.Foundations.Analysis.Pending.PoleCoalescingCapacity
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

/-!
# Quasi-continuity of quasi-psh functions and of their differences (global case)

Source `ex:psh_qc` (chapter `chapter_npp.tex`, section `sec:qc`): a quasi-psh function is
quasi-continuous (`def:qc_fun`), and so is the difference

  `f(x) = φ(x) - ψ(x)` if `(φ ∨ ψ)(x) ≠ -∞`,  `f(x) = +∞` otherwise

of two quasi-psh functions `φ, ψ`.  This file proves both claims for quasi-psh functions
defined on all of the compact Kähler manifold `X` (and their restrictions to any open
`U ⊆ X`), with the capacity `Cap_θ` of an arbitrary big reference form `θ`
(`SourceQuasiContinuousOn`, the literal `def:qc_fun`: Borel measurability and, for every
`ε > 0`, an open `G ⊆ U` with `Cap_θ(G) ≤ ε` off which `f` is real-valued and continuous).

Proof: a global quasi-psh `u` is `Cω`-psh for some `C > 0`; after normalization it is a
nonpositive `ω`-psh function, whose real part is quasi-continuous for the Kähler capacity
(`PoleCoalescingCapacity.quasiContinuousFor_toReal_of_le_zero`, Bedford--Taylor in charts plus
the Guedj--Zeriahi sublevel estimate).  The pole set is pluripolar, hence of outer Kähler
capacity zero (`PluripolarOuterCapacity.outerCapacityZero_of_manifoldLocallyPluripolar`), so it
can be put inside the exceptional open set.  Finally the Kähler capacity controls `Cap_θ`
(`exists_source_capacity_control_by_kahler`, the half of `thm:comp_capa` proved in
`Capacity2Comparison`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity CapacityWeightedConvergence PluripolarOuterCapacity PluripolarCapacityZero
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Real form of a normalized potential. -/
theorem toReal_normalized {C b : ℝ} {v : EReal} (hvt : v ≠ ⊤) (hvb : v ≠ ⊥) :
    (((C⁻¹ : ℝ) : EReal) * (v - (b : EReal))).toReal = C⁻¹ * (v.toReal - b) := by
  have he : ((C⁻¹ * (v.toReal - b) : ℝ) : EReal) =
      ((C⁻¹ : ℝ) : EReal) * (v - (b : EReal)) := by
    rw [EReal.coe_mul, EReal.coe_sub, EReal.coe_toReal hvt hvb]
  rw [← he, EReal.toReal_coe]

/-- **Kähler-capacity quasi-continuity of a global quasi-psh function, with its poles inside
the exceptional set.**  For every `η > 0` there is an open `G` of Kähler capacity `< η` with
`u` finite and (in its real form) continuous on `X \ G`. -/
theorem exists_isOpen_kahlerCapacity_lt_finite_continuousOn (ω : KahlerBackground n M)
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity ω.form (fun _ => 0) G < η ∧
      (∀ x, x ∉ G → u x ≠ ⊥) ∧ ContinuousOn (fun x => (u x).toReal) Gᶜ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨∅, isOpen_empty, by simpa using hη, fun x => isEmptyElim x, ?_⟩
    intro x; exact isEmptyElim x
  obtain ⟨C, hC, huC⟩ := GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul ω hu
  obtain ⟨b, hb⟩ := huC.exists_global_upper_bound
  let q : M → EReal := fun x => ((C⁻¹ : ℝ) : EReal) * (u x - (b : EReal))
  have hq : IsThetaPshPotential ω.form.val q := by
    have h := PotentialMassComparison.isThetaPshPotential_smul (huC.sub_const b) (inv_pos.mpr hC)
    have he : C⁻¹ • (C • ω.form) = ω.form := by
      rw [smul_smul, inv_mul_cancel₀ hC.ne', one_smul]
    simpa only [he] using h
  have hq0 : q ≤ 0 := by
    intro x
    exact EReal.mul_nonpos_iff.mpr (Or.inl
      ⟨EReal.coe_nonneg.mpr (inv_pos.mpr hC).le, EReal.sub_nonpos.mpr (hb x)⟩)
  have hqc := PoleCoalescingCapacity.quasiContinuousFor_toReal_of_le_zero ω ω.isSemipositive hq hq0
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨G₁, hG₁o, hG₁c, hG₁f⟩ := hqc (η / 2) hη2
  obtain ⟨G₂, hG₂o, hpG₂, hG₂c⟩ := outerCapacityZero_of_manifoldLocallyPluripolar ω
    (quasiPsh_poles_manifoldLocallyPluripolar hu) (η / 2) hη2
  refine ⟨G₁ ∪ G₂, hG₁o.union hG₂o, ?_, ?_, ?_⟩
  · calc thetaCapacity ω.form (fun _ => 0) (G₁ ∪ G₂)
        ≤ thetaCapacity ω.form (fun _ => 0) G₁ + thetaCapacity ω.form (fun _ => 0) G₂ :=
          thetaCapacity_union_le _ _ _ _
      _ < η / 2 + η / 2 := ENNReal.add_lt_add hG₁c hG₂c
      _ = η := ENNReal.add_halves η
  · intro x hx hbot
    exact hx (Or.inr (hpG₂ hbot))
  · have hcont : ContinuousOn (fun x => b + C * (q x).toReal) (G₁ ∪ G₂)ᶜ :=
      continuousOn_const.add (continuousOn_const.mul
        (hG₁f.mono (compl_subset_compl.mpr subset_union_left)))
    refine hcont.congr ?_
    intro x hx
    have hxb : u x ≠ ⊥ := fun hbot => hx (Or.inr (hpG₂ hbot))
    have hxt : u x ≠ ⊤ := huC.1.quasiPlurisubharmonic.ne_top x
    change (u x).toReal = b + C * (q x).toReal
    rw [show q x = ((C⁻¹ : ℝ) : EReal) * (u x - (b : EReal)) from rfl,
      toReal_normalized hxt hxb]
    field_simp
    ring

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A source quasi-psh function on `X` (`def:qpsh`: `θ'`-psh for some closed smooth real
`(1,1)`-form `θ'`) is a global quasi-psh potential. -/
theorem isGlobalQuasiPshPotential_of_isQPSH {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ', hθ'⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ' u).mp hθ').quasiPshPotential

/-- Kähler capacity controls the source capacity of a big form on open sets: the open sets of
`exists_isOpen_kahlerCapacity_lt_finite_continuousOn` can be taken of `Cap_θ ≤ ε`. -/
theorem exists_isOpen_sourceCapacity_le_finite_continuousOn (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set M, IsOpen G ∧ sourceThetaCapacity θ G ≤ ENNReal.ofReal ε ∧
      (∀ x, x ∉ G → u x ≠ ⊥) ∧ ContinuousOn (fun x => (u x).toReal) Gᶜ := by
  obtain ⟨C, hC, hctl⟩ := exists_source_capacity_control_by_kahler ω θ hbig (half_pos hε)
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2 / C) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ := exists_isOpen_kahlerCapacity_lt_finite_continuousOn ω hu hη
  refine ⟨G, hGo, ?_, hGf, hGcont⟩
  calc sourceThetaCapacity θ G
      ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C *
          sourceThetaCapacity (nativeClosedFormToAtlas ω.form) G := hctl G
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal C * ENNReal.ofReal (ε / 2 / C) := by
        rw [sourceThetaCapacity_kahler]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hGc.le zero_le)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne',
          ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

omit [BorelSpace M] in
/-- Literal `def:qc_fun` from a single open exceptional set (shrunk into `U`). -/
theorem sourceQuasiContinuousOn_of_forall (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) {f : U → EReal} (hf : Measurable f)
    (h : ∀ ε : ℝ, 0 < ε → ∃ G : Set M, IsOpen G ∧ sourceThetaCapacity θ G ≤ ENNReal.ofReal ε ∧
      ∃ g : M → ℝ, ContinuousOn g Gᶜ ∧ ∀ x : U, x.1 ∉ G → f x = (g x.1 : EReal)) :
    SourceQuasiContinuousOn θ U f := by
  refine ⟨hf, fun ε hε => ?_⟩
  obtain ⟨G, hGo, hGc, g, hg, hfg⟩ := h ε hε
  refine ⟨G ∩ U, hGo.inter U.isOpen, inter_subset_right,
    (sourceThetaCapacity_mono θ inter_subset_left).trans hGc, fun x => g x.1, ?_, ?_⟩
  · intro x hx
    have hxG : x.1 ∉ G := fun hG => hx ⟨hG, x.2⟩
    exact ((hg x.1 hxG).comp continuous_subtype_val.continuousWithinAt
      (fun y hy => fun hG => hy ⟨hG, y.2⟩))
  · intro x hx
    exact hfg x (fun hG => hx ⟨hG, x.2⟩)

/-- A global quasi-psh potential is Borel measurable. -/
theorem measurable_of_isGlobalQuasiPshPotential (ω : KahlerBackground n M) {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) : Measurable u := by
  obtain ⟨C, _hC, huC⟩ := GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul ω hu
  exact huC.1.quasiPlurisubharmonic.upperSemicontinuous.measurable

/-- **Source `ex:psh_qc`, first claim (global quasi-psh functions).**  A quasi-psh function
`u` on the compact Kähler manifold `X` (`def:qpsh`) is quasi-continuous on every open `U ⊆ X`
(in particular on `U = X`) for the capacity of any big reference form `θ`. -/
theorem sourceQuasiContinuousOn_of_isQPSH (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {u : M → EReal} (hu : (ofFixedModel n M).IsQPSH u) :
    SourceQuasiContinuousOn θ U (fun x => u x.1) := by
  have hq := isGlobalQuasiPshPotential_of_isQPSH hu
  refine sourceQuasiContinuousOn_of_forall θ U
    ((measurable_of_isGlobalQuasiPshPotential ω hq).comp measurable_subtype_coe) fun ε hε => ?_
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hq hε
  refine ⟨G, hGo, hGc, fun x => (u x).toReal, hGcont, fun x hx => ?_⟩
  exact (EReal.coe_toReal (hq.1.ne_top x.1) (hGf x.1 hx)).symm

/-- The source's difference of two quasi-psh functions (`ex:psh_qc`): `φ - ψ` where
`φ ∨ ψ ≠ -∞`, and `+∞` where both functions are `-∞`. -/
def qpshDifference {X : Type*} (φ ψ : X → EReal) : X → EReal := fun x =>
  if max (φ x) (ψ x) ≠ ⊥ then φ x - ψ x else ⊤

/-- Off the poles of both functions the difference is the real difference. -/
theorem qpshDifference_eq_coe {X : Type*} {φ ψ : X → EReal} {x : X}
    (hφt : φ x ≠ ⊤) (hφb : φ x ≠ ⊥) (hψt : ψ x ≠ ⊤) (hψb : ψ x ≠ ⊥) :
    qpshDifference φ ψ x = (((φ x).toReal - (ψ x).toReal : ℝ) : EReal) := by
  have hmax : max (φ x) (ψ x) ≠ ⊥ := fun h => hφb (le_bot_iff.mp (h ▸ le_max_left _ _))
  simp only [qpshDifference, hmax, ne_eq, not_false_eq_true, if_true]
  rw [EReal.coe_sub, EReal.coe_toReal hφt hφb, EReal.coe_toReal hψt hψb]

/-- The difference of two Borel functions is Borel. -/
theorem measurable_qpshDifference {X : Type*} [MeasurableSpace X] {φ ψ : X → EReal}
    (hφ : Measurable φ) (hψ : Measurable ψ) : Measurable (qpshDifference φ ψ) := by
  classical
  have hs : MeasurableSet {x | max (φ x) (ψ x) ≠ ⊥} :=
    (measurableSet_singleton (⊥ : EReal)).compl.preimage (hφ.max hψ)
  have hsub : Measurable fun x => φ x - ψ x := by
    have h : Measurable fun x => φ x + -(ψ x) := hφ.add hψ.neg
    simpa only [sub_eq_add_neg] using h
  exact Measurable.ite hs hsub measurable_const

/-- **Source `ex:psh_qc`, second claim (global quasi-psh functions).**  For quasi-psh `φ, ψ`
on `X`, the function equal to `φ - ψ` where `φ ∨ ψ ≠ -∞` and to `+∞` elsewhere is
quasi-continuous on every open `U ⊆ X`, for the capacity of any big reference form. -/
theorem sourceQuasiContinuousOn_qpshDifference (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {φ ψ : M → EReal} (hφ : (ofFixedModel n M).IsQPSH φ)
    (hψ : (ofFixedModel n M).IsQPSH ψ) :
    SourceQuasiContinuousOn θ U (fun x => qpshDifference φ ψ x.1) := by
  have hqφ := isGlobalQuasiPshPotential_of_isQPSH hφ
  have hqψ := isGlobalQuasiPshPotential_of_isQPSH hψ
  refine sourceQuasiContinuousOn_of_forall θ U
    ((measurable_qpshDifference (measurable_of_isGlobalQuasiPshPotential ω hqφ)
      (measurable_of_isGlobalQuasiPshPotential ω hqψ)).comp measurable_subtype_coe)
    fun ε hε => ?_
  obtain ⟨G, hGo, hGc, hGf, hGcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hqφ (half_pos hε)
  obtain ⟨H, hHo, hHc, hHf, hHcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hqψ (half_pos hε)
  refine ⟨G ∪ H, hGo.union hHo, ?_, fun x => (φ x).toReal - (ψ x).toReal, ?_, ?_⟩
  · calc sourceThetaCapacity θ (G ∪ H)
        ≤ sourceThetaCapacity θ G + sourceThetaCapacity θ H := sourceThetaCapacity_union_le θ G H
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hGc hHc
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  · exact (hGcont.mono (compl_subset_compl.mpr subset_union_left)).sub
      (hHcont.mono (compl_subset_compl.mpr subset_union_right))
  · intro x hx
    have hxG : x.1 ∉ G := fun h => hx (Or.inl h)
    have hxH : x.1 ∉ H := fun h => hx (Or.inr h)
    exact qpshDifference_eq_coe (hqφ.1.ne_top x.1) (hGf x.1 hxG) (hqψ.1.ne_top x.1)
      (hHf x.1 hxH)

end SGPT.NPP
