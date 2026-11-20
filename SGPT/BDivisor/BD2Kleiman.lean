import SGPT.BDivisor.BD2KleimanSlots
import SGPT.BDivisor.BD2NefRestrictedVolume
import SGPT.BDivisor.BDBlowupProjective
import SGPT.BDivisor.BDNumericalClasses
import SGPT.BDivisor.WeilBDivisor
import SGPT.BDivisor.MassPushforwardClassVolume
import SGPT.Foundations.Analysis.Pending.SmoothComponentReduction
import SGPT.Foundations.Analysis.Pending.NakamayeMainTheorem
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.Okounkov.TranscendentalVolumeConcavityContinuity

/-!
# Kleiman's criterion: curve-nef Néron–Severi classes are nef

Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef b-divisors are introduced by
Dang--Favre [DF20] [...] our transcendental intersection theory coincides with theirs in the
algebraic setting."  Dang–Favre's nef classes in `N¹(Y)_ℝ` are the classes with nonnegative
degree on every curve; the book's nef classes are the nef `(1,1)`-classes.  Read through the
cycle class map `N¹(Y)_ℝ ≃ NS(Y)_ℝ`, the two notions agree by Kleiman's criterion:

* `nefWithRespectTo_of_curveNef`, `classNef_of_isCurveNef` (**Kleiman**): on a compact connected
  projective manifold `Y`, a class `α ∈ NS(Y)_ℝ` with `∫_C g^*α ≥ 0` for every holomorphic map
  `g : C → Y` from a compact connected Riemann surface is nef; with
  `DFAlg.isCurveNef_of_classNef` this gives `isCurveNef_iff_classNef` on `NS(Y)_ℝ`.

The proof is transcendental: Kleiman's argument with Nakai–Moishezon replaced by the
transcendental Nakamaye theorem of Collins–Tosatti (`SGPT.Foundations.Analysis`).  Fix a Kähler form
`θ_h` with class in `NS(Y)_ℝ` and let `t₀ = min {t ≥ 0 : α + tθ_h nef}`.  If `t₀ > 0`, then
`β = α + t₀θ_h` is nef and
* for every positive-dimensional closed connected submanifold `W` of a modification `μ : Ỹ → Y`
  with `⟨(μ^*θ_h)^{dim W}⟩_{Ỹ|W} > 0`, the restricted volume
  `⟨(μ^*β)^{dim W}⟩_{Ỹ|W} = ∫_W (μ^*β)^{dim W} ≥ t₀^{dim W} ∫_W (μ^*θ_h)^{dim W} > 0`
  (`numericalRestrictedVolume_pos_of_curveNef`: restricted volumes of nef classes on smooth
  submanifolds are intersection numbers, `BD2NefRestrictedVolume`; the inequality is the
  polynomial step of Kleiman's argument, `BD2KleimanSlots.slotIntegral_pullback_le`, which uses
  complete-intersection curves on `W`);
* with `W = Y` this shows that `β` is big; if `E_nK(β) ≠ ∅`, a positive-dimensional component
  `V` has zero restricted volume (Collins–Tosatti, `ComponentVanishing`), and its strict transform
  `W` in an embedded resolution (`SmoothComponentReduction`) contradicts the previous point;
* so `E_nK(β) = ∅`: `β` contains a Kähler current with bounded potential, hence a Kähler form,
  and `α + (t₀ - δ)θ_h` is still nef for small `δ > 0`, contradicting the minimality of `t₀`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.BDivisor.Kleiman

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldMassCalculus
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Projective.NumEq SGPT.Projective.NumEq.CompleteIntersections
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open ManifoldTubePositivity

section Helpers

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A form `θ` with `θ + εω + ddᶜf_ε ≥ 0` for every `ε > 0` is nef. -/
theorem nefWithRespectTo_of_forall_isSemipositive (omega : KahlerBackground n X)
    {θ : ClosedRealOneOneForm n X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (f : X → ℝ) (hf : ChartSmooth (n := n) f),
      (θ + ε • omega.form + ddcClosedForm f hf).val.IsSemipositive) :
    NefWithRespectTo omega θ := by
  intro ε hε
  obtain ⟨f, hf, hsemi⟩ := h ε hε
  refine ⟨f, hf, fun e z hz v => ?_⟩
  have h1 := hsemi e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ddcClosedForm_coeff, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
  linarith

omit [IsComplexManifold n X] in
/-- **A potential with analytic singularities and no poles is bounded below** (compact `X`). -/
theorem exists_lower_bound_of_poleSet_eq_empty [CompactSpace X] {u : X → EReal}
    (hu : HasManifoldAnalyticSingularityType (n := n) u) (hpole : poleSet u = ∅) :
    ∃ C : ℝ, ∀ x, (C : EReal) ≤ u x := by
  have hloc : ∀ p : X, ∃ L : ℝ, ∀ᶠ y in 𝓝 p, (L : EReal) ≤ u y := by
    intro p
    let e := complexChartAt (n := n) p
    have hpe : p ∈ e.val.source := mem_complexChartAt_source p
    have hz : e.val p ∈ e.val.target := e.val.map_source hpe
    obtain ⟨c, k, f, hc, ⟨U, hUo, hzU, hf⟩, b, ⟨C, -, hb⟩, heq⟩ := hu e (e.val p) hz
    have hup : u p ≠ ⊥ := fun h => (Set.eq_empty_iff_forall_notMem.mp hpole) p h
    have hchart : chartFunction u e (e.val p) = u p := by
      simp only [chartFunction, e.val.left_inv hpe]
    obtain ⟨j, hj⟩ : ∃ j, f j (e.val p) ≠ 0 := by
      by_contra! hall
      apply hup
      rw [← hchart, heq.eq_of_nhds]
      exact (scaled_generatorLog_add_eq_bot_iff f _ hc (b _)).mpr hall
    have hcont : ContinuousAt (f j) (e.val p) :=
      ((hf j).differentiableAt (hUo.mem_nhds hzU)).continuousAt
    have hnorm : 0 < ‖f j (e.val p)‖ := norm_pos_iff.mpr hj
    set r := ‖f j (e.val p)‖ / 2 with hrdef
    have hr : 0 < r := half_pos hnorm
    have hev : ∀ᶠ w in 𝓝 (e.val p), r < ‖f j w‖ :=
      hcont.norm.eventually (lt_mem_nhds (half_lt_self hnorm))
    have hw : ∀ᶠ w in 𝓝 (e.val p),
        ((c * Real.log (r ^ 2) - C : ℝ) : EReal) ≤ chartFunction u e w := by
      filter_upwards [heq, hb, hev] with w hw hbw hfw
      rw [hw]
      have hnz : ∃ i, f i w ≠ 0 := ⟨j, fun h => by rw [h, norm_zero] at hfw; linarith⟩
      rw [generatorLog_of_nonzero hnz, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hsq : r ^ 2 ≤ generatorNormSq f w := by
        calc r ^ 2 ≤ ‖f j w‖ ^ 2 := by gcongr
          _ ≤ ∑ i, ‖f i w‖ ^ 2 :=
            Finset.single_le_sum (fun i _ => sq_nonneg ‖f i w‖) (Finset.mem_univ j)
      have hlog : Real.log (r ^ 2) ≤ Real.log (generatorNormSq f w) :=
        Real.log_le_log (by positivity) hsq
      have hbw' := (abs_le.mp hbw).1
      nlinarith [mul_le_mul_of_nonneg_left hlog hc.le]
    have htend : Tendsto e.val (𝓝 p) (𝓝 (e.val p)) := e.val.continuousAt hpe
    refine ⟨c * Real.log (r ^ 2) - C, ?_⟩
    filter_upwards [htend.eventually hw, e.val.open_source.mem_nhds hpe] with y hy hys
    simpa only [chartFunction, e.val.left_inv hys] using hy
  choose L hL using hloc
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover
    (fun p => {y | (L p : EReal) ≤ u y}) (fun p _ => hL p)
  obtain ⟨C, hC⟩ := (t.image L).bddBelow
  refine ⟨C, fun x => ?_⟩
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcover (mem_univ x))
  exact le_trans (EReal.coe_le_coe_iff.mpr (hC (Finset.mem_image_of_mem L hp))) hxp

/-- **A Kähler current with bounded potential makes its class Kähler.** -/
theorem exists_kahler_of_kahlerCurrent_of_bounded [CompactSpace X] {α : RealBottChern n X}
    (T : KahlerCurrent α) (hb : IsBoundedPotential T.potential) :
    ∃ κ : KahlerBackground n X, RealBottChern.ofRepresentative κ.form = α := by
  have hnef := DominationIntersectionNumbers.nefWithRespectTo_of_isBoundedPotential
    T.lowerBound T.strictlyPsh.1 hb
  obtain ⟨f, hf, hK⟩ := exists_isKahler_add_ddc_of_nef T.lowerBound hnef one_pos
  have heq : T.representative - T.lowerBound.form + (1 : ℝ) • T.lowerBound.form +
      ddcClosedForm f hf = T.representative + ddcClosedForm f hf := by
    rw [one_smul, sub_add_cancel]
  rw [heq] at hK
  refine ⟨⟨_, hK⟩, ?_⟩
  change RealBottChern.ofRepresentative (T.representative + ddcClosedForm f hf) = α
  rw [SGPT.Okounkov.TranscendentalLifting.ofRepresentative_add_ddc, T.represents]

/-- Slot integrals of constant tuples are homogeneous. -/
theorem slotIntegral_const_smul [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (κ : KahlerBackground n X) (c : ℝ) (x : ClosedRealOneOneForm n X) :
    slotIntegral κ (fun _ : Fin n => c • x) = c ^ n * slotIntegral κ (fun _ => x) := by
  have h := (slotIntegralMultilinear κ).map_smul_univ (fun _ => c) (fun _ => x)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  exact h

end Helpers

section Positivity

variable {m : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y]

omit [CompactSpace Y] in
/-- **Positivity of restricted volumes of `α + t₀θ_h` on smooth submanifolds of modifications.**
Let `θ_α` be curve-nef on `Y`, `θ_h` a Kähler form, `t₀ > 0` with `θ_α + t₀θ_h` nef, and assume
the classes `{θ_h + εθ_h}`, `{θ_h + t₀⁻¹θ_α + εθ_h}` are ample for `ε > 0`.  If `μ : Ỹ → Y` is a
holomorphic map from a compact manifold carrying a positive line bundle and `W ⊆ Ỹ` a closed
connected submanifold on which `μ^*θ_h` has positive restricted volume, then so does
`μ^*(θ_α + t₀θ_h)`. -/
theorem numericalRestrictedVolume_pos_of_curveNef
    {Xt : Type} [TopologicalSpace Xt] [ChartedSpace (ComplexModel (m + 1)) Xt]
    [IsComplexManifold (m + 1) Xt] [CompactSpace Xt]
    (A : NativePositiveLine (m + 1) Xt) (ωt : KahlerBackground (m + 1) Xt)
    {μ : Xt → Y} (hμ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ μ)
    (ωh : KahlerBackground (m + 1) Y) (θα : ClosedRealOneOneForm (m + 1) Y)
    (hα : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C)
      (g : C → Y) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g),
      0 ≤ degreeAlong κ hg θα)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hβ : NefWithRespectTo ωh (θα + t₀ • ωh.form))
    (hamp₀ : ∀ ε : ℝ, 0 < ε →
      DFAlg.IsAmpleRealClass (RealBottChern.ofRepresentative (ωh.form + ε • ωh.form)))
    (hamp₁ : ∀ ε : ℝ, 0 < ε → DFAlg.IsAmpleRealClass
      (RealBottChern.ofRepresentative ((ωh.form + t₀⁻¹ • θα) + ε • ωh.form)))
    (W : ClosedIrreducibleAnalyticSubvariety (m + 1) Xt)
    (hW : IsClosedConnectedSubmanifold (m + 1) W.carrier W.dim)
    (hb : 0 < numericalRestrictedVolume ωt
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hμ ωh.form)) W) :
    0 < numericalRestrictedVolume ωt
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hμ (θα + t₀ • ωh.form))) W := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  have hWr := hW.2.2
  let := chartedSpace hk hWr
  have := isComplexManifold_chartedSpace hk hWr
  let : MeasurableSpace W.carrier := borel _
  have : BorelSpace W.carrier := ⟨rfl⟩
  have : CompactSpace W.carrier := compactSpace_of_isClosed hW.1
  have hval := contMDiff_val hk hWr
  let ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hWr ωt
  have hψ := hμ.comp hval
  -- restricted volumes of pulled-back nef classes are intersection numbers on `W`
  have hcomp : ∀ θ : ClosedRealOneOneForm (m + 1) Y,
      slotIntegral ωV (fun _ => ClosedRealOneOneForm.pullback hval
        (ClosedRealOneOneForm.pullback hμ θ)) =
      slotIntegral ωV (fun _ => ClosedRealOneOneForm.pullback hψ θ) := by
    intro θ
    refine slotIntegral_eq_of_bottChernRel ωV _ _ (fun _ => ?_)
    exact (ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
      (FormPullbackCompMixed.pullback_comp_geometricallyEq hμ hval θ.val)).symm
  have hn : 0 < m + 1 := Nat.succ_pos m
  have hRVh := numericalRestrictedVolume_eq_ofReal_of_nef hn ωt
    (ClosedRealOneOneForm.pullback hμ ωh.form)
    (nefWithRespectTo_of_semipositive ωt (ClosedRealOneOneForm.pullback_isSemipositive hμ
      (KahlerBackground.isSemipositive ωh))) W hW
  have hRVβ := numericalRestrictedVolume_eq_ofReal_of_nef hn ωt
    (ClosedRealOneOneForm.pullback hμ (θα + t₀ • ωh.form))
    (SGPT.BDivisor.nefWithRespectTo_pullback hμ ωh ωt hβ) W hW
  have hb' : 0 < slotIntegral ωV (fun _ => ClosedRealOneOneForm.pullback hψ ωh.form) := by
    have h1 := hb
    rw [hRVh] at h1
    have h2 := ENNReal.ofReal_pos.mp h1
    rw [← hcomp]
    exact h2
  rw [hRVβ, ENNReal.ofReal_pos]
  suffices key : 0 < slotIntegral ωV
      (fun _ => ClosedRealOneOneForm.pullback hψ (θα + t₀ • ωh.form)) by
    rw [← hcomp] at key
    exact key
  -- curve-nefness of `ψ^*θ_α` on `W`
  have ha : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κC : KahlerBackground 1 C)
      (g : C → W.carrier) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel W.dim) ∞ g),
      0 ≤ degreeAlong κC hg (ClosedRealOneOneForm.pullback hψ θα) := by
    intro C _ _ _ _ _ κC g hg
    rw [← degreeAlong_comp_actual κC hψ hg θα]
    exact hα C κC _ (hψ.comp hg)
  have hle := slotIntegral_pullback_le hψ (A.restrict hk hWr) ωV θα ωh.form
    (inv_nonneg.mpr ht₀.le) ha hamp₀ hamp₁
  dsimp only at hle
  have hform : ωh.form + t₀⁻¹ • θα = t₀⁻¹ • (θα + t₀ • ωh.form) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht₀.ne', one_smul]
    exact add_comm _ _
  have hpb : ClosedRealOneOneForm.pullback hψ (t₀⁻¹ • (θα + t₀ • ωh.form)) =
      t₀⁻¹ • ClosedRealOneOneForm.pullback hψ (θα + t₀ • ωh.form) := by
    rw [← pullbackLinear_apply hψ, map_smul, pullbackLinear_apply]
  rw [hform, hpb, slotIntegral_const_smul] at hle
  have hle' : slotIntegral ωV (fun _ => ClosedRealOneOneForm.pullback hψ ωh.form) ≤
      (t₀⁻¹) ^ W.dim * slotIntegral ωV
        (fun _ => ClosedRealOneOneForm.pullback hψ (θα + t₀ • ωh.form)) := hle
  have hpow : 0 < (t₀⁻¹) ^ W.dim := pow_pos (inv_pos.mpr ht₀) _
  by_contra! hneg
  have : (t₀⁻¹) ^ W.dim * slotIntegral ωV
      (fun _ => ClosedRealOneOneForm.pullback hψ (θα + t₀ • ωh.form)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpow.le hneg
  linarith

end Positivity

section Main

variable {m : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y]

/-- A positive Hermitian line bundle on a projective manifold. -/
theorem nonempty_nativePositiveLine_of_isProjectiveManifold {n : ℕ} {Z : Type}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace Z] (hZ : SGPT.Trace.Bertini.IsProjectiveManifold n Z) :
    Nonempty (NativePositiveLine n Z) := by
  obtain ⟨omega, hK, hNS⟩ :=
    SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp hZ
  obtain ⟨G, hG, θ, hown, hpos⟩ :=
    SGPT.BDivisor.NSKodaira.exists_positive_native_bundle_of_kahler_mem_neronSeveri omega hK hNS
  exact ⟨⟨G, hG, θ, hown, hpos⟩⟩

/-- Nef classes are pseudo-effective. -/
theorem classPseudoeffective_of_nef [ConnectedSpace Y] (ωK : KahlerBackground (m + 1) Y)
    {θ : ClosedRealOneOneForm (m + 1) Y} (hθ : NefWithRespectTo ωK θ) :
    ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) := by
  apply SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_of_forall_add_smul ωK
  intro ε hε
  obtain ⟨κ, hκ⟩ := exists_kahler_ofRepresentative_eq_of_nef ωK hθ hε
  rw [← hκ]
  exact ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff κ.form).mpr
    (KahlerBackground.isSemipositive κ)⟩

/-- **Kleiman's criterion, form version.**  On a compact connected projective manifold `Y` with
a Kähler form `θ_h` whose class lies in `NS(Y)_ℝ`, every form `θ_α` with class in `NS(Y)_ℝ` and
nonnegative degree on every compact connected curve is nef. -/
theorem nefWithRespectTo_of_curveNef [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (ωh : KahlerBackground (m + 1) Y)
    (hhNS : RealBottChern.ofRepresentative ωh.form ∈ DFAlg.neronSeveri (m + 1) Y)
    (θα : ClosedRealOneOneForm (m + 1) Y)
    (hαNS : RealBottChern.ofRepresentative θα ∈ DFAlg.neronSeveri (m + 1) Y)
    (hα : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C)
      (g : C → Y) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g),
      0 ≤ degreeAlong κ hg θα) :
    NefWithRespectTo ωh θα := by
  classical
  have hn : 0 < m + 1 := Nat.succ_pos m
  set θh := ωh.form with hθh
  have hθhsemi : θh.val.IsSemipositive := KahlerBackground.isSemipositive ωh
  -- the nef threshold
  let S : Set ℝ := {t | 0 ≤ t ∧ NefWithRespectTo ωh (θα + t • θh)}
  have hSne : S.Nonempty := by
    obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωh θα
    exact ⟨A, hA.le, nefWithRespectTo_of_semipositive ωh hsemi⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set t₀ := sInf S with ht₀def
  have ht₀nn : 0 ≤ t₀ := le_csInf hSne fun t ht => ht.1
  have hnef_gt : ∀ t, t₀ < t → NefWithRespectTo ωh (θα + t • θh) := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hSne ht
    have h := nefWithRespectTo_add ωh hs.2
      (nefWithRespectTo_of_semipositive ωh (isSemipositive_smul hθhsemi (sub_nonneg.mpr hst.le)))
    have heq : θα + s • θh + (t - s) • θh = θα + t • θh := by
      rw [add_assoc, ← add_smul, add_sub_cancel]
    rwa [heq] at h
  have hβ : NefWithRespectTo ωh (θα + t₀ • θh) := by
    apply nefWithRespectTo_of_forall_isSemipositive ωh
    intro ε hε
    obtain ⟨f, hf, hsemi⟩ :=
      exists_isSemipositive_of_nef (hnef_gt (t₀ + ε / 2) (by linarith)) (half_pos hε)
    refine ⟨f, hf, ?_⟩
    have heq : θα + (t₀ + ε / 2) • θh + (ε / 2) • ωh.form + ddcClosedForm f hf =
        θα + t₀ • θh + ε • ωh.form + ddcClosedForm f hf := by
      rw [hθh, add_smul, ← add_assoc, add_assoc (θα + t₀ • ωh.form), ← add_smul, add_halves]
    rwa [heq] at hsemi
  rcases eq_or_lt_of_le ht₀nn with h0 | ht₀
  · rw [← h0, zero_smul, add_zero] at hβ
    exact hβ
  exfalso
  set θβ := θα + t₀ • θh with hθβ
  set β := RealBottChern.ofRepresentative θβ with hβdef
  -- ampleness of the two test classes
  have hNSβ : β ∈ DFAlg.neronSeveri (m + 1) Y := by
    rw [hβdef, hθβ, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
    exact Submodule.add_mem _ hαNS (Submodule.smul_mem _ _ hhNS)
  have hamp₀ : ∀ ε : ℝ, 0 < ε →
      DFAlg.IsAmpleRealClass (RealBottChern.ofRepresentative (θh + ε • θh)) := by
    intro ε hε
    refine (DFAlg.isAmpleRealClass_iff _).mpr ⟨?_, θh + ε • θh,
      NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive ωh hθhsemi hε, rfl⟩
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
    exact Submodule.add_mem _ hhNS (Submodule.smul_mem _ _ hhNS)
  have hamp₁ : ∀ ε : ℝ, 0 < ε → DFAlg.IsAmpleRealClass
      (RealBottChern.ofRepresentative ((θh + t₀⁻¹ • θα) + ε • θh)) := by
    intro ε hε
    have hform : (θh + t₀⁻¹ • θα) + ε • θh = t₀⁻¹ • θβ + ε • ωh.form := by
      rw [hθβ, smul_add, smul_smul, inv_mul_cancel₀ ht₀.ne', one_smul, add_comm θh]
    rw [hform]
    obtain ⟨f, hf, hK⟩ := exists_isKahler_add_ddc_of_nef ωh
      (nefWithRespectTo_smul ωh (inv_nonneg.mpr ht₀.le) hβ) hε
    refine (DFAlg.isAmpleRealClass_iff _).mpr ⟨?_, _, hK,
      SGPT.Okounkov.TranscendentalLifting.ofRepresentative_add_ddc _ hf⟩
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
      RealBottChern.ofRepresentative_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hNSβ) (Submodule.smul_mem _ _ hhNS)
  have hpsef : ClassPseudoeffectiveViaPotentials β := classPseudoeffective_of_nef ωh hβ
  have hEh : nonKahlerLocus (RealBottChern.ofRepresentative θh) = ∅ :=
    FlatComplexTorusNakamaye.nonKahlerLocus_kahler_eq_empty hn ωh
  have hpsefh : ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θh) :=
    ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff θh).mpr hθhsemi⟩
  -- Step 1: `β` is big (restricted volume on `Y` itself)
  have hbig : IsBigClass β := by
    obtain ⟨V₀, hV₀c, hV₀d⟩ := AnalyticIrreducibleComponents.exists_subvariety_univ
      (n := m + 1) (M := Y)
    have hV₀ : IsClosedConnectedSubmanifold (m + 1) V₀.carrier V₀.dim := by
      rw [hV₀c, hV₀d]
      exact ⟨isClosed_univ, isConnected_univ,
        fun x _ => AnalyticIrreducibleComponents.regularAtDim_univ x⟩
    obtain ⟨A⟩ := nonempty_nativePositiveLine_of_isProjectiveManifold hY
    have hb : 0 < numericalRestrictedVolume ωh (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback (contMDiff_id (I := 𝓘(ℂ, ComplexModel (m + 1)))
          (n := ∞)) θh)) V₀ := by
      rw [ClosedRealOneOneForm.ofRepresentative_pullback_id]
      refine LocusProperties.numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus ωh _
        hpsefh V₀ (by rw [hV₀d]; exact hn) ?_
      rw [hEh, hV₀c]
      exact fun h => h (mem_univ (Classical.arbitrary Y))
    have hpos := numericalRestrictedVolume_pos_of_curveNef A ωh
      (contMDiff_id (I := 𝓘(ℂ, ComplexModel (m + 1))) (n := ∞)) ωh θα hα ht₀ hβ hamp₀ hamp₁
      V₀ hV₀ hb
    rw [ClosedRealOneOneForm.ofRepresentative_pullback_id] at hpos
    by_contra hnb
    exact hpos.ne' ((LocusProperties.numericalRestrictedVolume_eq_zero_iff_not_isBigClass hn ωh β
      hpsef V₀ hV₀c).mpr hnb)
  -- Step 2: `E_nK(β) = ∅`
  have hEβ : nonKahlerLocus β = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    have hK : Nonempty (KahlerBackground (m + 1) Y) := ⟨ωh⟩
    obtain ⟨V, hcomp, hdim, hxV⟩ :=
      AnalyticIrreducibleComponents.exists_isIrreducibleComponent_pos_dim_of_accPt
        (LocusProperties.isComplexAnalyticSubset_nonKahlerLocus hn hK β hbig) hx
        (NoIsolatedPoints.accPt_nonKahlerLocus hn hK β hbig x hx)
    have hRV0 := ComponentVanishing.numericalRestrictedVolume_eq_zero_of_isIrreducibleComponent
      hn ωh β hpsef V hdim hcomp
    have hnonNef : ¬ V.carrier ⊆ nonNefLocus ωh β := by
      rw [hβdef, nonNefLocus_eq_empty_of_nef hn ωh hβ]
      exact fun h => h hxV
    obtain ⟨Xt, _, _, _, μ, hμ, hiso, hcpt, -, ⟨ωT⟩, -, Vt, hVtc, hVt, hVtd, -, hRVt⟩ :=
      SmoothComponentReduction.exists_modification_smooth_component ωh θβ hbig V hdim hcomp
        hnonNef
    have hsurj := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hμ).2
    obtain ⟨-, hXtproj⟩ := DFAlg.isProjectiveManifold_of_isBlowupSequence hY hμ
    obtain ⟨A⟩ := nonempty_nativePositiveLine_of_isProjectiveManifold hXtproj
    -- `W = Ṽ` is not contained in the exceptional locus
    have hVtExc : ¬ Vt.carrier ⊆ exceptionalLocus (m + 1) μ := by
      obtain ⟨x₀, hx₀⟩ := V.regularLocus_nonempty
      have hx₀V : x₀ ∈ V.carrier := regularLocus_subset _ _ hx₀
      obtain ⟨z, rfl⟩ := hsurj x₀
      have hz : z ∉ exceptionalLocus (m + 1) μ := by
        intro hzE
        have hzS : z ∈ μ ⁻¹' (singularLocus V)ᶜ := fun hs => hs.2 hx₀
        exact Set.disjoint_left.mp hiso.2 hzS hzE
      intro hsub
      apply hz
      apply hsub
      rw [hVtc]
      exact subset_closure ⟨hx₀V, hz⟩
    have hbigh : IsBigClass (RealBottChern.ofRepresentative θh) :=
      PluripolarCapacityDichotomy.isBigClass_kahler ωh
    let : MeasurableSpace Xt := borel Xt
    have : BorelSpace Xt := ⟨rfl⟩
    have hb : 0 < numericalRestrictedVolume ωT (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hμ.contMDiff θh)) Vt := by
      refine LocusProperties.numericalRestrictedVolume_pos_of_not_subset_nonKahlerLocus ωT _
        ?_ Vt (by rw [hVtd]; exact hdim) ?_
      · exact SGPT.BDivisor.classPseudoeffective_of_isBigClass ωT
          (LocusProperties.isBigClass_pullback hK θh hbigh μ hμ)
      · rw [LocusProperties.nonKahlerLocus_pullback hK θh hbigh μ hμ, hEh, preimage_empty,
          empty_union]
        exact hVtExc
    have hpos := numericalRestrictedVolume_pos_of_curveNef A ωT hμ.contMDiff ωh θα hα ht₀ hβ
      hamp₀ hamp₁ Vt hVt hb
    have hpos' : 0 < numericalRestrictedVolume ωT (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hμ.contMDiff θβ)) Vt := hpos
    have hRV0' : numericalRestrictedVolume ωh (RealBottChern.ofRepresentative θβ) V = 0 := hRV0
    rw [(hRVt ωT).2, hRV0'] at hpos'
    exact lt_irrefl _ hpos'
  -- Step 3: `β` is a Kähler class
  obtain ⟨T, hsing, hpole⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      hn β hbig
  rw [hEβ] at hpole
  obtain ⟨C₀, hC₀⟩ := exists_lower_bound_of_poleSet_eq_empty hsing hpole
  obtain ⟨C₁, hC₁⟩ := T.strictlyPsh.exists_global_upper_bound
  obtain ⟨κ, hκ⟩ := exists_kahler_of_kahlerCurrent_of_bounded T
    ⟨C₀, C₁, fun x => ⟨hC₀ x, hC₁ x⟩⟩
  -- Step 4: `α + (t₀ - δ)θ_h` is still nef
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-θh)
  set δ := min (t₀ / 2) (1 / (2 * A)) with hδ
  have hδpos : 0 < δ := lt_min (half_pos ht₀) (by positivity)
  have hδA : δ * A ≤ 1 / 2 := by
    have := min_le_right (t₀ / 2) (1 / (2 * A))
    calc δ * A ≤ 1 / (2 * A) * A := mul_le_mul_of_nonneg_right this hA.le
      _ = 1 / 2 := by field_simp
  have hsemiδ : (κ.form - δ • θh).val.IsSemipositive := by
    have h1 := isSemipositive_smul hsemi hδpos.le
    have h2 := isSemipositive_smul (KahlerBackground.isSemipositive κ)
      (show (0 : ℝ) ≤ 1 - δ * A by linarith)
    have hid : κ.form - δ • θh = δ • (-θh + A • κ.form) + (1 - δ * A) • κ.form := by
      module
    rw [hid]
    intro e z hz v
    have a1 := h1 e z hz v
    have a2 := h2 e z hz v
    simp only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
    linarith
  have hrel : ClosedRealOneOneForm.BottChernRel (θα + (t₀ - δ) • θh) (κ.form - δ • θh) := by
    apply (RealBottChern.ofRepresentative_eq_iff _ _).mp
    have h1 : RealBottChern.ofRepresentative κ.form =
        RealBottChern.ofRepresentative θα + t₀ • RealBottChern.ofRepresentative θh := by
      rw [hκ, hβdef, hθβ, RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_smul]
    rw [sub_eq_add_neg κ.form, RealBottChern.ofRepresentative_add κ.form,
      RealBottChern.ofRepresentative_neg, RealBottChern.ofRepresentative_smul δ, h1,
      RealBottChern.ofRepresentative_add θα, RealBottChern.ofRepresentative_smul]
    module
  have hmem : t₀ - δ ∈ S := by
    refine ⟨by linarith [min_le_left (t₀ / 2) (1 / (2 * A))], ?_⟩
    exact (nefWithRespectTo_bottChernRel_iff ωh hrel).mpr
      (nefWithRespectTo_of_semipositive ωh hsemiδ)
  have := csInf_le hSbdd hmem
  linarith

/-- **Kleiman's criterion** (the Kleiman half of the nef-cone comparison in `rmk:bdiv:L749`):
on a compact connected projective manifold `Y`, a class of `NS(Y)_ℝ` which is curve-nef
(`DFAlg.IsCurveNef`: nonnegative degree on every compact connected curve) is nef. -/
theorem classNef_of_isCurveNef [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y) (ωK : KahlerBackground (m + 1) Y)
    {α : RealBottChern (m + 1) Y} (hNS : α ∈ DFAlg.neronSeveri (m + 1) Y)
    (hα : DFAlg.IsCurveNef α) : ClassNefWithRespectTo ωK α := by
  obtain ⟨θh, hK, hhNS⟩ :=
    SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp hY
  rw [SGPT.BDivisor.classNefWithRespectTo_iff ωK ⟨θh, hK⟩]
  induction α using Quotient.inductionOn with
  | h θα =>
  exact nefWithRespectTo_of_curveNef hY ⟨θh, hK⟩ hhNS θα hNS
    (fun C _ _ _ _ _ κ g hg => hα C κ g hg)

/-- **Nef = curve-nef on `NS(Y)_ℝ`** for a compact connected projective manifold `Y`. -/
theorem isCurveNef_iff_classNef [ConnectedSpace Y]
    (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y) (ωK : KahlerBackground (m + 1) Y)
    {α : RealBottChern (m + 1) Y} (hNS : α ∈ DFAlg.neronSeveri (m + 1) Y) :
    DFAlg.IsCurveNef α ↔ ClassNefWithRespectTo ωK α :=
  ⟨classNef_of_isCurveNef hY ωK hNS, DFAlg.isCurveNef_of_classNef ωK⟩

end Main

end SGPT.BDivisor.Kleiman
