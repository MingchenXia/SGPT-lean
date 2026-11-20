import SGPT.Trace.BertiniGeneral
import SGPT.Trace.BertiniSmooth
import SGPT.Trace.TraceMultiplier
import SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

/-!
# The analytic Bertini theorem: the Ohsawa–Takegoshi half, and `cor:ABTfortrace`

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems": `thm:Bert` and
`cor:ABTfortrace` (blueprint `claude-trace2.tex`).

Setting (`SGPT.Trace.Bertini`): `X` is a compact complex manifold of dimension `n`,
`p : X → ℙᴺ` is holomorphic, `Λ = |𝒪_{ℙᴺ}(1)| = HyperplaneSpace N`, the members are
`H ∩ X = p⁻¹(H)` (`member p ℓ`) and "quasi-every `H`" means: outside a pluripolar subset of `Λ`
(`VariableComplexAtlas.CoPluripolar`).

## `thm:Bert`

The set `𝒢` of `thm:Bert` is `bertiniGoodSet p hp φ`: `H ∩ X` is smooth and
`𝓘(φ|_{H ∩ X}) = Rest_{H ∩ X}(𝓘(φ))`. Its smoothness clause holds quasi-everywhere
(`coPluripolar_exists_isSmoothMemberOfDim`, package B). Here:

* `multiplierIdeal_restrict_le_restStalk_of_regular`: the Ohsawa–Takegoshi inclusion
  `𝓘(c φ|_W) ⊆ Rest_W 𝓘(c φ)` at every point of a closed submanifold `W` of pure dimension `k`
  (no connectedness; the book's `thm:OT` is stated for connected `W`);
* `member_multiplier_le_restStalk`: hence the inclusion `𝓘(c φ|_{H'}) ⊆ Rest_{H'} 𝓘(c φ)` holds
  for **every** `H ∈ Λ` whose member `H'` is smooth, at every level `c`;
* `coPluripolar_smooth_multiplier_le`: for quasi-every `H`, `H'` is smooth and the inclusion
  `⊆` of the multiplier clause holds (at every level);
* `mem_bertiniGoodSet_iff`: `H ∈ 𝒢` iff `H'` is smooth and the reverse inclusion
  `Rest_{H'} 𝓘(φ) ⊆ 𝓘(φ|_{H'})` holds; and `coPluripolar_bertiniGoodSet_of_reverse`: `thm:Bert`
  is equivalent to the reverse inclusion for quasi-every `H` (the remaining open input, which
  the book obtains from the positivity of the Hodge metric of
  `π₁*(ω_{U/Λ} ⊗ π₂^*L ⊗ 𝓘(π₂^*φ))`).

## `cor:ABTfortrace`

`coPluripolar_abtTracePartial`: quasi-every `H ∈ Λ` is connected and smooth, satisfies
`ν(φ, H) = 0`, admits a trace operator `Tr_H(φ)`, and every trace operator satisfies
`φ|_H ⪯_P Tr_H(φ)` and `φ|_H ⪯_𝓘 Tr_H(φ)` (one half of `Tr_H(φ) ∼_𝓘 φ|_H`).
`iOrder_trace_restriction_of_restrictIdeal_le` and `coPluripolar_iEquivalent_trace_of_reverse`:
the other half `Tr_H(φ) ⪯_𝓘 φ|_H` follows from `prop:OT2` once the reverse Bertini inclusion
`Rest_H 𝓘(c φ) ⊆ 𝓘(c φ|_H)` holds at every level `c > 0` (for quasi-every `H`); so
`cor:ABTfortrace` is reduced exactly to the multiplier clause of `thm:Bert` at all levels.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.Trace2Bertini

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi

/-! ### The Ohsawa–Takegoshi inclusion on a possibly disconnected submanifold -/

section OT

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-- **Ohsawa–Takegoshi inclusion (`thm:OT`) on a closed submanifold of pure dimension `k`.**
For `φ` quasi-psh on `X`, every `y ∈ W` and every real `c`, the stalk `𝓘(c φ|_W)_y ⊆ 𝒪_{↥W,y}`,
transported to `𝒪_{W,y} = 𝒪_{X,y}/𝓘_{W,y}` by restriction of germs (`structureStalkEquiv`), lies
in `(Rest_W 𝓘(c φ))_y`. Unlike `multiplierIdeal_restrict_le_restStalk_of_quasi`, `W` need not be
connected (the statement is local). -/
theorem multiplierIdeal_restrict_le_restStalk_of_regular (hk : k ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) (hC : IsClosedSubmanifold n W)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (c : ℝ) :
    letI := chartedSpace hk hreg
    ∀ q : W,
      Ideal.comap (structureStalkEquiv hk hreg hC q)
          (stalkIdeal (multiplierIdeal (n := k) c (fun y : W => φ y.1)) q) ≤
        restStalk (multiplierIdeal (n := n) c φ) (submanifoldSubspace hC) q.1 := by
  let := chartedSpace hk hreg
  intro q
  set e := structureStalkEquiv hk hreg hC q
  rw [← Ideal.map_symm, Ideal.map_le_iff_le_comap]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨f, hf, hmem, rfl⟩
  obtain ⟨F, hF, hFf⟩ := exists_extension_mem_multiplierIdeal hk hreg hφ q f hmem
  have hFhol : HolomorphicAt n F q.1 := hF.1
  have he : e (Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol)) = NativeHolGerm.mk f hf := by
    rw [structureStalkEquiv_mk, restrictGerm_mk]
    exact NativeHolGerm.mk_eq_mk_iff.mpr hFf
  have hsymm : e.symm (NativeHolGerm.mk f hf) =
      Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol) := by
    rw [← he]
    exact e.symm_apply_apply _
  rw [SetLike.mem_coe, Ideal.mem_comap]
  change e.symm (NativeHolGerm.mk f hf) ∈ _
  rw [hsymm]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨F, hFhol, hF, rfl⟩)

end OT

/-! ### `thm:Bert`: the Ohsawa–Takegoshi half of the multiplier clause -/

section Bertini

open SGPT.Trace.Bertini SGPT.Projective

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)
  (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)

/-- A smooth member `H' = p⁻¹(H_ℓ)` of dimension `k` is a closed submanifold. -/
theorem isClosedSubmanifold_of_isSmoothMemberOfDim {l : HyperplaneSpace N} {k : ℕ}
    (hsm : IsSmoothMemberOfDim p hp l k) : IsClosedSubmanifold n (member p l) :=
  ⟨isClosed_member p hp.continuous l, fun _ hx => ⟨k, hsm.1 _ hx⟩⟩

/-- **`thm:Bert`, the inclusion `⊆` of the multiplier clause, for every smooth member.** If
`H' = H ×_{ℙᴺ} X` is smooth (of dimension `k`), then for every quasi-psh `φ`, every real `c` and
every `y ∈ H'`, `𝓘(c φ|_{H'})_y ⊆ (Rest_{H'} 𝓘(c φ))_y` inside `𝒪_{H',y}` (Ohsawa–Takegoshi).
(The book's `𝒢` uses `c = 1`; the convention `𝓘(-∞) = 0` is automatic.) -/
theorem member_multiplier_le_restStalk {l : HyperplaneSpace N} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothMemberOfDim p hp l k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (c : ℝ) :
    letI := chartedSpace hk hsm.1
    ∀ q : member p l,
      Ideal.comap (structureStalkEquiv hk hsm.1 (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm) q)
          (stalkIdeal (multiplierIdeal (n := k) c (fun y : member p l => φ y.1)) q) ≤
        restStalk (multiplierIdeal (n := n) c φ)
          (submanifoldSubspace (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm)) q.1 :=
  multiplierIdeal_restrict_le_restStalk_of_regular hk hsm.1
    (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm) hφ c

/-- The pointwise reverse inclusion `Rest_{H'} 𝓘(c φ) ⊆ 𝓘(c φ|_{H'})` on a smooth member `H'` of
dimension `k` (the half of the multiplier clause of `thm:Bert` that is not Ohsawa–Takegoshi). -/
def ReverseMultiplierInclusion {l : HyperplaneSpace N} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothMemberOfDim p hp l k) (φ : X → EReal) (c : ℝ) : Prop :=
  letI := chartedSpace hk hsm.1
  ∀ q : member p l,
    restStalk (multiplierIdeal (n := n) c φ)
        (submanifoldSubspace (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm)) q.1 ≤
      Ideal.comap (structureStalkEquiv hk hsm.1 (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm) q)
        (stalkIdeal (multiplierIdeal (n := k) c (fun y : member p l => φ y.1)) q)

/-- **`thm:Bert` reduced to the reverse inclusion.** For quasi-psh `φ`, `H ∈ 𝒢` iff `H'` is
smooth and `Rest_{H'} 𝓘(φ) ⊆ 𝓘(φ|_{H'})` (the other inclusion is
`member_multiplier_le_restStalk`). -/
theorem mem_bertiniGoodSet_iff {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (l : HyperplaneSpace N) :
    l ∈ bertiniGoodSet p hp φ ↔
      ∃ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
        ReverseMultiplierInclusion p hp hk hsm φ 1 := by
  constructor
  · rintro ⟨k, hk, hsm, h⟩
    refine ⟨k, hk, hsm, fun q => ?_⟩
    exact (h q).symm.le
  · rintro ⟨k, hk, hsm, h⟩
    refine ⟨k, hk, hsm, fun q => ?_⟩
    exact le_antisymm (member_multiplier_le_restStalk p hp hk hsm hφ 1 q) (h q)

/-- **`thm:Bert`, the smoothness clause and the inclusion `𝓘(c φ|_{H'}) ⊆ Rest_{H'} 𝓘(c φ)`
quasi-everywhere.** For `N ≥ 1` and quasi-psh `φ`, for quasi-every `H ∈ Λ` the member
`H' = H ×_{ℙᴺ} X` is smooth and `𝓘(c φ|_{H'}) ⊆ Rest_{H'} 𝓘(c φ)` at every point and every
level `c`. -/
theorem coPluripolar_smooth_multiplier_le [CompactSpace X] (hN : 1 ≤ N) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
        letI := chartedSpace hk hsm.1
        ∀ (c : ℝ) (q : member p l),
          Ideal.comap
              (structureStalkEquiv hk hsm.1 (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm) q)
              (stalkIdeal (multiplierIdeal (n := k) c (fun y : member p l => φ y.1)) q) ≤
            restStalk (multiplierIdeal (n := n) c φ)
              (submanifoldSubspace (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm)) q.1} := by
  refine SGPT.Trace.BertiniGeneral.coPluripolar_mono
    (coPluripolar_exists_isSmoothMemberOfDim p hp hN) fun l hl => ?_
  obtain ⟨k, hk, hsm⟩ := hl
  exact ⟨k, hk, hsm, fun c => member_multiplier_le_restStalk p hp hk hsm hφ c⟩

/-- **`thm:Bert` from the reverse inclusion.** If for quasi-every `H ∈ Λ` the reverse inclusion
`Rest_{H'} 𝓘(φ) ⊆ 𝓘(φ|_{H'})` holds on `H'` whenever `H'` is smooth, then `𝒢` is co-pluripolar
(the conclusion of `thm:Bert`). Conversely `𝒢` co-pluripolar gives the hypothesis
(`mem_bertiniGoodSet_iff`). This isolates the analytic input still missing for `thm:Bert`. -/
theorem coPluripolar_bertiniGoodSet_of_reverse [CompactSpace X] (hN : 1 ≤ N) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hrev : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
        ReverseMultiplierInclusion p hp hk hsm φ 1}) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      (bertiniGoodSet p hp φ) := by
  refine SGPT.Trace.BertiniGeneral.coPluripolar_mono
    (SGPT.Trace.BertiniGeneral.coPluripolar_inter
      (coPluripolar_exists_isSmoothMemberOfDim p hp hN) hrev) fun l hl => ?_
  obtain ⟨⟨k, hk, hsm⟩, hr⟩ := hl
  exact (mem_bertiniGoodSet_iff p hp hφ l).mpr ⟨k, hk, hsm, hr k hk hsm⟩

/-- Conversely, `thm:Bert` gives the reverse inclusion for quasi-every `H`. -/
theorem coPluripolar_reverse_of_bertiniGoodSet {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hG : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      (bertiniGoodSet p hp φ)) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
        ReverseMultiplierInclusion p hp hk hsm φ 1} :=
  SGPT.Trace.BertiniGeneral.coPluripolar_mono hG fun l hl =>
    (mem_bertiniGoodSet_iff p hp hφ l).mp hl

end Bertini

/-! ### `cor:ABTfortrace` -/

section ABT

open SGPT.Trace.Bertini SGPT.Trace.BertiniGeneral SGPT.Projective
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition SingularGlobalPOrder
  SubmanifoldIdealRestriction

section Member

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {W : Set X}

/-- The proved clauses of `cor:ABTfortrace` on one closed connected submanifold `W` (with its
own complex structure; traces along `W` are `IsNaturalSourceTraceRepresentative`, `def:traceop`):
`ν(φ, W) = 0`, `φ` has a trace operator `Tr_W(φ)` along `W`, and every trace operator `τ` (for
every auxiliary Kähler form) satisfies `φ|_W ⪯_P τ` and `φ|_W ⪯_𝓘 τ`. -/
def IsABTTracePartial (omega : KahlerBackground n X) (hW : IsClosedConnectedSubmanifold n W k)
    (φ : X → EReal) : Prop :=
  let hk : k ≤ n := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := chartedSpace hk hW.2.2
  let : IsComplexManifold k W := isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0 ∧
    (∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW φ τ) ∧
    ∀ (omega' : KahlerBackground n X) (τ : W → EReal),
      IsNaturalSourceTraceRepresentative omega' hW φ τ →
        SourcePOrder (n := k) (fun y : W => φ y) τ ∧
          IOrderOnManifold (n := k) (fun y : W => φ y) τ

/-- The full conclusion of `cor:ABTfortrace` on `W`: `ν(φ, W) = 0`, a trace operator exists, and
every trace operator is `𝓘`-equivalent to `φ|_W` (`Tr_W(φ) ∼_𝓘 φ|_W`). -/
def IsABTTrace (omega : KahlerBackground n X) (hW : IsClosedConnectedSubmanifold n W k)
    (φ : X → EReal) : Prop :=
  let hk : k ≤ n := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := chartedSpace hk hW.2.2
  let : IsComplexManifold k W := isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0 ∧
    (∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW φ τ) ∧
    ∀ (omega' : KahlerBackground n X) (τ : W → EReal),
      IsNaturalSourceTraceRepresentative omega' hW φ τ →
        IEquivalentOnManifold (n := k) τ (fun y : W => φ y)

/-- The reverse Bertini inclusion on `W` at every level: `Rest_W 𝓘(c φ) ⊆ 𝓘(c φ|_W)` for all
`c > 0` (`Rest_W` is `restrictIdeal`, the restriction ideal of `def:restidealsheaf`, as in
`prop:OT2`). -/
def ReverseRestrictionInclusion (hW : IsClosedConnectedSubmanifold n W k) (φ : X → EReal) :
    Prop :=
  let hk : k ≤ n := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := chartedSpace hk hW.2.2
  ∀ c : ℝ, 0 < c →
    (restrictIdeal (k := k) (W := W) (multiplierIdeal (n := n) c φ)).Le
      (multiplierIdeal (n := k) c (fun y : W => φ y))

/-- **`cor:ABTfortrace`, proved clauses, on one member.** If `n ≠ 0`, `φ ∈ PSH(X, θ)` and
`φ|_W ≢ -∞`, then `ν(φ, W) = 0`, a trace operator exists, and `φ|_W ⪯_P Tr_W(φ)` and
`φ|_W ⪯_𝓘 Tr_W(φ)` for every trace operator (`prop:Trdominarest`, `cor:PimpliesI`). -/
theorem isABTTracePartial_of (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hne : ∃ x ∈ W, φ x ≠ ⊥) :
    IsABTTracePartial omega hW φ := by
  let hk : k ≤ n := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := chartedSpace hk hW.2.2
  have : IsComplexManifold k W := isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hι := contMDiff_val hk hW.2.2
  obtain ⟨x, hx, hφx⟩ := hne
  have hne' : ∃ y : W, φ (y : X) ≠ ⊥ := ⟨⟨x, hx⟩, hφx⟩
  have hgen : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0 :=
    SGPT.Trace.BertiniGeneral.sourceGenericLelongNumber_eq_zero (ι := (Subtype.val : W → X))
      hn hφ hne'
  refine ⟨hgen, ?_, ?_⟩
  · exact SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega) hφ.quasiPshPotential hι
      hgen
  · intro omega' τ hτ
    have hP : SourcePOrder (n := k) (fun y : W => φ y) τ :=
      sourcePOrder_restriction_trace hk
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega') hι hτ hne'
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    exact ⟨hP, GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder hP⟩

/-- **The remaining half of `cor:ABTfortrace` from the reverse Bertini inclusion.** If
`Rest_W 𝓘(c φ) ⊆ 𝓘(c φ|_W)` for every `c > 0`, then every trace operator `τ` of `φ` along `W`
satisfies `τ ⪯_𝓘 φ|_W`: by `prop:OT2`, `𝓘(c τ) ⊆ Rest_W 𝓘(c φ) ⊆ 𝓘(c φ|_W)`. -/
theorem iOrder_trace_restriction_of_reverse (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hne : ∃ x ∈ W, φ x ≠ ⊥) {τ : W → EReal}
    (htrace : IsNaturalSourceTraceRepresentative omega hW φ τ)
    (hrev : ReverseRestrictionInclusion hW φ) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    IOrderOnManifold (n := k) τ (fun y : W => φ y) := by
  let hk : k ≤ n := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := chartedSpace hk hW.2.2
  have : IsComplexManifold k W := isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have hι := contMDiff_val hk hW.2.2
  obtain ⟨x, hx, hφx⟩ := hne
  have hne' : ∃ y : W, φ (y : X) ≠ ⊥ := ⟨⟨x, hx⟩, hφx⟩
  have hφW : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y : W => φ y) := isThetaPshPotential_comp hι hφ hne'
  have hT := htrace
  obtain ⟨-, -, -, -, -, β, -, hτ, -, -⟩ := hT
  intro c hc
  have h1 := multiplierIdeal_trace_le_restrictIdeal omega hW htrace hc
  have hle : (multiplierIdeal (n := k) c τ).Le
      (multiplierIdeal (n := k) c (fun y : W => φ y)) :=
    fun y g hg => hrev c hc y g (h1 y g hg)
  exact GenuineMultiplierIdealChartInclusion.multiplierIdealIncluded_of_multiplierIdeal_le
    hτ.1 hφW.1 hc hc hle

/-- **`cor:ABTfortrace` on one member, from the reverse Bertini inclusion.** If `n ≠ 0`,
`φ ∈ PSH(X, θ)`, `φ|_W ≢ -∞` and `Rest_W 𝓘(c φ) ⊆ 𝓘(c φ|_W)` for every `c > 0`, then
`ν(φ, W) = 0`, a trace operator exists and every trace operator satisfies
`Tr_W(φ) ∼_𝓘 φ|_W`. -/
theorem isABTTrace_of_reverse (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hW : IsClosedConnectedSubmanifold n W k) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hne : ∃ x ∈ W, φ x ≠ ⊥)
    (hrev : ReverseRestrictionInclusion hW φ) : IsABTTrace omega hW φ := by
  obtain ⟨hgen, hex, hP⟩ := isABTTracePartial_of hn omega hW hφ hne
  refine ⟨hgen, hex, fun omega' τ hτ => ⟨?_, (hP omega' τ hτ).2⟩⟩
  exact iOrder_trace_restriction_of_reverse omega' hW hφ hne hτ hrev

end Member

section General

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
  (p : X → ComplexProjectiveSpace N)
  (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)

/-- **Source `cor:ABTfortrace`, proved clauses.** Let `X` be a compact connected complex manifold
of dimension `n ≠ 0` (the book: connected projective, `n ≥ 2`) with a Kähler form, `Λ` a
base-point-free linear system (`p` nondegenerate, `N ≥ 1`) whose connected members form a
co-pluripolar set (the book's standing assumption), and `φ ∈ PSH(X, θ)`. Then quasi-every
`H ∈ Λ` is connected and smooth, satisfies `ν(φ, H) = 0`, admits a trace operator `Tr_H(φ)`,
and every trace operator satisfies `φ|_H ⪯_P Tr_H(φ)` and `φ|_H ⪯_𝓘 Tr_H(φ)`. -/
theorem coPluripolar_abtTracePartial (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        IsABTTracePartial omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  refine coPluripolar_mono (coPluripolar_generalPositionSet p
    (qpshGeneralRestriction p hp hnd hN) hconn hφ) fun l hl => ?_
  obtain ⟨h, hx⟩ := hl
  exact ⟨h, isABTTracePartial_of hn omega _ hφ hx⟩

/-- **Source `cor:ABTfortrace` from the reverse Bertini inclusion.** Under the hypotheses of
`coPluripolar_abtTracePartial`, if for quasi-every `H ∈ Λ` whose member is connected and smooth
the reverse inclusion `Rest_H 𝓘(c φ) ⊆ 𝓘(c φ|_H)` holds for all `c > 0` (the multiplier clause
of `thm:Bert`, at every level), then quasi-every `H ∈ Λ` is connected and smooth, satisfies
`ν(φ, H) = 0`, and `Tr_H(φ) ∼_𝓘 φ|_H`. -/
theorem coPluripolar_abtTrace_of_reverse (hn : n ≠ 0) (omega : KahlerBackground n X)
    (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hrev : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∀ h : IsConnectedSmoothMember n p l,
        ReverseRestrictionInclusion (isClosedConnectedSubmanifold_member p hp h) φ}) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        IsABTTrace omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  refine coPluripolar_mono (coPluripolar_inter (coPluripolar_generalPositionSet p
    (qpshGeneralRestriction p hp hnd hN) hconn hφ) hrev) fun l hl => ?_
  obtain ⟨⟨h, hx⟩, hr⟩ := hl
  exact ⟨h, isABTTrace_of_reverse hn omega _ hφ hx (hr h)⟩

end General

end ABT

end SGPT.Trace.Trace2Bertini
