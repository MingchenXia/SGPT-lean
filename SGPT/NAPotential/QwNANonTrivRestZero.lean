import SGPT.NAPotential.NANSNonTrivRest
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

/-!
# `lma:non-trivrest` in dimension zero


Source `lma:non-trivrest` (`chapter_NApotential.tex`): for `Γ ∈ PSH^NA(X, θ)` and an irreducible
analytic subset `Y ⊆ X`, the following are equivalent: (1) `Γ^An(v_{Y,triv}) ≠ -∞`;
(2) `Γ^An|_{Y^An} ≢ -∞`; (3) `Γ` has a well-defined restriction to `Y`.  Lane NA-NS proved it
(`SGPT.NAPotential.NANS.source_nonTrivRest`) for `X` of dimension `m + 1 ≥ 1`.  Here the
dimension-zero case (`X` smooth projective of dimension `0`, `X(ℂ)` connected, i.e. a point):

* `potentialAn_eq_zero_of_dim_zero`: `φ^An ≡ 0` on `X^An` for every quasi-psh `φ` (every
  multiplier ideal is the unit ideal);
* `naPotentialAnAt_eq_of_dim_zero`: `Γ^An ≡ Γ_max` on `X^An` (`eq:psiandef`);
* `traceWellDefined_of_dim_zero`: every `Γ` has a well-defined restriction to every `Y` (Lelong
  numbers vanish in dimension zero);
* **`source_nonTrivRest_of_dim_zero`**: the equivalence of (1), (2), (3) — all three hold;
* `potentialAn_subvarietyTrivial_of_dim_zero`, `naPotentialAnAt_le_subvarietyTrivial_of_dim_zero`,
  `naPotentialAnAt_subvarietyTrivial_eq_traceCutoff_of_dim_zero`: the displayed formula of the
  proof (`ν(φ, Y) = 0` and `φ^An(v_{Y,triv}) = 0`), the maximum principle and the endpoint
  identity `Γ^An(v_{Y,triv}) = (Tr_Y Γ)_max` in dimension zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.NANS

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SourceTraceRepresentativeDefinition

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 0 f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance qwNAZeroPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwNAZeroPointCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance qwNAZeroPointManifold : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

/-- In dimension zero the algebraic models of the multiplier ideals of a quasi-psh `φ` are the
unit ideal at every point: `v(𝓘(kφ)) = 0` for `k > 0` and every `v ∈ X^An`. -/
theorem multiplierIdealVal_eq_zero_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := 0) φ) (v : BerkovichPoint f) {k : ℕ} (hk : 0 < k) :
    v.multiplierIdealVal 0 E φ k = 0 := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold BerkovichPoint.multiplierIdealVal
  rw [BerkovichPoint.idealVal_eq_zero_iff,
    stalkIdeal_algebraization_multiplierIdeal_eq_top_iff hφ hk']
  obtain ⟨q, hq, -⟩ := exists_mem_subvarietyPoints (f := f) (W := ⊤) (y := v.center) trivial
  exact ⟨q, hq, (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
    hφ hk' q _).mpr (holomorphicAt_const 1)⟩

/-- **In dimension zero `φ^An ≡ 0` on `X^An`** for every quasi-psh `φ`. -/
theorem potentialAn_eq_zero_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := 0) φ) (v : BerkovichPoint f) :
    potentialAn 0 E φ v = 0 := by
  have hlim : Tendsto (fun k : ℕ => v.multiplierIdealVal 0 E φ k / k) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [multiplierIdealVal_eq_zero_of_dim_zero hφ v hk, ENNReal.zero_div]
  unfold potentialAn BerkovichPoint.potentialVal
  rw [hlim.limUnder_eq]
  simp

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

/-- `sup_{τ < a} τ = a` in `[-∞, ∞]`. -/
theorem iSup_Iio_coe_eq (a : ℝ) : (⨆ τ : Iio a, ((τ : ℝ) : EReal)) = (a : EReal) := by
  refine le_antisymm (iSup_le fun τ => EReal.coe_le_coe_iff.mpr τ.2.le) ?_
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨r, hbr, hra⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  exact lt_iSup_iff.mpr ⟨⟨r, EReal.coe_lt_coe_iff.mp hra⟩, hbr⟩

/-- **In dimension zero `Γ^An ≡ Γ_max` on `X^An`** (`eq:psiandef`, every Kähler index). -/
theorem naPotentialAnAt_eq_of_dim_zero (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt 0 E Γ ω v = ((Γ.component ω).val.max : EReal) := by
  unfold naPotentialAnAt
  have h : ∀ τ : Iio (Γ.component ω).val.max,
      potentialAn 0 E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal) =
        ((τ : ℝ) : EReal) := fun τ => by
    have hτ := naComponent_potential_isThetaPshPotential 0 Γ ω τ
    rw [potentialAn_eq_zero_of_dim_zero ⟨hτ.1.quasiPlurisubharmonic, hτ.2⟩ v, zero_add]
  simp_rw [h]
  exact iSup_Iio_coe_eq _

/-- In dimension zero every slice of `Γ` has vanishing generic Lelong number along `Y`:
`ν(Γ^{θ+ω}_τ, Y) = 0` for every `τ < Γ_max`. -/
theorem sliceTraceable_of_dim_zero (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm 0 (SchemeComplexPoint f)) (y : X) {τ : ℝ}
    (hτ : τ < (Γ.component κ).val.max) :
    NATrace.SliceTraceable (subvarietyInclusion f y) Γ κ τ := by
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨q, hq, -⟩ := exists_mem_subvarietyPoints (f := f) (W := ⊤) (y := y) trivial
  have : Nonempty (subvarietyPoints f y) := ⟨⟨q, hq⟩⟩
  exact ⟨hτ, sourceGenericLelongNumber_zero_dimension rfl _ _⟩

/-- **In dimension zero every `Γ` has a well-defined restriction to every `Y`.** -/
theorem traceWellDefined_of_dim_zero (Γ : SourceNAPotential θ) (y : X) :
    NATrace.TraceWellDefined (subvarietyInclusion f y) Γ := fun κ =>
  ⟨(Γ.component κ).val.max, fun _ hτ => sliceTraceable_of_dim_zero Γ κ y hτ⟩

/-- **Source `lma:non-trivrest` in dimension zero**: for every `Γ ∈ PSH^NA(X, θ)`, every Kähler
index `ω` and every irreducible closed subvariety `Y = closure {y}`, the following are equivalent
(and all three hold): (1) `Γ^An(v_{Y,triv}) ≠ -∞`; (2) `Γ^An(w) ≠ -∞` for some `w ∈ Y^An`;
(3) `Γ` has a well-defined restriction to `Y`. -/
theorem source_nonTrivRest_of_dim_zero (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (y : X) :
    List.TFAE [naPotentialAnAt 0 E Γ ω (subvarietyTrivial f y) ≠ ⊥,
      ∃ w ∈ subvarietyAn f y, naPotentialAnAt 0 E Γ ω w ≠ ⊥,
      NATrace.TraceWellDefined (subvarietyInclusion f y) Γ] := by
  have h1 : naPotentialAnAt 0 E Γ ω (subvarietyTrivial f y) ≠ ⊥ := by
    rw [naPotentialAnAt_eq_of_dim_zero]
    exact EReal.coe_ne_bot _
  have h2 : ∃ w ∈ subvarietyAn f y, naPotentialAnAt 0 E Γ ω w ≠ ⊥ :=
    ⟨_, subvarietyTrivial_mem_subvarietyAn y, h1⟩
  have h3 := traceWellDefined_of_dim_zero Γ y
  tfae_have 1 → 2 := fun _ => h2
  tfae_have 2 → 3 := fun _ => h3
  tfae_have 3 → 1 := fun _ => h1
  tfae_finish

omit [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
/-- The displayed formula of the proof of `lma:non-trivrest` in dimension zero: `ν(φ, Y) = 0` and
`φ^An(v_{Y,triv}) = 0` for every quasi-psh `φ`. -/
theorem potentialAn_subvarietyTrivial_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := 0) φ) (y : X) :
    sourceGenericLelongNumber (n := 0) (subvarietyInclusion f y) φ = 0 ∧
      potentialAn 0 E φ (subvarietyTrivial f y) = 0 := by
  have := E.locallyOfFiniteType
  obtain ⟨q, hq, -⟩ := exists_mem_subvarietyPoints (f := f) (W := ⊤) (y := y) trivial
  have : Nonempty (subvarietyPoints f y) := ⟨⟨q, hq⟩⟩
  exact ⟨sourceGenericLelongNumber_zero_dimension rfl _ _, potentialAn_eq_zero_of_dim_zero hφ _⟩

/-- The maximum principle used for (1) ⟺ (2), in dimension zero (with equality):
`Γ^An(w) ≤ Γ^An(v_{Y,triv})` for every `w ∈ Y^An`. -/
theorem naPotentialAnAt_le_subvarietyTrivial_of_dim_zero (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) {y : X} {w : BerkovichPoint f}
    (_hw : w ∈ subvarietyAn f y) :
    naPotentialAnAt 0 E Γ ω w ≤ naPotentialAnAt 0 E Γ ω (subvarietyTrivial f y) := by
  rw [naPotentialAnAt_eq_of_dim_zero, naPotentialAnAt_eq_of_dim_zero]

/-- The endpoint identity `Γ^An(v_{Y,triv}) = (Tr_Y Γ)_max` in dimension zero. -/
theorem naPotentialAnAt_subvarietyTrivial_eq_traceCutoff_of_dim_zero (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (y : X) :
    naPotentialAnAt 0 E Γ ω (subvarietyTrivial f y) =
      ((NATrace.traceCutoff (subvarietyInclusion f y) Γ ω : ℝ) : EReal) := by
  rw [naPotentialAnAt_eq_of_dim_zero]
  congr 1
  have hset : {τ | NATrace.SliceTraceable (subvarietyInclusion f y) Γ ω τ} =
      Iio (Γ.component ω).val.max := by
    ext τ
    exact ⟨fun h => h.1, fun h => sliceTraceable_of_dim_zero Γ ω y h⟩
  unfold NATrace.traceCutoff
  rw [hset, csSup_Iio]

end SGPT.NAPotential.NANS

end
