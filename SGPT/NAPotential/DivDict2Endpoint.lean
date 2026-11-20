import SGPT.NAPotential.DivDict2Unconditional
import SGPT.NAPotential.BJModelFlagIdeal

/-! # The endpoint `τ = Γ_max` in `eq:psiandef` and the convention `(-∞)^An = -∞`

Source `chapter_NApotential.tex`, `def:Gammaana`: for `Γ ∈ PSH^NA(X, θ)` and `ω ∈ Kah(X)`,
`Γ^An(v) = sup_{τ ≤ Γ_max} (Γ_τ^{θ+ω,An}(v) + τ)`, *which can be equivalently written as*
`sup_{τ ∈ ℝ} (Γ_τ^{θ+ω,An}(v) + τ)` *with `(-∞)^An(v) = -∞` understood*.
Blueprint `claude-div-dict2:bot`, `claude-div-dict2:endpoint`.

The workspace definition `naPotentialAnAt` takes the supremum over `τ < Γ_max`, where the slices
`Γ_τ` are the data of the test curve.  The endpoint slice is the literal infimum
`Γ_{Γ_max} = inf_{τ < Γ_max} Γ_τ` (`sourceTestCurveCutoff`), and beyond the cutoff the slices are
`≡ -∞` (`sourceTestCurveAt`, the three branches of the source extension remark).

* The endpoint slice is a decreasing limit of `(θ + ω)`-psh functions; the slices of an
  `𝓘`-model test curve are fixed points of the envelope, so they have supremum `0` and the limit
  does not collapse: `Γ_{Γ_max}` is `(θ + ω)`-psh (`naComponent_cutoff_isThetaPshPotential`,
  from `SourceTestCurvePredata.cutoff_thetaPSH`).  In particular the dichotomy "quasi-psh or
  `≡ -∞`" holds (`naComponent_cutoff_isThetaPSH_or_eq_bot`), with the first alternative always.
* `potentialAn_bot`: the workspace analytification of the constant `-∞` is `-∞` at every point of
  `X^An`, so the convention `(-∞)^An = -∞` of the source is a theorem: the multiplier ideals
  `𝓘(c · (-∞))` only contain germs vanishing near the point, their algebraic models are the zero
  ideal sheaf (`algebraization_multiplierIdeal_bot`), whose value is `+∞` at every valuation.
* `naPotentialAnAt_eq_iSup_le`, `naPotentialAnAt_eq_iSup`: the printed supremum over
  `τ ≤ Γ_max`, and the supremum over all `τ ∈ ℝ`, equal `naPotentialAnAt` (no hypothesis).
* `naPotentialAnAt_le_max`, `naPotentialAnAt_ne_top`: `Γ^An` takes values in `[-∞, Γ_max]`, in
  particular in `[-∞, ∞)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.DivDict2

open Set Filter MeasureTheory
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

/-! ### `(-∞)^An = -∞` -/

section Bot

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance divDict2BotPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDict2BotPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- A germ in the multiplier ideal `𝓘(c · (-∞))` vanishes near the point: `|g|² e^{+∞}` is only
integrable when `g = 0` almost everywhere, hence (continuity) near the point. -/
theorem eventually_eq_zero_of_mem_multiplierIdeal_bot {c : ℝ} {x : SchemeComplexPoint f}
    {g : SchemeComplexPoint f → ℂ}
    (hg : (multiplierIdeal (n := n) c (⊥ : SchemeComplexPoint f → EReal)).mem x g) :
    g =ᶠ[𝓝 x] 0 := by
  obtain ⟨-, hc, U, hUo, hxU, hdiff, hmeas, hint⟩ := hg
  set e := complexChartAt (n := n) x with he
  have hae : ∀ᵐ z ∂(volume.restrict U), multiplierDensity
      (chartFunction (⊥ : SchemeComplexPoint f → EReal) e) c (fun z => g (e.val.symm z)) z < ⊤ :=
    ae_lt_top' hmeas hint.ne
  have hae0 : (fun z => g (e.val.symm z)) =ᵐ[volume.restrict U] fun _ => (0 : ℂ) := by
    filter_upwards [hae] with z hz
    by_contra hne
    rw [multiplierDensity_eq_top_at_pole (φ := chartFunction (⊥ : SchemeComplexPoint f → EReal) e)
      (f := fun z => g (e.val.symm z)) (x := z) hc rfl hne] at hz
    exact lt_irrefl _ hz
  have heq : EqOn (fun z => g (e.val.symm z)) (fun _ => (0 : ℂ)) U :=
    Measure.eqOn_open_of_ae_eq hae0 hUo hdiff.continuousOn continuousOn_const
  have hev : ∀ᶠ y in 𝓝 x, y ∈ e.val.source ∧ e.val y ∈ U :=
    Filter.Eventually.and (e.val.open_source.mem_nhds (mem_complexChartAt_source x))
      (e.val.continuousAt (mem_complexChartAt_source x) (hUo.mem_nhds hxU))
  filter_upwards [hev] with y hy
  have h := heq hy.2
  simp only at h
  rw [e.val.left_inv hy.1] at h
  exact h

/-- `𝓘(c · (-∞)) ⊆ (0)^an`. -/
theorem multiplierIdeal_bot_le (c : ℝ) :
    (multiplierIdeal (n := n) c (⊥ : SchemeComplexPoint f → EReal)).Le
      (analytificationIdeal f n E (⊥ : X.IdealSheafData)) := by
  intro x g hg
  refine ⟨hg.1, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  filter_upwards [eventually_eq_zero_of_mem_multiplierIdeal_bot n hg] with y hy
  simpa using hy

/-- The algebraic model of `𝓘(c · (-∞))` is the zero ideal sheaf. -/
theorem algebraization_multiplierIdeal_bot (c : ℝ) :
    algebraization f n E (multiplierIdeal (n := n) c (⊥ : SchemeComplexPoint f → EReal)) = ⊥ :=
  le_bot_iff.mp ((algebraization_mono f n E (multiplierIdeal_bot_le n E c)).trans
    (algebraization_analytificationIdeal_le f n E ⊥))

/-- **The convention `(-∞)^An(v) = -∞` of `def:Gammaana` is a theorem**: the analytification of
the constant `-∞` is `-∞` at every point `v ∈ X^An`. -/
theorem potentialAn_bot [IsProper f] (v : BerkovichPoint f) :
    potentialAn n E (⊥ : SchemeComplexPoint f → EReal) v = ⊥ := by
  have hk : ∀ k : ℕ, v.multiplierIdealVal n E ⊥ k / k = ⊤ := fun k => by
    unfold BerkovichPoint.multiplierIdealVal
    rw [algebraization_multiplierIdeal_bot, SGPT.NAPotential.BJModel.idealVal_bot]
    exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top k)
  have hv : v.potentialVal n E ⊥ = ⊤ := by
    unfold BerkovichPoint.potentialVal
    simp_rw [hk]
    exact tendsto_const_nhds.limUnder_eq
  unfold potentialAn
  rw [hv, EReal.coe_ennreal_top, EReal.neg_top]

end Bot

/-! ### The endpoint and the supremum over all `τ` -/

section NA

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance divDict2EndPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDict2EndPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDict2EndPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

/-- **The endpoint slice `Γ_{Γ_max} = inf_{τ < Γ_max} Γ_τ` is `(θ + ω)`-psh**: a decreasing limit
of `(θ + ω)`-psh functions which are fixed points of the envelope (supremum `0`), hence not
`≡ -∞`. -/
theorem naComponent_cutoff_isThetaPshPotential (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    IsThetaPshPotential (atlasClosedFormToNative (sourceNAComponentBackground θ ω)).val
      (sourceTestCurveCutoff (Γ.component ω).val.toSourceTestCurvePredata) :=
  (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (Γ.component ω).val.toSourceTestCurvePredata.cutoff_thetaPSH

/-- **The dichotomy for the endpoint slice** (`def:Gammaana`): `Γ_{Γ_max}` is `(θ + ω)`-psh or
`≡ -∞` (the first alternative always holds, `naComponent_cutoff_isThetaPshPotential`). -/
theorem naComponent_cutoff_isThetaPSH_or_eq_bot (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    (ofFixedModel (m + 1) (SchemeComplexPoint f)).IsThetaPSH (sourceNAComponentBackground θ ω)
        (sourceTestCurveCutoff (Γ.component ω).val.toSourceTestCurvePredata) ∨
      sourceTestCurveCutoff (Γ.component ω).val.toSourceTestCurvePredata = ⊥ :=
  Or.inl (Γ.component ω).val.toSourceTestCurvePredata.cutoff_thetaPSH

/-- The endpoint term `Γ_{Γ_max}^{θ+ω,An}(v) + Γ_max` lies below `Γ^An(v)`. -/
theorem potentialAn_cutoff_add_le (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    potentialAn (m + 1) E (sourceTestCurveCutoff (Γ.component ω).val.toSourceTestCurvePredata) v +
        (((Γ.component ω).val.max : ℝ) : EReal) ≤ naPotentialAnAt (m + 1) E Γ ω v :=
  Berkovich.naPotentialAnAt_endpoint (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) Γ ω v
    (naComponent_cutoff_isThetaPshPotential Γ ω) fun τ _ => iInf_le _ τ

/-- **The endpoint `τ = Γ_max` of the printed supremum does not change it** (`def:Gammaana`),
unconditionally: `max(sup_{τ < Γ_max}(Γ_τ^An(v) + τ), Γ_{Γ_max}^An(v) + Γ_max)
= sup_{τ < Γ_max}(Γ_τ^An(v) + τ)`. -/
theorem naPotentialAnAt_sup_endpoint (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    max (naPotentialAnAt (m + 1) E Γ ω v)
      (potentialAn (m + 1) E (sourceTestCurveCutoff (Γ.component ω).val.toSourceTestCurvePredata)
        v + (((Γ.component ω).val.max : ℝ) : EReal)) = naPotentialAnAt (m + 1) E Γ ω v :=
  max_eq_left (potentialAn_cutoff_add_le Γ ω v)

/-- Every slice `Γ_τ`, `τ ∈ ℝ` (with `Γ_τ ≡ -∞` for `τ > Γ_max`), contributes at most `Γ^An(v)`. -/
theorem potentialAn_sourceTestCurveAt_add_le (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) (τ : ℝ) :
    potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata τ) v +
      (τ : EReal) ≤ naPotentialAnAt (m + 1) E Γ ω v := by
  set C := (Γ.component ω).val.toSourceTestCurvePredata with hC
  rcases lt_trichotomy τ C.max with hlt | heq | hgt
  · rw [sourceTestCurveAt_of_lt C hlt]
    exact le_naPotentialAnAt (m + 1) E Γ ω v ⟨τ, hlt⟩
  · rw [heq, sourceTestCurveAt_eq_max]
    exact potentialAn_cutoff_add_le Γ ω v
  · rw [sourceTestCurveAt_of_gt C hgt, potentialAn_bot, EReal.bot_add]
    exact bot_le

/-- **`eq:psiandef` as printed**: `Γ^An(v) = sup_{τ ≤ Γ_max} (Γ_τ^{θ+ω,An}(v) + τ)`, the endpoint
slice being `Γ_{Γ_max} = inf_{τ < Γ_max} Γ_τ`. -/
theorem naPotentialAnAt_eq_iSup_le (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E Γ ω v =
      ⨆ τ : Iic (Γ.component ω).val.max,
        potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata τ)
          v + ((τ : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have hτ : (τ : ℝ) ≤ (Γ.component ω).val.max := le_of_lt τ.2
    refine le_trans (le_of_eq ?_) (le_iSup (fun σ : Iic (Γ.component ω).val.max =>
      potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata σ)
        v + ((σ : ℝ) : EReal)) ⟨τ, hτ⟩)
    rw [sourceTestCurveAt_of_lt _ τ.2]
  · exact iSup_le fun τ => potentialAn_sourceTestCurveAt_add_le Γ ω v τ

/-- **The second form of `eq:psiandef`**: `Γ^An(v) = sup_{τ ∈ ℝ} (Γ_τ^{θ+ω,An}(v) + τ)`, with
`Γ_τ ≡ -∞` for `τ > Γ_max` and `(-∞)^An = -∞` (`potentialAn_bot`). -/
theorem naPotentialAnAt_eq_iSup (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E Γ ω v =
      ⨆ τ : ℝ,
        potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata τ)
          v + (τ : EReal) := by
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    refine le_trans (le_of_eq ?_) (le_iSup (fun σ : ℝ =>
      potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata σ)
        v + (σ : EReal)) τ)
    rw [sourceTestCurveAt_of_lt _ τ.2]
  · exact iSup_le fun τ => potentialAn_sourceTestCurveAt_add_le Γ ω v τ

/-- `Γ^An(v) ≤ Γ_max` for every `v ∈ X^An`. -/
theorem naPotentialAnAt_le_max (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E Γ ω v ≤ (((Γ.component ω).val.max : ℝ) : EReal) := by
  refine iSup_le fun τ => ?_
  calc potentialAn (m + 1) E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal)
      ≤ 0 + ((τ : ℝ) : EReal) := add_le_add (potentialAn_nonpos (m + 1) E _ v) le_rfl
    _ ≤ (((Γ.component ω).val.max : ℝ) : EReal) := by
        rw [zero_add]
        exact EReal.coe_le_coe_iff.mpr (le_of_lt τ.2)

/-- **`Γ^An` takes values in `[-∞, ∞)`** (`def:Gammaana`). -/
theorem naPotentialAnAt_ne_top (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E Γ ω v ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (naPotentialAnAt_le_max Γ ω v)

/-- **`def:Gammaana` on `X^Div`**: `Γ^An : X^Div → [-∞, ∞)` is the printed supremum over
`τ ≤ Γ_max`, and the supremum over all `τ ∈ ℝ`. -/
theorem naPotentialAnDiv_eq_iSup_le [IrreducibleSpace X] (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : sourceDivisorialSet f) :
    naPotentialAnDiv (m + 1) E Γ ω v =
        ⨆ τ : Iic (Γ.component ω).val.max,
          potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata τ)
            v.1 + ((τ : ℝ) : EReal) ∧
      naPotentialAnDiv (m + 1) E Γ ω v =
        ⨆ τ : ℝ,
          potentialAn (m + 1) E (sourceTestCurveAt (Γ.component ω).val.toSourceTestCurvePredata τ)
            v.1 + (τ : EReal) ∧
      naPotentialAnDiv (m + 1) E Γ ω v ≠ ⊤ :=
  ⟨naPotentialAnAt_eq_iSup_le Γ ω v.1, naPotentialAnAt_eq_iSup Γ ω v.1,
    naPotentialAnAt_ne_top Γ ω v.1⟩

end NA

end SGPT.NAPotential.DivDict2

end
