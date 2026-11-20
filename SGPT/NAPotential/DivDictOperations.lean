import SGPT.NAPotential.AnTransIndependence
import SGPT.NAPotential.GAGAMult2Limit
import SGPT.PSH.SourceNAOrder
import SGPT.PSH.SourceNATranslation

/-! # `Γ ↦ Γ^An` on `X^An`: order, translation, the endpoint of the supremum

Source `chapter_NApotential.tex`: `def:Gammaana` (`eq:psiandef`), the first sentence of
`lma:anaorder` (*the map `Γ ↦ Γ^An` is order preserving by definition*), the translation clause
of `thm:NApotential:L1352`, and the remark in the proof of `prop:anpreinf` that the endpoint
`τ = Γ_max` does not affect the supremum.  Blueprint `claude-div-dict:order-preserving`,
`claude-div-dict:translate`, `claude-div-dict:endpoint`.

All statements hold at every point `v` of the Berkovich space `X^An` (not only on `X^Div`).

* `naPotentialAnAt_mono`: `Γ ≤ Γ'` implies `Γ^An(v) ≤ Γ'^An(v)`; this uses the monotonicity of
  `φ ↦ φ^An`, available conditionally on the algebraicity of multiplier ideals
  (`MultiplierIdealAlgebraic`, GAGA).
* `naPotentialAnAt_translate`: `(Γ + c)^An(v) = Γ^An(v) + c` (unconditional).
* `naPotentialAnAt_endpoint`: if `ψ` is quasi-psh and `ψ ≤ Γ_τ` for all `τ < Γ_max` (e.g. the
  endpoint slice `Γ_{Γ_max} = inf_{τ < Γ_max} Γ_τ`, when it is not `≡ -∞`), then
  `ψ^An(v) + Γ_max ≤ sup_{τ < Γ_max} (Γ_τ^An(v) + τ)`; so adding the endpoint `τ = Γ_max` to the
  supremum of `eq:psiandef` does not change it (conditional on `MultiplierIdealAlgebraic`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance divDictOpPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDictOpPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance divDictOpPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}

/-- The slices of the components of `Γ` are `(θ + ω)`-psh potentials in the sense of
`SGPT.Foundations.Analysis`. -/
theorem naComponent_potential_isThetaPshPotential (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (τ : Iio (Γ.component ω).val.max) :
    IsThetaPshPotential (atlasClosedFormToNative (sourceNAComponentBackground θ ω)).val
      ((Γ.component ω).val.potential τ) :=
  (isThetaPSH_iff_nativeThetaPotential _ _).mp ((Γ.component ω).val.thetaPSH τ)

variable {k E}

/-- **Order preservation** (first sentence of `lma:anaorder`): `Γ ≤ Γ'` implies
`Γ^An(v) ≤ Γ'^An(v)` for every `v ∈ X^An`, conditionally on `MultiplierIdealAlgebraic`. -/
theorem naPotentialAnAt_mono (hA : MultiplierIdealAlgebraic f k E) {Γ Γ' : SourceNAPotential θ}
    (h : SourceNAPOrder Γ Γ') (ω : SourceKahlerForm k (SchemeComplexPoint f))
    (v : BerkovichPoint f) : naPotentialAnAt k E Γ ω v ≤ naPotentialAnAt k E Γ' ω v := by
  obtain ⟨hcut, hle⟩ := (sourceTestCurvePOrder_iff (sourceKahlerFormRepresentative ω) _ _).mp
    ((sourceNAPOrder_iff_component Γ Γ' ω).mp h)
  refine iSup_le fun τ => ?_
  have hτ' : (τ : ℝ) < (Γ'.component ω).val.max := lt_of_lt_of_le τ.2 hcut
  refine le_trans ?_ (le_naPotentialAnAt k E Γ' ω v ⟨τ, hτ'⟩)
  exact add_le_add (BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic k E hA
    (naComponent_potential_isThetaPshPotential k Γ ω τ)
    (naComponent_potential_isThetaPshPotential k Γ' ω ⟨τ, hτ'⟩) (hle τ τ.2) v) le_rfl

private theorem ereal_add_sub_add (x : EReal) (τ c : ℝ) :
    x + ((τ - c : ℝ) : EReal) + (c : EReal) = x + (τ : EReal) := by
  rw [add_assoc, ← EReal.coe_add, sub_add_cancel]

/-- **Translation** (the translation clause of `thm:NApotential:L1352`, on all of `X^An`):
`(Γ + c)^An(v) = Γ^An(v) + c`. -/
theorem naPotentialAnAt_translate (Γ : SourceNAPotential θ) (c : ℝ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt k E (Γ.translate c) ω v = naPotentialAnAt k E Γ ω v + (c : EReal) := by
  set C := (Γ.component ω).val with hC
  have hmax : (C.translate c).max = C.max + c := C.translate_max c
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have hτ : (τ : ℝ) < (C.translate c).max := τ.2
    have hτ' : (τ : ℝ) - c < C.max := by rw [hmax] at hτ; linarith
    have hle := le_naPotentialAnAt k E Γ ω v ⟨(τ : ℝ) - c, hτ'⟩
    calc potentialAn k E (((Γ.translate c).component ω).val.potential τ) v + ((τ : ℝ) : EReal)
        = potentialAn k E (C.potential ⟨(τ : ℝ) - c, hτ'⟩) v + (((τ : ℝ) - c : ℝ) : EReal) +
            (c : EReal) := (ereal_add_sub_add _ _ c).symm
      _ ≤ naPotentialAnAt k E Γ ω v + (c : EReal) := add_le_add hle le_rfl
  · have hA : naPotentialAnAt k E Γ ω v ≤
        naPotentialAnAt k E (Γ.translate c) ω v + ((-c : ℝ) : EReal) := by
      refine iSup_le fun σ => ?_
      have hσ : (σ : ℝ) < C.max := σ.2
      have hσ' : (σ : ℝ) + c < (C.translate c).max := by rw [hmax]; linarith
      have hle := le_naPotentialAnAt k E (Γ.translate c) ω v ⟨(σ : ℝ) + c, hσ'⟩
      have hpot : ((Γ.translate c).component ω).val.potential ⟨(σ : ℝ) + c, hσ'⟩ =
          C.potential σ := by
        change C.potential ⟨(σ : ℝ) + c - c, _⟩ = C.potential σ
        congr 1
        apply Subtype.ext
        change (σ : ℝ) + c - c = σ
        ring
      rw [hpot] at hle
      calc potentialAn k E (C.potential σ) v + ((σ : ℝ) : EReal)
          = potentialAn k E (C.potential σ) v + (((σ : ℝ) + c : ℝ) : EReal) +
              ((-c : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
            congr 2
            ring
        _ ≤ _ := add_le_add hle le_rfl
    calc naPotentialAnAt k E Γ ω v + (c : EReal)
        ≤ naPotentialAnAt k E (Γ.translate c) ω v + ((-c : ℝ) : EReal) + (c : EReal) :=
          add_le_add hA le_rfl
      _ = naPotentialAnAt k E (Γ.translate c) ω v := by
          rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

/-- A bound `x + τ ≤ S` for all `τ < M` gives `x + M ≤ S` (for `x ≠ ⊤`). -/
theorem add_coe_le_of_forall_lt {x S : EReal} {M : ℝ} (hx : x ≠ ⊤)
    (h : ∀ τ : ℝ, τ < M → x + (τ : EReal) ≤ S) : x + (M : EReal) ≤ S := by
  rcases eq_or_ne x ⊥ with hbot | hbot
  · rw [hbot, EReal.bot_add]
    exact bot_le
  · lift x to ℝ using ⟨hx, hbot⟩
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hSq, hq⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hq' : q < x + M := by
      rw [← EReal.coe_add] at hq
      exact EReal.coe_lt_coe_iff.mp hq
    have hle := h (q - x) (by linarith)
    rw [← EReal.coe_add] at hle
    have : ((x + (q - x) : ℝ) : EReal) = (q : EReal) := by
      congr 1
      ring
    rw [this] at hle
    exact absurd hSq (not_lt.mpr hle)

/-- **The endpoint of the supremum in `eq:psiandef`** (`def:Gammaana`; the remark in the proof of
`prop:anpreinf`).  If `ψ` is quasi-psh and lies below every slice `Γ_τ`, `τ < Γ_max`, of the
component of `Γ` at `ω` — e.g. `ψ = Γ_{Γ_max} = inf_{τ < Γ_max} Γ_τ` when this is not `≡ -∞` —
then `ψ^An(v) + Γ_max ≤ sup_{τ < Γ_max} (Γ_τ^An(v) + τ)` for every `v ∈ X^An`: the endpoint
`τ = Γ_max` does not change the supremum.  Conditional on `MultiplierIdealAlgebraic`. -/
theorem naPotentialAnAt_endpoint (hA : MultiplierIdealAlgebraic f k E) (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (v : BerkovichPoint f)
    {ψ : SchemeComplexPoint f → EReal} {θ' : SmoothRealForm k (SchemeComplexPoint f) 2}
    (hψ : IsThetaPshPotential θ' ψ)
    (hle : ∀ (τ : Iio (Γ.component ω).val.max) (x : SchemeComplexPoint f),
      ψ x ≤ (Γ.component ω).val.potential τ x) :
    potentialAn k E ψ v + (((Γ.component ω).val.max : ℝ) : EReal) ≤ naPotentialAnAt k E Γ ω v := by
  have hx : potentialAn k E ψ v ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (potentialAn_nonpos k E ψ v)
  refine add_coe_le_of_forall_lt hx fun τ hτ => ?_
  refine le_trans ?_ (le_naPotentialAnAt k E Γ ω v ⟨τ, hτ⟩)
  exact add_le_add (BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic k E hA hψ
    (naComponent_potential_isThetaPshPotential k Γ ω ⟨τ, hτ⟩) (hle ⟨τ, hτ⟩) v) le_rfl

/-- The endpoint slice `Γ_{Γ_max} = inf_{τ < Γ_max} Γ_τ` (when it is quasi-psh, i.e. not
`≡ -∞`) can be added to the supremum of `eq:psiandef` without changing it. -/
theorem naPotentialAnAt_sup_endpoint (hA : MultiplierIdealAlgebraic f k E)
    (Γ : SourceNAPotential θ) (ω : SourceKahlerForm k (SchemeComplexPoint f))
    (v : BerkovichPoint f) {θ' : SmoothRealForm k (SchemeComplexPoint f) 2}
    (hend : IsThetaPshPotential θ'
      (fun x => ⨅ τ : Iio (Γ.component ω).val.max, (Γ.component ω).val.potential τ x)) :
    max (naPotentialAnAt k E Γ ω v)
      (potentialAn k E (fun x => ⨅ τ : Iio (Γ.component ω).val.max,
        (Γ.component ω).val.potential τ x) v + (((Γ.component ω).val.max : ℝ) : EReal)) =
      naPotentialAnAt k E Γ ω v :=
  max_eq_left (naPotentialAnAt_endpoint hA Γ ω v hend fun τ _ => iInf_le _ τ)

end SGPT.NAPotential.Berkovich

end
