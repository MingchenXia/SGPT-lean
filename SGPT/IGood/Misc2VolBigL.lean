import SGPT.IGood.DXMainStatement

/-!
# `cor:volbigL`: the volume of a pseudo-effective line bundle against `∫_X θ_{V_θ}ⁿ`

Source `cor:volbigL` (chapter *`𝓘`-good singularities*): for a pseudo-effective line bundle `L`
with a smooth Hermitian metric `h`, `θ = c₁(L, h)`,
`lim_{k → ∞} n! h⁰(X, Lᵏ) / kⁿ = ∫_X θ_{V_θ}ⁿ`.

The existing formalization (`SGPT.IGood.DXMain.volume_le_iVolume_thetaPshSupremum`) proves the
upper bound `vol L = limsup_k n! h⁰(X, Lᵏ)/kⁿ ≤ vol θ_{V_θ}` with the right-hand side in the
`𝓘`-volume form `vol θ_{V_θ} = ∫_X θ_{P_θ[V_θ]_𝓘}ⁿ`. This file identifies that right-hand
side with the book's `∫_X θ_{V_θ}ⁿ` (the non-pluripolar mass of `V_θ`): `V_θ` is `𝓘`-model,
`P_θ[V_θ]_𝓘 = V_θ`, because every competitor of the `𝓘`-envelope is a nonpositive `θ`-psh
function, hence `≤ V_θ`, while `V_θ` itself is a competitor.

## Main results

* `iSingularityEnvelope_thetaPshSupremum`: `P_θ[V_θ]_𝓘 = V_θ` on any complex manifold.
* `iVolume_thetaPshSupremum`: `vol θ_{V_θ} = ∫_X θ_{V_θ}ⁿ`.
* `volume_le_mass_thetaPshSupremum`: **`cor:volbigL`, the inequality `≤`** in the book's form
  `limsup_k n! h⁰(X, Lᵏ)/kⁿ ≤ ∫_X θ_{V_θ}ⁿ` (projective `X` carrying a smooth flag).
* `tendsto_normalized_h0_of_dxMain1Holds`, `tendsto_normalized_h0_of_lowerBound`: the equality
  of `cor:volbigL` follows from the instance `φ = V_θ` of `thm:DXmain1`, i.e. from
  `DXMainLowerBound` for `V_θ` (not proved here).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.Misc2VolBigL

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH SGPT.IGood.DXMain
open scoped Topology ENNReal Nat

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `V_θ` is `𝓘`-model: `P_θ[V_θ]_𝓘 = V_θ` whenever `V_θ ∈ PSH(X, θ)`. -/
theorem iSingularityEnvelope_thetaPshSupremum (θ : SmoothRealForm n M 2)
    (hV : IsThetaPshPotential θ (thetaPshSupremum θ)) :
    iSingularityEnvelope θ (thetaPshSupremum θ) = thetaPshSupremum θ := by
  apply le_antisymm
  · exact (iSingularityEnvelope_le_iff hV.1.quasiPlurisubharmonic.upperSemicontinuous).mpr
      fun u hu hu0 _ => le_thetaPshSupremum hu hu0
  · exact le_iSingularityEnvelope hV (thetaPshSupremum_le_zero θ)
      (IEquivalentOnManifold.refl _)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
theorem diagonalPotentialMass_congr (θ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (huv : u = v) (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ v hv := by
  subst huv
  rfl

omit [BorelSpace M] in
/-- `vol θ_{V_θ} = ∫_X θ_{P_θ[V_θ]_𝓘}ⁿ = ∫_X θ_{V_θ}ⁿ`. -/
theorem iVolume_thetaPshSupremum [Nonempty M] (θ : ClosedRealOneOneForm n M)
    (hlocal : HasSmoothLocalPotentials θ.val)
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val)) :
    iVolume θ hlocal (thetaPshSupremum θ.val) hV =
      diagonalPotentialMass θ (thetaPshSupremum θ.val) hV := by
  unfold iVolume
  exact diagonalPotentialMass_congr θ (iSingularityEnvelope_thetaPshSupremum θ.val hV) _ _

end General

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance volBigLTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance volBigLCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance volBigLManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

include Y hY in
/-- **Source `cor:volbigL`, the inequality `≤`, in the book's form**: for a pseudo-effective
line bundle `L` (`V_θ ∈ PSH(X, θ)`) with a smooth metric `H`, `θ = c₁(L, H)`, on a smooth
projective `X` carrying a smooth flag,
`limsup_k n! h⁰(X, Lᵏ) / kⁿ ≤ ∫_X θ_{V_θ}ⁿ`. -/
theorem volume_le_mass_thetaPshSupremum
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    SGPT.LineBundle.volume f L (m + 1) ≤
      diagonalPotentialMass (H.curvature a) (thetaPshSupremum (H.curvature a).val) hV := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
  have h := volume_le_iVolume_thetaPshSupremum f E a H Y hY hV
  rwa [iVolume_thetaPshSupremum] at h

/-- With the weight `V_θ` the normalized multiplier dimensions are the normalized
`n! h⁰(X, Lᵏ)/kⁿ`. -/
theorem normalizedMultiplierH0_thetaPshSupremum
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) (k : ℕ) :
    normalizedMultiplierH0 f E a H hV k =
      (((m + 1)! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1) := by
  unfold normalizedMultiplierH0
  rw [multiplierH0_thetaPshSupremum f E a H hV k]

/-- **Source `cor:volbigL` from `thm:DXmain1`**: the instance `φ = V_θ` of the asymptotic
Riemann–Roch formula gives `lim_k n! h⁰(X, Lᵏ)/kⁿ = ∫_X θ_{V_θ}ⁿ` (`eq:volbig`). The hypothesis
is the conclusion of `thm:DXmain1` for `φ = V_θ`, whose lower bound is open in this
formalization; this theorem is the consumer that closes `cor:volbigL` once it is available. -/
theorem tendsto_normalized_h0_of_dxMain1Holds [Nonempty (SchemeComplexPoint f)]
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hDX : DXMain1Holds f E a H hV) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    Tendsto (fun k : ℕ => (((m + 1)! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1))
      atTop (𝓝 (diagonalPotentialMass (H.curvature a)
        (thetaPshSupremum (H.curvature a).val) hV)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have h := hDX
  unfold DXMain1Holds at h
  rw [iVolume_thetaPshSupremum] at h
  have hfun : normalizedMultiplierH0 f E a H hV = fun k : ℕ =>
      (((m + 1)! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1) :=
    funext (normalizedMultiplierH0_thetaPshSupremum f E a H hV)
  rw [hfun] at h
  exact h

include Y hY in
/-- **Source `cor:volbigL` from the lower bound of `thm:DXmain1` for `φ = V_θ`**: on `X` carrying
a smooth flag, `DXMainLowerBound` for the weight `V_θ` (the open half of `thm:DXmain1`, owned by
another lane) gives `lim_k n! h⁰(X, Lᵏ)/kⁿ = ∫_X θ_{V_θ}ⁿ` (`eq:volbig`). -/
theorem tendsto_normalized_h0_of_lowerBound [Nonempty (SchemeComplexPoint f)]
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    Tendsto (fun k : ℕ => (((m + 1)! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1))
      atTop (𝓝 (diagonalPotentialMass (H.curvature a)
        (thetaPshSupremum (H.curvature a).val) hV)) :=
  tendsto_normalized_h0_of_dxMain1Holds f E a H hV
    (dxMain1Holds_of_lowerBound f E a H Y hY hV hlow)

end SGPT.IGood.Misc2VolBigL
