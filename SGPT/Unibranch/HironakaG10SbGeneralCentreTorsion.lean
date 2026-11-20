import SGPT.Unibranch.HironakaG10SbGeneralCentreSaturation
import SGPT.Unibranch.HironakaG10SbTorsionSaturation

/-!
# Full pullback saturation is the exceptional torsion (G10-02-08.a)

Lane G10SB, run 0081, plan item G10-02-08 (sub-item 08.a, manifold ambient, general admissible centre).
Hironaka 1975 Lemma 3.1 / Remark 3.1.2 (printed p. 530) and (4.2.2) (p. 534): after blowing up, the strict
transform of the pulled module `F'` is `F'` modulo its `I`-torsion, `I` the (invertible) exceptional ideal,
i.e. modulo `⋃ₘ ker (F' → Hom(Iᵐ, F'))`.  In the chart of G10-02-07.a the exceptional ideal is the principal
ideal of the pivot `p`, so the `I`-torsion of `F' = 𝒪_{Y,y} ⧸ I_p` is its literal `p`-power torsion.  Here,
for the WHOLE (possibly nonreduced) native pullback stalk ideal `I_p`:

* `strict_eq_powerSat` — the normalized strict ideal `J` of 07.a is exactly the `p`-saturation of `I_p`;
* `exists_actual_hs_centre_exceptional_torsion` — one chart in which the whole exceptional stalk ideal is
  `(p)`, `J = powerSat I_p p`, the kernel of `𝒪/I_p → 𝒪/J` is the `p`-power torsion of `𝒪/I_p`, and
  `(𝒪/I_p)/torsion ≅ 𝒪/J`.

No named input; the comparison is on the full nonreduced ideal, not on zero sets or radicals.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG10SbGeneralCentreTorsion

noncomputable section

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences HolGerm BlowupFlatCoordinates
  BlowupExceptionalDivisor HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualCoefficientPresentationCentrePower HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetMonomialSpan HironakaActualHistoricalMovingCentreChart
  SGPT.Unibranch.HironakaG10AdaptedStalkIdeal
  SGPT.Unibranch.HironakaG10SbTorsionSaturation SGPT.Unibranch.HironakaG10SbGeneralCentreSaturation

variable {d t : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]

/-- **G10-02-08.a.**  In one chart of a general admissible blowup, the whole exceptional stalk ideal is
`(p)`, the actual strict ideal is the full `p`-saturation of the whole native pullback stalk ideal, its
quotient map has kernel the literal `p`-power torsion, and the torsion quotient is the strict quotient. -/
theorem exists_actual_hs_centre_exceptional_torsion
    (I : GermIdeal (d+t) X) (hI : I.IsCoherent) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (d+t) C π) (y : Y)
    (hCy : RegularAtDim (n := d+t) C (π y) d)
    (hhs : ∀ c ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt I c ℓ = hilbertSamuelAt I (π y) ℓ) :
    ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π y) (π y)))
      (j : Fin t) (b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π y)) = 0)
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y) = 0),
      let E := adaptedStalkEquiv y Θ hΘ0
      let p := E.symm (coordinateGerm (j.natAdd d))
      let Ip := actualWholeSheafStalkIdeal (GermIdeal.pullback (m := d+t) π I) y
      let J := (actualAnalyticNormalizedMemberIdeal (adaptedIdeal I (π y) Φ hΦ0)
        (actualTangentCentreVariables d t) (j.natAdd d) b).comap E.toRingHom
      actualWholeSheafStalkIdeal (exceptionalDivisor hπ).ideal y = Ideal.span {p} ∧
      J = powerSat Ip p ∧
      RingHom.ker (toSat Ip p) = pivotTorsion Ip p ∧
      IsRegular (Ideal.Quotient.mk J p) := by
  obtain ⟨Φ, j, b, Θ, hΦ0, hΘ0, _hΦsrc, _hΘsrc, _hb, _hflat, _hSquare, hrest⟩ :=
    exists_actual_hs_centre_exceptional_stalk_saturation I hI hπ y hCy hhs
  obtain ⟨_hEp, hExc, _hmap, _hmapJ, hwhole, _hpivot, hreg, _hcolon⟩ := hrest
  refine ⟨Φ, j, b, Θ, hΦ0, hΘ0, ?_⟩
  exact ⟨hExc, eq_powerSat_of_forall hwhole, ker_toSat _ _, hreg⟩

end

end SGPT.Unibranch.HironakaG10SbGeneralCentreTorsion
