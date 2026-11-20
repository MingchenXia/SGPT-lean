import SGPT.Toric.ToricMonomialValuation
import SGPT.Toric.LatticeRationalDensity
import SGPT.Toric.ToricFlagVolume
import SGPT.Toric.ToricIVolumeNewtonBody
import SGPT.Okounkov.ValuativeFirstCoordinate
import SGPT.Okounkov.PartialBodyDS

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Okounkov SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody SGPT.Okounkov.Valuative
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {d : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (d + 1) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The first source I-monotonicity inclusion needs no bigness hypothesis:
each positive εω perturbation is an actual Kähler current. -/
theorem generalPartialBody_mono_iOrder_only {F : OriginalFlagGeometry (d + 1)}
    {θ : ClosedRealOneOneForm (d + 1) F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hI : IOrderOnManifold (n := d + 1) u v) :
    generalPartialBody F θ u ⊆ generalPartialBody F θ v := by
  apply iInter_mono
  intro j
  exact (kahlerPartialBody_subset_of_iOrder
    (isKahlerCurrentPotential_add_smul hu F.omega (by positivity))
    (isKahlerCurrentPotential_add_smul hv F.omega (by positivity)) hI).1

namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- Every ACTUAL normalized lattice point in the original Newton body is
the original current valuation of a produced analytic monomial current
I-below the original potential, hence belongs to its actual partial body. -/
theorem flagImage_normalizedLatticePoints_subset_partialBody
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (e : Fin (d + 1) ≃ Fin (d + 1)) :
    toricFlagRealMap hs v e D '' normalizedLatticePoints (h.newtonBody φ) ⊆
      generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ := by
  rintro _ ⟨p, ⟨hp, q, hq, m, hpq⟩, rfl⟩
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφ
  have hpP := (h.newtonBody_properties hP hφ).2.2.2 hp
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm : m ∈ toricLatticePoints ((q : ℤ) • D) := by
    change latticeVector m ∈ toricDivisorPolytope ((q : ℤ) • D)
    rw [mem_toricDivisorPolytope_smul_iff D hq]
    have hmx : latticeVector m = (q : ℝ) • p := by
      rw [hpq, smul_smul, mul_inv_cancel₀ hqR, one_smul]
    rw [hmx]
    exact Set.smul_mem_smul_set hpP
  have hψ := h.monomialPotential_mem hq hm
  have hI : sourceIOrder (ofFixedModel (d + 1) (PolytopeToricVariety γ hs))
      (h.monomialPotential hq hm) φ := by
    apply (h.sourceIOrder_iff_newtonBody_subset hψ hφ).mpr
    rw [monomialPotential, h.newtonBody_linearPotential]
    exact singleton_subset_iff.mpr (by rwa [← hpq])
  have hψn : IsThetaPshPotential h.form.val (h.monomialPotential hq hm) :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mp hψ.1
  have hφn : IsThetaPshPotential h.form.val φ :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mp hφ.1
  obtain ⟨c, I, htype⟩ := h.monomialPotential_hasAnalyticSingularities hq hm
  have hA : h.monomialPotential hq hm ∈ analyticCurrents h.form :=
    ⟨hψn, SGPT.Okounkov.TranscendentalPole.hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType htype⟩
  have hmember := flagValuation_mem_generalPartialBody_of_analytic
    (F := toricFlagGeometry (hs := hs) v e) hA
  have hmono := generalPartialBody_mono_iOrder_only
    (F := toricFlagGeometry (hs := hs) v e) hψn hφn
    ((sourceIOrder_iff_native (h.isQPSH_of_mem hψ) (h.isQPSH_of_mem hφ)).mp hI)
  have hmember' := hmono hmember
  rwa [h.flagValuation_monomialPotential hq hm v e, ← hpq] at hmember'

/-- Positive original mass and actual lattice approximation give literal
Newton-image containment in the original general partial body. -/
theorem flagImage_newtonBody_subset_partialBody
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (hpos : 0 < h.MA hφ univ)
    (v : latticePolytopeVertices γ) (e : Fin (d + 1) ≃ Fin (d + 1)) :
    toricFlagRealMap hs v e D '' h.newtonBody φ ⊆
      generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφ
  obtain ⟨_, hc, hconv, _⟩ := h.newtonBody_properties hP hφ
  have hvol := (h.volume_newtonBody_pos_iff hP hφ).mp hpos
  have hint := interior_nonempty_of_convex_of_measure_pos volume hconv hvol
  have hcl := closure_normalizedLatticePoints_eq hconv hc.isClosed hint
  have hclosed : IsClosed ((toricFlagRealMap hs v e D) ⁻¹'
      generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ) :=
    (isClosed_generalPartialBody (F := toricFlagGeometry (hs := hs) v e) h.form φ).preimage (continuous_toricFlagRealMap v e D)
  have hsub := closure_minimal
    (Set.image_subset_iff.mp (h.flagImage_normalizedLatticePoints_subset_partialBody hφ v e)) hclosed
  rw [hcl] at hsub
  exact Set.image_subset_iff.mpr hsub

/-- Whole positive-dimensional source `thm:toricpob`: the actual general
partial Okounkov body is the literal image of the original Newton body.
Only the original toric PSH and positive non-pluripolar mass are assumed. -/
theorem sourceToricPartialBody_eq_flagImage_pos
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (hpos : 0 < h.MA hφ univ)
    (v : latticePolytopeVertices γ) (e : Fin (d + 1) ≃ Fin (d + 1)) :
    toricFlagRealMap hs v e D '' h.newtonBody φ =
      generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ := by
  have hφn : IsThetaPshPotential h.form.val φ :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mp hφ.1
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφ
  obtain ⟨_, hc, hconv, _⟩ := h.newtonBody_properties hP hφ
  have hCcomp := hc
  have hAcomp := hCcomp.image (continuous_toricFlagRealMap v e D)
  have hAconv : Convex ℝ (toricFlagRealMap hs v e D '' h.newtonBody φ) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • y, hconv hx hy ha hb hab, ?_⟩
    funext j
    simp only [toricFlagRealMap, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (intPairing (toricCartierDatum D v)
      (polytopeToricRayGenerator γ hs v (e j)) : ℝ) * hab
  have hB := convex_isCompact_generalPartialBody
    (F := toricFlagGeometry (hs := hs) v e) hφn
  have hfactor : ((d + 1).factorial : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (d + 1)).ne'
  have hvolB : volume (generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ) =
      volume (h.newtonBody φ) := by
    let : MeasurableSpace (toricFlagGeometry (hs := hs) v e).carrier :=
      borel (toricFlagGeometry (hs := hs) v e).carrier
    let : BorelSpace (toricFlagGeometry (hs := hs) v e).carrier := ⟨rfl⟩
    have hnative : iVolume h.form
        (LocalPotentials.closedRealOneOne_hasLocalPotentials h.form) φ hφn =
        sourceIVolume h.atlasForm φ hφ.1 :=
      (sourceIVolume_eq_native h.atlasForm φ hφ.1
        (LocalPotentials.closedRealOneOne_hasLocalPotentials h.form)).symm
    calc
      volume (generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ) =
          iVolume h.form (LocalPotentials.closedRealOneOne_hasLocalPotentials h.form) φ hφn /
            ((d + 1).factorial : ENNReal) :=
        volume_generalPartialBody_of_borelSpace (F := toricFlagGeometry (hs := hs) v e) hφn
      _ = sourceIVolume h.atlasForm φ hφ.1 / ((d + 1).factorial : ENNReal) := by rw [hnative]
      _ = volume (h.newtonBody φ) := by
        rw [h.sourceIVolume_eq_factorial_volume_newtonBody hφ, mul_comm,
          ENNReal.mul_div_cancel_right hfactor (ENNReal.natCast_ne_top _)]

  have hvolA := volume_image_toricFlagRealMap v e D (h.newtonBody φ)
  exact eq_of_subset_of_equal_haar_volume volume hAconv hAcomp.isClosed hB.1 hB.2.isBounded
    (h.flagImage_newtonBody_subset_partialBody hφ hpos v e)
    (by rw [hvolA]; exact (h.volume_newtonBody_pos_iff hP hφ).mp hpos)
    hAcomp.measure_lt_top.ne (hvolA.trans hvolB.symm)

end BigToricMetric
end SGPT.Toric
