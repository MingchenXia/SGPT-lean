import SGPT.Toric.ToricMonomialDivisor
import SGPT.Okounkov.TranscendentalCoreValuationBounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Okounkov SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup.Counting
open scoped Topology ContDiff BigOperators Manifold ENNReal NNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The original CURRENT valuation of the actual monomial potential is
exactly the normalized integer SECTION valuation. Both recursions are
independently defined and proved equal through the literal principal ideal. -/
theorem flagValuation_monomialPotential {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    flagValuation (toricFlagGeometry (hs := hs) v e) (h.monomialPotential hq hm) =
      toricFlagRealMap hs v e D ((q : ℝ)⁻¹ • latticeVector m) := by
  let F := toricFlagGeometry (hs := hs) v e
  let x := toricFlagPoint (hs := hs) v e
  let g := NativeHolGerm.mk (monomialChartCoefficient D q m v)
    (holomorphicAt_toricMonomial_comp v ((q : ℤ) • D) m)
  have hval : originalFlagGermValuation F x g =
      ((toLex (toricFlagLatticeMap hs v e ((q : ℤ) • D) m) : Lex (Fin n → ℤ)) :
        WithTop (Lex (Fin n → ℤ))) :=
    originalFlagGermValuation_toricMonomial v e ((q : ℤ) • D) hm
  have hg : g ≠ 0 := by
    intro hz
    rw [hz, (originalFlagGermValuation F x).map_zero] at hval
    exact WithTop.coe_ne_top hval.symm
  let ν := originalFlagGermVector F x g hg
  have hνint : (fun i => (ν i : ℤ)) = toricFlagLatticeMap hs v e ((q : ℤ) • D) m := by
    rw [originalFlagGermValuation_apply_of_ne_zero F x g hg] at hval
    exact toLex_inj.mp (WithTop.coe_injective hval)
  have hνreal : (fun i => (ν i : ℝ)) = integerCast (toricFlagLatticeMap hs v e ((q : ℤ) • D) m) := by
    funext i
    change (ν i : ℝ) = ((toricFlagLatticeMap hs v e ((q : ℤ) • D) m i : ℤ) : ℝ)
    exact_mod_cast congrFun hνint i
  obtain ⟨E, htype, hread⟩ := h.exists_monomial_effectiveDivisor hq hm
  have hgen : ∀ f, E.ideal.mem x.1 f ↔ ∃ hf : HolomorphicAt n f x.1,
      NativeHolGerm.mk f hf ∈ Ideal.span {g} := by
    intro f
    rw [hread v x.1 (vertexPoint_mem_source v 0) f]
    have hgh : HolomorphicAt n (monomialChartCoefficient D q m v) x.1 :=
      holomorphicAt_toricMonomial_comp v ((q : ℤ) • D) m
    constructor
    · intro hf
      exact ⟨hf.1, (NativeHolGerm.mem_span_singleton_mk_iff f _ hf.1 hgh).mpr hf⟩
    · rintro ⟨hf, hmem⟩
      exact (NativeHolGerm.mem_span_singleton_mk_iff f _ hf hgh).mp hmem
  have hCartier := originalCartierFlagValuation_of_native_generator n F x E g hg hgen
  obtain ⟨ED, _hEDsupport, hED⟩ := DivisorMetric.exists_divisorMetric E
  have hEDpsh := isThetaPshPotential_effectiveDivisorMetric E ED hED
  have hEDvector := originalPotentialFlagValuation_of_originalCartierFlagValuation
    n F E ED hED ν hCartier
  have hEDunique := originalPotentialFlagValuation_eq_of_iEquivalent n F ED.weight ED.weight
    (potentialFlagValuation F hEDpsh) (fun i => (ν i : ℝ≥0))
    (potentialFlagValuation_spec F hEDpsh) hEDvector (IEquivalentOnManifold.refl ED.weight)
  have hEDval : flagValuation F ED.weight = integerCast
      (toricFlagLatticeMap hs v e ((q : ℤ) • D) m) := by
    rw [flagValuation_eq hEDpsh, hEDunique]
    simpa only [NNReal.coe_natCast] using hνreal
  have hu : IsThetaPshPotential h.form.val (h.monomialPotential hq hm) :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mp (h.monomialPotential_mem hq hm).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huq := RestrictedApproximantComparison.isThetaPshPotential_smul hu hqR
  have hsame := IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type htype
    (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hED)
  have hI : IEquivalentOnManifold (n := n)
      (fun y => ((q : ℝ) : EReal) * h.monomialPotential hq hm y) ED.weight := by
    constructor
    · obtain ⟨C, hC⟩ := hsame.1
      exact iOrderOnManifold_of_le_add hEDpsh.quasiPshPotential.1
        (fun y => hC y (mem_univ y))
    · obtain ⟨C, hC⟩ := hsame.2
      exact iOrderOnManifold_of_le_add huq.quasiPshPotential.1
        (fun y => hC y (mem_univ y))
  have hv : (q : ℝ) • flagValuation F (h.monomialPotential hq hm) =
      integerCast (toricFlagLatticeMap hs v e ((q : ℤ) • D) m) := by
    rw [← flagValuation_smul hu hqR.le]
    exact (flagValuation_eq_of_iEquivalent huq hEDpsh hI).trans hEDval
  calc
    flagValuation F (h.monomialPotential hq hm) =
        (q : ℝ)⁻¹ • ((q : ℝ) • flagValuation F (h.monomialPotential hq hm)) := by
      rw [smul_smul, inv_mul_cancel₀ hqR.ne', one_smul]
    _ = (q : ℝ)⁻¹ • integerCast (toricFlagLatticeMap hs v e ((q : ℤ) • D) m) := by rw [hv]
    _ = toricFlagRealMap hs v e D ((q : ℝ)⁻¹ • latticeVector m) :=
      integerCast_toricFlagLatticeMap_smul v e D hq m

end BigToricMetric
end SGPT.Toric
