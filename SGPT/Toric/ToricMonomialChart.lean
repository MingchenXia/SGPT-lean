import SGPT.Toric.ToricMonomialPotential
import SGPT.Okounkov.TranscendentalCoreSiuLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- An actual section lattice point gives its normalized point in the
original divisor polytope; no rational-point certificate is added. -/
theorem normalized_toricLatticePoint_mem {D : ToricDivisor γ hs} {q : ℕ} (hq : 0 < q)
    {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    (q : ℝ)⁻¹ • latticeVector m ∈ toricDivisorPolytope D := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hp := (mem_toricDivisorPolytope_smul_iff D hq _).mp hm
  rwa [Set.mem_smul_set_iff_inv_smul_mem₀ hqR] at hp

/-- Literal logarithmic norm of the actual section coefficient in the
actual original torus chart. -/
theorem logNormSq_toricMonomial_embedding (D : ToricDivisor γ hs)
    {q : ℕ} {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    logNormSq (toricMonomial ((q : ℤ) • D) v m
      (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a))) =
      ((latticeFunctional m (unitTorusLog a) -
        q * latticeFunctional (toricCartierDatum D v) (unitTorusLog a) : ℝ) : EReal) := by
  have hchar := latticeCharacter_eq_toricMonomial (hs := hs) ((q : ℤ) • D) hm v a
  have hne : (latticeCharacter (toricCartierDatum ((q : ℤ) • D) v) a : ℂ) ≠ 0 :=
    Units.ne_zero _
  have hmono : toricMonomial ((q : ℤ) • D) v m
      (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      (latticeCharacter m a : ℂ) /
        latticeCharacter (toricCartierDatum ((q : ℤ) • D) v) a := by
    rw [hchar, mul_div_cancel_right₀ _ hne]
  have hnorm : ‖toricMonomial ((q : ℤ) • D) v m
      (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a))‖ ^ 2 =
      Real.exp (latticeFunctional m (unitTorusLog a) -
        q * latticeFunctional (toricCartierDatum D v) (unitTorusLog a)) := by
    rw [hmono, norm_div, div_pow, BigToricMetric.norm_sq_latticeCharacter,
      BigToricMetric.norm_sq_latticeCharacter, ← Real.exp_sub, toricCartierDatum_smul]
    congr 1
    simp only [latticeFunctional_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
      Int.cast_natCast, Finset.mul_sum, mul_assoc]
  rw [logNormSq, hnorm, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]

namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The genuine global current potential produced from the actual monomial
section χ^m of O(qD), in the original θ background. -/
def monomialPotential {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    PolytopeToricVariety γ hs → EReal :=
  h.linearPotential (normalized_toricLatticePoint_mem hq hm)

theorem monomialPotential_mem {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    h.monomialPotential hq hm ∈ h.PSHTor :=
  h.linearPotential_mem _

/-- The whole original chart equality includes every zero of the section.
The proof uses actual PSH a.e.-uniqueness, not density plus USC. -/
theorem monomialPotential_chart {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    h.monomialPotential hq hm ((originalPolytopeNativeModelChart γ hs v).symm z) +
      (h.weight v z : EReal) =
      (((q : ℝ)⁻¹ : ℝ) : EReal) *
        logNormSq (toricMonomial ((q : ℤ) • D) v m z) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmem := h.monomialPotential_mem hq hm
  have hL := h.plurisubharmonicOn_vertexChart hmem.1 v
  have hR : PlurisubharmonicOn
      (fun w => (((q : ℝ)⁻¹ : ℝ) : EReal) *
        logNormSq (toricMonomial ((q : ℤ) • D) v m w)) univ := by
    intro w _
    have hgen : HolomorphicGeneratorsAt
        (fun _ : Fin 1 => toricMonomial ((q : ℤ) • D) v m) w :=
      ⟨univ, isOpen_univ, mem_univ w,
        fun _ y _ => (differentiable_toricMonomial ((q : ℤ) • D) v m y).differentiableWithinAt⟩
    simpa only [SGPT.Okounkov.TranscendentalCore.generatorLog_single, logNormSq] using
      (plurisubharmonicAt_scaled_generatorLog hgen (inv_pos.mpr hqR))
  apply hL.eqOn_of_ae_eq hR isOpen_univ volume _ (mem_univ z)
  filter_upwards [ae_restrict_of_ae ae_mem_complexTorus_volume] with w hw
  obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hw
  have hsrc := embedding_mem_vertexChart_source (hs := hs) v a
  have hchart : originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs a) = w := by
    rw [ha, (originalPolytopeNativeModelChart γ hs v).right_inv (by
      rw [originalPolytopeNativeModelChart_target]; exact mem_univ w)]
  have hu := h.chartFunction_vertexChart_embedding hmem v a
  have hu' : h.monomialPotential hq hm (polytopeToricEmbedding γ hs a) =
      ((inner ℝ (unitTorusLog a) ((q : ℝ)⁻¹ • latticeVector m) -
        h.potential (unitTorusLog a) : ℝ) : EReal) := by
    change h.monomialPotential hq hm
      ((originalPolytopeNativeModelChart γ hs v).symm
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a))) = _ at hu
    rw [(originalPolytopeNativeModelChart γ hs v).left_inv hsrc] at hu
    simpa only [monomialPotential, h.realProfile_linearPotential] using hu
  rw [← hchart, (originalPolytopeNativeModelChart γ hs v).left_inv hsrc, hu', h.weight_chart_embedding, ← EReal.coe_add,
    logNormSq_toricMonomial_embedding D hm v a, ← EReal.coe_mul]
  apply congrArg (fun t : ℝ => (t : EReal))
  rw [inner_smul_right, real_inner_comm, inner_latticeVector]
  field_simp [hqR.ne']
  ring

end BigToricMetric
end SGPT.Toric
