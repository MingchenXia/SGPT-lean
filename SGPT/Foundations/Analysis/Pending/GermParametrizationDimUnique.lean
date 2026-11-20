import SGPT.Foundations.Analysis.Pending.GermComponentDimension

set_option autoImplicit false

/-!
# The dimension of parametrization data of an irreducible germ is intrinsic

`Pending.GermParametrizationData.nonempty_parametrizationData` builds parametrization data
for a germ in Noether position, but the data it returns carries its own `dim` field and
nothing relates it to the `d` of the Noether position it came from — the dimension is
"forgotten" on the way.  For a single consumer that does not matter; for a statement that
puts SEVERAL germs in Noether position at once, and must then assert that they share one
dimension, it does.

`Pending.GermComponentDimension` already contains the fix, in the form needed for a
subvariety: the dimension of parametrization data of an irreducible germ is the PURE
dimension of that germ (`exists_pure_nhds_dim`, via the fact that regular points of
dimension `P.dim` accumulate at `0`, `exists_regularAtDim_near_zero`).  Since the pure
dimension mentions neither the data nor the change of coordinates, two sets of data for the
same germ must agree.

`dim_eq_dim` is that statement, isolated with no ambient manifold: an irreducible germ `B` of
`ℂⁿ` and two linear changes of coordinates `L`, `L'` both putting it in Noether position
carry parametrization data of the SAME dimension.
-/

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationDimUnique

open FirstPass FirstPass.RegularLocusDense AnalyticGermDecomposition GermParametrization
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
open SGPT.Foundations.Analysis.Pending.GermComponentDimension
open SGPT.Foundations.Analysis.Pending.RegularPointDimension

noncomputable section

variable {n : ℕ}

/-- **The dimension of parametrization data of an irreducible germ does not depend on the
data.**  Both dimensions are the pure dimension of the germ. -/
theorem dim_eq_dim {B : Set (ComplexModel n)} (hB : IsIrreducibleGerm B)
    {L L' : ComplexModel n ≃L[ℂ] ComplexModel n}
    {P : ParametrizationData (L ⁻¹' B)} (S : SetsData P)
    {P' : ParametrizationData (L' ⁻¹' B)} (S' : SetsData P') :
    P'.dim = P.dim := by
  obtain ⟨Ω, hΩo, hΩ0, hΩ⟩ :=
    exists_pure_nhds_dim hB fun ε hε => exists_regularAtDim_near_zero L S hε
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩo 0 hΩ0
  obtain ⟨y, hyb, Δ, hΔo, hyΔ, hyreg⟩ := exists_regularAtDim_near_zero L' S' hρ
  have hΩ'o : IsOpen (ball (0 : ComplexModel n) ρ ∩ Δ) := isOpen_ball.inter hΔo
  have hΩ'sub : ball (0 : ComplexModel n) ρ ∩ Δ ⊆ Ω := fun z hz => hball hz.1
  have heq : (B ∩ Δ) ∩ (ball (0 : ComplexModel n) ρ ∩ Δ)
      = (B ∩ (ball (0 : ComplexModel n) ρ ∩ Δ)) ∩ (ball (0 : ComplexModel n) ρ ∩ Δ) := by
    ext z
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.2.2⟩, h.2⟩⟩
  exact (hΩ _ hΩ'o hΩ'sub).1 (regularAtDim_of_inter_eq hΩ'o ⟨hyb, hyΔ⟩ heq hyreg)

end

end SGPT.Foundations.Analysis.Pending.GermParametrizationDimUnique
