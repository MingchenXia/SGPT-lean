import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Preservation of a finite holomorphic division identity under limits

This elementary auxiliary lemma does not construct a division sequence.
The Skoda assembly must obtain the actual identities from the fixed-
truncation stage and the convergence from the common normal-family
subsequence; they are not assumptions of the intended final theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter
open scoped Topology

variable {ι X : Type*} [Fintype ι]

/-- A finite division identity passes to pointwise limits on its actual
domain, with the same original generators. -/
theorem finite_division_identity_of_tendsto
    {U : Set X} {g : ι → X → ℂ} {f : X → ℂ}
    {H : ℕ → ι → X → ℂ} {h : ι → X → ℂ}
    (hH : ∀ i z, z ∈ U → Tendsto (fun j => H j i z) atTop (𝓝 (h i z)))
    (hid : ∀ j z, z ∈ U → f z = ∑ i, g i z * H j i z) :
    ∀ z ∈ U, f z = ∑ i, g i z * h i z := by
  intro z hz
  have hsum : Tendsto (fun j => ∑ i, g i z * H j i z) atTop
      (𝓝 (∑ i, g i z * h i z)) :=
    tendsto_finsetSum _ fun i _ => (hH i z hz).const_mul (g i z)
  exact tendsto_nhds_unique (tendsto_const_nhds.congr (fun j => hid j z hz)) hsum

end SGPT.NAPotential.GAGAMult
