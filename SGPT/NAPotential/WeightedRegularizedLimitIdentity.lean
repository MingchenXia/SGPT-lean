import SGPT.NAPotential.WeightedSkodaAuxiliary
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Passing the regularized division equation to the limit

The finite family of locally uniform limits is to be produced by the normal
family argument, and the identities by smooth division.  This lemma records
the resulting passage to the original tuple, including the vanishing extra
coordinate.  It does not construct either of those inputs.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Filter Set
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

theorem regularized_division_identity_of_locally_uniform_limit
    {n r : ℕ} {U : Set (ComplexModel n)} {g : Fin r → ComplexModel n → ℂ}
    {f : ComplexModel n → ℂ} {H : ℕ → Fin (r + 1) → ComplexModel n → ℂ}
    {h : Fin (r + 1) → ComplexModel n → ℂ} {σ : ℕ → ℕ}
    (hσ : StrictMono σ)
    (hH : ∀ i, TendstoLocallyUniformlyOn (fun j => H (σ j) i) (h i) atTop U)
    (hid : ∀ j z, z ∈ U →
      f z = (∑ i : Fin r, g i z * H j i.castSucc z) +
        ((Real.sqrt (1 / ((j : ℝ) + 1)) : ℝ) : ℂ) * H j (Fin.last r) z) :
    ∀ z ∈ U, f z = ∑ i : Fin r, g i z * h i.castSucc z := by
  intro z hz
  have hsum : Tendsto (fun j => ∑ i : Fin r, g i z * H (σ j) i.castSucc z)
      atTop (𝓝 (∑ i : Fin r, g i z * h i.castSucc z)) :=
    tendsto_finsetSum _ fun i _ => ((hH i.castSucc).tendsto_at hz).const_mul (g i z)
  have haux := regularized_auxiliary_tendsto_zero hσ
    (H := fun j => H j (Fin.last r)) (Hlim := h (Fin.last r)) (hH (Fin.last r)) hz
  have htotal := hsum.add haux
  rw [add_zero] at htotal
  exact tendsto_nhds_unique (tendsto_const_nhds.congr (fun j => hid (σ j) z hz)) htotal

end SGPT.NAPotential.GAGAMult
