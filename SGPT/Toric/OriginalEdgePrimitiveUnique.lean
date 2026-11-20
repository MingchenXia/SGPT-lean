import SGPT.Toric.NativeEdgeBasisReadback
import SGPT.Toric.ToricFaceEdgeEquiv

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting

/-- The ORIGINAL first-point condition makes the primitive vector on every
ACTUAL original edge unique, independently of the chosen ALL-edge basis. -/
theorem originalEdgeBasis_primitive_unique
    {n : ℕ} {K : Type*} (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (b c : Module.Basis (latticePolytopeEdgesAt γ v) ℤ (Fin n → ℤ))
    (hb : ∀ E, integerCast (v + b E) ∈ E.val)
    (hc : ∀ E, integerCast (v + c E) ∈ E.val)
    (E : latticePolytopeEdgesAt γ v) : b E = c E := by
  classical
  have hcne : v + c E ≠ v := by
    intro heq
    exact c.ne_zero E (add_left_cancel (heq.trans (add_zero v).symm))
  have hbne : v + b E ≠ v := by
    intro heq
    exact b.ne_zero E (add_left_cancel (heq.trans (add_zero v).symm))
  obtain ⟨k, hk, hck⟩ := latticeEdgeBasis_first_lattice_point γ v b hb E (v + c E) (hc E) hcne
  obtain ⟨l, hl, hbl⟩ := latticeEdgeBasis_first_lattice_point γ v c hc E (v + b E) (hb E) hbne
  rw [add_sub_cancel_left] at hck hbl
  have heq : b E = (l * k) • b E := by
    calc
      b E = l • c E := hbl
      _ = l • (k • b E) := congrArg (fun m : Fin n → ℤ => l • m) hck
      _ = (l * k) • b E := by rw [smul_smul]
  have hcoeff := congrArg (fun m : Fin n → ℤ => b.repr m E) heq
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
    Finsupp.single_eq_same, mul_one] at hcoeff
  have hk0 : 0 ≤ k := by omega
  have hk_le : k ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hl hk0
    nlinarith
  have hk1 : k = 1 := le_antisymm hk_le hk
  rw [hk1, one_smul] at hck
  exact hck.symm

end SGPT.Toric
