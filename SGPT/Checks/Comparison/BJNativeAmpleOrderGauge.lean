import SGPT.Checks.Comparison.BJModuleGauge
import SGPT.Foundations.Envelope.Source.Numerical

/-! Genuine geometric ample-order neighborhoods in the SAME native numerical
space. Every absorption/finite-family/radius output is produced internally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.NativePicard
open AlgebraicGeometry CategoryTheory Filter Topology Set
open Scheme.Modules SGPT.Foundations.Envelope NativeRealNumericalClasses
open scoped Pointwise
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- Literal original ample-order unit neighborhood, for ANY actual class η. -/
def ampleOrderNeighborhood (η : Space p) : Set (Space p) :=
  {x | η+x∈ampleCone p ∧ η-x∈ampleCone p}

theorem ampleOrderNeighborhood_convex (η : Space p) :
    Convex ℝ (ampleOrderNeighborhood p η) := by
  intro x hx y hy r s hr hs hrs
  change η+(r•x+s•y)∈ampleCone p ∧ η-(r•x+s•y)∈ampleCone p
  have hplus : η+(r•x+s•y)=r•(η+x)+s•(η+y) := by
    calc
      _ = (r+s)•η+(r•x+s•y) := by rw [hrs,one_smul]
      _ = _ := by module
  have hminus : η-(r•x+s•y)=r•(η-x)+s•(η-y) := by
    calc
      _ = (r+s)•η-(r•x+s•y) := by rw [hrs,one_smul]
      _ = _ := by module
  rw [hplus,hminus]
  exact ⟨(ampleCone p).convex hx.1 hy.1 hr hs hrs,
    (ampleCone p).convex hx.2 hy.2 hr hs hrs⟩

theorem ampleOrderNeighborhood_balanced (η : Space p) :
    Balanced ℝ (ampleOrderNeighborhood p η) := by
  apply (balanced_iff_neg_mem (ampleOrderNeighborhood_convex p η)).mpr
  intro x hx
  change η+(-x)∈ampleCone p ∧ η-(-x)∈ampleCone p
  exact ⟨by simpa only [sub_eq_add_neg] using hx.2,
    by simpa only [sub_neg_eq_add] using hx.1⟩

theorem zero_mem_ampleOrderNeighborhood {η : Space p} (hη : η∈ampleCone p) :
    (0:Space p)∈ampleOrderNeighborhood p η := by
  exact ⟨by simpa using hη,by simpa using hη⟩

variable [IsIntegral X]

/-- EVERY original numerical direction is absorbed, from internally produced
finite true line generators and genuine geometric Serre-twist radii. -/
theorem ampleOrderNeighborhood_absorbent {η : Space p} (hη : η∈ampleCone p) :
    Absorbent ℝ (ampleOrderNeighborhood p η) := by
  apply absorbent_iff_eventually_nhdsNE_zero.mpr
  intro x
  obtain ⟨n,B,hB,a,hx⟩ := exists_finite_line_family p x
  obtain ⟨ε,hε,hrad⟩ := exists_ampleCone_lineFamily_radius p B hB η hη
  let S : ℝ := ∑ i,|a i|
  have hS : 0≤S := Finset.sum_nonneg fun i _ => abs_nonneg (a i)
  let δ : ℝ := ε/(S+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  have hsmall (c : ℝ) (hc : |c|<δ) (i : Fin n) : |(c•a) i|<ε := by
    rw [Pi.smul_apply,smul_eq_mul,abs_mul]
    have hi : |a i|≤S := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    calc
      |c| *|a i|≤|c| *(S+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
      _ < δ*(S+1) := mul_lt_mul_of_pos_right hc (by linarith)
      _ = ε := div_mul_cancel₀ ε (by linarith : S+1≠0)
  have hevent : ∀ᶠ c : ℝ in 𝓝 0, |c|<δ :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hδ)
  have hnear : ∀ᶠ c : ℝ in 𝓝 0,c•x∈ampleOrderNeighborhood p η := by
    filter_upwards [hevent] with c hc
    have hp := hrad (c•a) (hsmall c hc)
    have hm := hrad ((-c)•a) (hsmall (-c) (by simpa only [abs_neg] using hc))
    change η+c•x∈ampleCone p ∧ η-c•x∈ampleCone p
    rw [(lineFamilyMap p B hB).map_smul,← hx] at hp hm
    exact ⟨hp,by simpa only [neg_smul,sub_eq_add_neg] using hm⟩
  exact hnear.filter_mono inf_le_left

/-- The actual original ample-order neighborhood is a genuine neighborhood
for the canonical module topology, with NO FD/order-unit certificate input. -/
theorem ampleOrderNeighborhood_mem_nhds_zero {η : Space p} (hη : η∈ampleCone p) :
    ampleOrderNeighborhood p η∈@nhds _ (numericalModuleTopology p) 0 :=
  ModuleGauge.mem_nhds_zero_of_balanced_convex_absorbent
    (ampleOrderNeighborhood_balanced p η) (ampleOrderNeighborhood_convex p η)
    (ampleOrderNeighborhood_absorbent p hη)

/-- GENUINE one-way actual-class topology bridge WITHOUT global numerical
finite dimensionality. No equality with a weaker topology is asserted. -/
theorem ampleTendsto_of_moduleTopology {J : Type u} {c : J → Space p} {l : Filter J}
    {θ : Space p} (h : Tendsto c l (@nhds _ (numericalModuleTopology p) θ)) :
    Variety.AmpleTendsto p c l θ := by
  let := numericalModuleTopology p
  let : IsTopologicalAddGroup (Space p) :=
    IsModuleTopology.topologicalAddGroup ℝ (Space p)
  have h0 : Tendsto (fun j => c j-θ) l (𝓝 (0:Space p)) := by
    simpa only [sub_self] using h.sub_const θ
  intro η hη
  exact h0.eventually (ampleOrderNeighborhood_mem_nhds_zero p hη)

end SGPT.NAPotential.BJ.NativePicard
