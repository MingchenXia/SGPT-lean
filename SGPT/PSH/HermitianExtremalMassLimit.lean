import SGPT.PSH.HermitianExtremalPoleAlternative
import SGPT.PSH.CompactAntitoneSupremum

/-!
# The actual supremum and scalar double limits in Hermitian Josefson

For the decreasing inner limit, compact upper-semicontinuous superlevels
give supremum convergence directly; no closed background or unproved
subsequence compactness is needed. The final scalar estimate passes a
`C/N` bound through the inner and outer limits.

Source: FPT, `thm:compact-complex-global-josefson`, Steps 1, 2 and 4.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalMassLimit

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremalNormalization HermitianExtremalCurrentLimits
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [ConnectedSpace M]

/-- A finite lower bound for the actual suprema of a decreasing family
manufactures its genuine limit in the nonclosed Hermitian PSH domain. -/
theorem isHermitianPSH_iInf_of_sup_lower_bound (ω : Background (m + 1) M)
    {w : ℕ → M → EReal} (hw : ∀ j, IsHermitianPSH ω (w j))
    (hanti : ∀ x, Antitone fun j => w j x) (a : ℝ)
    (ha : ∀ j, (a : EReal) ≤ ⨆ x, w j x) :
    IsHermitianPSH ω (fun x => ⨅ j, w j x) := by
  have hne := exists_iInf_ne_bot_of_compact_antitone_iSup_lower_bound w
    (fun j => (hw j).quasiPshPotential.1.upperSemicontinuous) hanti a ha
  exact isHermitianPSH_iInf_of_exists_ne_bot ω (hasCommonLocalCorrections ω) hw hanti hne

/-- Nonnegative decreasing Hermitian PSH potentials have a genuine
nonnegative Hermitian PSH infimum; its nonpole is internally produced. -/
theorem isHermitianPSH_iInf_of_nonneg (ω : Background (m + 1) M)
    {w : ℕ → M → EReal} (hw : ∀ j, IsHermitianPSH ω (w j))
    (hanti : ∀ x, Antitone fun j => w j x) (hpos : ∀ j x, 0 ≤ w j x) :
    IsHermitianPSH ω (fun x => ⨅ j, w j x) ∧ ∀ x, 0 ≤ ⨅ j, w j x := by
  refine ⟨isHermitianPSH_iInf_of_sup_lower_bound ω hw hanti 0 (fun j => ?_),
    fun x => le_iInf (fun j => hpos j x)⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  simpa only [EReal.coe_zero] using (hpos j x).trans (le_iSup (w j) x)

/-- Compactness alone passes the literal extended suprema through the
decreasing inner limit used in the capacity proof. -/
theorem tendsto_iSup_iInf (ω : Background (m + 1) M)
    {w : ℕ → M → EReal} (hw : ∀ j, IsHermitianPSH ω (w j))
    (hanti : ∀ x, Antitone fun j => w j x) :
    Tendsto (fun j => ⨆ x, w j x) atTop (𝓝 (⨆ x, ⨅ j, w j x)) :=
  tendsto_iSup_of_compact_antitone w
    (fun j => (hw j).quasiPshPotential.1.upperSemicontinuous) hanti

/-- The same supremum convergence is ordinary real convergence once the
actual limiting function belongs to the genuine Hermitian PSH class. -/
theorem tendsto_real_iSup_iInf (ω : Background (m + 1) M)
    {w : ℕ → M → EReal} (hw : ∀ j, IsHermitianPSH ω (w j))
    (hanti : ∀ x, Antitone fun j => w j x)
    (hlim : IsHermitianPSH ω (fun x => ⨅ j, w j x)) :
    Tendsto (fun j => (⨆ x, w j x).toReal) atTop (𝓝 (⨆ x, ⨅ j, w j x).toReal) := by
  obtain ⟨b, hb, _, _⟩ := exists_real_sup ω hlim
  have htop : (⨆ x, ⨅ j, w j x) ≠ ⊤ := by rw [hb]; exact EReal.coe_ne_top b
  have hbot : (⨆ x, ⨅ j, w j x) ≠ ⊥ := by rw [hb]; exact EReal.coe_ne_bot b
  exact (EReal.tendsto_toReal htop hbot).comp (tendsto_iSup_iInf ω hw hanti)

/-- A nonnegative convergent sequence bounded by a finite inverse-linear
budget has zero limit. The natural index `N` represents source `N+1`. -/
theorem eq_zero_of_nonneg_of_eventually_le_inv_nat
    {a : ℕ → ℝ} {L C : ℝ} (ha : ∀ N, 0 ≤ a N)
    (hlim : Tendsto a atTop (𝓝 L))
    (hbound : ∀ᶠ N in atTop, a N ≤ C / ((N : ℝ) + 1)) : L = 0 := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (by
      apply tendsto_atTop.mpr
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt b
      filter_upwards [eventually_ge_atTop N] with k hk
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith)
  have hupper : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul C
  have hle : L ≤ 0 := le_of_tendsto_of_tendsto hlim hupper hbound
  have hge : 0 ≤ L := isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall ha)
  exact le_antisymm hle hge

/-- The final two-limit scalar step: inner mass and supremum convergence,
the actual extremal-capacity bound and one common bound for the limiting
suprema force the outer mass limit to be zero. -/
theorem zero_of_double_limit_capacity_bound (n : ℕ) (C D : ℝ) (hD : 0 ≤ D)
    (mass sup : ℕ → ℕ → ℝ) (a b : ℕ → ℝ) (L : ℝ)
    (hmass : ∀ N, Tendsto (fun j => mass j N) atTop (𝓝 (a N)))
    (hsup : ∀ N, Tendsto (fun j => sup j N) atTop (𝓝 (b N)))
    (hbound : ∀ N, ∀ᶠ j in atTop,
      mass j N ≤ max 1 (sup j N) ^ n * D / ((N : ℝ) + 1))
    (hb : ∀ N, b N ≤ C) (ha : ∀ N, 0 ≤ a N)
    (halim : Tendsto a atTop (𝓝 L)) : L = 0 := by
  have hinner (N : ℕ) : a N ≤ max 1 C ^ n * D / ((N : ℝ) + 1) := by
    have hright : Tendsto (fun j => max 1 (sup j N) ^ n * D / ((N : ℝ) + 1)) atTop
        (𝓝 (max 1 (b N) ^ n * D / ((N : ℝ) + 1))) :=
      (((tendsto_const_nhds.max (hsup N)).pow n).mul_const D).div_const _
    refine (le_of_tendsto_of_tendsto (hmass N) hright (hbound N)).trans ?_
    gcongr
    exact hb N
  exact eq_zero_of_nonneg_of_eventually_le_inv_nat ha halim (Eventually.of_forall hinner)

end SGPT.PSH.HermitianExtremalMassLimit
