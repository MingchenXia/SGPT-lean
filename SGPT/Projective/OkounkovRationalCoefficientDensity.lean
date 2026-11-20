import SGPT.Projective.OkounkovConvexLeftNativeLimit
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual positive integral presentations and strict-left rational coefficient sequences.
Blueprint: okounkov-rational-coefficient-density.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.RationalCoefficientDensity
open Set Filter
open scoped Topology

theorem exists_positive_nat_ratio (r : ℚ) (hr0 : 0<r) (hr1 : r<1) :
    ∃ p q : ℕ, 0<p ∧ 0<q ∧ r=(p:ℚ)/(p+q) := by
  let p := r.num.toNat
  have hn := Rat.num_pos.mpr hr0
  have hpZ : (p:ℤ)=r.num := Int.toNat_of_nonneg hn.le
  have hpQ : (p:ℚ)=(r.num:ℚ) := by exact_mod_cast hpZ
  have hp : 0<p := by exact_mod_cast (show (0:ℤ)<p by simpa only [hpZ] using hn)
  have hd : (0:ℚ)<r.den := by exact_mod_cast r.pos
  have hread : r=(p:ℚ)/r.den := by rw [hpQ,Rat.num_div_den]
  have hpltQ : (p:ℚ)<r.den := (div_lt_one hd).mp (by rw [←hread];exact hr1)
  have hplt : p<r.den := by exact_mod_cast hpltQ
  refine ⟨p,r.den-p,hp,Nat.sub_pos_of_lt hplt,?_⟩
  have hsum : p+(r.den-p)=r.den := Nat.add_sub_of_le hplt.le
  rw [←Nat.cast_add,hsum]
  exact hread

theorem exists_positive_rat_sequence_from_left {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    ∃ r : ℕ → ℚ, (∀j, 0<r j ∧ (r j:ℝ)<t ∧ r j<1) ∧
      Tendsto (fun j => (r j:ℝ)) atTop (𝓝 t) := by
  have hex (j : ℕ) : ∃ r : ℚ, max 0 (t-1/((j:ℝ)+1))<(r:ℝ) ∧ (r:ℝ)<t := by
    apply exists_rat_btwn
    exact max_lt_iff.mpr ⟨ht0,sub_lt_self t (one_div_pos.mpr (by positivity))⟩
  choose r hr using hex
  refine ⟨r,?_,?_⟩
  · intro j
    refine ⟨?_,(hr j).2,?_⟩
    · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) (hr j).1)
    · exact_mod_cast ((hr j).2.trans ht1)
  · have hlo : Tendsto (fun j : ℕ => t-1/((j:ℝ)+1)) atTop (𝓝 t) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).sub
          tendsto_one_div_add_atTop_nhds_zero_nat)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun j => (lt_of_le_of_lt (le_max_right _ _) (hr j).1).le) (fun j => (hr j).2.le)
end SGPT.Okounkov.RationalCoefficientDensity
