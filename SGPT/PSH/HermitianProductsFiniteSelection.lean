import SGPT.PSH.HermitianProducts
import SGPT.Foundations.Analysis.Pending.NormalDirectionVanishing
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Finset.Sort

/-!
# Finite selection of smooth two-form factors

The actual finite exterior product can be regrouped into its selected
factors and a repeated complementary form. All degree identifications are
explicit; no one-one or positivity hypothesis is needed for this even-degree
algebra.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms TopDegreeDensity
  ConstantFormProducts CoordinateWedgeAssoc NormalDirectionVanishing

variable {n : ℕ}

private theorem init_append (k l : ℕ) (α : Fin k → RealForm n 2)
    (β : Fin (l + 1) → RealForm n 2) :
    Fin.init (n := k + l) (Fin.append (m := k) (n := l + 1) α β) =
      Fin.append (m := k) (n := l) α (Fin.init (n := l) β) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    change Fin.append α β (j.castAdd (l + 1)) = Fin.append α (Fin.init β) (j.castAdd l)
    rw [Fin.append_left, Fin.append_left]
  · intro j
    change Fin.append α β (Fin.natAdd k j.castSucc) = Fin.append α (Fin.init β) (Fin.natAdd k j)
    rw [Fin.append_right, Fin.append_right]
    rfl

private theorem last_append (k l : ℕ) (α : Fin k → RealForm n 2)
    (β : Fin (l + 1) → RealForm n 2) :
    Fin.append α β (Fin.last (k + l)) = β (Fin.last l) := by
  change Fin.append α β (Fin.natAdd k (Fin.last l)) = _
  rw [Fin.append_right]

/-- Appending two actual tuples of two-forms gives their exterior product
with the genuine prescribed-degree cast. -/
theorem wedgeProd_append (k l : ℕ) (α : Fin k → RealForm n 2)
    (β : Fin l → RealForm n 2) :
    wedgeProd (k + l) (Fin.append α β) =
      wedgeTo (by omega : 2 * k + 2 * l = 2 * (k + l)) (wedgeProd k α) (wedgeProd l β) := by
  induction l with
  | zero =>
    have heq : Fin.append α β = α := by
      rw [Fin.append_right_nil α β rfl]
      rfl
    rw [heq]
    change wedgeProd k α = wedgeTo (by omega : 2 * k + 0 = 2 * k)
      (wedgeProd k α) (coordinateWedgeUnit : RealForm n 0)
    rw [wedgeTo_unit_right (by omega) rfl]
    rfl
  | succ l ih =>
    change wedgeProd ((k + l) + 1) (Fin.append (m := k) (n := l + 1) α β) = _
    have hi : (fun i : Fin (k + l) =>
        Fin.append (m := k) (n := l + 1) α β i.castSucc) =
        Fin.append α (Fin.init β) := init_append k l α β
    rw [wedgeProd_succ (k + l) (Fin.append (m := k) (n := l + 1) α β), hi,
      last_append k l α β, ih, wedgeProd_succ l β]
    exact wedgeTo_assoc (by omega : 2 * k + 2 * l = 2 * (k + l))
      (by omega : 2 * (k + l) + 2 = 2 * (k + (l + 1))) rfl
      (by omega : 2 * k + 2 * (l + 1) = 2 * (k + (l + 1))) _ _ _

/-- Regrouping by a selected subset, in fixed block cardinalities. -/
theorem wedgeProd_selected_const_blocks (k l : ℕ) (s : Finset (Fin (k + l)))
    (hs : s.card = k) (α : Fin (k + l) → RealForm n 2) (β : RealForm n 2) :
    wedgeProd (k + l) (s.piecewise α (fun _ => β)) =
      wedgeTo (by omega : 2 * k + 2 * l = 2 * (k + l))
        (wedgeProd k (fun i => α (s.orderEmbOfFin hs i)))
        (wedgeProd l (fun _ => β)) := by
  classical
  have hc : (sᶜ).card = l := by simp only [Finset.card_compl, Fintype.card_fin, hs]; omega
  let es : Fin k ≃ ↥s := (s.orderIsoOfFin hs).toEquiv
  let ec : Fin l ≃ ↥((s : Set (Fin (k + l)))ᶜ) :=
    ((sᶜ).orderIsoOfFin hc).toEquiv.trans (Equiv.subtypeEquivRight (fun i => by simp))
  let e : Fin k ⊕ Fin l ≃ Fin (k + l) :=
    (Equiv.sumCongr es ec).trans (Equiv.Set.sumCompl (s : Set (Fin (k + l))))
  let π : Equiv.Perm (Fin (k + l)) := finSumFinEquiv.symm.trans e
  have hleft (i : Fin k) : π (i.castAdd l) = s.orderEmbOfFin hs i := by
    simp only [π, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
      e, Equiv.sumCongr_apply, Sum.map_inl]
    rfl
  have hright (i : Fin l) : π (Fin.natAdd k i) = (ec i : Fin (k + l)) := by
    simp only [π, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
      e, Equiv.sumCongr_apply, Sum.map_inr]
    rfl
  have htuple : (s.piecewise α (fun _ => β)) ∘ π =
      Fin.append (fun i => α (s.orderEmbOfFin hs i)) (fun _ : Fin l => β) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Function.comp_apply, hleft, Fin.append_left]
      exact s.piecewise_eq_of_mem α (fun _ => β) (s.orderEmbOfFin_mem hs j)
    · intro j
      rw [Function.comp_apply, hright, Fin.append_right]
      exact s.piecewise_eq_of_notMem α (fun _ => β) (by exact (ec j).property)
  calc
    wedgeProd (k + l) (s.piecewise α (fun _ => β)) =
        wedgeProd (k + l) ((s.piecewise α (fun _ => β)) ∘ π) :=
      (wedgeProd_comp_perm (k + l) _ π).symm
    _ = wedgeProd (k + l)
        (Fin.append (fun i => α (s.orderEmbOfFin hs i)) (fun _ : Fin l => β)) := by rw [htuple]
    _ = _ := wedgeProd_append k l _ _

private theorem wedgeProd_selected_const_of_eq (p k l : ℕ) (hp : p = k + l)
    (s : Finset (Fin p)) (hs : s.card = k) (α : Fin p → RealForm n 2) (β : RealForm n 2) :
    wedgeProd p (s.piecewise α (fun _ => β)) =
      wedgeTo (by omega : 2 * k + 2 * l = 2 * p)
        (wedgeProd k (fun i => α (s.orderEmbOfFin hs i)))
        (wedgeProd l (fun _ => β)) := by
  subst p
  exact wedgeProd_selected_const_blocks k l s hs α β

/-- The full finite exterior product with a repeated complementary form
regroups into the actual selected product and its complementary power. -/
theorem wedgeProd_selected_const (p : ℕ) (s : Finset (Fin p))
    (α : Fin p → RealForm n 2) (β : RealForm n 2) :
    wedgeProd p (s.piecewise α (fun _ => β)) =
      wedgeTo (by have h := Finset.card_le_univ s; simp only [Fintype.card_fin] at h; omega :
        2 * s.card + 2 * (p - s.card) = 2 * p)
        (wedgeProd s.card (fun i => α (s.orderEmbOfFin rfl i)))
        (wedgeProd (p - s.card) (fun _ => β)) := by
  have hcard : s.card ≤ p := by simpa using Finset.card_le_univ s
  exact wedgeProd_selected_const_of_eq p s.card (p - s.card) (by omega) s rfl α β

end SGPT.PSH.HermitianProducts
