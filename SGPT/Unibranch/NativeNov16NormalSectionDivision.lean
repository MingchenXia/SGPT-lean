import SGPT.Unibranch.PrimeNov16AnalyticNormalizationClearedMonicDivision
import Mathlib.Topology.Sheaves.Stalks

/-! Actual global sections, manufactured from normal original stalks.
Blueprint: native-nov16-normal-section-division.tex. -/
set_option autoImplicit false
noncomputable section
open TopologicalSpace CategoryTheory Opposite
namespace SGPT.Unibranch.NativeNov16NormalSectionDivision

variable {X : TopCat} (S : X.Sheaf CommRingCat)

theorem exists_local_divisor (U : Opens X)
    (g h : (S.presheaf.obj (op U)).carrier) (x : X) (hx : x ∈ U)
    (hd : ∃ q : (S.presheaf.stalk x).carrier,
      S.presheaf.germ U x hx g = S.presheaf.germ U x hx h * q) :
    ∃ (V : Opens X) (_hxV : x ∈ V) (iVU : V ⟶ U)
      (q : (S.presheaf.obj (op V)).carrier),
      S.presheaf.map iVU.op g = S.presheaf.map iVU.op h * q := by
  let F := S.presheaf
  obtain ⟨q,hq⟩ := hd
  obtain ⟨V,hVU,hxV,s,hs⟩ := F.exists_le_germ_eq q hx
  let iVU : V ⟶ U := homOfLE hVU
  have he : F.germ V x hxV (F.map iVU.op g) =
      F.germ V x hxV (F.map iVU.op h * s) := by
    rw [map_mul,F.germ_res_apply,F.germ_res_apply,hs]
    exact hq
  obtain ⟨W,hxW,iW,jW,hw⟩ := F.germ_eq x hxV hxV _ _ he
  have hij : jW = iW := Subsingleton.elim _ _
  subst jW
  rw [map_mul] at hw
  refine ⟨W,hxW,iW ≫ iVU,F.map iW.op s,?_⟩
  simpa only [op_comp,Functor.map_comp,CommRingCat.comp_apply] using hw

theorem section_mul_cancel (U : Opens X)
    (h : (S.presheaf.obj (op U)).carrier)
    (hdom : ∀ x ∈ U, IsDomain (S.presheaf.stalk x).carrier)
    (hreg : ∀ (x : X) (hx : x ∈ U), S.presheaf.germ U x hx h ≠ 0)
    (a b : (S.presheaf.obj (op U)).carrier) (heq : h*a = h*b) : a = b := by
  apply TopCat.Presheaf.section_ext S U a b
  intro x hx
  let _ := hdom x hx
  apply mul_left_cancel₀ (hreg x hx)
  simpa only [map_mul] using congrArg (S.presheaf.germ U x hx) heq

theorem exists_unique_section_divisor (U : Opens X)
    (g h : (S.presheaf.obj (op U)).carrier)
    (hdom : ∀ x ∈ U, IsDomain (S.presheaf.stalk x).carrier)
    (hreg : ∀ (x : X) (hx : x ∈ U), S.presheaf.germ U x hx h ≠ 0)
    (hd : ∀ (x : X) (hx : x ∈ U), ∃ q : (S.presheaf.stalk x).carrier,
      S.presheaf.germ U x hx g = S.presheaf.germ U x hx h * q) :
    ∃! q : (S.presheaf.obj (op U)).carrier, g = h*q := by
  classical
  let F := S.presheaf
  have hlocal (x : U) := exists_local_divisor S U g h x.val x.property (hd x.val x.property)
  choose V hxV iVU sf heq using hlocal
  have hcover : U ≤ iSup V := by
    intro x hx
    simp only [Opens.mem_iSup]
    exact ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hcompatible : TopCat.Presheaf.IsCompatible F V sf := by
    intro i j
    let W := V i ⊓ V j
    let l : W ⟶ V i := homOfLE inf_le_left
    let r : W ⟶ V j := homOfLE inf_le_right
    let t : W ⟶ U := l ≫ iVU i
    apply section_mul_cancel S W (F.map t.op h)
      (fun x hx => hdom x (t.le hx))
      (fun x hx => by
        change F.germ W x hx (F.map t.op h) ≠ 0
        rw [F.germ_res_apply]
        exact hreg x (t.le hx))
    have hi := congrArg (F.map l.op) (heq i)
    have hj := congrArg (F.map r.op) (heq j)
    simp only [map_mul] at hi hj
    have htr : t = r ≫ iVU j := Subsingleton.elim _ _
    have hgi : F.map l.op (F.map (iVU i).op g) = F.map t.op g := by
      simp only [t,op_comp,Functor.map_comp,CommRingCat.comp_apply]
    have hgj : F.map r.op (F.map (iVU j).op g) = F.map t.op g := by
      rw [htr]
      simp only [op_comp,Functor.map_comp,CommRingCat.comp_apply]
    have hhi : F.map l.op (F.map (iVU i).op h) = F.map t.op h := by
      simp only [t,op_comp,Functor.map_comp,CommRingCat.comp_apply]
    have hhj : F.map r.op (F.map (iVU j).op h) = F.map t.op h := by
      rw [htr]
      simp only [op_comp,Functor.map_comp,CommRingCat.comp_apply]
    rw [hgi,hhi] at hi
    rw [hgj,hhj] at hj
    exact hi.symm.trans hj
  obtain ⟨q,hq,_hu⟩ := S.existsUnique_gluing' V U iVU hcover sf hcompatible
  have hqeq : g = h*q := by
    apply S.eq_of_locally_eq' V U iVU hcover
    intro i
    rw [map_mul,hq i]
    exact heq i
  refine ⟨q,hqeq,?_⟩
  intro q' hq'
  exact section_mul_cancel S U h hdom hreg q' q (hq'.symm.trans hqeq)

theorem exists_unique_divisor_of_cleared_relation (U : Opens X) {k : ℕ}
    (c : Fin k → (S.presheaf.obj (op U)).carrier)
    (g h : (S.presheaf.obj (op U)).carrier)
    (hnormal : ∀ x ∈ U, IsDomain (S.presheaf.stalk x).carrier ∧
      IsIntegrallyClosed (S.presheaf.stalk x).carrier)
    (hreg : ∀ (x : X) (hx : x ∈ U), S.presheaf.germ U x hx h ≠ 0)
    (hrel : g^k + ∑ i : Fin k,c i*h^(k-i.val)*g^i.val = 0) :
    ∃! q : (S.presheaf.obj (op U)).carrier, g = h*q := by
  apply exists_unique_section_divisor S U g h (fun x hx => (hnormal x hx).1) hreg
  intro x hx
  let _ := (hnormal x hx).1
  let _ := (hnormal x hx).2
  apply PrimeNov16AnalyticNormalizationClearedMonicDivision.exists_divisor_of_cleared_relation
    (fun i => S.presheaf.germ U x hx (c i)) _ _ (hreg x hx)
  simpa only [map_add,map_sum,map_mul,map_pow,map_zero] using
    congrArg (S.presheaf.germ U x hx) hrel

end SGPT.Unibranch.NativeNov16NormalSectionDivision
