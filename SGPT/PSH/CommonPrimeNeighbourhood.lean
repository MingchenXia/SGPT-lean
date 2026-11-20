import SGPT.PSH.PrimeEquationNeighbourhood
import SGPT.Foundations.Analysis.Pending.ActualPrimeHypersurfacePureNeighbourhood
import SGPT.Foundations.Analysis.Pending.IrreducibleGermConnected
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import SGPT.Foundations.Analysis.Pending.GlobalComponents
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm OkaRelationSheaf OkaIdealOperations AnalyticGermDecomposition
open RegularLocusComponent AnalyticSubsetOpens
open scoped Topology Manifold ContDiff

/-- One actual open neighborhood retains EVERY original reduced prime
equation and its SAME connected dense regular part simultaneously. -/
theorem exists_common_prime_regular_neighbourhood {m r : ℕ}
    (q : Fin r → ComplexModel (m + 1) → ℂ) (hq : ∀ i, HolAt (q i) 0)
    (hQ : ∀ i, Prime (HolGerm.mk (q i) (hq i)))
    (hnot : ∀ i j, i ≠ j → ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (q j) (hq j))
    (N : Set (ComplexModel (m + 1))) (hN : N ∈ 𝓝 0) :
    ∃ U : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ U ∧
      (U : Set (ComplexModel (m + 1))) ⊆ N ∧
      (∀ i, DifferentiableOn ℂ (q i) U ∧
        (∀ W : Set (ComplexModel (m + 1)), IsOpen W → W ⊆ U → W.Nonempty →
          ∃ y ∈ W, q i y ≠ 0) ∧
        ∀ y ∈ U, ∀ a : ComplexModel (m + 1) → ℂ,
          vanishingIdealF {x | q i x = 0} y a ↔ InSpanAt (fun _ : Fin 1 => q i) y a) ∧
      ∃ G : Fin r → Set (ComplexModel (m + 1)), ∀ i,
        (G i).Nonempty ∧ G i ⊆ {x | q i x = 0} ∩ U ∧ IsPreconnected (G i) ∧
        {x | q i x = 0} ∩ U ⊆ closure (G i) ∧
        ∀ y ∈ G i, RegularAtDim (n := m + 1) {x | q i x = 0} y m := by
  classical
  choose ε hε hqB hnon hgen using fun i =>
    exists_original_prime_equation_neighbourhood (q i) (hq i) (hQ i)
  choose P hP h0P hpure using fun i =>
    ActualPrimeHypersurfacePureNeighbourhood.exists_pure_hypersurface_neighbourhood
      (q i) (hq i) (hQ i)
  obtain ⟨N₀, hN₀sub, hN₀, h0N₀⟩ := _root_.mem_nhds_iff.mp hN
  let N₁ : Set (ComplexModel (m + 1)) := N₀ ∩ (⋂ i, ball 0 (ε i)) ∩ ⋂ i, P i
  have hN₁ : IsOpen N₁ := (hN₀.inter (isOpen_iInter_of_finite fun _ => isOpen_ball)).inter
    (isOpen_iInter_of_finite hP)
  have h0N₁ : (0 : ComplexModel (m + 1)) ∈ N₁ :=
    ⟨⟨h0N₀, mem_iInter.mpr fun i => mem_ball_self (hε i)⟩, mem_iInter.mpr h0P⟩
  have hN₁B : ∀ i, N₁ ⊆ ball 0 (ε i) := fun i _ hx => mem_iInter.mp hx.1.2 i
  have hN₁P : ∀ i, N₁ ⊆ P i := fun i _ hx => mem_iInter.mp hx.2 i
  let A : Fin r → Set (ComplexModel (m + 1)) := fun i => {x | q i x = 0}
  have hirr : ∀ i, IsIrreducibleGerm (A i) := fun i =>
    (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible
      (q i) (hq i) (hQ i)).2
  have hAnot : ∀ i j, i ≠ j → ¬A i ≤ᶠ[𝓝 0] A j := by
    intro i j hij hle
    have hmem : HolGerm.mk (q j) (hq j) ∈ vanishingIdeal (A i) :=
      mem_vanishingIdeal_mk.mpr hle
    rw [(ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible
      (q i) (hq i) (hQ i)).1] at hmem
    exact hnot i j hij (Ideal.mem_span_singleton.mp hmem)
  have h0A : ∀ i, (0 : ComplexModel (m + 1)) ∈ A i := by
    intro i
    by_contra hbad
    change q i 0 ≠ 0 at hbad
    exact (hQ i).not_isUnit ((HolGerm.isUnit_iff_eval_ne_zero _).mpr
      (by simpa only [HolGerm.eval_mk] using hbad))
  have hparts : ∀ i, ∃ (d : ℕ) (Δ G : Set (ComplexModel (m + 1))),
      IsOpen Δ ∧ (0 : ComplexModel (m + 1)) ∈ Δ ∧ A i ∩ Δ ⊆ N₁ ∧
      G ⊆ A i ∩ Δ ∧ IsPreconnected G ∧ A i ∩ Δ ⊆ closure G ∧
      (∀ y ∈ G, ∀ j, j ≠ i → y ∉ A j) ∧
      ∀ y ∈ G, RegularAtDim (n := m + 1) (A i ∩ Δ) y d := by
    intro i
    obtain ⟨d, Δ, G, hΔ, h0Δ, hsub, hG, hconn, hdense, havoid, hreg⟩ :=
      IrreducibleGermConnected.exists_connected_nhds (hirr i)
        (fun j => if j = i then ∅ else A j)
        (fun j => by
          split_ifs
          exacts [isAnalyticGerm_empty, (hirr j).1])
        (fun j => by
          split_ifs with hji
          · intro h
            exact (hirr i).2.1 (h.antisymm (Eventually.of_forall fun _ h => h.elim))
          · exact hAnot i j (Ne.symm hji))
        (hN₁.mem_nhds h0N₁)
    refine ⟨d, Δ, G, hΔ, h0Δ, hsub, hG, hconn, hdense, ?_, hreg⟩
    intro y hy j hji
    simpa only [if_neg hji] using havoid y hy j
  choose d Δ G hΔ h0Δ hsub hG hconn hdense havoid hreg using hparts
  let U : Set (ComplexModel (m + 1)) := N₁ ∩ ⋂ i, (A i)ᶜ ∪ Δ i
  have hU : IsOpen U := by
    have hpartsOpen : ∀ i, IsOpen (N₁ ∩ ((A i)ᶜ ∪ Δ i)) := by
      intro i
      have hopen : IsOpen (N₁ ∩ (A i)ᶜ) :=
        ((hqB i).continuousOn.mono (hN₁B i)).isOpen_inter_preimage hN₁
          isClosed_singleton.isOpen_compl
      simpa only [inter_union_distrib_left] using hopen.union (hN₁.inter (hΔ i))
    have hset : U = N₁ ∩ ⋂ i, (N₁ ∩ ((A i)ᶜ ∪ Δ i)) := by
      ext z
      simp only [U, mem_inter_iff, mem_iInter]
      exact ⟨fun h => ⟨h.1, fun i => ⟨h.1, h.2 i⟩⟩,
        fun h => ⟨h.1, fun i => (h.2 i).2⟩⟩
    rw [hset]
    exact hN₁.inter (isOpen_iInter_of_finite hpartsOpen)
  have h0U : (0 : ComplexModel (m + 1)) ∈ U :=
    ⟨h0N₁, mem_iInter.mpr fun i => Or.inr (h0Δ i)⟩
  have hGU : ∀ i, G i ⊆ U := by
    intro i y hy
    refine ⟨hsub i (hG i hy), mem_iInter.mpr fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      exact Or.inr (hG i hy).2
    · exact Or.inl (havoid i y hy j hji)
  have hGm : ∀ i, ∀ y ∈ G i, RegularAtDim (n := m + 1) (A i) y m := by
    intro i y hy
    have hyN := hsub i (hG i hy)
    have hR := AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff
      (hΔ i) (hG i hy).2 |>.mp (hreg i y hy)
    have hR' := AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff
      hN₁ hyN |>.mpr hR
    have hdm := (hpure i N₁ hN₁ (hN₁P i)).1 hR'
    rwa [hdm] at hR
  refine ⟨⟨U, hU⟩, h0U, fun y hy => hN₀sub hy.1.1.1, ?_, G, ?_⟩
  · intro i
    refine ⟨(hqB i).mono (fun y hy => hN₁B i hy.1),
      fun W hW hWU hWne => hnon i W hW
        (fun y hy => hN₁B i (hWU hy).1) hWne,
      fun y hy a => hgen i y (hN₁B i hy.1) a⟩
  · intro i
    have h0cl : (0 : ComplexModel (m + 1)) ∈ closure (G i) := hdense i ⟨h0A i, h0Δ i⟩
    have hne : (G i).Nonempty := by
      by_contra hbad
      have hempty := Set.not_nonempty_iff_eq_empty.mp hbad
      rw [hempty, closure_empty] at h0cl
      exact h0cl
    refine ⟨hne, fun y hy => ⟨(hG i hy).1, hGU i hy⟩, hconn i, ?_, hGm i⟩
    intro y hy
    have hyΔ : y ∈ Δ i := ((mem_iInter.mp hy.2.2 i).resolve_left (not_not.mpr hy.1))
    exact hdense i ⟨hy.1, hyΔ⟩

#print axioms exists_common_prime_regular_neighbourhood

private theorem holomorphicAt_opens_model {n : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (y : U) (hf : HolAt f (y : ComplexModel n)) :
    HolomorphicIdealSheaves.HolomorphicAt n (fun z : U => f z) y := by
  have hy := mem_complexChartAt_source (n := n) y
  have heval : (complexChartAt (n := n) y).val y = (y : ComplexModel n) := by
    simp [complexChartAt, chartAt_opens_apply, chartAt_self_eq]
  have h := CartanLocalReduction.holomorphicAt_comp_chart (x := y) hy (heval ▸ hf)
  simpa only [complexChartAt, chartAt_opens_apply, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_eq] using h

private theorem isComplexAnalytic_zero_opens {n : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f U) :
    IsComplexAnalyticSubset (n := n) {y : U | f y = 0} := by
  intro x
  let e := (complexChartAt (n := n) x).val
  have htarget : e.target ⊆ U := by
    intro z hz
    exact mem_opens_of_chart_mem_target (x := x) (y := z)
      (by simp [chartAt_self_eq]) hz
  refine ⟨{
    generatorCount := 1
    generator := fun _ => f
    coordinateNeighborhood := e.target
    isOpen_coordinateNeighborhood := e.open_target
    center_mem_coordinateNeighborhood := e.map_source (mem_complexChartAt_source x)
    coordinateNeighborhood_subset_target := subset_rfl
    generator_holomorphic := fun _ => hf.mono htarget
    zeroLocus := ?_ }⟩
  intro y _ _
  simp only [complexChartAt, chartAt_opens_apply, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, Set.mem_ofPred_eq, Fin.forall_fin_one, id_eq]

private theorem reduced_generator_opens {n : ℕ} (U : Opens (ComplexModel n))
    (q : ComplexModel n → ℂ)
    (hgen : ∀ y ∈ U, ∀ a : ComplexModel n → ℂ,
      vanishingIdealF {x | q x = 0} y a ↔ InSpanAt (fun _ : Fin 1 => q) y a)
    (y : U) (f : U → ℂ) :
    (HolomorphicIdealSheaves.vanishingIdeal (n := n) {z : U | q z = 0}).mem y f ↔
      HolomorphicIdealSheaves.IsInSpanAt (n := n) (· = fun z : U => q z) y f := by
  constructor
  · intro ha
    let e := (complexChartAt (n := n) y).val
    have hyE : y ∈ e.source := mem_complexChartAt_source y
    have heval : ∀ z : U, e z = (z : ComplexModel n) := by
      intro z
      simp only [e, complexChartAt, chartAt_opens_apply, chartAt_self_eq,
        OpenPartialHomeomorph.refl_apply, id_eq]
    let F : ComplexModel n → ℂ := fun z => f (e.symm z)
    have hF : HolAt F (y : ComplexModel n) := by
      have h := CartanLocalReduction.holAt_comp_chart_symm hyE ha.1
      change HolAt F (e y) at h
      rwa [heval y] at h
    have ht : Tendsto e.symm (𝓝 (y : ComplexModel n)) (𝓝 y) := by
      have h := (e.continuousAt_symm (e.map_source hyE)).tendsto
      rw [e.left_inv hyE, heval y] at h
      exact h
    have hvan : vanishingIdealF {z | q z = 0} (y : ComplexModel n) F := by
      refine ⟨hF, ?_⟩
      filter_upwards [ht.eventually ha.2, e.open_target.mem_nhds
        (by simpa only [heval] using e.map_source hyE)] with z hz hzE hqz
      apply hz
      have hinv : (e.symm z : ComplexModel n) = z := by
        rw [← heval, e.right_inv hzE]
      rwa [hinv]
    obtain ⟨_, c, hc, heq⟩ := (hgen y y.2 F).mp hvan
    apply HolomorphicIdealSheaves.isInSpanAt_eq_iff.mpr
    refine ⟨ha.1, fun z : U => c 0 z, holomorphicAt_opens_model U (c 0) y (hc 0), ?_⟩
    filter_upwards [continuous_subtype_val.tendsto y |>.eventually heq,
      e.open_source.mem_nhds hyE] with z hz hzE
    simpa only [F, ← heval z, e.left_inv hzE, Fin.sum_univ_one] using hz
  · intro ha
    obtain ⟨hhol, a, _, heq⟩ := HolomorphicIdealSheaves.isInSpanAt_eq_iff.mp ha
    refine ⟨hhol, ?_⟩
    filter_upwards [heq] with z hz hqz
    change q z = 0 at hqz
    simpa only [hqz, mul_zero] using hz

/-- Original finite prime factors produce actual prime divisors on ONE
open manifold, with their SAME reduced defining equation at EVERY stalk. -/
theorem exists_common_open_prime_carriers {m r : ℕ}
    (q : Fin r → ComplexModel (m + 1) → ℂ) (hq : ∀ i, HolAt (q i) 0)
    (hQ : ∀ i, Prime (HolGerm.mk (q i) (hq i)))
    (hnot : ∀ i j, i ≠ j → ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (q j) (hq j))
    (N : Set (ComplexModel (m + 1))) (hN : N ∈ 𝓝 0) :
    ∃ U : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ U ∧
      (U : Set (ComplexModel (m + 1))) ⊆ N ∧
      ∃ V : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) U,
        ∀ i, (V i).carrier = {y : U | q i y = 0} ∧ (V i).dim = m ∧
          (∀ y : U, HolomorphicIdealSheaves.HolomorphicAt (m + 1) (fun z : U => q i z) y) ∧
          (HolomorphicIdealSheaves.vanishingIdeal (n := m + 1) (V i).carrier).IsInvertible ∧
          ∀ (y : U) (a : U → ℂ),
            (HolomorphicIdealSheaves.vanishingIdeal (n := m + 1) (V i).carrier).mem y a ↔
              HolomorphicIdealSheaves.IsInSpanAt (n := m + 1) (· = fun z : U => q i z) y a := by
  classical
  obtain ⟨U, h0U, hUN, hqU, G, hG⟩ :=
    exists_common_prime_regular_neighbourhood q hq hQ hnot N hN
  have hV : ∀ i, ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) U,
      V.carrier = {y : U | q i y = 0} ∧ V.dim = m := by
    intro i
    let A : Set U := {y | q i y = 0}
    let H : Set U := (Subtype.val : U → ComplexModel (m + 1)) ⁻¹' G i
    have hA : IsComplexAnalyticSubset (n := m + 1) A :=
      isComplexAnalytic_zero_opens U (q i) (hqU i).1
    have hHG : H ⊆ A := fun y hy => ((hG i).2.1 hy).1
    have hHconn : IsPreconnected H :=
      (hG i).2.2.1.preimage_of_isOpenMap Subtype.val_injective U.isOpen.isOpenMap_subtype_val
        (fun z hz => ⟨⟨z, ((hG i).2.1 hz).2⟩, rfl⟩)
    have hHdense : A ⊆ closure H := by
      intro y hy
      exact U.isOpen.isOpenMap_subtype_val.preimage_closure_subset_closure_preimage
        ((hG i).2.2.2.1 ⟨hy, y.2⟩)
    have hHreg : ∀ y ∈ H, RegularAtDim (n := m + 1) A y m :=
      fun y hy => regularAtDim_preimage_val_iff.mpr ((hG i).2.2.2.2 y hy)
    obtain ⟨c, hcG⟩ := (hG i).1
    let cU : U := ⟨c, ((hG i).2.1 hcG).2⟩
    have hcH : cU ∈ H := hcG
    have hcR := hHreg cU hcH
    have hHC : H ⊆ component (n := m + 1) A cU :=
      subset_component_of_isPreconnected hHconn (fun y hy => ⟨m, hHreg y hy⟩)
        ⟨cU, hcH, mem_component_self hcR⟩
    have hclosure : closure (component (n := m + 1) A cU) = A :=
      le_antisymm (closure_minimal (component_subset A cU) hA.isClosed)
        (hHdense.trans (closure_mono hHC))
    have hirr : IsComplexAnalyticallyIrreducible (n := m + 1) A := by
      rw [← hclosure]
      exact isComplexAnalyticallyIrreducible_closure_component hA hcR
    exact ⟨⟨A, hA.isClosed, hirr, m, Nat.le_succ m, ⟨cU, hcR⟩⟩, rfl, rfl⟩
  choose V hcarrier hdim using hV
  refine ⟨U, h0U, hUN, V, ?_⟩
  intro i
  have hhol : ∀ y : U, HolomorphicIdealSheaves.HolomorphicAt (m + 1)
      (fun z : U => q i z) y :=
    fun y => holomorphicAt_opens_model U (q i) y
      (holAt_of_differentiableOn U.isOpen (hqU i).1 y.2)
  have hgen : ∀ (y : U) (a : U → ℂ),
      (HolomorphicIdealSheaves.vanishingIdeal (n := m + 1) (V i).carrier).mem y a ↔
        HolomorphicIdealSheaves.IsInSpanAt (n := m + 1) (· = fun z : U => q i z) y a := by
    rw [hcarrier i]
    exact reduced_generator_opens U (q i) (hqU i).2.2
  refine ⟨hcarrier i, hdim i, hhol, ?_, hgen⟩
  intro y
  refine ⟨univ, isOpen_univ, mem_univ _, fun z : U => q i z,
    fun z _ => (hhol z).mdifferentiableAt.mdifferentiableWithinAt, ?_, fun z _ => hgen z⟩
  intro W hW _ hWne
  obtain ⟨z, hzW, hqz⟩ := (hqU i).2.1 (Subtype.val '' W)
    (U.isOpen.isOpenMap_subtype_val W hW)
    (fun z ⟨w, _, heq⟩ => heq ▸ w.2) (hWne.image Subtype.val)
  obtain ⟨w, hw, rfl⟩ := hzW
  exact ⟨w, hw, hqz⟩

#print axioms exists_common_open_prime_carriers

end SGPT.PSH
