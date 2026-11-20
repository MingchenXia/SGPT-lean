import SGPT.Foundations.Analysis.Pending.ComponentwiseNormalizedCurrentPotentials
import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound

set_option autoImplicit false

/-! Uniform Harnack propagation and local integrals on the ORIGINAL compact
complex manifold, with normalization in EACH connected component.
Full BP statements and ENTIRE proofs precede this source. No connectedness,
nonempty manifold, incoming integral bounds or limit/class certificates. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ComponentwiseThetaPshUniformL1
open FirstPass ThetaPshUniformL1Bound

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] {θ : SmoothRealForm n M 2}

/-- Actual propagation inside the target component with a uniform finite cover,
without changing the original manifold or assuming it is connected. -/
theorem exists_forall_mem_set_le_componentwise (hθ : HasSmoothLocalPotentials θ)
    (H : HarnackBall θ) (c : ℝ) :
    ∃ c' : ℝ, ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∀ y, ∃ x ∈ connectedComponent y, ((-c : ℝ) : EReal) ≤ u x) →
      ∃ x ∈ H.set, ((-c' : ℝ) : EReal) ≤ u x := by
  classical
  have hex : ∀ x : M, ∃ Hx : HarnackBall θ, Hx.e = complexChartAt (n := n) x ∧
      Hx.z = (complexChartAt (n := n) x).val x ∧ Hx.r < 1 := fun x =>
    exists_harnackBall hθ _ ((complexChartAt (n := n) x).val.map_source
      (mem_complexChartAt_source x)) one_pos
  choose Hx hHxe hHxz _ using hex
  have hmem : ∀ x, x ∈ (Hx x).set := by
    intro x
    refine ⟨by rw [hHxe]; exact mem_complexChartAt_source x, ?_⟩
    rw [mem_preimage, hHxe, ← hHxz]
    exact mem_ball_self (Hx x).r_pos
  let Good : M → M → Prop := fun x y => ∀ a : ℝ, ∃ b : ℝ, ∀ u : M → EReal,
    ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ t ∈ (Hx x).set, ((-a : ℝ) : EReal) ≤ u t) →
      ∃ t ∈ (Hx y).set, ((-b : ℝ) : EReal) ≤ u t
  have hloc : ∀ x, ∀ᶠ y in 𝓝 x, Good x y ∧ Good y x := by
    intro x
    filter_upwards [(Hx x).isOpen_set.mem_nhds (hmem x)] with y hy
    exact ⟨fun a => HarnackBall.transfer (Hx x) (Hx y) ⟨y,hy,hmem y⟩ a,
      fun a => HarnackBall.transfer (Hx y) (Hx x) ⟨y,hmem y,hy⟩ a⟩
  have htrans : ∀ x y z, Good x y → Good y z → Good x z := by
    intro x y z hxy hyz a
    obtain ⟨b,hb⟩ := hxy a
    obtain ⟨d,hd⟩ := hyz b
    exact ⟨d,fun u hu hle h => hd u hu hle (hb u hu hle h)⟩
  let y : M := H.e.val.symm H.z
  let C : Set M := connectedComponent y
  have hall : ∀ x ∈ C, ∀ z ∈ C, Good x z := by
    intro x hx z hz
    exact isConnected_connectedComponent.isPreconnected.induction₂' Good
      (fun x _ => (hloc x).filter_mono nhdsWithin_le_nhds)
      (fun x y z _ _ _ => htrans x y z) hx hz
  obtain ⟨s,hs⟩ := isClosed_connectedComponent.isCompact.elim_finite_subcover
    (fun x : C => (Hx x).set) (fun x => (Hx x).isOpen_set)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hmem x⟩)
  choose cx hcx using fun x : C => hall x x.2 y mem_connectedComponent c
  let cmax : ℝ := ∑ x ∈ s, |cx x|
  have hcmax : ∀ x ∈ s, cx x ≤ cmax := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (cx i)) hx)
  have hyH : y ∈ H.set := H.symm_mem_set (mem_ball_self H.r_pos)
  obtain ⟨c',hc'⟩ := HarnackBall.transfer (Hx y) H ⟨y,hmem y,hyH⟩ cmax
  refine ⟨c',fun u hu hle hnorm => ?_⟩
  obtain ⟨x₀,hx₀,hx₀u⟩ := hnorm y
  obtain ⟨x,hxs,hx₀x⟩ := mem_iUnion₂.mp (hs hx₀)
  obtain ⟨t,ht,hct⟩ := hcx x u hu hle ⟨x₀,hx₀x,hx₀u⟩
  refine hc' u hu hle ⟨t,ht,le_trans ?_ hct⟩
  exact EReal.coe_le_coe_iff.mpr (by linarith [hcmax x hxs])

/-- The actual deficit estimate bounds the original Haar lower integral,
retaining all poles and one finite bound before all normalized potentials. -/
theorem exists_lintegral_harnack_ball_le_componentwise
    (hθ : HasSmoothLocalPotentials θ) (H : HarnackBall θ) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ u : M → EReal, ThetaPlurisubharmonic θ u →
      (∀ x, u x ≤ 0) →
      (∀ y, ∃ x ∈ connectedComponent y, ((-c : ℝ) : EReal) ≤ u x) →
      ∫⁻ z in ball H.z H.r, (-u (H.e.val.symm z)).toENNReal ≤ B := by
  obtain ⟨c',hc'⟩ := exists_forall_mem_set_le_componentwise hθ H c
  obtain ⟨A,P,hAP⟩ := H.exists_bounds
  refine ⟨volume (ball (0 : ComplexModel n) (2 * H.r)) * ENNReal.ofReal (A + c' - P),
    ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top,?_⟩
  intro u hu hle hnorm
  obtain ⟨x,hx,hcx⟩ := hc' u hu hle hnorm
  have hcx' : ((-c' : ℝ) : EReal) ≤ u (H.e.val.symm (H.e.val x)) := by
    rw [H.e.val.left_inv hx.1]
    exact hcx
  refine le_trans ?_ (H.deficit_le hAP hu hle hx.2 hcx')
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).mpr
    (Eventually.of_forall fun z hz => ?_))
  exact H.neg_le_deficit (fun w hw => (hAP w hw).2) u hz

/-- Every actual chart compact set has a finite uniform local integral bound
from componentwise normalization, including an empty compact set or dimension zero. -/
theorem exists_lintegral_compact_le_componentwise (hθ : HasSmoothLocalPotentials θ)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) (c : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ u : M → EReal, ThetaPlurisubharmonic θ u →
      (∀ x, u x ≤ 0) →
      (∀ y, ∃ x ∈ connectedComponent y, ((-c : ℝ) : EReal) ≤ u x) →
      ∫⁻ z in K, (-u (e.val.symm z)).toENNReal ≤ B := by
  classical
  have hex : ∀ z : K, ∃ Hz : HarnackBall θ, Hz.e = e ∧ Hz.z = z ∧ Hz.r < 1 :=
    fun z => exists_harnackBall hθ e (hKe z.2) one_pos
  choose Hz hHze hHzz _ using hex
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun z : K => ball (z : ComplexModel n) (Hz z).r)
    (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (Hz _).r_pos⟩)
  choose B hB hBu using fun z : K => exists_lintegral_harnack_ball_le_componentwise hθ (Hz z) c
  refine ⟨∑ z ∈ s, B z,ENNReal.sum_lt_top.mpr fun z _ => hB z,?_⟩
  intro u hu hle hnorm
  calc
    (∫⁻ z in K, (-u (e.val.symm z)).toENNReal) ≤
        ∫⁻ z in ⋃ a ∈ s, ball (a : ComplexModel n) (Hz a).r, (-u (e.val.symm z)).toENNReal :=
      lintegral_mono_set hs
    _ ≤ ∑ a ∈ s, ∫⁻ z in ball (a : ComplexModel n) (Hz a).r,
        (-u (e.val.symm z)).toENNReal := ThetaPshUniformL1Bound.lintegral_biUnion_finset_le _ _ _ _
    _ ≤ ∑ a ∈ s, B a := Finset.sum_le_sum fun a _ => by
      have h := hBu a u hu hle hnorm
      rw [hHze a,hHzz a] at h
      exact h

end SGPT.Foundations.Analysis.Pending.ComponentwiseThetaPshUniformL1
