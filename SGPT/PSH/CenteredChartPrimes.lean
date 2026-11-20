import SGPT.PSH.OriginalPrimeFactorization
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.RegularAtDimChart
import SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticSubsetOpens
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal ORIGINAL open subset corresponding to a centered
coordinate open set; all chart-source conditions are retained. -/
def centeredChartOpen (x : M) (Ω : Opens (ComplexModel n)) : Opens M :=
  let e := (complexChartAt (n := n) x).val
  ⟨e.source ∩ e ⁻¹' ((fun z => z - e x) ⁻¹' (Ω : Set (ComplexModel n))),
    e.isOpen_inter_preimage (Ω.isOpen.preimage (continuous_id.sub continuous_const))⟩

/-- The actual centered chart identifies the SAME original open manifold
with its coordinate open manifold, using literal chart inverse equations. -/
def centeredChartHomeomorph (x : M) (Ω : Opens (ComplexModel n))
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target) :
    centeredChartOpen x Ω ≃ₜ Ω := by
  let e := (complexChartAt (n := n) x).val
  refine {
    toFun := fun y => ⟨e y - e x, y.2.2⟩
    invFun := fun z => ⟨e.symm ((z : ComplexModel n) + e x),
      e.map_target (htarget z z.2), ?_⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · change e (e.symm ((z : ComplexModel n) + e x)) - e x ∈ Ω
    rw [e.right_inv (htarget z z.2), add_sub_cancel_right]
    exact z.2
  · intro y
    apply Subtype.ext
    change e.symm ((e y - e x) + e x) = y
    rw [sub_add_cancel, e.left_inv y.2.1]
  · intro z
    apply Subtype.ext
    change e (e.symm ((z : ComplexModel n) + e x)) - e x = z
    rw [e.right_inv (htarget z z.2), add_sub_cancel_right]
  · have he : Continuous (fun y : centeredChartOpen x Ω => e (y : M)) :=
      e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.2.1)
    exact (he.sub continuous_const).subtype_mk _
  · have ha : Continuous (fun z : Ω => (z : ComplexModel n) + e x) :=
      continuous_subtype_val.add_const (e x)
    have he : Continuous (fun z : Ω => e.symm ((z : ComplexModel n) + e x)) :=
      e.symm.continuousOn.comp_continuous ha (fun z => htarget z z.2)
    exact he.subtype_mk _

/-- Holomorphy of the forward map is produced by the actual chart and
translation, restricted to their literal original domains. -/
theorem centeredChartHomeomorph_contMDiff (x : M) (Ω : Opens (ComplexModel n))
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (centeredChartHomeomorph x Ω htarget) := by
  let e := (complexChartAt (n := n) x).val
  have he : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e e.source :=
    contMDiffOn_chart
  apply (ContMDiff.subtypeVal_comp_iff Ω (centeredChartHomeomorph x Ω htarget)).mp
  have hsub : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : M => e y - e x) (centeredChartOpen x Ω) :=
    (he.sub contMDiffOn_const).mono (fun y hy => hy.1)
  exact contMDiff_restrict hsub

/-- The SAME actual inverse centered chart is holomorphic throughout
the actual coordinate open manifold, by its genuine target condition. -/
theorem centeredChartHomeomorph_symm_contMDiff (x : M) (Ω : Opens (ComplexModel n))
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (centeredChartHomeomorph x Ω htarget).symm := by
  let e := (complexChartAt (n := n) x).val
  have ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : Ω => (z : ComplexModel n) + e x) :=
    contMDiff_subtype_val.add contMDiff_const
  apply (ContMDiff.subtypeVal_comp_iff (centeredChartOpen x Ω)
    (centeredChartHomeomorph x Ω htarget).symm).mp
  intro z
  have he : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      e.symm ((z : ComplexModel n) + e x) :=
    (contMDiffOn_chart_symm (x := x)).contMDiffAt (e.open_target.mem_nhds (htarget z z.2))
  change ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
    (fun z : Ω => e.symm ((z : ComplexModel n) + e x)) z
  exact he.comp z (ha z)


omit [IsComplexManifold n M] in
private theorem holomorphicAt_comp_native {k : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]
    {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    {f : M → ℂ} {y : Z} (hf : HolomorphicAt n f (g y)) :
    HolomorphicAt k (fun z => f (g z)) y := by
  filter_upwards [(hg.continuous.tendsto y).eventually hf] with z hz
  exact hz.comp z ((hg z).mdifferentiableAt (by simp))

private theorem centeredChart_regularAtDim (x : M) (Ω : Opens (ComplexModel n))
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target)
    (B : Set Ω) (y : centeredChartOpen x Ω) {k : ℕ}
    (hB : RegularAtDim (n := n) B (centeredChartHomeomorph x Ω htarget y) k) :
    RegularAtDim (n := n) ((centeredChartHomeomorph x Ω htarget) ⁻¹' B) y k := by
  let e := (complexChartAt (n := n) x).val
  let S : Set (ComplexModel n) := Subtype.val '' B
  let T : Set (ComplexModel n) := {z | z - e x ∈ S}
  have hS : RegularAtDim (n := n) S (e y - e x) k :=
    regularAtDim_image_val_iff.mpr hB
  have hT : RegularAtDim (n := n) T (e y) k :=
    (AnalyticLocalStatement.regularAtDim_translate_iff (e x) (e y)).mpr hS
  have hT' : RegularAtDim (n := n) (T ∩ e.target) (e y) k :=
    (AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff
      e.open_target (e.map_source y.2.1)).mpr hT
  have hA : RegularAtDim (n := n) (e.source ∩ e ⁻¹' T) (y : M) k :=
    (RegularAtDimChart.regularAtDim_chart_iff (complexChartAt (n := n) x) T y.2.1).mpr hT'
  have heq : (Subtype.val : centeredChartOpen x Ω → M) ⁻¹' (e.source ∩ e ⁻¹' T) =
      (centeredChartHomeomorph x Ω htarget) ⁻¹' B := by
    ext z
    change (z : M) ∈ e.source ∧ e z - e x ∈ S ↔ _
    constructor
    · rintro ⟨_, w, hw, hweq⟩
      have hwz : w = centeredChartHomeomorph x Ω htarget z := Subtype.ext hweq
      change centeredChartHomeomorph x Ω htarget z ∈ B
      rwa [hwz] at hw
    · intro hz
      exact ⟨z.2.1, centeredChartHomeomorph x Ω htarget z, hz, rfl⟩
  rw [← heq]
  exact regularAtDim_preimage_val_iff.mpr hA

/-- The SAME reduced equation is transported at EVERY original stalk by
actual holomorphic composition in both directions. -/
theorem centeredChart_reduced_ideal (x : M) (Ω : Opens (ComplexModel n))
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target)
    (B : Set Ω) (q : Ω → ℂ) (hq : ∀ z, HolomorphicAt n q z)
    (hgen : ∀ (z : Ω) (a : Ω → ℂ),
      (vanishingIdeal (n := n) B).mem z a ↔ IsInSpanAt (n := n) (· = q) z a)
    (y : centeredChartOpen x Ω) (a : centeredChartOpen x Ω → ℂ) :
    (vanishingIdeal (n := n) ((centeredChartHomeomorph x Ω htarget) ⁻¹' B)).mem y a ↔
      IsInSpanAt (n := n) (· = fun z => q (centeredChartHomeomorph x Ω htarget z)) y a := by
  let κ := centeredChartHomeomorph x Ω htarget
  have hκ := centeredChartHomeomorph_contMDiff x Ω htarget
  have hκs := centeredChartHomeomorph_symm_contMDiff x Ω htarget
  constructor
  · intro ha
    have hhol : HolomorphicAt n (fun z => a (κ.symm z)) (κ y) := by
      have ha' : HolomorphicAt n a (κ.symm (κ y)) := by
        rw [κ.symm_apply_apply]
        exact ha.1
      exact holomorphicAt_comp_native hκs ha'
    have hvan : (vanishingIdeal (n := n) B).mem (κ y) (fun z => a (κ.symm z)) := by
      refine ⟨hhol, ?_⟩
      have ht : Tendsto κ.symm (𝓝 (κ y)) (𝓝 y) := by
        convert κ.symm.continuous.tendsto (κ y) using 1
        exact congrArg 𝓝 (κ.symm_apply_apply y).symm
      have hev := ht.eventually ha.2
      filter_upwards [hev] with z hz hzB
      apply hz
      change κ (κ.symm z) ∈ B
      rw [κ.apply_symm_apply]
      exact hzB
    obtain ⟨_, b, hb, heq⟩ := isInSpanAt_eq_iff.mp ((hgen (κ y) _).mp hvan)
    apply isInSpanAt_eq_iff.mpr
    refine ⟨ha.1, fun z => b (κ z), holomorphicAt_comp_native hκ hb, ?_⟩
    filter_upwards [(κ.continuous.tendsto y).eventually heq] with z hz
    simpa only [κ.symm_apply_apply] using hz
  · intro ha
    obtain ⟨hhol, b, _, heq⟩ := isInSpanAt_eq_iff.mp ha
    refine ⟨hhol, ?_⟩
    filter_upwards [heq] with z hz hzB
    have hqmem : (vanishingIdeal (n := n) B).mem (κ z) q :=
      (hgen (κ z) q).mpr (isInSpanAt_eq_iff.mpr
        ⟨hq (κ z), fun _ => 1, holomorphicAt_const 1,
          Eventually.of_forall (fun _ => by simp only [one_mul])⟩)
    have hqzero : q (κ z) = 0 := hqmem.2.self_of_nhds hzB
    change a z = b z * q (κ z) at hz
    rw [hqzero, mul_zero] at hz
    exact hz

/-- Original native chart transport constructs the actual irreducible
carrier, actual regular dimension witness and SAME reduced ideal at all stalks. -/
theorem exists_original_chart_prime_transport (x : M) (Ω : Opens (ComplexModel n))
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := n) x).val x ∈
      (complexChartAt (n := n) x).val.target)
    (V : ClosedIrreducibleAnalyticSubvariety n Ω) (q : Ω → ℂ)
    (hq : ∀ z, HolomorphicAt n q z)
    (hgen : ∀ (z : Ω) (a : Ω → ℂ),
      (vanishingIdeal (n := n) V.carrier).mem z a ↔ IsInSpanAt (n := n) (· = q) z a) :
    ∃ W : ClosedIrreducibleAnalyticSubvariety n (centeredChartOpen x Ω),
      W.carrier = (centeredChartHomeomorph x Ω htarget) ⁻¹' V.carrier ∧ W.dim = V.dim ∧
      (∀ y, HolomorphicAt n (fun z => q (centeredChartHomeomorph x Ω htarget z)) y) ∧
      ∀ (y : centeredChartOpen x Ω) (a : centeredChartOpen x Ω → ℂ),
        (vanishingIdeal (n := n) W.carrier).mem y a ↔
          IsInSpanAt (n := n) (· = fun z => q (centeredChartHomeomorph x Ω htarget z)) y a := by
  let κ := centeredChartHomeomorph x Ω htarget
  have hκ := centeredChartHomeomorph_contMDiff x Ω htarget
  have hκs := centeredChartHomeomorph_symm_contMDiff x Ω htarget
  let A : Set (centeredChartOpen x Ω) := κ ⁻¹' V.carrier
  have hA : IsComplexAnalyticSubset (n := n) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hκ V.analytic
  have hirr : IsComplexAnalyticallyIrreducible (n := n) A := by
    refine ⟨hA, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := V.nonempty
      exact ⟨κ.symm z, by simpa only [A, mem_preimage, κ.apply_symm_apply] using hz⟩
    · intro B C hB hC hBA hCA hcover
      have hBi := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hκs hB
      have hCi := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hκs hC
      have hBV : κ.symm ⁻¹' B ⊆ V.carrier := by
        intro z hz
        have h := hBA hz
        simpa only [A, mem_preimage, κ.apply_symm_apply] using h
      have hCV : κ.symm ⁻¹' C ⊆ V.carrier := by
        intro z hz
        have h := hCA hz
        simpa only [A, mem_preimage, κ.apply_symm_apply] using h
      have hcover' : V.carrier = κ.symm ⁻¹' B ∪ κ.symm ⁻¹' C := by
        ext z
        have h := Set.ext_iff.mp hcover (κ.symm z)
        simpa only [A, mem_preimage, κ.apply_symm_apply, mem_union] using h
      rcases V.irreducible_carrier.eq_left_or_eq_right hBi hCi hBV hCV hcover' with h | h
      · left
        ext y
        have hh := Set.ext_iff.mp h (κ y)
        change (κ y ∈ V.carrier ↔ κ.symm (κ y) ∈ B) at hh
        rw [κ.symm_apply_apply] at hh
        exact hh
      · right
        ext y
        have hh := Set.ext_iff.mp h (κ y)
        change (κ y ∈ V.carrier ↔ κ.symm (κ y) ∈ C) at hh
        rw [κ.symm_apply_apply] at hh
        exact hh
  obtain ⟨z, hz⟩ := V.regularLocus_nonempty
  have hreg : RegularAtDim (n := n) A (κ.symm z) V.dim := by
    apply centeredChart_regularAtDim x Ω htarget V.carrier (κ.symm z)
    change RegularAtDim (n := n) V.carrier (κ (κ.symm z)) V.dim
    rw [κ.apply_symm_apply]
    exact hz
  refine ⟨⟨A, V.isClosed_carrier.preimage κ.continuous, hirr, V.dim, V.dim_le,
    ⟨κ.symm z, hreg⟩⟩, rfl, rfl,
    fun y => holomorphicAt_comp_native hκ (hq (κ y)), ?_⟩
  exact centeredChart_reduced_ideal x Ω htarget V.carrier q hq hgen

#print axioms centeredChartOpen
#print axioms centeredChartHomeomorph
#print axioms centeredChartHomeomorph_contMDiff
#print axioms centeredChartHomeomorph_symm_contMDiff
#print axioms centeredChart_reduced_ideal
#print axioms exists_original_chart_prime_transport

end SGPT.PSH
