import SGPT.Foundations.Analysis.Pending.ActualLocalMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination

set_option autoImplicit false

/-! # Genuine all-chart multiplier orders and equivalences are preserved by addition -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition

open FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses IEquivalentMax ActualLocalMultiplierOrderAddition
  MixedSummandCapacityDomination GlobalMultilinearExpansion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem genuineAdd {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h

private theorem correctionSameType {X : Type*} {u : X → EReal} {ρ : X → ℝ}
    {O : Set X} {C : ℝ} (hρ : ∀ y ∈ O, -C ≤ ρ y ∧ ρ y ≤ C) :
    SameSingularityTypeOn u (fun y => u y + (ρ y : EReal)) O := by
  refine ⟨⟨C, fun y hy => le_add_coe_add_coe (by linarith [(hρ y hy).1])⟩,
    ⟨C, fun y hy => ?_⟩⟩
  simpa only [EReal.coe_zero, add_zero] using
    (add_coe_add_coe_le (x := u y) (r := ρ y) (s := 0) (t := C)
      (by linarith [(hρ y hy).2]))

private theorem exists_correction_bound {O : Set (ComplexModel n)}
    (hO : IsOpen O) {z : ComplexModel n} (hz : z ∈ O) {ρ : ComplexModel n → ℝ}
    (hρ : ContinuousOn ρ O) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧ W ⊆ O ∧
      ∃ C : ℝ, ∀ y ∈ W, -C ≤ ρ y ∧ ρ y ≤ C := by
  have hclose : ∀ᶠ y in 𝓝 z, |ρ y - ρ z| < 1 := by
    simpa only [Real.dist_eq] using
      (hρ.continuousAt (hO.mem_nhds hz)).eventually (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp hclose
  refine ⟨O ∩ W, hO.inter hW, ⟨hz, hzW⟩, inter_subset_left, |ρ z| + 1, ?_⟩
  intro y hy
  have h1 := hWsub hy.2
  change |ρ y - ρ z| < 1 at h1
  have h2 := abs_sub_abs_le_abs_sub (ρ y) (ρ z)
  constructor
  · have := neg_abs_le (ρ y)
    linarith
  · have := le_abs_self (ρ y)
    linarith

/-- Both smooth corrections and every auxiliary local addition datum are internally
produced in an arbitrary actual chart, preserving all positive multiplier levels. -/
theorem iOrderOnManifold_add {θ σ : ClosedRealOneOneForm n M} {u v a b : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential σ.val b)
    (hua : IOrderOnManifold (n := n) u a) (hvb : IOrderOnManifold (n := n) v b) :
    IOrderOnManifold (n := n) (fun x => u x + v x) (fun x => a x + b x) := by
  intro c hc e z hz f hf hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨O₁, ρ₁, hzO₁, hρ₁⟩ := hu.1.hasSmoothLocalPotentials e z hz
  obtain ⟨O₂, ρ₂, hzO₂, hρ₂⟩ := hv.1.hasSmoothLocalPotentials e z hz
  have hp₁ : ∀ {q : M → EReal}, IsThetaPshPotential θ.val q →
      PlurisubharmonicOn (fun y => chartFunction q e y + (ρ₁ y : EReal)) O₁ :=
    fun {q} hq => chartCorrectedFamily_plurisubharmonicOn (F := {q})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hq) e hρ₁ _
      ⟨q, mem_singleton _, rfl⟩
  have hp₂ : ∀ {q : M → EReal}, IsThetaPshPotential σ.val q →
      PlurisubharmonicOn (fun y => chartFunction q e y + (ρ₂ y : EReal)) O₂ :=
    fun {q} hq => chartCorrectedFamily_plurisubharmonicOn (F := {q})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hq) e hρ₂ _
      ⟨q, mem_singleton _, rfl⟩
  obtain ⟨W₁, hW₁, hzW₁, hW₁O₁, C₁, hC₁⟩ :=
    exists_correction_bound hρ₁.1 hzO₁ hρ₁.2.2.1.continuousOn
  obtain ⟨W₂, hW₂, hzW₂, hW₂O₂, C₂, hC₂⟩ :=
    exists_correction_bound hρ₂.1 hzO₂ hρ₂.2.2.1.continuousOn
  let W := W₁ ∩ W₂
  have hW : IsOpen W := hW₁.inter hW₂
  have hzW : z ∈ W := ⟨hzW₁, hzW₂⟩
  have hWO₁ : W ⊆ O₁ := fun _ hy => hW₁O₁ hy.1
  have hWO₂ : W ⊆ O₂ := fun _ hy => hW₂O₂ hy.2
  have hWt : W ⊆ e.val.target := hWO₁.trans hρ₁.2.1
  let U := fun y => chartFunction u e y + (ρ₁ y : EReal)
  let V := fun y => chartFunction v e y + (ρ₂ y : EReal)
  let A := fun y => chartFunction a e y + (ρ₁ y : EReal)
  let B := fun y => chartFunction b e y + (ρ₂ y : EReal)
  have hU : PlurisubharmonicOn U W := (hp₁ hu).mono hWO₁
  have hV : PlurisubharmonicOn V W := (hp₂ hv).mono hWO₂
  have hA : PlurisubharmonicOn A W := (hp₁ ha).mono hWO₁
  have hB : PlurisubharmonicOn B W := (hp₂ hb).mono hWO₂
  have htype₁ (q : M → EReal) : SameSingularityTypeOn (chartFunction q e)
      (fun y => chartFunction q e y + (ρ₁ y : EReal)) W :=
    correctionSameType (fun y hy => hC₁ y hy.1)
  have htype₂ (q : M → EReal) : SameSingularityTypeOn (chartFunction q e)
      (fun y => chartFunction q e y + (ρ₂ y : EReal)) W :=
    correctionSameType (fun y hy => hC₂ y hy.2)
  have horder₁ : ∀ y ∈ W, ∀ r : ℝ, 0 < r → ∀ g : ComplexModel n → ℂ,
      AnalyticAt ℂ g y → MultiplierIntegrableAt U r g y volume →
        MultiplierIntegrableAt A r g y volume := by
    intro y hy r hr g hg hgm
    have hiu := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := r) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (hu.1.quasiPlurisubharmonic e y (hWt hy)) (hU y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) (htype₁ u)
    have hia := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := r) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (ha.1.quasiPlurisubharmonic e y (hWt hy)) (hA y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) (htype₁ a)
    exact hia.mp (hua r hr e y (hWt hy) g hg (hiu.mpr hgm))
  have horder₂ : ∀ y ∈ W, ∀ r : ℝ, 0 < r → ∀ g : ComplexModel n → ℂ,
      AnalyticAt ℂ g y → MultiplierIntegrableAt V r g y volume →
        MultiplierIntegrableAt B r g y volume := by
    intro y hy r hr g hg hgm
    have hiv := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := r) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (hv.1.quasiPlurisubharmonic e y (hWt hy)) (hV y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) (htype₂ v)
    have hib := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := r) (f := g)
      (μ := (volume : Measure (ComplexModel n)))
      (hb.1.quasiPlurisubharmonic e y (hWt hy)) (hB y hy).quasiPlurisubharmonicAt
      (hW.mem_nhds hy) (htype₂ b)
    exact hib.mp (hvb r hr e y (hWt hy) g hg (hiv.mpr hgm))
  have htypesum (q r : M → EReal) : SameSingularityTypeOn
      (chartFunction (fun x => q x + r x) e)
      (fun y => (chartFunction q e y + (ρ₁ y : EReal)) +
        (chartFunction r e y + (ρ₂ y : EReal))) W := by
    have hbound : ∀ y ∈ W, -(C₁ + C₂) ≤ ρ₁ y + ρ₂ y ∧
        ρ₁ y + ρ₂ y ≤ C₁ + C₂ := fun y hy => by
      constructor <;> linarith [(hC₁ y hy.1).1, (hC₁ y hy.1).2,
        (hC₂ y hy.2).1, (hC₂ y hy.2).2]
    have h := correctionSameType (u := chartFunction (fun x => q x + r x) e) hbound
    convert h using 1
    funext y
    simp only [chartFunction, EReal.coe_add]
    ac_rfl
  have hiuv := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := c) (f := f)
    (μ := (volume : Measure (ComplexModel n)))
    ((genuineAdd hu hv).1.quasiPlurisubharmonic e z hz)
    ((hU.add hV) z hzW).quasiPlurisubharmonicAt (hW.mem_nhds hzW) (htypesum u v)
  have hiab := multiplierIntegrableAt_iff_of_sameSingularityTypeOn (c := c) (f := f)
    (μ := (volume : Measure (ComplexModel n)))
    ((genuineAdd ha hb).1.quasiPlurisubharmonic e z hz)
    ((hA.add hB) z hzW).quasiPlurisubharmonicAt (hW.mem_nhds hzW) (htypesum a b)
  exact hiab.mpr (multiplierIntegrableAt_add_of_all_levels hW hU hV hA hB
    horder₁ horder₂ hzW hc hf (hiuv.mp hmem))

/-- The two defining directions both use the actual natural addition-order producer. -/
theorem iEquivalentOnManifold_add {θ σ : ClosedRealOneOneForm n M}
    {u v a b : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential σ.val b)
    (hua : IEquivalentOnManifold (n := n) u a)
    (hvb : IEquivalentOnManifold (n := n) v b) :
    IEquivalentOnManifold (n := n) (fun x => u x + v x) (fun x => a x + b x) :=
  ⟨iOrderOnManifold_add hu hv ha hb hua.1 hvb.1,
    iOrderOnManifold_add ha hb hu hv hua.2 hvb.2⟩

end

end SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
