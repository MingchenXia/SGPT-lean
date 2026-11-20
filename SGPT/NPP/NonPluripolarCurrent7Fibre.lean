import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback

/-!
# Fibres of `Θ`-psh functions on products

Source: `chapter_npp.tex`, `cor:compactfibreslicing`, first assertion: *for
`W ∈ PSH(X × Z, Θ)`, `Θ = p₁^*θ + p₂^*γ`, with `Φ - C ≤ W` for `Φ = p₁^*φ`, `φ ∈ PSH(X, θ)`, every
fibre `W_z = W(·, z)` lies in `PSH(X, θ)`*.  Proof: Xia, *Foundations of pluripotential theory*,
`cor:compact-nonpluripolar-fibre-fubini`, first paragraph ("in product charts choose smooth local
potentials `a(x)` of `θ` and `b(z)` of `γ`; then `W + a + b` is plurisubharmonic, so its restriction
`W_z + a + b(z)` to a fibre is plurisubharmonic in `x` …; `W_z ≥ φ - C` excludes `-∞`").

`X × Z` is TN's product complex manifold modelled on `ℂⁿ⁺ᵐ` (`ProductComplexManifold`, the charts
`prodChart e c`), `Θ = prodForm θ γ`, and `PSH(·, θ)` is TN's `IsThetaPshPotential`
(the project's `PSH(X, θ)`, used for presentations `T = θ + dd^c φ` of `𝒵₊(X)`).

* `isSmoothLocalPotential_add` — local potentials add.
* **`isThetaPshPotential_fibre`** — `W_z ∈ PSH(X, θ)` for every `z ∈ Z` (no compactness,
  connectedness or Kähler hypothesis is needed, and only the lower bound `Φ - C ≤ W` is used).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.NPP.CompactFibreSlicing

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold

/-- Smooth local potentials of two closed forms add to a local potential of the sum. -/
theorem isSmoothLocalPotential_add {N : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] {a b : ClosedRealOneOneForm N Y}
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ σ : ComplexModel N → ℝ}
    (ha : IsSmoothLocalPotential a.val e W ρ) (hb : IsSmoothLocalPotential b.val e W σ) :
    IsSmoothLocalPotential (a + b).val e W (fun z => ρ z + σ z) := by
  refine ⟨ha.1, ha.2.1, ha.2.2.1.add hb.2.2.1, fun z hz => ?_⟩
  rw [smoothDDC_add ha.1 ha.2.2.1 hb.2.2.1 hz, ha.2.2.2 hz, hb.2.2.2 hz,
    ClosedRealOneOneForm.coeff_add]

/-- Adding and then subtracting a real number does not change an extended real. -/
theorem ereal_add_coe_add_coe_neg (a : EReal) (r : ℝ) :
    a + (r : EReal) + ((-r : ℝ) : EReal) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

variable {n m : ℕ} {X Z : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-- **`cor:compactfibreslicing`, first assertion**: for `Θ = p₁^*θ + p₂^*γ` on `X × Z`,
`φ ∈ PSH(X, θ)` and `W ∈ PSH(X × Z, Θ)` with `p₁^*φ - C ≤ W`, every fibre `W_z = W(·, z)` lies in
`PSH(X, θ)`. -/
theorem isThetaPshPotential_fibre (θ : ClosedRealOneOneForm n X) (γ : ClosedRealOneOneForm m Z)
    {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) {W : X × Z → EReal}
    (hW : IsThetaPshPotential (prodForm θ γ).val W) {C : ℝ}
    (hC : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p) (z : Z) :
    IsThetaPshPotential θ.val fun x => W (x, z) := by
  refine ⟨fun e x' hx' => ?_, fun x U hU hx => ?_⟩
  · set c : ComplexChart m Z := complexChartAt (n := m) z
    have hz : z ∈ c.val.source := mem_complexChartAt_source z
    let d : ComplexChart (n + m) (X × Z) :=
      ⟨prodChart e.val c.val, mem_image2_of_mem e.2 c.2⟩
    set L := prodModelEquiv n m
    obtain ⟨Wa, a, hxWa, ha⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e x' hx'
    obtain ⟨Wb, b, hzWb, hb⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials γ c
      (c.val z) (c.val.map_source hz)
    have hfst := contMDiff_fst (n := n) (m := m) (X := X) (Y := Z)
    have hsnd := contMDiff_snd (n := n) (m := m) (X := X) (Y := Z)
    have hpa := isSmoothLocalPotential_pullback hfst d ha
    have hpb := isSmoothLocalPotential_pullback hsnd d hb
    set D := potentialDomain Prod.fst d e Wa ∩ potentialDomain Prod.snd d c Wb with hD_def
    have hD : IsOpen D :=
      (potentialDomain_isOpen hfst d e ha.1).inter (potentialDomain_isOpen hsnd d c hb.1)
    have hρ : IsSmoothLocalPotential (prodForm θ γ).val d D
        (fun w => (a ∘ coordinateMap Prod.fst d e) w + (b ∘ coordinateMap Prod.snd d c) w) :=
      isSmoothLocalPotential_add (hpa.mono hD inter_subset_left) (hpb.mono hD inter_subset_right)
    have hpsh := ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      hW.1 d hρ
    -- the slice `y ↦ (y, c z)` in the product chart
    set s : ComplexModel n → ComplexModel (n + m) := fun y => L (y, c.val z) with hs_def
    set S : Set (ComplexModel n) := e.val.target ∩ Wa with hS_def
    have hS : IsOpen S := e.val.open_target.inter ha.1
    have hsymm : ∀ y, d.val.symm (s y) = (e.val.symm y, z) := by
      intro y
      change (prodChart e.val c.val).symm (L (y, c.val z)) = _
      rw [prodChart_symm_apply, ContinuousLinearEquiv.symm_apply_apply, c.val.left_inv hz]
    have hcoord1 : ∀ y ∈ S, coordinateMap Prod.fst d e (s y) = y := by
      intro y hy
      change e.val (d.val.symm (s y)).1 = y
      rw [hsymm, e.val.right_inv hy.1]
    have hcoord2 : ∀ y, coordinateMap Prod.snd d c (s y) = c.val z := by
      intro y
      change c.val (d.val.symm (s y)).2 = _
      rw [hsymm]
    have hmaps : MapsTo s S D := by
      intro y hy
      have htd : s y ∈ d.val.target := by
        change s y ∈ (prodChart e.val c.val).target
        rw [prodChart_target]
        change L.symm (L (y, c.val z)) ∈ e.val.target ×ˢ c.val.target
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact ⟨hy.1, c.val.map_source hz⟩
      refine ⟨⟨⟨htd, ?_⟩, ?_⟩, ⟨⟨htd, ?_⟩, ?_⟩⟩
      · change (d.val.symm (s y)).1 ∈ e.val.source
        rw [hsymm]
        exact e.val.map_target hy.1
      · change coordinateMap Prod.fst d e (s y) ∈ Wa
        rw [hcoord1 y hy]
        exact hy.2
      · change (d.val.symm (s y)).2 ∈ c.val.source
        rw [hsymm]
        exact hz
      · change coordinateMap Prod.snd d c (s y) ∈ Wb
        rw [hcoord2]
        exact hzWb
    have hsd : DifferentiableOn ℂ s S :=
      (L.differentiable.comp (differentiable_id.prodMk (differentiable_const _))).differentiableOn
    have hcomp := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hS hsd hmaps hpsh
    refine ⟨S, a, ⟨hx', hxWa⟩, ha.mono hS inter_subset_right, fun y hy => ?_⟩
    have hconst : SGPT.Foundations.Analysis.PlurisubharmonicAt
        (fun _ : ComplexModel n => (((-b (c.val z)) : ℝ) : EReal)) y :=
      plurisubharmonicAt_const _ (EReal.coe_ne_top _) y
    refine ((hcomp y hy).add hconst).congr ?_
    filter_upwards [hS.mem_nhds hy] with w hw
    simp only [Function.comp_apply, chartFunction]
    rw [hsymm, hcoord1 w hw, hcoord2, EReal.coe_add, ← add_assoc,
      ereal_add_coe_add_coe_neg]
  · obtain ⟨y, hyU, hy⟩ := hφ.2 x U hU hx
    refine ⟨y, hyU, fun h => hy ?_⟩
    have h1 := hC (y, z)
    have h' : W (y, z) = ⊥ := h
    rw [h'] at h1
    have h2 : φ y - (C : EReal) = ⊥ := le_bot_iff.mp h1
    induction hφy : φ y using EReal.rec with
    | bot => rfl
    | top => rw [hφy] at h2; simp at h2
    | coe r =>
      rw [hφy, ← EReal.coe_sub] at h2
      exact absurd h2 (EReal.coe_ne_bot _)

end SGPT.NPP.CompactFibreSlicing
