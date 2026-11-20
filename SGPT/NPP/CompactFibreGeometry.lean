import SGPT.NPP.NonPluripolarCurrent7Kahler
import SGPT.NPP.NonPluripolarCurrent2Opens
import SGPT.NPP.NonPluripolarCurrent7Fibre
import SGPT.NPP.NonPluripolarCurrent5Fubini
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import SGPT.NPP.CompactFibreLocalFubini
import SGPT.Foundations.Analysis.Pending.IntegrationCurrent
import SGPT.Foundations.Analysis.Pending.NonPluripolarGauge
import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStar
import Lean.Elab.Command

/-! Genuine compact fibre slicing, original source proof fragments under proper canonical module identity. -/

section CompactFibreCanonicalFragment000

/-! An actual global original geometric-current product reads as the actual
local corrected-potential NPP product, on any genuine potential patch.
The local well-definedness is produced from compact Kahler geometry. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

theorem original_theta_product_local_reading {N p q : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (N + 1)) M]
    [IsComplexManifold (N + 1) M] [CompactSpace M]
    (omega : KahlerBackground (N + 1) M) (hqp : q + p = N + 1)
    (θ : Fin p → ClosedRealOneOneForm (N + 1) M) (u : Fin p → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (e : ComplexChart (N + 1) M) {B : Opens (ComplexModel (N + 1))}
    (hB : (B : Set (ComplexModel (N + 1))) ⊆ e.val.target)
    (ρ : Fin p → ComplexModel (N + 1) → ℝ)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e B (ρ i)) :
    IsWellDefinedOn hqp B (fun i z => chartFunction (u i) e z + (ρ i z : EReal)) ∧
      restrict hB
        ((currentProduct hqp (fun i => thetaReadingCurrent (θ i).val (u i) (hu i))
          (isCurrentProductWellDefined_thetaReadingCurrent omega hqp θ u hu)).inChart e) =
        SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct hqp B
          (fun i z => chartFunction (u i) e z + (ρ i z : EReal)) := by
  let hT := isCurrentProductWellDefined_thetaReadingCurrent omega hqp θ u hu
  let ψ := fun i y => u i y + (ρ i (e.val y) : EReal)
  have hψ := isLocalPotential_patch (fun i => (θ i).val) u hu e ρ hρ
  have hlocal := hT.productInChart_restrict hψ e
  have hBE : B ≤ chartDomain e (patchSource e B) := by
    rw [chartDomain_patchSource e hB]
  have hpsh := hψ.chartPsh e
  have hc := nonPluripolarProduct_congr hqp (U := B)
    (φ := fun i z => ψ i (e.val.symm z))
    (φ' := fun i z => chartFunction (u i) e z + (ρ i z : EReal))
    (fun i z hz => by dsimp only [ψ, chartFunction]; rw [e.val.right_inv (hB hz)])
  have hWB : IsWellDefinedOn hqp B (fun i z => ψ i (e.val.symm z)) :=
    isWellDefinedOn_restrict hqp hpsh hlocal.1 hBE
  refine ⟨hc.1.mp hWB, ?_⟩
  change restrict hB (hT.productInChart e) = _
  rw [← restrict_restrict hBE (chartDomain_le e (patchSource e B)), hlocal.2,
    restrict_nonPluripolarProduct hqp hpsh hlocal.1 hBE]
  exact hc.2

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment000

section CompactFibreCanonicalFragment001

/-! Original actual compact Kahler current products in ALL ambient dimensions.
At dimension zero the existing empty-product current of integration is used. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {N p q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] [CompactSpace M]

def originalThetaProduct (omega : KahlerBackground N M) (hqp : q + p = N)
    (θ : Fin p → ClosedRealOneOneForm N M) (u : Fin p → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) : PositiveCurrent N M q := by
  cases N with
  | zero =>
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    exact bedfordTaylor hqp (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ N =>
    exact currentProduct hqp (fun i => thetaReadingCurrent (θ i).val (u i) (hu i))
      (isCurrentProductWellDefined_thetaReadingCurrent omega hqp θ u hu)

theorem originalThetaProduct_local_reading (omega : KahlerBackground N M)
    (hqp : q + p = N) (θ : Fin p → ClosedRealOneOneForm N M) (u : Fin p → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (e : ComplexChart N M) {B : Opens (ComplexModel N)}
    (hB : (B : Set (ComplexModel N)) ⊆ e.val.target) (ρ : Fin p → ComplexModel N → ℝ)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e B (ρ i)) :
    IsWellDefinedOn hqp B (fun i z => chartFunction (u i) e z + (ρ i z : EReal)) ∧
      restrict hB ((originalThetaProduct omega hqp θ u hu).inChart e) =
        SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct hqp B
          (fun i z => chartFunction (u i) e z + (ρ i z : EReal)) := by
  cases N with
  | zero =>
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have heq : (fun i z => chartFunction (u i) e z + (ρ i z : EReal)) =
        (fun i z => ((Fin.elim0 i : ℝ) : EReal)) := by
      funext i
      exact Fin.elim0 i
    have hbound : ∀ i : Fin 0, IsLocallyBoundedPshOn B (fun _ => (Fin.elim0 i : ℝ)) :=
      fun i => Fin.elim0 i
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact isWellDefinedOn_of_isLocallyBoundedPshOn hqp hbound
    · rw [heq, nonPluripolarProduct_of_isLocallyBoundedPshOn hqp hbound]
      dsimp only [originalThetaProduct, bedfordTaylor, bedfordTaylorInChart]
      exact restrict_oneCurrentOf' hqp hB
  | succ N =>
    exact original_theta_product_local_reading omega hqp θ u hu e hB ρ hρ

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment001

section CompactFibreCanonicalFragment002

/-! The existing original global current wedge measure has its literal
original local-current measure in each genuine coordinate patch. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {N q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

def chartPatchSource (e : ComplexChart N M) (B : Opens (ComplexModel N)) : Opens M :=
  ⟨e.val.source ∩ e.val ⁻¹' B, e.val.isOpen_inter_preimage B.isOpen⟩

theorem global_wedgeMeasure_restrict_chart_patch (T : PositiveCurrent N M q)
    (β : SemipositiveFormOn N (⊤ : Opens M)) (e : ComplexChart N M)
    {B : Opens (ComplexModel N)} (hB : (B : Set (ComplexModel N)) ⊆ e.val.target) :
    (wedgeMeasureOn T β (isCompact_univ : IsCompact (univ : Set M))).restrict
        (chartPatchSource e B) =
      (wedgePowerMeasure (restrict hB (T.inChart e)) (β.coeff e)).map (chartInv e) := by
  let S := chartPatchSource e B
  have hSe : (S : Set M) ⊆ e.val.source := inter_subset_left
  have hchart := wedgeMeasureOn_restrict_source T β (isCompact_univ : IsCompact (univ : Set M)) e
  simp only [univ_inter] at hchart
  have hS : (wedgeMeasureOn T β (isCompact_univ : IsCompact (univ : Set M))).restrict S =
      (chartWedgeMeasure T β e).restrict S := by
    calc
      _ = ((wedgeMeasureOn T β (isCompact_univ : IsCompact (univ : Set M))).restrict
          e.val.source).restrict S := (Measure.restrict_restrict_of_subset hSe).symm
      _ = _ := by rw [hchart, Measure.restrict_restrict_of_subset hSe]
  rw [hS, chartWedgeMeasure, Measure.restrict_map (measurable_chartInv e) S.isOpen.measurableSet,
    Measure.restrict_restrict ((measurable_chartInv e) S.isOpen.measurableSet)]
  have hset : chartInv e ⁻¹' (S : Set M) ∩ (chartDomain e (⊤ : Opens M) : Set (ComplexModel N)) = B := by
    ext z
    constructor
    · rintro ⟨hzS, hzD⟩
      rw [mem_preimage, chartInv_of_mem hzD.1] at hzS
      have hzB : e.val (e.val.symm z) ∈ B := hzS.2
      rwa [e.val.right_inv hzD.1] at hzB
    · intro hz
      have hzt := hB hz
      refine ⟨?_, hzt, mem_univ _⟩
      rw [mem_preimage, chartInv_of_mem hzt]
      refine ⟨e.val.map_target hzt, ?_⟩
      change e.val (e.val.symm z) ∈ B
      rwa [e.val.right_inv hzt]
  rw [hset, ← wedgePowerMeasure_restrict (T.isPositive e) hB]

theorem global_wedgeMeasure_chart_pairing (T : PositiveCurrent N M q)
    (β : SemipositiveFormOn N (⊤ : Opens M)) (e : ComplexChart N M)
    {B : Opens (ComplexModel N)} (hB : (B : Set (ComplexModel N)) ⊆ e.val.target)
    {F : M → ℝ} (hF : Measurable F) (hF0 : ∀ x ∉ chartPatchSource e B, F x = 0) :
    (Integrable F (wedgeMeasureOn T β (isCompact_univ : IsCompact (univ : Set M))) ↔
      Integrable (fun z => F (e.val.symm z))
        (wedgePowerMeasure (restrict hB (T.inChart e)) (β.coeff e))) ∧
    (∫ x, F x ∂wedgeMeasureOn T β (isCompact_univ : IsCompact (univ : Set M))) =
      ∫ z, F (e.val.symm z) ∂wedgePowerMeasure (restrict hB (T.inChart e)) (β.coeff e) := by
  let S := chartPatchSource e B
  let μ := wedgeMeasureOn T β (isCompact_univ : IsCompact (univ : Set M))
  let ν := wedgePowerMeasure (restrict hB (T.inChart e)) (β.coeff e)
  have hmeasure : μ.restrict S = ν.map (chartInv e) :=
    global_wedgeMeasure_restrict_chart_patch T β e hB
  have hind : (S : Set M).indicator F = F := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hF0 x hx]
  have hνB : ν (B : Set (ComplexModel N))ᶜ = 0 := by
    dsimp only [ν]
    rw [wedgePowerMeasure, dif_pos (isPositive_restrict (T.isPositive e) hB)]
    exact withDensity_absolutelyContinuous _ _ (isPositive_restrict (T.isPositive e) hB).traceMeasure_compl
  have hread : (fun z => F (chartInv e z)) =ᵐ[ν] (fun z => F (e.val.symm z)) := by
    filter_upwards [ae_iff.mpr hνB] with z hz
    rw [chartInv_of_mem (hB hz)]
  have hint : Integrable F μ ↔ Integrable F (ν.map (chartInv e)) := by
    rw [← hmeasure]
    change Integrable F μ ↔ IntegrableOn F S μ
    rw [← integrable_indicator_iff S.isOpen.measurableSet, hind]
  refine ⟨?_, ?_⟩
  · rw [hint, integrable_map_measure hF.aestronglyMeasurable (measurable_chartInv e).aemeasurable]
    exact integrable_congr hread
  · calc
      _ = ∫ x in S, F x ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
      _ = ∫ x, F x ∂ν.map (chartInv e) := by rw [hmeasure]
      _ = ∫ z, F (chartInv e z) ∂ν :=
        integral_map (measurable_chartInv e).aemeasurable hF.aestronglyMeasurable
      _ = _ := integral_congr_ae hread

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment002

section CompactFibreCanonicalFragment003

/-! Genuine simultaneous product-chart potentials from the original source
forms. No supplied common potential, chart refinement certificate, or finiteness. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending ProductComplexManifold
open SGPT.NPP.FibreSlicing
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]

def productChart (e : ComplexChart n X) (f : ComplexChart m Z) : ComplexChart (n + m) (X × Z) :=
  ⟨prodChart e.val f.val, mem_image2_of_mem e.2 f.2⟩

omit [IsComplexManifold n X] [IsComplexManifold m Z] in
private theorem product_coordinate_fst (e : ComplexChart n X) (f : ComplexChart m Z)
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    (hQ : (Q : Set (ComplexModel n)) ⊆ e.val.target)
    {q : ComplexModel (n + m)} (hq : q ∈ prodOpens Q D) :
    coordinateMap Prod.fst (productChart e f) e q = ProductMixedMeasure.projFst n m q := by
  change e.val ((prodChart e.val f.val).symm q).1 = _
  rw [prodChart_symm_apply, ← ProductMixedMeasure.projFst_apply]
  exact e.val.right_inv (hQ hq.1)

omit [IsComplexManifold n X] [IsComplexManifold m Z] in
private theorem product_coordinate_snd (e : ComplexChart n X) (f : ComplexChart m Z)
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    (hD : (D : Set (ComplexModel m)) ⊆ f.val.target)
    {q : ComplexModel (n + m)} (hq : q ∈ prodOpens Q D) :
    coordinateMap Prod.snd (productChart e f) f q = ProductMixedMeasure.projSnd n m q := by
  change f.val ((prodChart e.val f.val).symm q).2 = _
  rw [prodChart_symm_apply, ← ProductMixedMeasure.projSnd_apply]
  exact f.val.right_inv (hD hq.2)

theorem isSmoothLocalPotential_product_chart
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {e : ComplexChart n X} {f : ComplexChart m Z}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {a : ComplexModel n → ℝ} {b : ComplexModel m → ℝ}
    (ha : IsSmoothLocalPotential θ.val e Q a) (hb : IsSmoothLocalPotential γ.val f D b) :
    IsSmoothLocalPotential (prodForm θ γ).val (productChart e f) (prodOpens Q D)
      (fun q => a (coordinateMap Prod.fst (productChart e f) e q) +
        b (coordinateMap Prod.snd (productChart e f) f q)) := by
  have hfst := contMDiff_fst (n := n) (m := m) (X := X) (Y := Z)
  have hsnd := contMDiff_snd (n := n) (m := m) (X := X) (Y := Z)
  have htarget {q : ComplexModel (n + m)} (hq : q ∈ prodOpens Q D) :
      q ∈ (productChart e f).val.target := by
    change q ∈ (prodChart e.val f.val).target
    rw [prodChart_target]
    exact ⟨ha.2.1 hq.1, hb.2.1 hq.2⟩
  have hdomfst : (prodOpens Q D : Set (ComplexModel (n + m))) ⊆
      potentialDomain Prod.fst (productChart e f) e Q := by
    intro q hq
    refine ⟨⟨htarget hq, ?_⟩, ?_⟩
    · change ((prodChart e.val f.val).symm q).1 ∈ e.val.source
      rw [prodChart_symm_apply]
      exact e.val.map_target (ha.2.1 hq.1)
    · change coordinateMap Prod.fst (productChart e f) e q ∈ Q
      rw [product_coordinate_fst e f ha.2.1 hq]
      exact hq.1
  have hdomsnd : (prodOpens Q D : Set (ComplexModel (n + m))) ⊆
      potentialDomain Prod.snd (productChart e f) f D := by
    intro q hq
    refine ⟨⟨htarget hq, ?_⟩, ?_⟩
    · change ((prodChart e.val f.val).symm q).2 ∈ f.val.source
      rw [prodChart_symm_apply]
      exact f.val.map_target (hb.2.1 hq.2)
    · change coordinateMap Prod.snd (productChart e f) f q ∈ D
      rw [product_coordinate_snd e f hb.2.1 hq]
      exact hq.2
  exact CompactFibreSlicing.isSmoothLocalPotential_add
    ((isSmoothLocalPotential_pullback hfst (productChart e f) ha).mono (prodOpens Q D).isOpen hdomfst)
    ((isSmoothLocalPotential_pullback hsnd (productChart e f) hb).mono (prodOpens Q D).isOpen hdomsnd)

theorem plurisubharmonicOn_original_product_corrected
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {e : ComplexChart n X} {f : ComplexChart m Z}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {a : ComplexModel n → ℝ} {b : ComplexModel m → ℝ}
    (ha : IsSmoothLocalPotential θ.val e Q a) (hb : IsSmoothLocalPotential γ.val f D b)
    {V : X × Z → EReal} (hV : IsThetaPshPotential (prodForm θ γ).val V) :
    PlurisubharmonicOn (fun q => V ((productChart e f).val.symm q) +
      ((a (ProductMixedMeasure.projFst n m q) + b (ProductMixedMeasure.projSnd n m q) : ℝ) : EReal))
      (prodOpens Q D) := by
  have hpsh := ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
    hV.1 (productChart e f) (isSmoothLocalPotential_product_chart ha hb)
  intro q hq
  refine (hpsh q hq).congr ?_
  filter_upwards [(prodOpens Q D).isOpen.mem_nhds hq] with y hy
  simp only [chartFunction, product_coordinate_fst e f ha.2.1 hy,
    product_coordinate_snd e f hb.2.1 hy]

theorem exists_original_common_product_chart (θ : ClosedRealOneOneForm n X)
    (γ : ClosedRealOneOneForm m Z) (x : X) (z : Z) :
    ∃ (e : ComplexChart n X) (f : ComplexChart m Z)
      (Q : Opens (ComplexModel n)) (D : Opens (ComplexModel m))
      (a : ComplexModel n → ℝ) (b : ComplexModel m → ℝ),
      x ∈ e.val.source ∧ z ∈ f.val.source ∧ e.val x ∈ Q ∧ f.val z ∈ D ∧
      IsSmoothLocalPotential θ.val e Q a ∧ IsSmoothLocalPotential γ.val f D b ∧
      ∀ V : X × Z → EReal, IsThetaPshPotential (prodForm θ γ).val V →
        PlurisubharmonicOn (fun q => V ((productChart e f).val.symm q) +
          ((a (ProductMixedMeasure.projFst n m q) + b (ProductMixedMeasure.projSnd n m q) : ℝ) : EReal))
          (prodOpens Q D) := by
  let e := complexChartAt (n := n) x
  let f := complexChartAt (n := m) z
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ f.val.source := mem_complexChartAt_source z
  obtain ⟨Qa, a, hxa, ha⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x)
    (e.val.map_source hx)
  obtain ⟨Db, b, hzb, hb⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials γ f (f.val z)
    (f.val.map_source hz)
  refine ⟨e, f, ⟨Qa, ha.1⟩, ⟨Db, hb.1⟩, a, b, hx, hz, hxa, hzb, ha, hb, ?_⟩
  exact fun V hV => plurisubharmonicOn_original_product_corrected ha hb hV

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment003

section CompactFibreCanonicalFragment004

/-! The original closed forms internally produce genuine finite product-chart
partitions and actual coordinate test functions, in all dimensions including zero. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalSlotStokes
open FiniteGeodesicStripCharts
open SGPT.NPP.FibreSlicing
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]

structure OriginalProductPotentialChart (θ : ClosedRealOneOneForm n X)
    (γ : ClosedRealOneOneForm m Z) where
  first : ComplexChart n X
  second : ComplexChart m Z
  Q : Opens (ComplexModel n)
  D : Opens (ComplexModel m)
  a : ComplexModel n → ℝ
  b : ComplexModel m → ℝ
  firstPotential : IsSmoothLocalPotential θ.val first Q a
  secondPotential : IsSmoothLocalPotential γ.val second D b

namespace OriginalProductPotentialChart

variable {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}

def chart (J : OriginalProductPotentialChart θ γ) : ComplexChart (n + m) (X × Z) :=
  productChart J.first J.second

def domain (J : OriginalProductPotentialChart θ γ) : Opens (ComplexModel (n + m)) :=
  prodOpens J.Q J.D

def source (J : OriginalProductPotentialChart θ γ) : Opens (X × Z) :=
  ⟨(J.first.val.source ∩ J.first.val ⁻¹' J.Q) ×ˢ
      (J.second.val.source ∩ J.second.val ⁻¹' J.D),
    (J.first.val.isOpen_inter_preimage J.Q.isOpen).prod
      (J.second.val.isOpen_inter_preimage J.D.isOpen)⟩

theorem source_subset (J : OriginalProductPotentialChart θ γ) :
    (J.source : Set (X × Z)) ⊆ J.chart.val.source := by
  intro p hp
  change p ∈ (prodChart J.first.val J.second.val).source
  rw [prodChart_source]
  exact ⟨hp.1.1, hp.2.1⟩

theorem domain_le_target (J : OriginalProductPotentialChart θ γ) :
    (J.domain : Set (ComplexModel (n + m))) ⊆ J.chart.val.target := by
  intro q hq
  change q ∈ (prodChart J.first.val J.second.val).target
  rw [prodChart_target]
  exact ⟨J.firstPotential.2.1 hq.1, J.secondPotential.2.1 hq.2⟩

theorem map_source (J : OriginalProductPotentialChart θ γ) {p : X × Z} (hp : p ∈ J.source) :
    J.chart.val p ∈ J.domain := by
  change prodModelEquiv n m (J.first.val p.1, J.second.val p.2) ∈ prodOpens J.Q J.D
  constructor
  · change ProductMixedMeasure.projFst n m (prodModelEquiv n m (J.first.val p.1, J.second.val p.2)) ∈ J.Q
    change ProductMixedMeasure.projFst n m (prodModelEquiv n m (J.first.val p.1, J.second.val p.2)) ∈ (J.Q : Set (ComplexModel n))
    rw [ProductMixedMeasure.projFst_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact hp.1.2
  · change ProductMixedMeasure.projSnd n m (prodModelEquiv n m (J.first.val p.1, J.second.val p.2)) ∈ J.D
    change ProductMixedMeasure.projSnd n m (prodModelEquiv n m (J.first.val p.1, J.second.val p.2)) ∈ (J.D : Set (ComplexModel m))
    rw [ProductMixedMeasure.projSnd_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact hp.2.2

theorem map_target (J : OriginalProductPotentialChart θ γ)
    {q : ComplexModel (n + m)} (hq : q ∈ J.domain) : J.chart.val.symm q ∈ J.source := by
  change (prodChart J.first.val J.second.val).symm q ∈ J.source
  rw [prodChart_symm_apply]
  refine ⟨⟨J.first.val.map_target (J.firstPotential.2.1 hq.1), ?_⟩,
    ⟨J.second.val.map_target (J.secondPotential.2.1 hq.2), ?_⟩⟩
  · change J.first.val (J.first.val.symm (ProductMixedMeasure.projFst n m q)) ∈ J.Q
    rw [J.first.val.right_inv (J.firstPotential.2.1 hq.1)]
    exact hq.1
  · change J.second.val (J.second.val.symm (ProductMixedMeasure.projSnd n m q)) ∈ J.D
    rw [J.second.val.right_inv (J.secondPotential.2.1 hq.2)]
    exact hq.2

end OriginalProductPotentialChart

theorem exists_finite_original_product_partition [CompactSpace X] [CompactSpace Z]
    (θ : ClosedRealOneOneForm n X) (γ : ClosedRealOneOneForm m Z) :
    ∃ (r : ℕ) (χ : Fin r → X × Z → ℝ) (J : Fin r → OriginalProductPotentialChart θ γ),
      (∀ a, ChartSmooth (n := n + m) (χ a)) ∧ (∀ a p, 0 ≤ χ a p) ∧
      (∀ a, tsupport (χ a) ⊆ ((J a).source : Set (X × Z))) ∧
      (∀ a, IsCompact (tsupport (χ a))) ∧ ∀ p, ∑ a, χ a p = 1 := by
  apply ChartPartition.exists_chartSmooth_partitionOfUnity
    (fun J : OriginalProductPotentialChart θ γ => J.source)
  intro p
  obtain ⟨e, f, Q, D, a, b, hx, hz, hxQ, hzD, ha, hb, -⟩ :=
    exists_original_common_product_chart θ γ p.1 p.2
  exact ⟨⟨e, f, Q, D, a, b, ha, hb⟩, ⟨⟨hx, hxQ⟩, ⟨hz, hzD⟩⟩⟩

def productChartTest {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z))) : 𝓓(J.domain, ℝ) where
  toFun := chartRead J.chart χ
  contDiff' := contDiff_chartRead hχ hχc (hχJ.trans J.source_subset)
  hasCompactSupport' := hasCompactSupport_chartRead hχc (hχJ.trans J.source_subset)
  tsupport_subset' := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := tsupport_chartRead_subset hχc (hχJ.trans J.source_subset) hq
    exact J.map_source (hχJ hp)

theorem productChartTest_nonneg {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z))) (hχ0 : ∀ p, 0 ≤ χ p)
    (q : ComplexModel (n + m)) : 0 ≤ productChartTest J hχ hχc hχJ q := by
  change 0 ≤ chartRead J.chart χ q
  by_cases hq : q ∈ J.chart.val.target
  · rw [chartRead_of_mem hq]
    exact hχ0 _
  · rw [chartRead_of_notMem hq]

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment004

section CompactFibreCanonicalFragment010

/-! Full actual base tensors and the existing global smooth-wedge interface.
The auxiliary Kahler form is a reader of the original current, not a
replacement for the original possibly degenerate gamma. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ProductComplexManifold StronglyPositiveForms
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]

theorem original_pullbackSnd_coeff {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (J : OriginalProductPotentialChart θ γ) {k : ℕ} (η : SmoothRealForm m Z k)
    {q : ComplexModel (n + m)} (hq : q ∈ J.domain) :
    (SmoothRealForm.pullback (contMDiff_snd (n := n) (m := m) (X := X) (Y := Z)) η).coeff J.chart q =
      (η.coeff J.second (ProductMixedMeasure.projSnd n m q)).compContinuousLinearMap
        (ProductMixedMeasure.projSnd n m) := by
  have hcoordDomain : q ∈ coordinateDomain Prod.snd J.chart J.second :=
    ⟨J.domain_le_target hq, (J.map_target hq).2.1⟩
  have hcoord : coordinateMap Prod.snd J.chart J.second =ᶠ[𝓝 q] ProductMixedMeasure.projSnd n m := by
    filter_upwards [J.domain.isOpen.mem_nhds hq] with y hy
    change J.second.val ((prodChart J.first.val J.second.val).symm y).2 = _
    rw [prodChart_symm_apply, ← ProductMixedMeasure.projSnd_apply]
    exact J.second.val.right_inv (J.secondPotential.2.1 hy.2)
  rw [SmoothRealForm.pullback_coeff contMDiff_snd η J.chart J.second hcoordDomain,
    hcoord.eq_of_nhds, hcoord.fderiv_eq, (ProductMixedMeasure.projSnd n m).fderiv]

def semipositiveFormOn_closed {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M]
    (β : ClosedRealOneOneForm N M) (hβ : β.val.IsSemipositive) :
    SemipositiveFormOn N (⊤ : Opens M) where
  coeff := β.val.coeff
  smooth e := (β.val.smooth e).mono (fun _ hz => hz.1)
  semipositive e z hz := ⟨β.property.2 e z hz.1, hβ e z hz.1⟩
  compatible _e _f _z _ hz := IntegrationCurrent.coeff_eq_compContinuousLinearMap β.val hz

def originalBaseWedgeForm (omega : KahlerBackground m Z) :
    SemipositiveFormOn (n + m) (⊤ : Opens (X × Z)) :=
  semipositiveFormOn_closed
    (ClosedRealOneOneForm.pullback (contMDiff_snd (n := n) (m := m) (X := X) (Y := Z)) omega.form)
    (ClosedRealOneOneForm.pullback_isSemipositive contMDiff_snd omega.isSemipositive)

theorem originalBaseWedgeForm_coeff {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (omega : KahlerBackground m Z) (J : OriginalProductPotentialChart θ γ)
    {q : ComplexModel (n + m)} (hq : q ∈ J.domain) :
    (originalBaseWedgeForm (X := X) omega).coeff J.chart q =
      baseTwoFormPullback (omega.form.val.coeff J.second) q :=
  original_pullbackSnd_coeff J omega.form.val hq

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment010

section CompactFibreCanonicalFragment013

/-! The SAME actual original fibre measure, internally identified by removing
the finite original base potential and by genuine global patch uniqueness. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending ProductComplexManifold MixedNonPluripolar GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.NPP.FibreSlicing
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]

def originalProductCorrectedTuple (e : ComplexChart n X) (f : ComplexChart m Z)
    (a : ComplexModel n → ℝ) (b : ComplexModel m → ℝ) (V : Fin n → X × Z → EReal) :
    Fin n → ComplexModel (n + m) → EReal := fun i q =>
  V i ((productChart e f).val.symm q) +
    ((a (ProductMixedMeasure.projFst n m q) + b (ProductMixedMeasure.projSnd n m q) : ℝ) : EReal)

def originalFibrePatch {θ : ClosedRealOneOneForm n X} {e : ComplexChart n X}
    {Q : Opens (ComplexModel n)} {a : ComplexModel n → ℝ}
    (ha : IsSmoothLocalPotential θ.val e Q a) (v : Fin n → X → EReal)
    (hv : ∀ i, ThetaPlurisubharmonic θ.val (v i)) : Patch (fun _ => θ) v where
  chart := e
  domain := Q
  domain_le_target := ha.2.1
  potential := fun _ => a
  localPotential := fun _ => ha
  plurisubharmonic i :=
    ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic (hv i) e ha

theorem original_fibre_npLimit_eq_original_patch
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {e : ComplexChart n X} {f : ComplexChart m Z}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {a : ComplexModel n → ℝ} {b : ComplexModel m → ℝ}
    (ha : IsSmoothLocalPotential θ.val e Q a) (hb : IsSmoothLocalPotential γ.val f D b)
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    {z : ComplexModel m} (hz : z ∈ D)
    (hv : ∀ i, ThetaPlurisubharmonic θ.val (fun x => V i (x, f.val.symm z))) :
    mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
        (originalFibrePotentialsM (originalProductCorrectedTuple e f a b V) z)
        (plurisubharmonicOn_originalFibrePotentialsM
          (fun i => plurisubharmonicOn_original_product_corrected ha hb (hV i)) z) =
      mixedTruncationLimitMeasure Q (originalFibrePatch ha (fun i x => V i (x, f.val.symm z)) hv).corrected
        (originalFibrePatch ha (fun i x => V i (x, f.val.symm z)) hv).plurisubharmonic := by
  let P := originalFibrePatch ha (fun i x => V i (x, f.val.symm z)) hv
  let U := originalProductCorrectedTuple e f a b V
  have hU (i : Fin n) : PlurisubharmonicOn (U i) (prodOpens Q D) :=
    plurisubharmonicOn_original_product_corrected ha hb (hV i)
  have hdom : fibreOpensM (prodOpens Q D) z = Q := fibreOpensM_prodOpens hz
  have hf (i : Fin n) : PlurisubharmonicOn (originalFibrePotentialsM U z i) Q := by
    rw [← hdom]
    exact plurisubharmonicOn_originalFibrePotentialsM hU z i
  have heq (i : Fin n) : EqOn (originalFibrePotentialsM U z i)
      (fun x => P.corrected i x + (b z : EReal)) Q := by
    intro x _
    simp only [originalFibrePotentialsM, U, originalProductCorrectedTuple, productChart,
      prodChart_symm_apply, fibreMapM, ContinuousLinearEquiv.symm_apply_apply,
      ProductMixedMeasure.projFst_apply, ProductMixedMeasure.projSnd_apply,
      P, originalFibrePatch, Patch.corrected, chartFunction, EReal.coe_add, add_assoc]
  have hpc (i : Fin n) : PlurisubharmonicOn (fun x => P.corrected i x + (b z : EReal)) Q := by
    intro x hx
    refine (hf i x hx).congr ?_
    filter_upwards [Q.isOpen.mem_nhds hx] with y hy
    exact heq i hy
  have hg := mixedTruncationLimitMeasure_add_pluriharmonic P.plurisubharmonic
    (fun _ => (show IsSmoothPluriharmonicOn Q (fun _ => b z) from
      ⟨contDiffOn_const, fun y _ => complexHessian_const (b z) y⟩)) hpc
  have hm := mixedTruncationLimitMeasure_congr hf hpc heq
  have hgQ : mixedTruncationLimitMeasure Q (fun i x => P.corrected i x + (b z : EReal)) hpc =
      mixedTruncationLimitMeasure Q P.corrected P.plurisubharmonic := hg
  rw [hgQ] at hm
  have hchange {A B : Opens (ComplexModel n)} (hab : A = B)
      (w : Fin n → ComplexModel n → EReal)
      (hA : ∀ i, PlurisubharmonicOn (w i) A) (hB : ∀ i, PlurisubharmonicOn (w i) B) :
      mixedTruncationLimitMeasure A w hA = mixedTruncationLimitMeasure B w hB := by
    cases hab
    rfl
  exact (hchange hdom _ _ hf).trans hm

theorem original_fibre_npLimit_push_eq_original_global_restrict
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {e : ComplexChart n X} {f : ComplexChart m Z}
    {Q : Opens (ComplexModel n)} {D : Opens (ComplexModel m)}
    {a : ComplexModel n → ℝ} {b : ComplexModel m → ℝ}
    (ha : IsSmoothLocalPotential θ.val e Q a) (hb : IsSmoothLocalPotential γ.val f D b)
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    {z : ComplexModel m} (hz : z ∈ D)
    (hv : ∀ i, ThetaPlurisubharmonic θ.val (fun x => V i (x, f.val.symm z))) :
    (originalFibrePatch ha (fun i x => V i (x, f.val.symm z)) hv).pushMeasure
      (mixedTruncationLimitMeasure (fibreOpensM (prodOpens Q D) z)
        (originalFibrePotentialsM (originalProductCorrectedTuple e f a b V) z)
        (plurisubharmonicOn_originalFibrePotentialsM
          (fun i => plurisubharmonicOn_original_product_corrected ha hb (hV i)) z)) =
      (globalMixedMeasure (fun _ => θ) (fun i x => V i (x, f.val.symm z)) hv).restrict
        (originalFibrePatch ha (fun i x => V i (x, f.val.symm z)) hv).source := by
  rw [original_fibre_npLimit_eq_original_patch ha hb hV hz hv,
    globalMixedMeasure_restrict_patch hv]
  rfl

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment013

section CompactFibreCanonicalFragment016

/-! Actual original base volume integration for EVERY real fibre function.
Output measurability/integrability is not supplied: genuine inverse-chart
embeddings transport the produced local integral and integrability. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent DiagonalMass SmoothMixedMeasureDensity
open ProductTestForms StronglyPositiveForms TopDegreeDensity

variable {N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M]
  [MeasurableSpace M] [BorelSpace M]

private def chartTargetInv (e : ComplexChart N M) : e.val.target → M :=
  fun z => ((e.val.toHomeomorphSourceTarget).symm z : M)

omit [IsComplexManifold N M] in
private theorem measurableEmbedding_chartTargetInv (e : ComplexChart N M) :
    MeasurableEmbedding (chartTargetInv e) :=
  (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
    (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding

omit [IsComplexManifold N M] in
private theorem inverse_chart_pairing (e : ComplexChart N M)
    (ν : Measure (ComplexModel N)) (hν : ν e.val.targetᶜ = 0) (F : M → ℝ) :
    (Integrable F (ν.map (chartInv e)) ↔ Integrable (fun z => F (e.val.symm z)) ν) ∧
    (∫ x, F x ∂ν.map (chartInv e)) = ∫ z, F (e.val.symm z) ∂ν := by
  let sub := (Subtype.val : e.val.target → ComplexModel N)
  have hsub : MeasurableEmbedding sub :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  have hfun : chartTargetInv e = chartInv e ∘ sub := by
    funext z
    exact (chartInv_of_mem z.property).symm
  have hmap : (ν.comap sub).map (chartTargetInv e) = ν.map (chartInv e) := by
    rw [hfun, ← Measure.map_map (measurable_chartInv e) hsub.measurable,
      map_comap_subtype_coe e.val.open_target.measurableSet,
      Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)]
  have hint := integrableOn_iff_comap_subtypeVal (μ := ν) e.val.open_target.measurableSet
    (f := fun z => F (e.val.symm z))
  change Integrable (fun z => F (e.val.symm z)) (ν.restrict e.val.target) ↔
    Integrable (fun z : e.val.target => F (e.val.symm z)) (ν.comap sub) at hint
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)] at hint
  refine ⟨?_, ?_⟩
  · rw [← hmap, (measurableEmbedding_chartTargetInv e).integrable_map_iff]
    exact hint.symm
  · rw [← hmap, (measurableEmbedding_chartTargetInv e).integral_map]
    exact (integral_subtype_comap e.val.open_target.measurableSet
      (fun z => F (e.val.symm z))).trans (by
        rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)])

theorem kahlerVolume_chart_pairing [CompactSpace M]
    (omega : KahlerBackground N M) (e : ComplexChart N M) (F : M → ℝ)
    (hF0 : ∀ x ∉ e.val.source, F x = 0) :
    (Integrable F (kahlerVolume omega) ↔
      IntegrableOn (fun z => topDensity ((formPow omega.form.val N).coeff e z) * F (e.val.symm z))
        e.val.target volume) ∧
    (∫ x, F x ∂kahlerVolume omega) =
      ∫ z in e.val.target, topDensity ((formPow omega.form.val N).coeff e z) * F (e.val.symm z) := by
  let ρ := fun z => topDensity ((formPow omega.form.val N).coeff e z)
  let ν := (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z))
  have hρ : ContDiffOn ℝ ∞ ρ e.val.target :=
    (ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ (topBasis N)).contDiff.comp_contDiffOn
      ((formPow omega.form.val N).smooth e)
  have hρae : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict e.val.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ.continuousOn).aemeasurable e.val.open_target.measurableSet
  have hρfin : ∀ᵐ z ∂volume.restrict e.val.target, ENNReal.ofReal (ρ z) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hρreal : (fun z => (ENNReal.ofReal (ρ z)).toReal) =ᵐ[volume.restrict e.val.target] ρ := by
    filter_upwards [ae_restrict_mem e.val.open_target.measurableSet] with z hz
    exact ENNReal.toReal_ofReal (topDensity_formPow_pos omega.isKahler.1 hz).le
  have hdensity : chartDensity (fun _ => omega.form) e = fun z => ENNReal.ofReal (ρ z) := by
    funext z
    simp only [chartDensity, ρ, formPow_coeff, formPower_eq_wedgeProd, topDensity_wedgeProd]
  have h0 : IsThetaPshPotential omega.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact e.val.map_target hz
    · intro hx
      exact ⟨e.val x, e.val.map_source hx, e.val.left_inv hx⟩
  have hν : ν e.val.targetᶜ = 0 := by
    dsimp only [ν]
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply e.val.open_target.measurableSet.compl, compl_inter_self, measure_empty]
  have hνmap : (kahlerVolume omega).restrict e.val.source = ν.map (chartInv e) := by
    have hread : (kahlerVolume omega).restrict e.val.source = ν.map e.val.symm := by
      rw [← himage, kahlerVolume, diagonalPotentialMeasure]
      simpa only [hdensity] using restrict_image_eq_map (fun _ => h0.1) e
        e.val.open_target.measurableSet (Subset.refl _)
    refine hread.trans (Measure.map_congr ?_)
    filter_upwards [ae_iff.mpr hν] with z hz
    exact (chartInv_of_mem hz).symm
  have hinverse := inverse_chart_pairing e ν hν F
  have hind : e.val.source.indicator F = F := by
    funext x
    by_cases hx : x ∈ e.val.source
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hF0 x hx]
  have hreduce : Integrable F (kahlerVolume omega) ↔ Integrable F (ν.map (chartInv e)) := by
    rw [← hνmap]
    change Integrable F (kahlerVolume omega) ↔ IntegrableOn F e.val.source (kahlerVolume omega)
    rw [← integrable_indicator_iff e.val.open_source.measurableSet, hind]
  have hweight : (fun z => (ENNReal.ofReal (ρ z)).toReal • F (e.val.symm z)) =ᵐ[volume.restrict e.val.target]
      (fun z => ρ z * F (e.val.symm z)) := hρreal.mono (fun z hz => by
        simpa only [smul_eq_mul] using congrArg (fun r : ℝ => r * F (e.val.symm z)) hz)
  refine ⟨?_, ?_⟩
  · rw [hreduce, hinverse.1]
    exact (integrable_withDensity_iff_integrable_smul₀' hρae hρfin).trans (integrable_congr hweight)
  · calc
      _ = ∫ x in e.val.source, F x ∂kahlerVolume omega :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
      _ = ∫ x, F x ∂ν.map (chartInv e) := by rw [hνmap]
      _ = ∫ z, F (e.val.symm z) ∂ν := hinverse.2
      _ = ∫ z in e.val.target, (ENNReal.ofReal (ρ z)).toReal • F (e.val.symm z) :=
        integral_withDensity_eq_integral_toReal_smul₀ hρae hρfin _
      _ = _ := integral_congr_ae hweight

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment016

section CompactFibreCanonicalFragment025

/-! Actual full-tensor signed top-form dictionary. The auxiliary Kahler form
comes from source geometry; the original possibly degenerate gamma is untouched. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent TopDegreeDensity PositiveProductCurrents StronglyPositiveForms
open ProductTestForms NaturalHermitianHodgeStar

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-- Actual equality of the ENTIRE original top form, in every original chart;
no density-only substitute and no positive-dimensional condition. -/
theorem smooth_top_form_coeff_eq_topRatio_smul (omega : KahlerBackground m Z)
    (η : SmoothRealForm m Z (2 * m)) (e : ComplexChart m Z)
    (z : ComplexModel m) (hz : z ∈ e.val.target) :
    η.coeff e z = topRatio omega.form.val η (e.val.symm z) •
      (formPow omega.form.val m).coeff e z := by
  apply topDensity_injective
  rw [topDensity_smul, topRatio_eq_chartRatio omega.isKahler.1 η (e.val.symm.map_source hz),
    e.val.right_inv hz, chartRatio]
  exact (div_mul_cancel₀ _ (topDensity_formPow_pos omega.isKahler.1 hz).ne').symm

/-- Every original SIGNED smooth real top form is internally the difference
of TWO actual smooth positive top forms, including base dimension zero. -/
theorem exists_smooth_positive_top_form_difference [CompactSpace Z]
    (omega : KahlerBackground m Z) (η : SmoothRealForm m Z (2 * m)) :
    ∃ ηp ηm : SmoothRealForm m Z (2 * m), η = ηp - ηm ∧
      (∀ e : ComplexChart m Z, ∀ z ∈ e.val.target, ηp.coeff e z ∈ spCone m) ∧
      (∀ e : ComplexChart m Z, ∀ z ∈ e.val.target, ηm.coeff e z ∈ spCone m) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_topRatio omega.isKahler.1 η).continuousOn
  let A : ℝ := max B 0
  let ηp := η + A • formPow omega.form.val m
  let ηm := A • formPow omega.form.val m
  refine ⟨ηp, ηm, ?_, ?_, ?_⟩
  · simp only [ηp, ηm, add_sub_cancel_right]
  · intro e z hz
    have hg := hB (e.val.symm z) (mem_univ _)
    rw [Real.norm_eq_abs] at hg
    have hA : 0 ≤ topRatio omega.form.val η (e.val.symm z) + A := by
      have hb := (abs_le.mp hg).1
      have hBA : B ≤ A := le_max_left _ _
      linarith
    dsimp only [ηp]
    rw [coeff_add, coeff_smul, smooth_top_form_coeff_eq_topRatio_smul omega η e z hz, ← add_smul,
      formPow_coeff]
    exact smul_mem_spCone (formPower_mem_spCone ⟨(omega.isKahler.1 e z hz).1, omega.isSemipositive e z hz⟩ m) hA
  · intro e z hz
    dsimp only [ηm]
    rw [coeff_smul, formPow_coeff]
    exact smul_mem_spCone (formPower_mem_spCone ⟨(omega.isKahler.1 e z hz).1, omega.isSemipositive e z hz⟩ m) (le_max_right B 0)

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment025

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.mainModule == `SGPT.NPP.CompactFibreGeometry do throwError "Wrong proper module identity: {env.mainModule}"
  let forbidden : Array Name := #[`OriginalCurrentProductDictionaryDraft, `AllDimensionCurrentProductDraft, `GlobalWedgeChartDictionaryDraft, `OriginalProductPotentialsDraft, `OriginalProductPartitionDraft, `PositiveCoefficientMeasureDraft, `FibreTruncationDictionaryDraft, `FibreTruncationMeasureDraft, `CurrentBasePowerMeasureDraft, `SmoothBaseWedgeMeasureDraft, `OriginalBaseFormDictionaryDraft, `PositiveFibreMRegularizationDraft, `NonPluripolarFibreMPositiveDraft, `FibreOriginalMeasureDictionaryDraft, `OriginalGlobalCurrentMeasureDraft, `OriginalFibreIntegralDraft, `BaseVolumeBorelDictionaryDraft, `OriginalOuterFibreIntegralDraft, `RealNonPluripolarFibreDraft, `SignedMultiplierFibreDraft, `LocalSignedCurrentDictionaryDraft, `OriginalLocalCurrentFubiniDraft, `OriginalWedgeMeasureFubiniDraft, `OriginalPartitionTermDraft, `OriginalCompactFubiniDraft, `SignedTopFormDictionaryDraft, `OriginalSignedCurrentDictionaryDraft, `OriginalSignedFubiniDraft, `OriginalCompactSlicingSourceDraft, `LiteralCompactSlicingContractDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m then throwError "Historical flat private provider leaked: {m}"
  logInfo m!"CANONICAL_COMPACT_FIBRE_PAYLOAD module={env.mainModule} proper_root=true old_flat_modules=0"
