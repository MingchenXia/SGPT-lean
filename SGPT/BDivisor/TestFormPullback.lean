import SGPT.Foundations.Analysis.Pending.NaturalSupportedChartTensorPullback
import SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension

/-!
# Pull-back of chart test forms along holomorphic maps

Let `g : Z → Y` be a holomorphic map between complex manifolds of the same dimension `n`, let
`f` be a chart of `Z`, `e` a chart of `Y` and `χ` a smooth cut-off on `Z` with compact support in
the source of `f`. For a test form `η` on the target of `e`, the form `χ · g^*(η extended by
zero)` read in the chart `f` is the test form

`z ↦ χ(f⁻¹ z) · η(G z) ∘ (D G_z)^{⊗q}`, `G = e ∘ g ∘ f⁻¹`,

on the coordinate domain of `G`, extended by zero. This file proves that this operation is a
continuous linear map between the LF spaces of test forms (Xia, *Foundations of pluripotential
theory*, `prop:proper-current-pushforward`, the chain-rule estimate in its proof). It is the
analytic input of the push-forward of currents (`SGPT.BDivisor.CurrentPushforward`).

Main declarations:

* `SGPT.BDivisor.TestFormPullback.weightedCompCLM` — on `𝓓_K`, the weighted composition
  `A ↦ 1_S · P(z) (A (F z))` is continuous for every smooth `F` and smooth operator field `P` on
  an open `S`, provided the output vanishes off a fixed compact `L ⊆ S` (Faà di Bruno and Leibniz
  bounds);
* `SGPT.BDivisor.TestFormPullback.pullTestCLM` — the cut-off pull-back of chart test forms
  along `g`, as a continuous linear map `TestForm (chartTarget e) q → TestForm (chartTarget f) q`;
* `SGPT.BDivisor.TestFormPullback.pullTestCLM_apply_eq` — its value is the chart coefficient of
  `χ · g^*(testExtension e η)`, the pull-back of the zero extension of `η` (no off-chart term).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.BDivisor.TestFormPullback

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.Pending.NaturalSupportedChartFormExtension
  SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension

section Model

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A function smooth on an open set has uniformly bounded jets of order `≤ m` on every compact
subset. -/
theorem exists_jet_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} (hS : IsOpen S) {L : Set E} (hL : IsCompact L) (hLS : L ⊆ S)
    {g : E → G} (hg : ContDiffOn ℝ ∞ g S) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ m, ∀ x ∈ L, ‖iteratedFDeriv ℝ i g x‖ ≤ B := by
  have hc : ContinuousOn (fun x => (Finset.range (m + 1)).sup'
      Finset.nonempty_range_add_one (fun i => ‖iteratedFDerivWithin ℝ i g S x‖)) S :=
    ContinuousOn.finset_sup'_apply Finset.nonempty_range_add_one fun i _ =>
      (hg.continuousOn_iteratedFDerivWithin
        (by exact WithTop.coe_le_coe.mpr le_top) hS.uniqueDiffOn).norm
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (hc.mono hLS)
  refine ⟨|B|, abs_nonneg B, fun i hi x hx => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen i hS (hLS hx)]
  exact (Finset.le_sup' _ (Finset.mem_range_succ_iff.mpr hi)).trans
    ((Real.le_norm_self _).trans ((hB x hx).trans (Real.le_norm_self B)))

omit [NormedSpace ℝ E] in
/-- The weighted composition `z ↦ P z (A (F z))` on `S`, extended by zero. -/
def weightedComp (S : Set E) (F : E → E) (P : E → V →L[ℝ] W) (A : E → V) : E → W :=
  S.indicator fun z => P z (A (F z))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weightedComp_of_mem {S : Set E} {F : E → E} {P : E → V →L[ℝ] W} {A : E → V}
    {z : E} (hz : z ∈ S) : weightedComp S F P A z = P z (A (F z)) :=
  indicator_of_mem hz _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weightedComp_of_notMem {S : Set E} {F : E → E} {P : E → V →L[ℝ] W} {A : E → V}
    {z : E} (hz : z ∉ S) : weightedComp S F P A z = 0 :=
  indicator_of_notMem hz _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The weighted composition vanishes off `L` when every point of `S \ L` has a vanishing weight
or is mapped outside the support `K` of the input. -/
theorem weightedComp_eq_zero {S : Set E} {F : E → E} {P : E → V →L[ℝ] W}
    {K : Set E} {L : Set E}
    (hvan : ∀ z ∈ S, z ∉ L → P z = 0 ∨ F z ∉ K) {A : E → V} (hA : ∀ y ∉ K, A y = 0)
    {z : E} (hz : z ∉ L) : weightedComp S F P A z = 0 := by
  by_cases hs : z ∈ S
  · rw [weightedComp_of_mem hs]
    rcases hvan z hs hz with h | h
    · rw [h]
      rfl
    · rw [hA _ h, map_zero]
  · exact weightedComp_of_notMem hs

theorem contDiff_weightedComp {S : Set E} (hS : IsOpen S) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F S) {P : E → V →L[ℝ] W} (hP : ContDiffOn ℝ ∞ P S)
    {K : Set E} {L : Set E} (hL : IsClosed L) (hLS : L ⊆ S)
    (hvan : ∀ z ∈ S, z ∉ L → P z = 0 ∨ F z ∉ K) {A : E → V} (hAs : ContDiff ℝ ∞ A)
    (hA : ∀ y ∉ K, A y = 0) : ContDiff ℝ ∞ (weightedComp S F P A) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ S
  · have hev : weightedComp S F P A =ᶠ[𝓝 x] fun z => P z (A (F z)) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact weightedComp_of_mem hz
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (hP.contDiffAt (hS.mem_nhds hx)).clm_apply
      (hAs.contDiffAt.comp x (hF.contDiffAt (hS.mem_nhds hx)))
  · have hxL : x ∉ L := fun h => hx (hLS h)
    have hev : weightedComp S F P A =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hL.isOpen_compl.mem_nhds hxL] with z hz
      exact weightedComp_eq_zero hvan hA hz
    exact contDiffAt_const.congr_of_eventuallyEq hev

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem supportedIn_eq_zero {K : Compacts E} (A : 𝓓_{K}(E, V)) {y : E}
    (hy : y ∉ (K : Set E)) : A y = 0 :=
  A.zero_on_compl hy

/-- **Continuity of weighted composition** on the Fréchet spaces `𝓓_K`: for `F` and the operator
field `P` smooth on an open `S`, and a compact `L ⊆ S` off which the output vanishes, the map
`A ↦ 1_S · P(z)(A(F z))` is a continuous linear map `𝓓_K(E, V) → 𝓓_L(E, W)`. Every derivative
seminorm of the output is bounded by finitely many seminorms of the input (Leibniz rule for
`P` and Faà di Bruno's formula for `A ∘ F`). -/
def weightedCompCLM {S : Set E} (hS : IsOpen S) {F : E → E} (hF : ContDiffOn ℝ ∞ F S)
    {P : E → V →L[ℝ] W} (hP : ContDiffOn ℝ ∞ P S) (K : Compacts E) (L : Compacts E)
    (hLS : (L : Set E) ⊆ S)
    (hvan : ∀ z ∈ S, z ∉ (L : Set E) → P z = 0 ∨ F z ∉ (K : Set E)) :
    𝓓_{K}(E, V) →L[ℝ] 𝓓_{L}(E, W) := by
  refine ContDiffMapSupportedIn.mkCLM ℝ (fun A => weightedComp S F P A)
    (fun A A' x => ?_) (fun c A x => ?_)
    (fun A => contDiff_weightedComp hS hF hP L.isCompact.isClosed hLS hvan A.contDiff
      (fun y hy => supportedIn_eq_zero A hy))
    (fun A x hx => by
      have h := weightedComp_eq_zero hvan (fun y hy => supportedIn_eq_zero A hy) hx
      simpa using h)
    (fun m _ => ?_)
  · by_cases hx : x ∈ S <;> simp [weightedComp, hx, map_add]
  · by_cases hx : x ∈ S <;> simp [weightedComp, hx, map_smul]
  · obtain ⟨B, hB, hb⟩ := exists_jet_bound hS L.isCompact hLS hP m
    obtain ⟨D₀, _, hd⟩ := exists_jet_bound hS L.isCompact hLS hF m
    let D := max D₀ 1
    have hD1 : 1 ≤ D := le_max_right _ _
    let C : ℝ := ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * B * ((m - i).factorial * D ^ (m - i))
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => by positivity
    refine ⟨Finset.Iic m, C, hC, fun A x hx => ?_⟩
    let N := ((Finset.Iic m).sup fun j =>
      ContDiffMapSupportedIn.seminorm ℝ E V ⊤ K j) A
    have hcomp : ContDiffOn ℝ ∞ (fun z => A (F z)) S :=
      A.contDiff.comp_contDiffOn hF
    have hp (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i A (F x)‖ ≤ N :=
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hi))
    have hdf (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
        ‖iteratedFDerivWithin ℝ i F S x‖ ≤ D ^ i := by
      rw [iteratedFDerivWithin_of_isOpen i hS (hLS hx)]
      exact (hd i him x hx).trans ((le_max_left D₀ 1).trans (le_self_pow₀ hD1 (by omega)))
    have hcg (i : ℕ) (hi : i ≤ m) :
        ‖iteratedFDerivWithin ℝ i (fun z => A (F z)) S x‖ ≤ i.factorial * N * D ^ i := by
      apply norm_iteratedFDerivWithin_comp_le A.contDiff.contDiffOn hF
        (by exact WithTop.coe_le_coe.mpr le_top) uniqueDiffOn_univ hS.uniqueDiffOn
        (mapsTo_univ _ _) (hLS hx)
      · intro j hj
        rw [iteratedFDerivWithin_univ]
        exact hp j (hj.trans hi)
      · intro j hj hji
        exact hdf j hj (hji.trans hi)
    have heq : EqOn (weightedComp S F P A) (fun z => P z (A (F z))) S :=
      fun z hz => weightedComp_of_mem hz
    change ‖iteratedFDeriv ℝ m (weightedComp S F P A) x‖ ≤ C * N
    rw [← iteratedFDerivWithin_of_isOpen m hS (hLS hx),
      iteratedFDerivWithin_congr heq (hLS hx) m]
    calc
      ‖iteratedFDerivWithin ℝ m (fun z => P z (A (F z))) S x‖ ≤
          ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i P S x‖ *
            ‖iteratedFDerivWithin ℝ (m - i) (fun z => A (F z)) S x‖ :=
        norm_iteratedFDerivWithin_clm_apply hP hcomp hS.uniqueDiffOn (hLS hx)
          (by exact WithTop.coe_le_coe.mpr le_top)
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B *
          ((m - i).factorial * N * D ^ (m - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · rw [iteratedFDerivWithin_of_isOpen i hS (hLS hx)]
          exact hb i (Finset.mem_range_succ_iff.mp hi) x hx
        · exact hcg (m - i) (Nat.sub_le m i)
      _ = C * N := by
        dsimp [C]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intros
        ring

@[simp] theorem weightedCompCLM_apply {S : Set E} (hS : IsOpen S) {F : E → E}
    (hF : ContDiffOn ℝ ∞ F S) {P : E → V →L[ℝ] W} (hP : ContDiffOn ℝ ∞ P S)
    (K : Compacts E) (L : Compacts E) (hLS : (L : Set E) ⊆ S)
    (hvan : ∀ z ∈ S, z ∉ (L : Set E) → P z = 0 ∨ F z ∉ (K : Set E))
    (A : 𝓓_{K}(E, V)) (z : E) :
    weightedCompCLM hS hF hP K L hLS hvan A z = weightedComp S F P A z := rfl

end Model

section Manifold

variable {n q : ℕ} {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {g : Z → Y}

/-- Real alternating `q`-forms on the model space. -/
local notation "Alt" q => (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ

/-- The tensor field `z ↦ χ(f⁻¹ z) · (D G_z)^*` (pull-back of `q`-covectors by the derivative of
the coordinate expression `G = e ∘ g ∘ f⁻¹`, weighted by the cut-off). -/
def pullField (g : Z → Y) (f : ComplexChart n Z) (e : ComplexChart n Y) (χ : Z → ℝ) (q : ℕ)
    (z : ComplexModel n) : (Alt q) →L[ℝ] (Alt q) :=
  χ (f.val.symm z) • ContinuousAlternatingMap.compContinuousLinearMapCLM
    (fderiv ℝ (coordinateMap g f e) z)

omit [IsComplexManifold n Z] [IsComplexManifold n Y] in
theorem pullField_apply (f : ComplexChart n Z) (e : ComplexChart n Y) (χ : Z → ℝ)
    (z : ComplexModel n) (A : Alt q) :
    pullField g f e χ q z A =
      χ (f.val.symm z) • A.compContinuousLinearMap (fderiv ℝ (coordinateMap g f e) z) := rfl

theorem contDiffOn_pullField
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (f : ComplexChart n Z) (e : ComplexChart n Y) {χ : Z → ℝ}
    (hχ : ChartSmooth (n := n) χ) :
    ContDiffOn ℝ ∞ (pullField g f e χ q) (coordinateDomain g f e) := by
  let : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) :=
    Module.Finite.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  let : FiniteDimensional ℝ (Alt q) :=
    Module.Finite.of_injective
      (ContinuousAlternatingMap.toContinuousMultilinearMapLinear (R := ℝ))
      ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  have hS := coordinateDomain_isOpen hg f e
  have hG := coordinateMap_contDiffOn_real hg f e
  have hD : ContDiffOn ℝ ∞ (fun z => fderiv ℝ (coordinateMap g f e) z)
      (coordinateDomain g f e) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hS).mp hG).2
  apply contDiffOn_clm_apply.mpr
  intro A
  have hT : ContDiffOn ℝ ∞ (fun z => A.compContinuousLinearMap
      (fderiv ℝ (coordinateMap g f e) z)) (coordinateDomain g f e) :=
    SGPT.Foundations.Analysis.Pending.NaturalSmoothTensorPullback.contDiffOn_compContinuousLinearMap
      contDiffOn_const hD
  exact ((hχ f).mono (fun z hz => hz.1)).smul hT

/-- The output support: chart image of the points of `supp χ` mapped into `e⁻¹(K)`. -/
def pullSet (g : Z → Y) (f : ComplexChart n Z) (e : ComplexChart n Y) (χ : Z → ℝ)
    (K : Set (ComplexModel n)) : Set (ComplexModel n) :=
  f.val '' (tsupport χ ∩ g ⁻¹' (e.val.symm '' K))

omit [IsComplexManifold n Z] in
theorem isCompact_pullSet (hg : Continuous g) (f : ComplexChart n Z) (e : ComplexChart n Y)
    {χ : Z → ℝ} (hχc : IsCompact (tsupport χ)) (hχs : tsupport χ ⊆ f.val.source)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    IsCompact (pullSet g f e χ K) := by
  have hC : IsClosed (g ⁻¹' (e.val.symm '' K)) :=
    ((hK.image_of_continuousOn (e.val.symm.continuousOn.mono hKe)).isClosed).preimage hg
  exact (hχc.inter_right hC).image_of_continuousOn
    (f.val.continuousOn.mono (inter_subset_left.trans hχs))

omit [IsComplexManifold n Z] [IsComplexManifold n Y] in
theorem pullSet_subset (f : ComplexChart n Z) (e : ComplexChart n Y) {χ : Z → ℝ}
    (hχs : tsupport χ ⊆ f.val.source) {K : Set (ComplexModel n)} (hKe : K ⊆ e.val.target) :
    pullSet g f e χ K ⊆ coordinateDomain g f e := by
  rintro _ ⟨x, ⟨hx, y, hy, hxy⟩, rfl⟩
  refine mem_coordinateDomain (hχs hx) ?_
  rw [← hxy]
  exact e.val.map_target (hKe hy)

omit [IsComplexManifold n Z] [IsComplexManifold n Y] in
theorem pullField_vanish (f : ComplexChart n Z) (e : ComplexChart n Y) (χ : Z → ℝ)
    (K : Set (ComplexModel n)) :
    ∀ z ∈ coordinateDomain g f e, z ∉ pullSet g f e χ K →
      pullField g f e χ q z = 0 ∨ coordinateMap g f e z ∉ K := by
  intro z hz hzL
  by_cases hχ : χ (f.val.symm z) = 0
  · left
    ext A v
    simp [pullField_apply, hχ]
  · right
    intro hK
    apply hzL
    refine ⟨f.val.symm z, ⟨subset_tsupport _ hχ, coordinateMap g f e z, hK, ?_⟩,
      f.val.right_inv hz.1⟩
    exact e.val.left_inv hz.2

variable (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
  (f : ComplexChart n Z) (e : ComplexChart n Y) {χ : Z → ℝ}
  (hχ : ChartSmooth (n := n) χ) (hχc : IsCompact (tsupport χ))
  (hχs : tsupport χ ⊆ f.val.source)

/-- The output compact of the stage maps. -/
def pullCompacts (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    Compacts (ComplexModel n) :=
  ⟨pullSet g f e χ K, isCompact_pullSet hg.continuous f e hχc hχs K.isCompact hK⟩

include hχ in
/-- Stage maps of the cut-off pull-back, continuous on each `𝓓_K`. -/
def pullStageCLM (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    𝓓_{K}(ComplexModel n, Alt q) →L[ℝ]
      𝓓_{pullCompacts hg f e hχc hχs K hK}(ComplexModel n, Alt q) :=
  weightedCompCLM (coordinateDomain_isOpen hg f e) (coordinateMap_contDiffOn_real hg f e)
    (contDiffOn_pullField hg f e hχ) K (pullCompacts hg f e hχc hχs K hK)
    (pullSet_subset f e hχs hK) (pullField_vanish f e χ K)

/-- The cut-off pull-back of a single chart test form. -/
def pullTestFun (η : LocalCurrents.TestForm (chartTarget e) q) :
    LocalCurrents.TestForm (chartTarget f) q where
  toFun := weightedComp (coordinateDomain g f e) (coordinateMap g f e) (pullField g f e χ q) η
  contDiff' := contDiff_weightedComp (coordinateDomain_isOpen hg f e)
    (coordinateMap_contDiffOn_real hg f e) (contDiffOn_pullField hg f e hχ)
    (isCompact_pullSet hg.continuous f e hχc hχs η.hasCompactSupport.isCompact
      η.tsupport_subset).isClosed
    (pullSet_subset f e hχs η.tsupport_subset) (pullField_vanish f e χ _) η.contDiff
    (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  hasCompactSupport' := HasCompactSupport.intro
    (isCompact_pullSet hg.continuous f e hχc hχs η.hasCompactSupport.isCompact
      η.tsupport_subset)
    (fun z hz => weightedComp_eq_zero (pullField_vanish f e χ _)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hz)
  tsupport_subset' := by
    have hL := isCompact_pullSet hg.continuous f e hχc hχs η.hasCompactSupport.isCompact
      η.tsupport_subset
    refine (closure_minimal ?_ hL.isClosed).trans
      ((pullSet_subset f e hχs η.tsupport_subset).trans fun z hz => hz.1)
    intro z hz
    by_contra hzL
    exact hz (weightedComp_eq_zero (pullField_vanish f e χ _)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hzL)

/-- **The cut-off pull-back of chart test forms along a holomorphic map** is a continuous linear
map between the LF spaces of test forms. -/
def pullTestCLM :
    LocalCurrents.TestForm (chartTarget e) q →L[ℝ] LocalCurrents.TestForm (chartTarget f) q :=
  TestFunction.limitCLM ℝ (pullTestFun hg f e hχ hχc hχs)
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ
      ((pullSet_subset f e hχs hK).trans fun _ hz => hz.1)).comp
        (pullStageCLM hg f e hχ hχc hχs K hK))
    (fun _ _ _ => TestFunction.ext fun _ => rfl)

theorem pullTestCLM_apply (η : LocalCurrents.TestForm (chartTarget e) q) (z : ComplexModel n) :
    pullTestCLM hg f e hχ hχc hχs η z =
      weightedComp (coordinateDomain g f e) (coordinateMap g f e) (pullField g f e χ q) η z :=
  rfl

/-- **The cut-off pull-back is the chart coefficient of `χ · g^*(η extended by zero)`.** -/
theorem pullTestCLM_apply_eq (η : LocalCurrents.TestForm (chartTarget e) q)
    (z : ComplexModel n) :
    pullTestCLM hg f e hχ hχc hχs η z = f.val.target.indicator
      (fun y => χ (f.val.symm y) • (SmoothRealForm.pullback hg (testExtension e η)).coeff f y)
        z := by
  rw [pullTestCLM_apply]
  by_cases hz : z ∈ coordinateDomain g f e
  · rw [weightedComp_of_mem hz, indicator_of_mem hz.1, pullField_apply,
      SmoothRealForm.pullback_coeff hg _ f e hz]
    congr 2
    exact (extend_coeff_self e η η.contDiff η.hasCompactSupport η.tsupport_subset
      (coordinateMap_mem_target hz)).symm
  · rw [weightedComp_of_notMem hz]
    by_cases hzt : z ∈ f.val.target
    · rw [indicator_of_mem hzt]
      let d := complexChartAt (n := n) (g (f.val.symm z))
      have hzd : z ∈ coordinateDomain g f d := ⟨hzt, mem_complexChartAt_source _⟩
      have hne : d.val.symm (coordinateMap g f d z) ∉ e.val.source := by
        intro h
        apply hz
        refine ⟨hzt, ?_⟩
        change d.val.symm (d.val (g (f.val.symm z))) ∈ e.val.source at h
        rwa [d.val.left_inv (mem_complexChartAt_source _)] at h
      rw [SmoothRealForm.pullback_coeff hg _ f d hzd]
      have h0 : (testExtension e η).coeff d (coordinateMap g f d z) = 0 :=
        extend_coeff_eq_zero e d η η.contDiff η.hasCompactSupport η.tsupport_subset hne
      rw [h0]
      ext v
      simp
    · rw [indicator_of_notMem hzt]

end Manifold

end SGPT.BDivisor.TestFormPullback
