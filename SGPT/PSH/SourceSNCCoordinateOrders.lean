import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder
import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport
import SGPT.Foundations.Analysis.Pending.ConnectedJacobianCoefficient
import SGPT.Foundations.Analysis.Pending.IntrinsicJacobianCoefficient
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicMultiplierGermCovariance

/-! # Original local orders in fixed SNC coordinates

Supplementary coordinate support for SGPT's valuative multiplier criterion:
the same actual local component, original holomorphic germ and adapted chart
give ideal powers and normal orders. The genuine inverse-coordinate Jacobian
unit reads the actual relative coefficient and exact weighted point threshold.
The unrestricted valuative converse and the printed prime-order convention
are separate obligations; no whole-source coverage is asserted here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.SameCoordinateOrder

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves
open BlowupFlatCoordinates DemaillyApproximantDivisorialLelong
  FixedGermNormalOrder HolomorphicGermReducednessBridge

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Original local holomorphy passes to the very same adapted inverse. -/
theorem adapted_holomorphic (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0)
    (F : Y → ℂ) (hF : HolomorphicAt n F y) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun z => F ((chartAt (ComplexModel n) y).symm (Φ.invFun z))) z := by
  have hself : IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => F) y F :=
    InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hF
  exact ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    y Φ h0 (fun _ : Fin 1 => F) F).mp hself).1.mono fun _ hz => hz.differentiableAt

/-- The full original function germ in the fixed actual adapted chart. -/
def adaptedGerm (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0)
    (F : Y → ℂ) (hF : HolomorphicAt n F y) : HolGerm (ComplexModel n) :=
  HolGerm.mk (fun z => F ((chartAt (ComplexModel n) y).symm (Φ.invFun z)))
    (adapted_holomorphic y Φ h0 F hF)

private theorem principalPow_mem_iff_coordinate_pow_dvd (I : GermIdeal n Y) (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) (j : Fin n)
    (hgen : ∀ G, I.mem y G ↔ IsInSpanAt (n := n) (· = flatCoord Φ j) y G)
    (k : ℕ) (F : Y → ℂ) (hF : HolomorphicAt n F y) :
    (IdealWeightPowers.idealPow I k).mem y F ↔
      HolGerm.mk (fun z : ComplexModel n => z j)
        (eventually_differentiableAt_coordinate j) ^ k ∣ adaptedGerm y Φ h0 F hF := by
  let q : Y → ℂ := flatCoord Φ j
  have hq : HolomorphicAt n q y := holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)
  have hpower := HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator
    hq hgen k F
  let Q : Fin 1 → Y → ℂ := fun _ z => q z ^ k
  have htrans := ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff y Φ h0 Q F
  have hcoord (i : Fin 1) :
      (fun z => Q i ((chartAt (ComplexModel n) y).symm (Φ.invFun z))) =ᶠ[𝓝 0]
        (fun z : ComplexModel n => z j ^ k) := by
    have hz0 : (0 : ComplexModel n) ∈ Φ.target := by
      simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
    filter_upwards [Φ.isOpen_target.mem_nhds hz0] with z hz
    dsimp only [Q, q, flatCoord]
    rw [(chartAt (ComplexModel n) y).right_inv (hsrc (Φ.mapsTo_invFun hz)), Φ.right_inv z hz]
  have hspan : IsInSpanAt (n := n) (· ∈ range fun i z =>
        Q i ((chartAt (ComplexModel n) y).symm (Φ.invFun z))) (0 : ComplexModel n)
        (fun z => F ((chartAt (ComplexModel n) y).symm (Φ.invFun z))) ↔
      IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => fun z : ComplexModel n => z j ^ k) 0
        (fun z => F ((chartAt (ComplexModel n) y).symm (Φ.invFun z))) :=
    ⟨CoherentIdealColon.isInSpanAt_range_congr hcoord EventuallyEq.rfl,
      CoherentIdealColon.isInSpanAt_range_congr (fun i => (hcoord i).symm) EventuallyEq.rfl⟩
  have hring := EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
    (fun _ : Fin 1 => fun z : ComplexModel n => z j ^ k)
    (fun _ => eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) k)
    (adapted_holomorphic y Φ h0 F hF)
  calc
    (IdealWeightPowers.idealPow I k).mem y F ↔
        IsInSpanAt (n := n) (· ∈ range Q) y F :=
      hpower.trans (MemberPullback.isInSpanAt_range_one_iff (fun z => q z ^ k) F).symm
    _ ↔ _ := htrans.trans hspan
    _ ↔ _ := by
      simp only [range_const, Ideal.mem_span_singleton] at hring
      have hpow : HolGerm.mk (fun z : ComplexModel n => z j ^ k)
          (eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) k) =
          HolGerm.mk (fun z : ComplexModel n => z j)
            (eventually_differentiableAt_coordinate j) ^ k :=
        HolGerm.mk_pow (fun z : ComplexModel n => z j)
          (eventually_differentiableAt_coordinate j) k
      rw [hpow] at hring
      simpa only [range_const, adaptedGerm] using hring

/-- Actual original ideal powers are literal same-coordinate germ divisibility. -/
theorem idealPow_mem_iff_coordinate_pow_dvd {E : Set Y} (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) (j : Fin n)
    (hflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel n) y).source →
      (chartAt (ComplexModel n) y) z ∈ Φ.source →
      (z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel n) y) z) j = 0))
    (k : ℕ) (F : Y → ℂ) (hF : HolomorphicAt n F y) :
    (IdealWeightPowers.idealPow (vanishingIdeal (n := n) E) k).mem y F ↔
      HolGerm.mk (fun z : ComplexModel n => z j)
        (eventually_differentiableAt_coordinate j) ^ k ∣ adaptedGerm y Φ h0 F hF :=
  principalPow_mem_iff_coordinate_pow_dvd _ y Φ hsrc h0 j
    (fun G => MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ hflat
      (mem_flatDomain_self Φ) G) k F hF

/-- A genuine LOCAL component equation suffices; the working chart is unchanged. -/
theorem component_coordinate_germ {A E : Set Y} (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y)) (j : Fin n)
    (hflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel n) y).source →
      (chartAt (ComplexModel n) y) z ∈ Φ.source →
      (z ∈ A ↔ Φ.toFun ((chartAt (ComplexModel n) y) z) j = 0))
    (hlocal : ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ A ∩ W = E ∩ W) :
    ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel n) y) z) j = 0 := by
  obtain ⟨W, hW, hyW, heq⟩ := hlocal
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ), hW.mem_nhds hyW]
    with z hz hzW
  have hEA : z ∈ E ↔ z ∈ A := by
    constructor
    · intro hE
      have h : z ∈ E ∩ W := ⟨hE, hzW⟩
      rw [← heq] at h
      exact h.1
    · intro hA
      have h : z ∈ A ∩ W := ⟨hA, hzW⟩
      rw [heq] at h
      exact h.1
  exact hEA.trans (hflat hz.1 hz.2)

/-- Only local equality with a coordinate hypersurface is required. -/
theorem idealPow_mem_iff_coordinate_pow_dvd_of_eventually {E : Set Y} (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) (j : Fin n)
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel n) y) z) j = 0)
    (k : ℕ) (F : Y → ℂ) (hF : HolomorphicAt n F y) :
    (IdealWeightPowers.idealPow (vanishingIdeal (n := n) E) k).mem y F ↔
      HolGerm.mk (fun z : ComplexModel n => z j)
        (eventually_differentiableAt_coordinate j) ^ k ∣ adaptedGerm y Φ h0 F hF := by
  let A : Set Y := {z | Φ.toFun ((chartAt (ComplexModel n) y) z) j = 0}
  have hgen (G : Y → ℂ) : (vanishingIdeal (n := n) E).mem y G ↔
      IsInSpanAt (n := n) (· = flatCoord Φ j) y G :=
    (BlowupStrictIdeal.vanishingIdeal_mem_congr (A := E) (B := A) hflat G).trans
      (MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ (A := A) (t := j)
        (by intro z _ _; rfl) (mem_flatDomain_self Φ) G)
  exact principalPow_mem_iff_coordinate_pow_dvd _ y Φ hsrc h0 j hgen k F hF

/-- Any actual flattening reads the same full normal order in the fixed coordinate. -/
theorem functionNormalOrder_eq_coordinate {m : ℕ}
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {E : Set Y} {y : Y}
    (Ψ : DivisorFlattening (m := m) E y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (m + 1)) y).source →
      (chartAt (ComplexModel (m + 1)) y) z ∈ Φ.source →
      (z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0))
    (F : Y → ℂ) (hF : HolomorphicAt (m + 1) F y) :
    functionNormalOrder Ψ F hF =
      emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
        (eventually_differentiableAt_coordinate j)) (adaptedGerm y Φ h0 F hF) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  change (k : ℕ∞) ≤ emultiplicity (divisorEquationGerm Ψ)
    (HironakaHolomorphicJetRankLoci.chartTranslatedGerm y y (mem_chart_source _ y) F hF) ↔ _
  rw [← pow_dvd_iff_le_emultiplicity, ← pow_dvd_iff_le_emultiplicity]
  exact (IdealPowerNormalOrder.mem_idealPow_iff_equation_pow_dvd Ψ k F hF).symm.trans
    (idealPow_mem_iff_coordinate_pow_dvd y Φ hsrc h0 j hflat k F hF)

/-- Only the actual component germ equation is needed to read the full order. -/
theorem functionNormalOrder_eq_coordinate_of_eventually {m : ℕ}
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {E : Set Y} {y : Y}
    (Ψ : DivisorFlattening (m := m) E y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0)
    (F : Y → ℂ) (hF : HolomorphicAt (m + 1) F y) :
    functionNormalOrder Ψ F hF =
      emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
        (eventually_differentiableAt_coordinate j)) (adaptedGerm y Φ h0 F hF) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  change (k : ℕ∞) ≤ emultiplicity (divisorEquationGerm Ψ)
    (HironakaHolomorphicJetRankLoci.chartTranslatedGerm y y (mem_chart_source _ y) F hF) ↔ _
  rw [← pow_dvd_iff_le_emultiplicity, ← pow_dvd_iff_le_emultiplicity]
  exact (IdealPowerNormalOrder.mem_idealPow_iff_equation_pow_dvd Ψ k F hF).symm.trans
    (idealPow_mem_iff_coordinate_pow_dvd_of_eventually y Φ hsrc h0 j hflat k F hF)

/-- A factorization in any selected coordinate computes its actual extended multiplicity. -/
theorem emultiplicity_coordinate_factorization (j : Fin n)
    (g : HolGerm (ComplexModel n)) (a : Fin n → ℕ) (H : ComplexModel n → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (hfactor : (g : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (fun z => H z * ∏ i, z i ^ a i : Germ (𝓝 (0 : ComplexModel n)) ℂ))
    (hnot : ¬HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) :
    emultiplicity (HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j)) g = (a j : ℕ∞) := by
  classical
  let t (i : Fin n) : HolGerm (ComplexModel n) :=
    HolGerm.mk (fun z : ComplexModel n => z i) (eventually_differentiableAt_coordinate i)
  have hprod : (((∏ i, t i ^ a i) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      (fun z : ComplexModel n => ∏ i, z i ^ a i : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
    rw [SubmonoidClass.coe_finsetProd]
    simp only [SubmonoidClass.coe_pow, t, HolGerm.coe_mk]
    have h := map_prod (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) :
      (ComplexModel n → ℂ) →+* Germ (𝓝 (0 : ComplexModel n)) ℂ)
      (fun i z => z i ^ a i) Finset.univ
    simp only [Germ.coe_coeRingHom] at h
    simp_rw [← Germ.coe_pow]
    change (∏ i, ((fun z : ComplexModel n => z i ^ a i) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ)) = _
    rw [← h, Finset.prod_fn]
  have heq : g = HolGerm.mk H hH * ∏ i, t i ^ a i := by
    apply Subtype.ext
    rw [Subring.coe_mul, HolGerm.coe_mk, hprod]
    exact hfactor
  have ht : Prime (t j) := HolomorphicCoordinatePrime.prime_coordinate_germ j
  change emultiplicity (t j) g = _
  rw [heq, emultiplicity_mul ht, emultiplicity_eq_zero.mpr hnot, zero_add,
    Finset.emultiplicity_prod ht]
  rw [Finset.sum_eq_single j]
  · exact emultiplicity_pow_self_of_prime ht _
  · intro i _ hij
    have hnd : ¬t j ∣ t i := SNCHolomorphicTestNecessity.coordinate_germ_not_dvd_of_ne hij
    rw [emultiplicity_pow ht, emultiplicity_eq_zero.mpr hnd, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The original normal order is read from the SAME arbitrary-coordinate factorization. -/
theorem functionNormalOrder_eq_factorization_coordinate {m : ℕ}
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {E : Set Y} {y : Y}
    (Ψ : DivisorFlattening (m := m) E y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (m + 1)) y).source →
      (chartAt (ComplexModel (m + 1)) y) z ∈ Φ.source →
      (z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0))
    (F : Y → ℂ) (hF : HolomorphicAt (m + 1) F y)
    (a : Fin (m + 1) → ℕ) (H : ComplexModel (m + 1) → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hfactor : (fun z => F ((chartAt (ComplexModel (m + 1)) y).symm (Φ.invFun z))) =ᶠ[𝓝 0]
      (fun z => H z * ∏ i, z i ^ a i))
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) :
    functionNormalOrder Ψ F hF = (a j : ℕ∞) := by
  rw [functionNormalOrder_eq_coordinate Ψ Φ hsrc h0 j hflat F hF]
  exact emultiplicity_coordinate_factorization j (adaptedGerm y Φ h0 F hF) a H hH
    (Germ.coe_eq.mpr hfactor) hnot

/-- The finite factorization terminal retains only the actual local component equation. -/
theorem functionNormalOrder_eq_factorization_coordinate_of_eventually {m : ℕ}
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {E : Set Y} {y : Y}
    (Ψ : DivisorFlattening (m := m) E y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0)
    (F : Y → ℂ) (hF : HolomorphicAt (m + 1) F y)
    (a : Fin (m + 1) → ℕ) (H : ComplexModel (m + 1) → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hfactor : (fun z => F ((chartAt (ComplexModel (m + 1)) y).symm (Φ.invFun z))) =ᶠ[𝓝 0]
      (fun z => H z * ∏ i, z i ^ a i))
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH) :
    functionNormalOrder Ψ F hF = (a j : ℕ∞) := by
  rw [functionNormalOrder_eq_coordinate_of_eventually Ψ Φ hsrc h0 j hflat F hF]
  exact emultiplicity_coordinate_factorization j (adaptedGerm y Φ h0 F hF) a H hH
    (Germ.coe_eq.mpr hfactor) hnot

section Jacobian

open FirstPass.HolomorphicMaps GlobalRelativeJacobianIdeal
  DivisorialChangeOfVariables HolomorphicGermJacobian

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The actual adapted determinant is the same preferred Jacobian times a
genuinely manufactured inverse-coordinate unit, even for a zero Jacobian. -/
theorem exists_adapted_jacobian_germ_mul_unit {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) y) y))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) y) y) = 0) :
    ∃ J U : HolGerm (ComplexModel n),
      (J : Germ (𝓝 (0 : ComplexModel n)) ℂ) =
        (complexJacobian ((coordinateMap π (complexChartAt (n := n) y)
          (complexChartAt (n := n) (π y))) ∘ Φ.invFun) :
            Germ (𝓝 (0 : ComplexModel n)) ℂ) ∧
      IsUnit U ∧
      J = adaptedGerm y Φ h0 (chartJacobianFunction (n := n) π y (π y))
        (holomorphicAt_chartJacobianFunction hπ y (π y)
          (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))) * U := by
  let e := complexChartAt (n := n) y
  let d := complexChartAt (n := n) (π y)
  let f := coordinateMap π e d
  have hzero : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val y := by
    rw [← h0, Φ.left_inv _ Φ.center_mem_source]
    rfl
  have ht : Tendsto Φ.invFun (𝓝 (0 : ComplexModel n)) (𝓝 (e.val y)) := by
    simpa only [hinv0] using
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hzero)).continuousAt.tendsto
  have hp : e.val y ∈ coordinateDomain π e d :=
    mem_coordinateDomain (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel n), Φ.invFun z ∈ coordinateDomain π e d :=
    ht.eventually ((coordinateDomain_isOpen hπ e d).mem_nhds hp)
  have hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f ∘ Φ.invFun) z := by
    filter_upwards [hnear, Φ.isOpen_target.mem_nhds hzero] with z hz hzT
    exact ((coordinateMap_contDiffAt hπ e d hz).differentiableAt (by simp)).comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hzT))
  obtain ⟨_hJto, hJinv, _hJto0, hJinv0⟩ :=
    LocalHolomorphicMultiplierGermCovariance.jacobian_units_of_local_holomorphic_equiv Φ
  have hJinv' : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (complexJacobian Φ.invFun) z := by simpa only [h0] using hJinv
  let U := HolGerm.mk (complexJacobian Φ.invFun) hJinv'
  have hU : IsUnit U := (HolGerm.isUnit_iff_eval_ne_zero U).mpr (by
    change complexJacobian Φ.invFun 0 ≠ 0
    simpa only [h0] using hJinv0)
  have hfactor : complexJacobian (f ∘ Φ.invFun) =ᶠ[𝓝 (0 : ComplexModel n)]
      (fun z => chartJacobianFunction (n := n) π y (π y)
        ((chartAt (ComplexModel n) y).symm (Φ.invFun z)) * complexJacobian Φ.invFun z) := by
    filter_upwards [hnear, Φ.isOpen_target.mem_nhds hzero] with z hz hzT
    have hA := (coordinateMap_contDiffAt hπ e d hz).differentiableAt (by simp)
    have hB := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hzT)
    change complexJacobian (f ∘ Φ.invFun) z =
      complexJacobian f (e.val (e.val.symm (Φ.invFun z))) * complexJacobian Φ.invFun z
    rw [e.val.right_inv hz.1]
    simp only [complexJacobian]
    rw [fderiv_comp z hA hB, ContinuousLinearMap.det]
    change LinearMap.det ((fderiv ℂ f (Φ.invFun z)).toLinearMap.comp
      (fderiv ℂ Φ.invFun z).toLinearMap) = _
    exact LinearMap.det_comp _ _
  refine ⟨jacobianGerm (f ∘ Φ.invFun) hf, U, jacobianGerm_source _ hf, hU, ?_⟩
  apply Subtype.ext
  rw [jacobianGerm_source, Subring.coe_mul]
  simp only [adaptedGerm, U, HolGerm.coe_mk, ← Germ.coe_mul]
  exact Germ.coe_eq.mpr hfactor

end Jacobian

section JacobianCoefficient

open FirstPass.HolomorphicMaps FirstPass.BlowupSequences GlobalRelativeJacobianIdeal
  DivisorialChangeOfVariables ConnectedJacobianCoefficient

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y} {y : Y}

/-- The SAME adapted determinant reads the genuinely produced whole-prime coefficient. -/
theorem emultiplicity_adapted_jacobian_eq_actualCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) (hy : y ∈ E)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0)
    (J : HolGerm (ComplexModel (m + 1)))
    (hJ : (J : Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ) =
      (complexJacobian ((coordinateMap π (complexChartAt (n := m + 1) y)
        (complexChartAt (n := m + 1) (π y))) ∘ Φ.invFun) :
          Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ)) :
    emultiplicity (HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (eventually_differentiableAt_coordinate j)) J = (actualRelativeJacobianCoefficient hπ hE : ℕ∞) := by
  obtain ⟨Ψ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  obtain ⟨J₀, U, hJ₀, hU, hfactor⟩ := exists_adapted_jacobian_germ_mul_unit hπ.1 y Φ h0
  have hJJ : J = J₀ := Subtype.ext (hJ.trans hJ₀.symm)
  have ht : Prime (HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (eventually_differentiableAt_coordinate j)) := HolomorphicCoordinatePrime.prime_coordinate_germ j
  rw [hJJ, hfactor, emultiplicity_mul ht, emultiplicity_of_isUnit_right ht.not_isUnit hU, add_zero]
  have hpreferred : functionNormalOrder Ψ
      (chartJacobianFunction (n := m + 1) π y (π y))
      (holomorphicAt_chartJacobianFunction hπ.1 y (π y)
        (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))) =
      (actualRelativeJacobianCoefficient hπ hE : ℕ∞) := by
    unfold functionNormalOrder
    rw [GlobalJacobianCoefficient.chartTranslatedJacobian_eq_preferred hπ.1 y]
    exact (ActualFlatNormalOrder.preferredJacobianOrder_eq_flat hπ.1 Ψ).trans
      (flatJacobianOrder_eq_actualRelativeJacobianCoefficient hπ hE y hy Ψ)
  exact (functionNormalOrder_eq_coordinate_of_eventually Ψ Φ hsrc h0 j hflat _
    (holomorphicAt_chartJacobianFunction hπ.1 y (π y)
      (mem_complexChartAt_source y) (mem_complexChartAt_source (π y)))).symm.trans hpreferred

/-- The actual unit-monomial Jacobian exponent is the actual relative coefficient. -/
theorem actualCoefficient_eq_adapted_jacobian_exponent
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) (hy : y ∈ E)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0)
    (d : Fin (m + 1) → ℕ) (L : ComplexModel (m + 1) → ℂ)
    (hL : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ L z) (hL0 : L 0 ≠ 0)
    (hfactor : complexJacobian ((coordinateMap π (complexChartAt (n := m + 1) y)
      (complexChartAt (n := m + 1) (π y))) ∘ Φ.invFun) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
        (fun z => L z * ∏ i, z i ^ d i)) :
    actualRelativeJacobianCoefficient hπ hE = d j := by
  obtain ⟨J, _U, hJ, _hU, _heq⟩ := exists_adapted_jacobian_germ_mul_unit hπ.1 y Φ h0
  have hunit : IsUnit (HolGerm.mk L hL) := (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by
    simpa only [HolGerm.eval_mk] using hL0)
  have hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk L hL := fun hdiv =>
    (HolomorphicCoordinatePrime.prime_coordinate_germ j).not_isUnit
      (isUnit_of_dvd_unit hdiv hunit)
  apply ENat.natCast_inj.mp
  exact (emultiplicity_adapted_jacobian_eq_actualCoefficient hπ hE hy Φ hsrc h0 j hflat J hJ).symm.trans
    (emultiplicity_coordinate_factorization j J d L hL (hJ.trans (Germ.coe_eq.mpr hfactor)) hnot)

/-- The SAME original test and actual Jacobian give the coordinate threshold
with the exact genuinely produced represented discrepancy. -/
theorem weighted_coordinate_order_add_one
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) (hy : y ∈ E)
    (Ψ : DivisorFlattening (m := m) E y)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0)
    (F : X → ℂ) (hF : HolomorphicAt (m + 1) F (π y))
    (b d : Fin (m + 1) → ℕ) (K L : ComplexModel (m + 1) → ℂ)
    (hK : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ K z)
    (hL : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ L z) (hL0 : L 0 ≠ 0)
    (hFfactor : (fun z => F (π ((chartAt (ComplexModel (m + 1)) y).symm (Φ.invFun z)))) =ᶠ[𝓝 0]
      (fun z => K z * ∏ i, z i ^ b i))
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk K hK)
    (hJac : complexJacobian ((coordinateMap π (complexChartAt (n := m + 1) y)
      (complexChartAt (n := m + 1) (π y))) ∘ Φ.invFun) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
        (fun z => L z * ∏ i, z i ^ d i)) :
    ((b j + d j + 1 : ℕ) : ℕ∞) = pullbackNormalOrder hπ Ψ F hF +
      (IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℕ∞) := by
  have hFpull : HolomorphicAt (m + 1) (F ∘ π) y :=
    hF.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hb : pullbackNormalOrder hπ Ψ F hF = (b j : ℕ∞) := by
    unfold pullbackNormalOrder
    exact functionNormalOrder_eq_factorization_coordinate_of_eventually Ψ Φ hsrc h0 j hflat
      (F ∘ π) hFpull b K hK hFfactor hnot
  have hd := actualCoefficient_eq_adapted_jacobian_exponent hπ hE hy Φ hsrc h0 j hflat
    d L hL hL0 hJac
  rw [hb, IntrinsicJacobianCoefficient.representedLogDiscrepancy, hd]
  simp only [ENat.natCast_add, ENat.natCast_one, add_assoc]

end JacobianCoefficient

end SGPT.PSH.SameCoordinateOrder
