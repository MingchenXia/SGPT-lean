import SGPT.Foundations.Analysis.Pending.SNCPrincipalPositiveCoordinateComponents
import SGPT.Foundations.Analysis.Pending.CenteredPrimeSNCCoordinateReaders
import SGPT.Foundations.Analysis.Pending.RawQuasiPshGivenCoordinateOrderBounds
import SGPT.Foundations.Analysis.Pending.SNCLogarithmicGenericCoordinateOrders
import SGPT.Foundations.Analysis.Pending.ManifoldAdaptedMultiplierGermTransport

set_option autoImplicit false

/-! # Actual whole-prime bounds give complete principal-family multiplier integrals

Natural numerical whole-prime comparison and a genuine original raw integral
internally produce the same test's strict coordinate thresholds. This is the
analytic-target step; the original raw-target valuative converse is separate.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.SNCPrincipalNumericalMultiplierSufficiency

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  NormalCrossings InvertibleIdealQuotient

noncomputable section

private theorem psh_generatorLog_of_near_holomorphic {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) {p : ComplexModel n}
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    PlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hG)
  have hgen : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hpU, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hgen (by norm_num : (0 : ℝ) < 1)

private theorem iInf_normal_form_eq {n s : ℕ} (G : Fin s → ComplexModel n → ℂ)
    (a : Fin n → ℕ) {η : ComplexModel n → ℝ} {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hη : ∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z)
    (hweight : ∀ z ∈ ball (0 : ComplexModel n) R, generatorLog G z =
      (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) (j : Fin n) :
    (⨅ z ∈ ball (0 : ComplexModel n) r ∩ {z | z j = 0},
      lelongNumber (n := n) (generatorLog G) z) = ENNReal.ofReal (2 * (a j : ℝ)) := by
  have heq : (⨅ z ∈ ball (0 : ComplexModel n) r ∩ {z | z j = 0},
      lelongNumber (n := n) (generatorLog G) z) =
      ⨅ z ∈ ball (0 : ComplexModel n) r ∩ {z | z j = 0},
        lelongNumber (n := n) (fun w =>
          (∑ i : Fin n, ((2 * (a i : ℝ) : ℝ) : EReal) *
            ENNReal.log (ENNReal.ofReal ‖w i‖)) + (η w : EReal)) z := by
    apply iInf_congr
    intro z
    apply iInf_congr
    intro hz
    have hnear : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ComplexModel n) R :=
      isOpen_ball.mem_nhds (ball_subset_ball hrR hz.1)
    exact LelongNumberComparison.lelongNumber_congr
      (hnear.mono fun w hw => hweight w hw)
  exact heq.trans (SNCLogarithmicGenericCoordinateOrders.iInf_lelongNumber_coordinate_hyperplane_eq
    (fun i => 2 * (a i : ℝ)) (fun _ => by positivity) j hr
      (fun z hz => hη z (ball_subset_ball hrR hz)))

/-- Natural whole-prime comparison and the original raw integral internally
produce the same test's strict analytic-target multiplier integral. -/
theorem multiplierIdeal_mem_of_whole_prime_bounds {n m s : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel n) ∞ π)
    (x : X) (y : Y) (hy : π y = x)
    (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y))
    (hE : IsSNCDivisor (m + 1) E) (hsupport : D.support = ⋃ H ∈ E, H)
    (hcomponents : ∀ i : Fin E.length, y ∈ E.get i →
      ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m ∧ (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) ∧
        y ∈ V.carrier ∧ (∀ z ∈ V.carrier, π z = x) ∧
        ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ E.get i ∩ O = V.carrier ∩ O)
    (G : Fin s → X → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (hgen : ∀ f : Y → ℂ, D.ideal.mem y f ↔
      IsInSpanAt (n := m + 1) (· ∈ range (fun i z => G i (π z))) y f)
    {u : Y → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    {F : Y → ℂ} (hF : HolomorphicAt (m + 1) F y)
    (hFnon : ∃ᶠ z in 𝓝 y, F z ≠ 0)
    {p q₀ q₁ : ℝ} (hp : 0 < p) (hq₁ : 0 < q₁) (hgap : q₁ < q₀)
    (hint : (multiplierIdeal (n := m + 1) q₀ u).mem y F)
    (hcompare : ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
      V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
      (∀ z ∈ V.carrier, π z = x) →
        (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (generatorLog (fun i w => G i (π w))) z) ≤
          ENNReal.ofReal p * ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) u z) :
    (multiplierIdeal (n := m + 1) (q₁ / p) (generatorLog (fun i w => G i (π w)))).mem y F := by
  classical
  have hq₀ : 0 < q₀ := hq₁.trans hgap
  have hGP (i : Fin s) : HolomorphicAt (m + 1) (fun z => G i (π z)) y :=
    (show HolomorphicAt n (G i) (π y) from hy ▸ hG i).comp_contMDiff
      (Eventually.of_forall fun _ => hπ.contMDiffAt)
  obtain ⟨S, Φ, hsrc, h0, _hcard, _hinj, hflat, a, η, R, hR, hη, hweight, hactive⟩ :=
    SNCPrincipalPositiveCoordinateComponents.exists_normal_form_with_active_components
      D E hE hsupport y (fun i z => G i (π z)) hGP hgen
  let e := complexChartAt (n := m + 1) y
  let T : ComplexModel (m + 1) → Y := fun z => e.val.symm (Φ.invFun z)
  let GT : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (π (T z))
  let FT : ComplexModel (m + 1) → ℂ := fun z => F (T z)
  let uT : ComplexModel (m + 1) → EReal := fun z => u (T z)
  have h0t : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val y := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have huP := hu e (e.val y) (e.val.map_source (mem_complexChartAt_source y))
  have huT : QuasiPlurisubharmonicAt uT 0 :=
    HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic Φ.isOpen_target
      (contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target) h0t
      (by simpa only [hinv0] using huP)
  have hFT := ManifoldAdaptedMultiplierGermTransport.holomorphic_nonzero_comp_adapted
    y Φ h0 hF hFnon
  have hintT : MultiplierIntegrableAt uT q₀ FT 0 volume :=
    (ManifoldAdaptedMultiplierGermTransport.multiplierIdeal_mem_comp_adapted_iff
      y Φ h0 hu hF q₀).mp hint
  obtain ⟨b, H, hH, _hHnon, hfactor, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hFT.1 hFT.2
  have hthreshold : ∀ j : Fin (m + 1), (q₁ / p) * (a j : ℝ) < (b j : ℝ) + 1 := by
    intro j
    by_cases haj : 0 < a j
    · obtain ⟨i, hyE, hS⟩ := hactive j haj
      obtain ⟨V, hdim, hreg, hyV, hcenter, O, hO, hyO, hlocal⟩ := hcomponents i hyE
      have hevent : ∀ᶠ z in 𝓝 y,
          z ∈ e.val.source ∧ e.val z ∈ Φ.source ∧ z ∈ O := by
        have hs : ∀ᶠ z in 𝓝 y, z ∈ e.val.source :=
          e.val.open_source.mem_nhds (mem_complexChartAt_source y)
        have ht : ∀ᶠ z in 𝓝 y, e.val z ∈ Φ.source :=
          (e.val.continuousAt (mem_complexChartAt_source y)).eventually
            (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
        have ho : ∀ᶠ z in 𝓝 y, z ∈ O := hO.mem_nhds hyO
        exact hs.and (ht.and ho)
      have hflatV : ∀ᶠ z in 𝓝 y, z ∈ V.carrier ↔ (Φ.toFun (e.val z)) j = 0 := by
        filter_upwards [hevent] with z hz
        have hEV : z ∈ E.get i ↔ z ∈ V.carrier := by
          have h := congrArg (fun A : Set Y => z ∈ A) hlocal
          simpa only [mem_inter_iff, hz.2.2, and_true] using Eq.to_iff h
        exact hEV.symm.trans (by simpa only [hS, coordSubspace, Finset.mem_singleton,
          Set.mem_ofPred_eq, forall_eq] using hflat i hyE hz.1 hz.2.1)
      obtain ⟨Rj, hRj, hread⟩ :=
        CenteredPrimeSNCCoordinateReaders.exists_radius_whole_prime_coordinate_readers
          hπ x V hcenter y hyV Φ hsrc h0 j hflatV
      let r := min R Rj
      have hr : 0 < r := lt_min hR hRj
      have hrR : r ≤ R := min_le_left _ _
      have hrRj : r ≤ Rj := min_le_right _ _
      have hreads := hread r hr hrRj
      have hGreader : (⨅ z ∈ V.carrier, lelongNumber (n := m + 1)
          (generatorLog (fun i w => G i (π w))) z) = ENNReal.ofReal (2 * (a j : ℝ)) := by
        have hwhole := hreads.1 s G hG 1 zero_lt_one
        simp only [EReal.coe_one, one_mul] at hwhole
        exact hwhole.trans (iInf_normal_form_eq GT a hr hrR hη hweight j)
      have huraw := hreads.2 u
      have hubound := RawQuasiPshGivenCoordinateOrderBounds.iInf_lelongNumber_coordinate_le_of_multiplier_integrable
        huT b hH hnot hfactor hintT hr j
      have hmul : ENNReal.ofReal p * (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) u z) ≤
          ENNReal.ofReal p * ENNReal.ofReal (2 * ((b j : ℝ) + 1) / q₀) := by
        gcongr
        exact huraw.trans hubound
      have hbound := (hcompare V hdim hreg hcenter).trans hmul
      rw [hGreader, ← ENNReal.ofReal_mul hp.le] at hbound
      have hreal : 2 * (a j : ℝ) ≤ p * (2 * ((b j : ℝ) + 1) / q₀) :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
      have hscaled : q₀ * (a j : ℝ) ≤ p * ((b j : ℝ) + 1) := by
        have heq : p * (2 * ((b j : ℝ) + 1) / q₀) =
            (p * (2 * ((b j : ℝ) + 1))) / q₀ := by ring
        rw [heq] at hreal
        have h := (le_div_iff₀ hq₀).mp hreal
        nlinarith
      have hajR : 0 < (a j : ℝ) := by exact_mod_cast haj
      have hstrict : q₁ * (a j : ℝ) < p * ((b j : ℝ) + 1) := by nlinarith
      have hdiv : q₁ * (a j : ℝ) / p < (b j : ℝ) + 1 :=
        (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using hstrict)
      convert hdiv using 1
      ring
    · have haz : a j = 0 := Nat.eq_zero_of_not_pos haj
      simp only [haz, Nat.cast_zero, mul_zero]
      positivity
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ ball 0 R := ball_mem_nhds _ hR
  have hηnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ContinuousAt η z :=
    hnear.mono fun z hz => hη z hz
  have hnorm := HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
    b (fun j => (a j : ℝ)) (div_pos hq₁ hp) hH hfactor hηnear hthreshold
  have heq : generatorLog GT =ᶠ[𝓝 (0 : ComplexModel (m + 1))] (fun z =>
      (∑ j : Fin (m + 1), ((2 * (a j : ℝ) : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) :=
    hnear.mono fun z hz => hweight z hz
  have hintGT : MultiplierIntegrableAt (generatorLog GT) (q₁ / p) FT 0 volume :=
    hnorm.congr heq.symm EventuallyEq.rfl
  let GP : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (π (e.val.symm z))
  have hGPnear (i : Fin s) : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ (GP i) z := by
    have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff
      (mem_complexChartAt_source y) (fun i z => G i (π z)) (fun z => G i (π z))).mp
        (isInSpanAt_self ⟨i, rfl⟩ (hGP i))
    exact h.1.mono fun _ hz => hz.differentiableAt
  have hpsh := (psh_generatorLog_of_near_holomorphic GP hGPnear).quasiPlurisubharmonicAt
  have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    Φ (f := fun z => F (e.val.symm z)) (c := q₁ / p) hpsh
  have hGcomp : (fun z => generatorLog GP (Φ.invFun z)) = generatorLog GT := by
    funext z
    rfl
  have hintP : MultiplierIntegrableAt (generatorLog GP) (q₁ / p)
      (fun z => F (e.val.symm z)) (e.val y) volume :=
    hcov.mp (by rw [h0, hGcomp]; exact hintGT)
  exact ⟨hF, hintP⟩

end
end SGPT.Foundations.Analysis.Pending.SNCPrincipalNumericalMultiplierSufficiency
