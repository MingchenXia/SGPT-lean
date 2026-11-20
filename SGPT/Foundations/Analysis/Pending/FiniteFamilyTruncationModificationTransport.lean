import SGPT.Foundations.Analysis.Pending.SNCFiniteFamilyTruncationStability
import SGPT.Foundations.Analysis.Pending.HolomorphicPointTruncationPullback
import SGPT.Foundations.Analysis.Pending.AnalyticModificationJacobianMultiplierGerms
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicMultiplierGermCovariance

set_option autoImplicit false

/-! # Strict full-family truncation stability through actual proper modification geometry -/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.FiniteFamilyTruncationModificationTransport

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps
  DivisorialChangeOfVariables NormalCrossings

noncomputable section

private theorem psh_generatorLog {n s : ℕ} {p : ComplexModel n}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    PlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hsub, hU, hp⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hG)
  have hg : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hp, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hg (by norm_num : (0 : ℝ) < 1)

private theorem holomorphic_adapted {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    {g : X → ℂ} (hg : HolomorphicAt n g x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) z := by
  have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => g) g).mp
      (InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hg)
  exact h.1.mono fun _ hz => hz.differentiableAt

private def inverse {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    LocalHolomorphicEquivAt (n := n) (Φ.toFun p) where
  source := Φ.target
  target := Φ.source
  isOpen_source := Φ.isOpen_target
  isOpen_target := Φ.isOpen_source
  center_mem_source := Φ.mapsTo_toFun Φ.center_mem_source
  toFun := Φ.invFun
  invFun := Φ.toFun
  toFun_holomorphic := Φ.invFun_holomorphic
  invFun_holomorphic := Φ.toFun_holomorphic
  mapsTo_toFun := Φ.mapsTo_invFun
  mapsTo_invFun := Φ.mapsTo_toFun
  left_inv := Φ.right_inv
  right_inv := Φ.left_inv

private theorem multiplier_comp_toFun_iff {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p)
    {w : ComplexModel n → EReal} {f : ComplexModel n → ℂ} {c : ℝ}
    (hw : QuasiPlurisubharmonicAt w (Φ.toFun p)) :
    MultiplierIntegrableAt (fun z => w (Φ.toFun z)) c
      (fun z => f (Φ.toFun z)) p volume ↔
      MultiplierIntegrableAt w c f (Φ.toFun p) volume := by
  simpa only [inverse, Φ.left_inv p Φ.center_mem_source] using
    LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
      (inverse Φ) hw

private theorem adapted_map {n s : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (x : X) (y : Y) (hy : π y = x)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (Ψ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hΨ0 : Ψ.toFun ((complexChartAt (n := n) y).val y) = 0)
    (G : Fin s → X → ℂ) :
    let d := complexChartAt (n := n) x
    let e := complexChartAt (n := n) y
    let η := fun z => Φ.toFun (coordinateMap π e d (Ψ.invFun z))
    (∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ η z) ∧ η 0 = 0 ∧
      ∀ i, (fun z => G i (d.val.symm (Φ.invFun (η z)))) =ᶠ[𝓝 0]
        (fun z => G i (π (e.val.symm (Ψ.invFun z)))) := by
  dsimp only
  let d := complexChartAt (n := n) x
  let e := complexChartAt (n := n) y
  let P := coordinateMap π e d
  let D := coordinateDomain π e d
  have hD := coordinateDomain_isOpen hπ e d
  have heD : e.val y ∈ D := by
    apply mem_coordinateDomain (mem_complexChartAt_source y)
    rw [hy]
    exact mem_complexChartAt_source x
  have hPy : coordinateMap π e d (e.val y) = d.val x := by
    rw [coordinateMap_at (f := π) (e := e) (d := d) (mem_complexChartAt_source y), hy]
  have hΨinv0 : Ψ.invFun 0 = e.val y := by
    rw [← hΨ0]
    exact Ψ.left_inv _ Ψ.center_mem_source
  have hΨt : Tendsto Ψ.invFun (𝓝 (0 : ComplexModel n)) (𝓝 (e.val y)) := by
    have h := (Ψ.invFun_holomorphic.differentiableAt
      (Ψ.isOpen_target.mem_nhds (Ψ.mapsTo_toFun Ψ.center_mem_source))).continuousAt.tendsto
    simpa only [hΨ0, hΨinv0] using h
  have hPd := coordinateMap_contDiffOn hπ e d
  have hPt : Tendsto (fun z => P (Ψ.invFun z)) (𝓝 (0 : ComplexModel n)) (𝓝 (d.val x)) := by
    have h := (hPd.contDiffAt (hD.mem_nhds heD)).continuousAt.tendsto.comp hΨt
    change Tendsto (fun z => P (Ψ.invFun z)) (𝓝 (0 : ComplexModel n)) (𝓝 (P (e.val y))) at h
    have hPy' : P (e.val y) = d.val x := hPy
    rwa [hPy'] at h
  have hPnear : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ P z :=
    (show ∀ᶠ z in 𝓝 (e.val y), z ∈ D from hD.mem_nhds heD).mono fun z hz =>
      (hPd.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have hΦnear : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ Φ.toFun z :=
    (show ∀ᶠ z in 𝓝 (d.val x), z ∈ Φ.source from
      Φ.isOpen_source.mem_nhds Φ.center_mem_source).mono fun z hz =>
      Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)
  have hΨnear : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ Ψ.invFun z := by
    have h := (show ∀ᶠ z in 𝓝 (Ψ.toFun (e.val y)), z ∈ Ψ.target from
      Ψ.isOpen_target.mem_nhds (Ψ.mapsTo_toFun Ψ.center_mem_source)).mono
      fun z hz => Ψ.invFun_holomorphic.differentiableAt (Ψ.isOpen_target.mem_nhds hz)
    change Ψ.toFun (e.val y) = 0 at hΨ0
    rwa [hΨ0] at h
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hΨnear, hΨt.eventually hPnear, hPt.eventually hΦnear]
      with z hz hPz hΦz
    exact hΦz.comp z (hPz.comp z hz)
  · rw [hΨinv0]
    change Φ.toFun (coordinateMap π e d (e.val y)) = 0
    rw [hPy]
    exact h0
  · intro i
    filter_upwards [hΨt.eventually (hD.mem_nhds heD),
      hPt.eventually (Φ.isOpen_source.mem_nhds Φ.center_mem_source)] with z hz hΦz
    rw [Φ.left_inv _ hΦz]
    exact congrArg (G i) (d.val.left_inv hz.2)

/-- The actual all-fiber geometry and full original SNC presentation return
strict stability for the literal target family and original test. -/
theorem multiplierIntegrableAt_of_all_truncations_of_modification
    {m s : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (x : X)
    (Φ : LocalHolomorphicEquivAt (n := m + 1)
      ((complexChartAt (n := m + 1) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := m + 1) x).val x) = 0)
    (G : Fin s → X → ℂ) (hG : ∀ i, HolomorphicAt (m + 1) (G i) x)
    (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y))
    (hE : IsSNCDivisor (m + 1) E) (hsupport : D.support = ⋃ H ∈ E, H)
    (hgen : ∀ y, π y = x → ∀ g : Y → ℂ, D.ideal.mem y g ↔
      IsInSpanAt (n := m + 1) (· ∈ Set.range fun i => G i ∘ π) y g)
    {q q' : ℝ} (hq' : 0 < q') (hqq' : q' < q) {F : ComplexModel (m + 1) → ℂ}
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 1) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span (Set.range fun i => HolGerm.mk
          (fun z => G i ((complexChartAt (n := m + 1) x).val.symm (Φ.invFun z)))
          (holomorphic_adapted x Φ h0 (hG i))) ⊔
        (Ideal.span (Set.range fun j : Fin (m + 1) => HolGerm.mk
          (fun z : ComplexModel (m + 1) => z j)
          (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt
      (generatorLog (fun i z => G i
        ((complexChartAt (n := m + 1) x).val.symm (Φ.invFun z)))) q' F 0 volume := by
  classical
  let d := complexChartAt (n := m + 1) x
  let A : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (d.val.symm (Φ.invFun z))
  let hA := fun i => holomorphic_adapted x Φ h0 (hG i)
  let w : ComplexModel (m + 1) → EReal := fun z => generatorLog A (Φ.toFun z)
  let f : ComplexModel (m + 1) → ℂ := fun z => F (Φ.toFun z)
  have hq : 0 < q := hq'.trans hqq'
  have hAw : QuasiPlurisubharmonicAt (generatorLog A) 0 :=
    (psh_generatorLog A hA).quasiPlurisubharmonicAt
  have hw : QuasiPlurisubharmonicAt w (d.val x) := by
    apply HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
      Φ.isOpen_source
      (contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source)
      Φ.center_mem_source
    simpa only [h0] using hAw
  obtain ⟨r₀, Q₀, hQ₀, _hmem₀, hint₀⟩ := htrunc 0
  have htarget₀ : MultiplierIntegrableAt
      (fun z => generatorLog Q₀ (Φ.toFun z)) q f (d.val x) volume :=
    (multiplier_comp_toFun_iff Φ (by simpa only [h0] using
      (psh_generatorLog Q₀ hQ₀).quasiPlurisubharmonicAt)).mpr
        (by simpa only [h0] using hint₀)
  have hf : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ f z := by
    obtain ⟨_, U, hU, hxU, hhol, _⟩ := htarget₀
    exact (show ∀ᶠ z in 𝓝 (d.val x), z ∈ U from hU.mem_nhds hxU).mono
      fun z hz => hhol.differentiableAt (hU.mem_nhds hz)
  have htarget : MultiplierIntegrableAt w q' f (d.val x) volume := by
    apply (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
      hπ x hq' hw hf).mpr
    intro y hy
    let e := complexChartAt (n := m + 1) y
    let P := coordinateMap π e d
    have hP0 : coordinateMap π e d (e.val y) = d.val x := by
      rw [coordinateMap_at (f := π) (e := e) (d := d) (mem_complexChartAt_source y), hy]
    have hDy : e.val y ∈ coordinateDomain π e d := by
      apply mem_coordinateDomain (mem_complexChartAt_source y)
      rw [hy]
      exact mem_complexChartAt_source x
    let H : Fin s → Y → ℂ := fun i => G i ∘ π
    have hH : ∀ i, HolomorphicAt (m + 1) (H i) y := by
      intro i
      apply HolomorphicAt.comp_contMDiff
        (show HolomorphicAt (m + 1) (G i) (π y) from by rw [hy]; exact hG i)
      exact Eventually.of_forall fun z => hπ.1.contMDiffAt
    obtain ⟨Ψ, hHT, hsrc, hΨ0, hstable⟩ :=
      SNCFiniteFamilyTruncationStability.exists_adapted_strict_truncation_stability
        D E hE hsupport y H hH (hgen y hy)
    let η : ComplexModel (m + 1) → ComplexModel (m + 1) :=
      fun z => Φ.toFun (P (Ψ.invFun z))
    obtain ⟨hη, hη0, hfamily⟩ := adapted_map hπ.1 x y hy Φ h0 Ψ hΨ0 G
    let ft : ComplexModel (m + 1) → ℂ := fun z =>
      f (P (Ψ.invFun z)) * complexJacobian P (Ψ.invFun z)
    have hsource : MultiplierIntegrableAt
        (generatorLog (fun i z => H i (e.val.symm (Ψ.invFun z)))) q' ft 0 volume := by
      apply hstable q q' hq' hqq' ft
      intro N
      obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
      let hQt := fun i => (HolomorphicPointTruncationPullback.mem_truncation_of_holomorphic_comp
        η hη hη0 A hA N (hF := hQ i) (hmem := hmem i)).choose
      refine ⟨r, (fun i => Q i ∘ η), hQt, ?_, ?_⟩
      · intro i
        obtain ⟨hQi, hAi, hi⟩ :=
          HolomorphicPointTruncationPullback.mem_truncation_of_holomorphic_comp
            η hη hη0 A hA N (hF := hQ i) (hmem := hmem i)
        have heq : (fun j => HolGerm.mk (A j ∘ η) (hAi j)) =
            (fun j => HolGerm.mk
              (fun z => H j (e.val.symm (Ψ.invFun z))) (hHT j)) := by
          funext j
          exact HolGerm.mk_eq_mk_iff.mpr (hfamily j)
        rw [heq] at hi
        exact hi
      · have hQt : QuasiPlurisubharmonicAt (fun z => generatorLog Q (Φ.toFun z))
            (d.val x) := by
          apply HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
            Φ.isOpen_source
            (contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source)
            Φ.center_mem_source
          simpa only [h0] using (psh_generatorLog Q hQ).quasiPlurisubharmonicAt
        have hintT : MultiplierIntegrableAt (fun z => generatorLog Q (Φ.toFun z))
            q f (d.val x) volume :=
          (multiplier_comp_toFun_iff Φ (by simpa only [h0] using
            (psh_generatorLog Q hQ).quasiPlurisubharmonicAt)).mpr
              (by simpa only [h0] using hint)
        have hintS := (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
          hπ x hq hQt hf).mp hintT y hy
        have hpull : QuasiPlurisubharmonicAt
            (fun z => generatorLog Q (Φ.toFun (P z))) (e.val y) := by
          exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
            (coordinateDomain_isOpen hπ.1 e d) (coordinateMap_contDiffOn hπ.1 e d) hDy
            (by simpa only [hP0] using hQt)
        have h := (LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
          Ψ hpull).mpr hintS
        have heq : (generatorLog (fun i => Q i ∘ η)) =
            (fun z => generatorLog Q (η z)) := by
          funext z
          rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
          rfl
        rw [heq]
        simpa only [hΨ0, η, ft, f, P, e, d] using h
    have hfamilyLog : (generatorLog (fun i z => H i (e.val.symm (Ψ.invFun z)))) =ᶠ[𝓝 0]
        (fun z => w (P (Ψ.invFun z))) := by
      filter_upwards [eventually_all.mpr hfamily] with z hz
      have heq : (fun i => H i (e.val.symm (Ψ.invFun z))) = (fun i => A i (η z)) := by
        funext i
        exact (hz i).symm
      simp only [generatorLog_eq_log_sum, w]
      exact congrArg (fun v : Fin s → ℂ => ENNReal.log (ENNReal.ofReal (∑ i, ‖v i‖ ^ 2))) heq
    have hsource' := hsource.congr hfamilyLog EventuallyEq.rfl
    have hpull : QuasiPlurisubharmonicAt (fun z => w (P z)) (e.val y) := by
      exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
        (coordinateDomain_isOpen hπ.1 e d) (coordinateMap_contDiffOn hπ.1 e d) hDy
        (by simpa only [hP0] using hw)
    exact (LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
      Ψ hpull).mp (by simpa only [hΨ0, ft] using hsource')
  have h := (multiplier_comp_toFun_iff Φ (by simpa only [h0] using hAw)).mp htarget
  simpa only [h0] using h

end
end SGPT.Foundations.Analysis.Pending.FiniteFamilyTruncationModificationTransport
