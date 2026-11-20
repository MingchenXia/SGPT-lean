import SGPT.Okounkov.ThetaPotentialCurrentReader
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ENNReal

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open ActualQuasiPshPotentialSmoothCompatibility ActualOriginalPotentialOverlapSmoothDifference
open NaturalThetaPshGeometricCurrent SourceTraceRepresentativeDefinition
open SingularGlobalPOrder
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- Genuine local continuous differences on the original compact space
produce actual finite global singularity bounds in both directions. -/
theorem sameSingularity_of_local_continuous_differences
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {u v : X → EReal}
    (hdiff : ∀ x : X, ∃ (U : Set X) (h : X → ℝ), IsOpen U ∧ x ∈ U ∧
      ContinuousOn h U ∧ EqOn u (fun y => v y + (h y : EReal)) U) :
    SameSingularityTypeOn u v univ := by
  classical
  have hlocal (x : X) : ∃ (U : Set X) (C : ℝ), IsOpen U ∧ x ∈ U ∧ 0 ≤ C ∧
      ∀ y ∈ U, u y ≤ v y + (C : EReal) ∧ v y ≤ u y + (C : EReal) := by
    obtain ⟨U, h, hU, hxU, hc, heq⟩ := hdiff x
    have hcAt := (hc x hxU).continuousAt (hU.mem_nhds hxU)
    have hev : ∀ᶠ y in 𝓝 x, |h y| < |h x| + 1 :=
      hcAt.abs.eventually_lt_const (by linarith : |h x| < |h x| + 1)
    obtain ⟨V, hVs, hV, hxV⟩ := mem_nhds_iff.mp hev
    refine ⟨U ∩ V, |h x| + 1, hU.inter hV, ⟨hxU, hxV⟩,
      by positivity, ?_⟩
    intro y hy
    have hbound : |h y| ≤ |h x| + 1 := (hVs hy.2).le
    have hup : h y ≤ |h x| + 1 := (le_abs_self _).trans hbound
    have hlo : 0 ≤ h y + (|h x| + 1) := by
      have := (neg_le_abs (h y)).trans hbound
      linarith
    constructor
    · rw [heq hy.1]
      have hcoe : (h y : EReal) ≤ ((|h x| + 1 : ℝ) : EReal) := by exact_mod_cast hup
      exact add_le_add_right hcoe _
    · calc
        v y ≤ v y + ((h y + (|h x| + 1) : ℝ) : EReal) :=
          le_add_of_nonneg_right (by exact_mod_cast hlo)
        _ = u y + ((|h x| + 1 : ℝ) : EReal) := by
          rw [heq hy.1, EReal.coe_add, add_assoc]
  choose U C hU hxU hC hbound using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  let B : ℝ := ∑ x ∈ s, C x
  have hglobal (x : X) : u x ≤ v x + (B : EReal) ∧ v x ≤ u x + (B : EReal) := by
    obtain ⟨y, hy, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    have hCB : C y ≤ B := Finset.single_le_sum (fun z _ => hC z) hy
    have hcoe : (C y : EReal) ≤ (B : EReal) := by exact_mod_cast hCB
    exact ⟨(hbound y x hx).1.trans (add_le_add le_rfl hcoe),
      (hbound y x hx).2.trans (add_le_add le_rfl hcoe)⟩
  exact ⟨⟨B, fun x _ => (hglobal x).1⟩, ⟨B, fun x _ => (hglobal x).2⟩⟩


variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The same whole current gives a genuine local real potential difference
in the original manifold neighborhood, including all pole values. -/
theorem exists_local_smooth_difference_of_thetaPotentialCurrent_eq
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv)
    (p : M) :
    ∃ (O : Set M) (h : M → ℝ), IsOpen O ∧ p ∈ O ∧
      ContinuousOn h O ∧ EqOn u (fun y => v y + (h y : EReal)) O := by
  let e := complexChartAt (n := m + 1) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  obtain ⟨S, ρ, hpS, hρ, _hP, _hν⟩ := exists_psh_local_theta_reader hu e p hp
  obtain ⟨P, κ, hpP, hκ, _hQ, _hμ⟩ := exists_psh_local_theta_reader hv e p hp
  let U : Opens (ComplexModel (m + 1)) := ⟨S, hρ.1⟩
  let V : Opens (ComplexModel (m + 1)) := ⟨P, hκ.1⟩
  let F : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction u e z + (ρ z : EReal)
  let G : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction v e z + (κ z : EReal)
  obtain ⟨hFp, hFfin, _hLF, hFc, _hFs, _hFpos⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader θ hu e (W := U) ρ hρ
  obtain ⟨hGp, hGfin, _hLG, hGc, _hGs, _hGpos⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader σ hv e (W := V) κ hκ
  have hlocal {ψ : SmoothRealForm (m + 1) M 2} {f : M → EReal}
      (hf : IsThetaPshPotential ψ f) (R : Opens (ComplexModel (m + 1)))
      (hR : R ≤ chartTarget e) (r : ComplexModel (m + 1) → ℝ)
      (hr : PlurisubharmonicOn (fun z => chartFunction f e z + (r z : EReal)) R) :
      LocalQuasiPshPotentialOn (fun z => chartFunction f e z + (r z : EReal)) R := by
    refine ⟨R.isOpen, fun z hz => (hr z hz).quasiPlurisubharmonicAt, ?_⟩
    intro z hz B hB hzB
    obtain ⟨y, hy, hyfin⟩ := hf.2.exists_chart_ne_bot e (R.isOpen.inter hB)
      (fun w hw => hR hw.1) ⟨hz, hzB⟩
    exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hyfin, EReal.coe_ne_bot _⟩⟩
  let hF : LocalQuasiPshPotentialOn F U := hlocal hu U hρ.2.1 ρ hFp
  let hG : LocalQuasiPshPotentialOn G V := hlocal hv V hκ.2.1 κ hGp
  have hreadF : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
      (thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e w
        (TestFunction.monoCLM ℝ φ) = ddC (regularLocalQuasiPsh hF) w φ := by
    intro w φ
    exact congrArg (fun A => A w φ) hFc
  have hreadG : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(V, ℝ)),
      (thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e w
        (TestFunction.monoCLM ℝ φ) = ddC (regularLocalQuasiPsh hG) w φ := by
    intro w φ
    rw [heq]
    exact congrArg (fun A => A w φ) hGc
  let H := chartTransition e e
  have hcore : e.val p ∈ (U : Set _) ∩ (H.source ∩ H ⁻¹' V) := by
    refine ⟨hpS, ⟨e.val.map_source hp, ?_⟩, ?_⟩
    · change e.val.symm (e.val p) ∈ e.val.source
      rwa [e.val.left_inv hp]
    · change e.val (e.val.symm (e.val p)) ∈ P
      simpa only [e.val.left_inv hp] using hpP
  obtain ⟨_hFU, _hGH, _hddc, hdiff⟩ := exists_original_chart_smooth_difference
    (thetaPotentialCurrent θ u hu) e e hρ.2.1 hκ.2.1 hF hG hreadF hreadG
  obtain ⟨W, hW, h, hpW, hsm, _hLh, hEq, _hreg, _hlevi⟩ := hdiff (e.val p) hcore
  have hWS : (W : Set _) ⊆ S := fun _ hy => (hW hy).1
  have hWP : (W : Set _) ⊆ P := by
    intro z hz
    have hzS : z ∈ e.val.target := hρ.2.1 (hWS hz)
    have hmem : e.val (e.val.symm z) ∈ P := (hW hz).2.2
    simpa only [e.val.right_inv hzS] using hmem
  let d : ComplexModel (m + 1) → ℝ := fun z => κ z + h z - ρ z
  let O : Set M := e.val.source ∩ e.val ⁻¹' (W : Set _)
  refine ⟨O, fun y => d (e.val y), e.val.isOpen_inter_preimage W.isOpen,
    ⟨hp, hpW⟩, ?_, ?_⟩
  · have hd : ContinuousOn d W :=
      ((hκ.2.2.1.continuousOn.mono hWP).add hsm.continuous.continuousOn).sub
        (hρ.2.2.1.continuousOn.mono hWS)
    exact hd.comp (e.val.continuousOn.mono inter_subset_left) (fun _ hy => hy.2)
  · intro y hy
    have hxy := hEq hy.2
    change chartFunction u e (e.val y) + (ρ (e.val y) : EReal) =
      (chartFunction v e (e.val (e.val.symm (e.val y))) +
        (κ (e.val (e.val.symm (e.val y))) : EReal)) + (h (e.val y) : EReal) at hxy
    simp only [chartFunction, e.val.left_inv hy.1] at hxy
    have hext : u y + (ρ (e.val y) : EReal) =
        (v y + (d (e.val y) : EReal)) + (ρ (e.val y) : EReal) := by
      calc
        _ = (v y + (κ (e.val y) : EReal)) + (h (e.val y) : EReal) := hxy
        _ = v y + ((κ (e.val y) + h (e.val y) : ℝ) : EReal) := by
          rw [EReal.coe_add, add_assoc]
        _ = v y + ((d (e.val y) + ρ (e.val y) : ℝ) : EReal) := by
          congr 2
          dsimp only [d]
          ring
        _ = (v y + (d (e.val y) : EReal)) + (ρ (e.val y) : EReal) := by
          rw [EReal.coe_add, add_assoc]
    exact le_antisymm
      ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hext.le)
      ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hext.ge)

/-- The original compact manifold turns the produced local smooth
differences into genuine global finite singularity bounds. -/
theorem sameSingularity_of_thetaPotentialCurrent_eq [CompactSpace M]
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv) :
    SameSingularityTypeOn u v univ :=
  sameSingularity_of_local_continuous_differences
    (exists_local_smooth_difference_of_thetaPotentialCurrent_eq hu hv heq)

/-- Actual equal whole currents give original P-equivalence through the
genuinely produced positive common Kähler background. -/
theorem sourcePEquivalent_of_thetaPotentialCurrent_eq
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground (m + 1) M)
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv) :
    SourcePEquivalent (n := m + 1) u v := by
  have hsame := sameSingularity_of_thetaPotentialCurrent_eq hu hv heq
  exact ⟨GlobalQuasiPshPositivePDomain.sourcePOrder_of_moreSingularOn_globalQuasiPsh
      omega hu.quasiPshPotential hv.quasiPshPotential hsame.1,
    GlobalQuasiPshPositivePDomain.sourcePOrder_of_moreSingularOn_globalQuasiPsh
      omega hv.quasiPshPotential hu.quasiPshPotential hsame.2⟩

/-- Every original multiplier ideal is identical for genuine global
potentials of the same whole current; no equality of ideals is a premise. -/
theorem iEquivalent_of_thetaPotentialCurrent_eq
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground (m + 1) M)
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv) :
    IEquivalentOnManifold (n := m + 1) u v :=
  GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent
    (sourcePEquivalent_of_thetaPotentialCurrent_eq omega hu hv heq)

end SGPT.Okounkov
