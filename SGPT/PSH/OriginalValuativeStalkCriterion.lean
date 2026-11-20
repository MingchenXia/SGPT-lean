import SGPT.Foundations.Analysis.Pending.UniformLocalCanonicalNecessity
import Mathlib.Data.ENat.Lattice
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison
import SGPT.Foundations.Analysis.Pending.ManifoldPointTruncationCoordinateMembership
import SGPT.Foundations.Analysis.Pending.FiniteFamilyStrictTruncationStability
import SGPT.Foundations.Analysis.Pending.NormalCrossings
import SGPT.Foundations.Analysis.Pending.AnalyticModificationJacobianMultiplierGerms
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
import SGPT.Foundations.Analysis.Pending.SNCPrincipalPositiveCoordinateComponents
import SGPT.Foundations.Analysis.Pending.AdmissibleSNCJacobianNormalForm
import SGPT.Foundations.Analysis.Pending.PointCenteredPrimeGermReaders
import SGPT.PSH.SourceSNCCoordinateOrders
import SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
import SGPT.Foundations.Analysis.Pending.MultiplierPullbackNonzero
import SGPT.Foundations.Analysis.Pending.CenteredPrimeSNCCoordinateReaders
import SGPT.Foundations.Analysis.Pending.SNCLogarithmicGenericCoordinateOrders
import SGPT.Foundations.Analysis.Pending.RawManifoldFullMultiplierFamily
import SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalModification
import SGPT.Foundations.Analysis.Pending.FiniteGermIdealPullbackGenerators






/-! An independently named actual fibre reader of ORIGINAL local functions.
The mathematical statements and complete proofs precede this file in
fibre-reader.tex. No equality with the source's printed ord_E is asserted. -/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalFibreReader

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance

universe u

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y} {x : X}

/-- The complete actual fibre and every actual flattening; only local F at x. -/
def fibreOrder
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x) : ℕ∞ :=
  ⨅ y : {y : Y // y ∈ E ∧ π y = x},
    ⨅ Φ : DivisorFlattening (m := m) E y.val,
      pullbackNormalOrder hπ Φ F (by rw [y.property.2]; exact hF)

/-- Exact original germ equality suffices at every actual fibre point. -/
theorem fibreOrder_congr
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) {F G : X → ℂ}
    (hF : HolomorphicAt (m + 1) F x) (hG : HolomorphicAt (m + 1) G x)
    (hFG : F =ᶠ[𝓝 x] G) : fibreOrder hπ E x F hF = fibreOrder hπ E x G hG := by
  apply iInf_congr
  intro y
  apply iInf_congr
  intro Φ
  apply pullbackNormalOrder_congr
  simpa only [y.property.2] using hFG

/-- No point reading or minimum certificate replaces this full actual infimum. -/
theorem fibreOrder_le
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (y : Y) (hy : y ∈ E) (hyx : π y = x) (Φ : DivisorFlattening (m := m) E y) :
    fibreOrder hπ E x F hF ≤
      pullbackNormalOrder hπ Φ F (by rw [hyx]; exact hF) := by
  exact iInf_le_of_le (⟨y, hy, hyx⟩ : {y : Y // y ∈ E ∧ π y = x}) (iInf_le _ Φ)

/-- Actual chart inverse transport proves nonzero translated germs. -/
theorem chartTranslatedGerm_ne_zero_of_frequently
    (y : Y) (F : Y → ℂ) (hF : HolomorphicAt (m + 1) F y)
    (hFnon : ∃ᶠ z in 𝓝 y, F z ≠ 0) :
    chartTranslatedGerm y y (mem_chart_source _ y) F hF ≠ 0 := by
  intro hzero
  let e := chartAt (ComplexModel (m + 1)) y
  have htranslated : (fun w : ComplexModel (m + 1) => F (e.symm (w + e y)))
      =ᶠ[𝓝 0] fun _ => 0 := by
    unfold chartTranslatedGerm translatedGerm at hzero
    rw [← HolGerm.mk_zero] at hzero
    exact HolGerm.mk_eq_mk_iff.mp hzero
  have hT : Tendsto (fun z : Y => e z - e y) (𝓝 y) (𝓝 0) := by
    simpa only [sub_self] using
      ((e.continuousAt (mem_chart_source _ y)).tendsto.sub_const (e y))
  have hzeroF : ∀ᶠ z in 𝓝 y, F z = 0 := by
    filter_upwards [hT.eventually htranslated, e.open_source.mem_nhds (mem_chart_source _ y)]
      with z hz hzs
    simpa only [sub_add_cancel, e.left_inv hzs] using hz
  exact (hFnon.and_eventually hzeroF).exists.elim fun _ hz => hz.1 hz.2

/-- A zero original germ is infinity; no nonempty-fibre premise is needed. -/
theorem fibreOrder_eq_top_of_zero
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (hzero : F =ᶠ[𝓝 x] fun _ => 0) : fibreOrder hπ E x F hF = ⊤ := by
  rw [fibreOrder_congr hπ E x hF (holomorphicAt_const (n := m + 1) 0) hzero]
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  intro Φ
  change ⊤ ≤ normalOrder Φ 0
  rw [normalOrder_zero]

/-- Original centre membership and genuine modification noncollapse manufacture finiteness. -/
theorem fibreOrder_ne_top
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hx : x ∈ π '' E) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) : fibreOrder hπ E x F hF ≠ ⊤ := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  have hFy : HolomorphicAt (m + 1) F (π y) := by rw [hyx]; exact hF
  have hFnony : ∃ᶠ z in 𝓝 (π y), F z ≠ 0 := by rw [hyx]; exact hFnon
  have hcomp := hFy.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hn := chartTranslatedGerm_ne_zero_of_frequently y (F ∘ π) hcomp
    (MultiplierPullbackNonzero.frequently_comp_ne_zero hπ y hFy hFnony)
  have hfinite : pullbackNormalOrder hπ Φ F hFy ≠ ⊤ := normalOrder_ne_top Φ hn
  exact ne_top_of_le_ne_top hfinite (fibreOrder_le hπ E x F hF y hy hyx Φ)

end SGPT.Foundations.Analysis.Pending.LocalFibreReader

namespace SGPT.PSH.FibreCoordinateThreshold

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps
  FirstPass.BlowupSequences DemaillyApproximantDivisorialLelong
  FixedGermNormalOrder HolomorphicGermReducednessBridge DivisorialChangeOfVariables

universe u

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y} {x : X} {y : Y}

/-- Actual local factorizations bound the full original fibre reader; its
finiteness is proved before the natural readback is used. -/
theorem fibreOrder_finite_and_weighted_bound_of_same_coordinates
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) (hy : y ∈ E) (hyx : π y = x)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) y) y))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) y).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) y) y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0)
    (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
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
    LocalFibreReader.fibreOrder hπ E x F hF ≠ ⊤ ∧
      (LocalFibreReader.fibreOrder hπ E x F hF).toNat +
        IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE ≤ b j + d j + 1 := by
  obtain ⟨Ψ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  have hFy : HolomorphicAt (m + 1) F (π y) := by rw [hyx]; exact hF
  have hw := SameCoordinateOrder.weighted_coordinate_order_add_one
    hπ hE hy Ψ Φ hsrc h0 j hflat F hFy b d K L hK hL hL0 hFfactor hnot hJac
  have hle : LocalFibreReader.fibreOrder hπ E x F hF +
      (IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℕ∞) ≤
        ((b j + d j + 1 : ℕ) : ℕ∞) := by
    calc
      _ ≤ pullbackNormalOrder hπ Ψ F hFy +
          (IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℕ∞) :=
        add_le_add (LocalFibreReader.fibreOrder_le hπ E x F hF y hy hyx Ψ) le_rfl
      _ = _ := hw.symm
  have hB : LocalFibreReader.fibreOrder hπ E x F hF ≤ ((b j + d j + 1 : ℕ) : ℕ∞) :=
    (le_add_of_nonneg_right (zero_le)).trans hle
  have hf : LocalFibreReader.fibreOrder hπ E x F hF ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hB
  refine ⟨hf, ?_⟩
  have hcast := (ENat.natCast_toNat_eq_self).mpr hf
  rw [← hcast] at hle
  exact_mod_cast hle

end SGPT.PSH.FibreCoordinateThreshold

namespace SGPT.PSH.SamePointSNC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves
  FirstPass.HolomorphicMaps FirstPass.BlowupSequences NormalCrossings HironakaAdmissibleSequence
  DivisorialChangeOfVariables HolomorphicGermReducednessBridge DemaillyApproximantDivisorialLelong

universe u

/-- On a natural actual point-supported principalization model, manufacture
ONE active-coordinate chart and its actual determinant before all original
tests. Every positive weight coordinate then supplies a genuine global prime
and the actual finite full-fibre threshold, without any incoming order data. -/
theorem exists_same_point_snc_data_with_actual_prime_thresholds
    {m s : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {E₀ : List (Set X)} {Z : Set X} {π : Y → X} {E : List (Set Y)}
    (hseq : IsAdmissibleBlowupSequence (m + 1) X E₀ Z Y π E)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsSNCDivisor (m + 1) E) (D : EffectiveDivisor (m + 1) Y)
    (hsupport : D.support = ⋃ H ∈ E, H) (x : X)
    (hpoint : D.support ⊆ π ⁻¹' {x}) (y : Y) (hyx : π y = x)
    (G : Fin s → Y → ℂ) (hG : ∀ i, HolomorphicAt (m + 1) (G i) y)
    (hgen : ∀ H : Y → ℂ, D.ideal.mem y H ↔
      IsInSpanAt (n := m + 1) (· ∈ Set.range G) y H) :
    ∃ (S : Fin E.length → Finset (Fin (m + 1)))
      (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y).val y)),
      Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target ∧
      Φ.toFun ((complexChartAt (n := m + 1) y).val y) = 0 ∧
      (∀ i, y ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | y ∈ E.get i} ∧
      (∀ i, y ∈ E.get i → ∀ {z : Y}, z ∈ (complexChartAt (n := m + 1) y).val.source →
        (complexChartAt (n := m + 1) y).val z ∈ Φ.source →
        (z ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := m + 1) y).val z) ∈ coordSubspace (S i))) ∧
      ∃ (a d : Fin (m + 1) → ℕ) (η : ComplexModel (m + 1) → ℝ) (R : ℝ)
        (L : ComplexModel (m + 1) → ℂ)
        (_hL : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ L z),
        0 < R ∧ (∀ z ∈ Metric.ball (0 : ComplexModel (m + 1)) R, ContinuousAt η z) ∧
        (∀ z ∈ Metric.ball (0 : ComplexModel (m + 1)) R,
          generatorLog (fun i w => G i ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w))) z =
            (∑ j, ((2 * (a j : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) ∧
        L 0 ≠ 0 ∧
        complexJacobian (fun z => (complexChartAt (n := m + 1) (π y)).val
          (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z)))) =ᶠ[𝓝 0]
          (fun z => L z * ∏ j, z j ^ d j) ∧
        ∀ (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x), (∃ᶠ z in 𝓝 x, F z ≠ 0) →
          ∃ (b : Fin (m + 1) → ℕ) (K : ComplexModel (m + 1) → ℂ)
            (hK : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ K z),
            (fun z => F (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z)))) =ᶠ[𝓝 0]
              (fun z => K z * ∏ j, z j ^ b j) ∧
            (∀ j, ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
              (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk K hK) ∧
            ∀ j, 0 < a j → ∃ (V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y)
              (hV : IsClosedConnectedSubmanifold (m + 1) V.carrier m),
              V.dim = m ∧ y ∈ V.carrier ∧ (∀ z ∈ V.carrier, π z = x) ∧
              (∀ᶠ z in 𝓝 y, z ∈ V.carrier ↔
                Φ.toFun ((complexChartAt (n := m + 1) y).val z) j = 0) ∧
              LocalFibreReader.fibreOrder hπ V.carrier x F hF ≠ ⊤ ∧
              (LocalFibreReader.fibreOrder hπ V.carrier x F hF).toNat +
                IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hV ≤ b j + d j + 1 := by
  classical
  obtain ⟨S, Φ, hsrc, h0, hcard, hinj, hflat, a, η, R, hR, hη, hweight, hactive⟩ :=
    SNCPrincipalPositiveCoordinateComponents.exists_normal_form_with_active_components
      D E hE hsupport y G hG hgen
  obtain ⟨d, L, hL, hL0, hJac⟩ :=
    AdmissibleSNCJacobianNormalForm.exists_unit_monomial_jacobian_in_adapted_coordinates
      hseq hE y S Φ hsrc h0 hcard hflat
  refine ⟨S, Φ, hsrc, h0, hcard, hinj, hflat, a, d, η, R, L, hL,
    hR, hη, hweight, hL0, hJac, ?_⟩
  intro F hF hFnon
  have hFy : HolomorphicAt (m + 1) F (π y) := by rw [hyx]; exact hF
  have hFnony : ∃ᶠ z in 𝓝 (π y), F z ≠ 0 := by rw [hyx]; exact hFnon
  have hcomp := hFy.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hnon := MultiplierPullbackNonzero.frequently_comp_ne_zero hπ y hFy hFnony
  obtain ⟨hFT, hFTnon⟩ := ManifoldAdaptedMultiplierGermTransport.holomorphic_nonzero_comp_adapted
    y Φ h0 hcomp hnon
  obtain ⟨b, K, hK, _hKnon, hfactor, hnot⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hFT hFTnon
  refine ⟨b, K, hK, hfactor, hnot, ?_⟩
  intro j hj
  obtain ⟨i, hyH, hSj⟩ := hactive j hj
  obtain ⟨V, hdim, _hcomp, hyV, _hVH, hconn, hreg, hlocal, hcenter, _hreaders⟩ :=
    PointCenteredPrimeGermReaders.exists_global_prime_germ_reader hπ.1.continuous
      D hE hsupport hpoint i hyH
  have hV : IsClosedConnectedSubmanifold (m + 1) V.carrier m := ⟨V.isClosed_carrier, hconn, hreg⟩
  have hflatH : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (m + 1)) y).source →
      (chartAt (ComplexModel (m + 1)) y) z ∈ Φ.source →
      (z ∈ E.get i ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) y) z) j = 0) := by
    intro z hz hzΦ
    simpa only [hSj, coordSubspace, Set.mem_ofPred_eq, Finset.mem_singleton, forall_eq, complexChartAt] using
      hflat i hyH hz hzΦ
  have hflatV := SameCoordinateOrder.component_coordinate_germ y Φ j hflatH (hlocal y hyV)
  obtain ⟨hfin, hbound⟩ := FibreCoordinateThreshold.fibreOrder_finite_and_weighted_bound_of_same_coordinates
    hπ hV hyV hyx Φ hsrc h0 j hflatV F hF b d K L hK hL hL0 hfactor (hnot j) hJac
  exact ⟨V, hV, hdim, hyV, hcenter, hflatV, hfin, hbound⟩

end SGPT.PSH.SamePointSNC



set_option autoImplicit false
noncomputable section

open Set Filter Metric
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.PSH.SamePointWholePrimeReader

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus

universe u

/-- The SAME actual coordinate normal form reads the analytic infimum on the
entire actual point-centred prime for the original finite holomorphic family.
This is a raw Lelong reader, with its genuine factor two retained. -/
theorem whole_prime_generatorLog_reader_eq_coordinate
    {m s : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (x : X) (V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y)
    (hcenter : ∀ z ∈ V.carrier, π z = x) (y : Y) (hyV : y ∈ V.carrier)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := m + 1) y).val y) = 0) (j : Fin (m + 1))
    (hflat : ∀ᶠ z in 𝓝 y, z ∈ V.carrier ↔
      Φ.toFun ((complexChartAt (n := m + 1) y).val z) j = 0)
    (Q : Fin s → X → ℂ) (hQ : ∀ i, HolomorphicAt (m + 1) (Q i) x)
    (a : Fin (m + 1) → ℕ) (η : ComplexModel (m + 1) → ℝ) (R : ℝ) (hR : 0 < R)
    (hη : ∀ z ∈ ball (0 : ComplexModel (m + 1)) R, ContinuousAt η z)
    (hweight : ∀ z ∈ ball (0 : ComplexModel (m + 1)) R,
      generatorLog (fun i w => Q i (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w)))) z =
        (∑ i, ((2 * (a i : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (η z : EReal)) :
    (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => generatorLog Q (π w)) z) =
      ENNReal.ofReal (2 * (a j : ℝ)) := by
  obtain ⟨R₀, hR₀, hread⟩ :=
    CenteredPrimeSNCCoordinateReaders.exists_radius_whole_prime_coordinate_readers
      hπ x V hcenter y hyV Φ hsrc h0 j hflat
  let r := min R R₀
  have hr : 0 < r := lt_min hR hR₀
  have hsmall : ball (0 : ComplexModel (m + 1)) r ⊆ ball 0 R :=
    ball_subset_ball (min_le_left _ _)
  have hprime := (hread r hr (min_le_right _ _)).1 s Q hQ 1 zero_lt_one
  let u : ComplexModel (m + 1) → EReal := fun z =>
    generatorLog Q (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z)))
  let v : ComplexModel (m + 1) → EReal := fun z =>
    (∑ i, ((2 * (a i : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (η z : EReal)
  have hlocal : (⨅ z ∈ ball (0 : ComplexModel (m + 1)) r ∩ {z | z j = 0},
      lelongNumber (n := m + 1) u z) =
      ⨅ z ∈ ball (0 : ComplexModel (m + 1)) r ∩ {z | z j = 0},
        lelongNumber (n := m + 1) v z := by
    apply iInf_congr
    intro z
    apply iInf_congr
    intro hz
    apply LelongNumberComparison.lelongNumber_congr
    filter_upwards [isOpen_ball.mem_nhds (hsmall hz.1)] with w hw
    simpa only [u, v, generatorLog, generatorVector] using hweight w hw
  have hgeneric := SNCLogarithmicGenericCoordinateOrders.iInf_lelongNumber_coordinate_hyperplane_eq
    (fun i => 2 * (a i : ℝ)) (fun _ => by positivity) j hr (fun z hz => hη z (hsmall hz))
  have hprime' : (⨅ z ∈ V.carrier,
      lelongNumber (n := m + 1) (fun w => generatorLog Q (π w)) z) =
      ⨅ z ∈ ball (0 : ComplexModel (m + 1)) r ∩ {z | z j = 0},
        lelongNumber (n := m + 1) u z := by
    simpa only [EReal.coe_one, one_mul, u] using hprime
  exact hprime'.trans (hlocal.trans hgeneric)

end SGPT.PSH.SamePointWholePrimeReader



set_option autoImplicit false

/-! # One original multiplier family before all point truncations

Supplementary original-input producer for the fixed-germ converse of SGPT
`thm:valuativemulti`. The same native multiplier family is retained before N;
literal concatenation with coherent truncation generators manufactures a full
original truncation family and preserves the finite exponential bound. No model,
finite family, norm comparison or reader equality is an incoming certificate.
The full converse and the printed prime-order convention remain separate.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.PSH.OriginalTruncationFamilies

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences RestrictedIdealExtension IdealWeightPowers
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder

universe u

/-- Original raw QPSH data choose ONE full base family and its genuine Young
reverse test before ALL point truncations. Concatenation supplies each full
truncation family, with the SAME finite exponential constant and every future
whole-fibre raw Lelong bound. -/
theorem exists_original_full_family_before_all_point_truncations
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) {p : ℕ} (hp : 0 < p) :
    ∃ (s : ℕ) (G : Fin s → X → ℂ),
      (∀ i, HolomorphicAt (m + 1) (G i) x) ∧
      (∀ F : X → ℂ, (multiplierIdeal (n := m + 1) (p : ℝ) φ).mem x F ↔
        IsInSpanAt (n := m + 1) (· ∈ range G) x F) ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        (∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * φ z) ≤
          C * ∑ i, ENNReal.ofReal (‖G i z‖ ^ 2)) ∧
        (∀ (c δ : ℝ), 0 < c → 0 < δ → 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) →
          ∀ F : X → ℂ,
            (multiplierIdeal (n := m + 1) (c * (1 + δ) / p) (generatorLog G)).mem x F →
            (multiplierIdeal (n := m + 1) c φ).mem x F) ∧
        ∀ N : ℕ, ∃ (t : ℕ) (Q : Fin t → X → ℂ),
          (∀ i, HolomorphicAt (m + 1) (Q i) x) ∧
          (∀ F : X → ℂ,
            (sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
              (idealPow (pointIdeal (m + 1) x) N)).mem x F ↔
              IsInSpanAt (n := m + 1) (· ∈ range Q) x F) ∧
          range G ⊆ range Q ∧
          (∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * φ z) ≤
            C * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2)) ∧
          ∀ (d : ℕ) (Y : Type u) [TopologicalSpace Y]
            [ChartedSpace (ComplexModel d) Y] (π : Y → X), Continuous π →
              ∀ V : Set Y, (∀ y ∈ V, π y = x) →
                (⨅ y ∈ V, lelongNumber (n := d) (generatorLog (fun i z => Q i (π z))) y) ≤
                  ENNReal.ofReal (p : ℝ) *
                    ⨅ y ∈ V, lelongNumber (n := d) (fun z => φ (π z)) y := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hI : (multiplierIdeal (n := m + 1) (p : ℝ) φ).IsCoherent :=
    GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      (Nat.zero_lt_succ m) hφ hpr
  obtain ⟨s, G, hG, hfull, C, hC, hdom, _hGfuture, hreverse⟩ :=
    RawManifoldFullMultiplierFamily.exists_full_family_before_all_whole_fiber_bounds.{u, u}
      hφ x hp
  refine ⟨s, G, hG, hfull, C, hC, hdom, hreverse, ?_⟩
  intro N
  obtain ⟨U, hU, hxU, t, H, hH, hHfull⟩ :=
    (PointSupportedIdealPrincipalization.truncation_properties x hI N).1 x
  have hHx (i : Fin t) : HolomorphicAt (m + 1) (H i) x :=
    holomorphicAt_of_mdifferentiableOn hU (hH i) hxU
  let Q : Fin (s + t) → X → ℂ := sumFamily G H
  have hQ (i : Fin (s + t)) : HolomorphicAt (m + 1) (Q i) x := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Q, sumFamily, Fin.append_left] using hG j
    · simpa only [Q, sumFamily, Fin.append_right] using hHx j
  have hQfull (F : X → ℂ) :
      (sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
        (idealPow (pointIdeal (m + 1) x) N)).mem x F ↔
        IsInSpanAt (n := m + 1) (· ∈ range Q) x F := by
    constructor
    · intro hF
      exact IsInSpanAt.mono (fun _ h => range_right_subset_sumFamily h)
        ((hHfull x hxU F).mp hF)
    · intro hF
      apply (hHfull x hxU F).mpr
      refine IsInSpanAt.trans ?_ hF
      intro f hf
      rcases mem_range_sumFamily hf with hfG | hfH
      · obtain ⟨i, rfl⟩ := hfG
        exact (hHfull x hxU (G i)).mp
          (le_sumIdeal_left hI x (G i)
            ((hfull (G i)).mpr (isInSpanAt_self ⟨i, rfl⟩ (hG i))))
      · obtain ⟨i, rfl⟩ := hfH
        exact isInSpanAt_self ⟨i, rfl⟩ (hHx i)
  have hsum (z : X) :
      (∑ i, ENNReal.ofReal (‖G i z‖ ^ 2)) ≤
        ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2) := by
    simp only [Q, sumFamily, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    exact le_add_right le_rfl
  have hdomQ : ∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * φ z) ≤
      C * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2) := by
    filter_upwards [hdom] with z hz
    apply hz.trans
    gcongr
    exact hsum z
  refine ⟨s + t, Q, hQ, hQfull, (fun _ h => range_left_subset_sumFamily h), hdomQ, ?_⟩
  intro d Y _ _ π hπ V hcenter
  have hpoint : ∀ y ∈ V,
      lelongNumber (n := d) (generatorLog (fun i z => Q i (π z))) y ≤
        ENNReal.ofReal (p : ℝ) * lelongNumber (n := d) (fun z => φ (π z)) y := by
    intro y hy
    have ht : Tendsto π (𝓝 y) (𝓝 x) := by
      simpa only [hcenter y hy] using hπ.continuousAt.tendsto (x := y)
    exact FiniteGeneratorExponentialLelongBound.lelongNumber_generatorLog_le_scaled_of_exp_domination
      (fun i z => Q i (π z)) hpr hC (ht.eventually hdomQ)
  have hcoef : ENNReal.ofReal (p : ℝ) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hpr)
  simp_rw [ENNReal.mul_iInf_of_ne hcoef ENNReal.ofReal_ne_top]
  exact iInf_mono fun y => iInf_mono fun hy => hpoint y hy

/-- Original raw QPSH data internally produce the actual whole-source point
principalization AND the SAME full original truncation family, with full literal
generation at EVERY point of the original fibre. -/
theorem exists_original_point_principalization_with_full_family
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    let 𝔟 := sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
      (idealPow (pointIdeal (m + 1) x) N)
    𝔟.zeroLocus ⊆ ({x} : Set X) ∧
      ∃ (s : ℕ) (Q : Fin s → X → ℂ),
        (∀ i, HolomorphicAt (m + 1) (Q i) x) ∧
        (∀ F : X → ℂ, 𝔟.mem x F ↔ IsInSpanAt (n := m + 1) (· ∈ range Q) x F) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          (∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * φ z) ≤
            C * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2)) ∧
          ∃ (Y : Type u) (_ : TopologicalSpace Y)
            (_ : ChartedSpace (ComplexModel (m + 1)) Y) (_ : IsComplexManifold (m + 1) Y)
            (π : Y → X) (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y)),
            HironakaAdmissibleSequence.IsAdmissibleBlowupSequence
              (m + 1) X [] 𝔟.zeroLocus Y π E ∧
            AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π ∧
            IsProperMap π ∧ Function.Surjective π ∧
            GermIdeal.pullback (m := m + 1) π 𝔟 = D.ideal ∧
            NormalCrossings.IsSNCDivisor (m + 1) E ∧ D.support = ⋃ H ∈ E, H ∧
            D.support ⊆ π ⁻¹' ({x} : Set X) ∧
            (∀ y : Y, π y = x → ∀ F : Y → ℂ,
              D.ideal.mem y F ↔
                IsInSpanAt (n := m + 1) (· ∈ range fun i => Q i ∘ π) y F) ∧
            ∀ V : Set Y, (∀ y ∈ V, π y = x) →
              (⨅ y ∈ V, lelongNumber (n := m + 1) (generatorLog (fun i z => Q i (π z))) y) ≤
                ENNReal.ofReal (p : ℝ) *
                  ⨅ y ∈ V, lelongNumber (n := m + 1) (fun z => φ (π z)) y := by
  classical
  dsimp only
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨_sG, _G, _hG, _hGfull, C, hC, _hGdom, _hGreverse, hfamilies⟩ :=
    exists_original_full_family_before_all_point_truncations hφ x hp
  obtain ⟨s, Q, hQ, hQfull, _hGQ, hdomQ, hfuture⟩ := hfamilies N
  obtain ⟨hzero, Y, tY, cY, mY, π, D, E, hseq, hmod, hhol, hproper, hsurj,
      hpull, hE, hsupport, hpre, _hiso, _hreaders⟩ :=
    RawMultiplierGlobalModification.exists_principalization_with_global_modification hφ x hpr N
  let _ := tY
  let _ := cY
  let _ := mY
  have hpoint : D.support ⊆ π ⁻¹' ({x} : Set X) := by
    rw [hpre]
    exact preimage_mono hzero
  refine ⟨hzero, s, Q, hQ, hQfull, C, hC, hdomQ,
    Y, tY, cY, mY, π, D, E, hseq, hmod, hproper, hsurj, hpull,
    hE, hsupport, hpoint, ?_, ?_⟩
  · intro y hy F
    have hQy (i : Fin s) : HolomorphicAt (m + 1) (Q i) (π y) := by
      rw [hy]
      exact hQ i
    have hgeny (A : X → ℂ) :
        (sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
          (idealPow (pointIdeal (m + 1) x) N)).mem (π y) A ↔
          IsInSpanAt (n := m + 1) (· ∈ range Q) (π y) A := by
      rw [hy]
      exact hQfull A
    have hdict := FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun z => hhol.contMDiffAt (x := z))
      (sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
        (idealPow (pointIdeal (m + 1) x) N)) Q hQy hgeny F
    rw [hpull] at hdict
    exact hdict
  · intro V hcenter
    exact hfuture (m + 1) Y π hhol.continuous V hcenter

end SGPT.PSH.OriginalTruncationFamilies


namespace SGPT.PSH.OriginalStrictSNCIntegral

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences FirstPass.HolomorphicMaps DivisorialChangeOfVariables
  DemaillyApproximantDivisorialLelong SquaredLogLelongSourceNormalization
  SGPT.PSH.OriginalTruncationFamilies SGPT.PSH.SamePointSNC
  SGPT.PSH.SamePointWholePrimeReader
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

private theorem strict_threshold_of_extended_prime_bounds
    {p a M : ℕ} (hp : 0 < p) (ha : 0 < a) {ε q : ℝ}
    (hε : 0 < ε) (hq : q < 1 + ε) (S : ℝ≥0∞)
    (hraw : ENNReal.ofReal (2 * (a : ℝ)) ≤ ENNReal.ofReal (p : ℝ) * (2 * S))
    (hprime : ENNReal.ofReal (1 + ε) * S ≤ ENNReal.ofReal (M : ℝ)) :
    (q / (p : ℝ)) * (a : ℝ) < (M : ℝ) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (a : ℝ) ≤
      2 * (ENNReal.ofReal (p : ℝ) * S) := by
    calc
      _ = ENNReal.ofReal (2 * (a : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal (p : ℝ) * (2 * S) := hraw
      _ = _ := by ac_rfl
  have hbase : ENNReal.ofReal (a : ℝ) ≤ ENNReal.ofReal (p : ℝ) * S :=
    (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp htwo
  have hscale : ENNReal.ofReal ((1 + ε) * (a : ℝ)) ≤
      ENNReal.ofReal ((p : ℝ) * (M : ℝ)) := by
    calc
      _ = ENNReal.ofReal (1 + ε) * ENNReal.ofReal (a : ℝ) :=
        ENNReal.ofReal_mul (by linarith)
      _ ≤ ENNReal.ofReal (1 + ε) * (ENNReal.ofReal (p : ℝ) * S) := by
        gcongr
      _ = ENNReal.ofReal (p : ℝ) * (ENNReal.ofReal (1 + ε) * S) := by ac_rfl
      _ ≤ ENNReal.ofReal (p : ℝ) * ENNReal.ofReal (M : ℝ) := by
        gcongr
      _ = _ := (ENNReal.ofReal_mul hpr.le).symm
  have hreal : (1 + ε) * (a : ℝ) ≤ (p : ℝ) * (M : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hscale
  have hstrict : q * (a : ℝ) < (p : ℝ) * (M : ℝ) :=
    (mul_lt_mul_of_pos_right hq har).trans_le hreal
  have heq : (q / (p : ℝ)) * (a : ℝ) = q * (a : ℝ) / (p : ℝ) := by ring
  rw [heq, div_lt_iff₀ hpr]
  simpa only [mul_comm] using hstrict

private theorem multiplierIntegral_of_actual_coordinate_forms
    {n : ℕ} (a b d : Fin n → ℕ) {c : ℝ} (hc : 0 < c)
    (w : ComplexModel n → EReal) (f J K L : ComplexModel n → ℂ)
    (η : ComplexModel n → ℝ)
    (hK : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ K z)
    (hL : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ L z) (hL0 : L 0 ≠ 0)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt η z)
    (hw : w =ᶠ[𝓝 (0 : ComplexModel n)] (fun z =>
      (∑ j, ((2 * (a j : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)))
    (hf : f =ᶠ[𝓝 (0 : ComplexModel n)] (fun z => K z * ∏ j, z j ^ b j))
    (hJ : J =ᶠ[𝓝 (0 : ComplexModel n)] (fun z => L z * ∏ j, z j ^ d j))
    (hthreshold : ∀ j, c * (a j : ℝ) < ((b j + d j : ℕ) : ℝ) + 1) :
    MultiplierIntegrableAt w c (fun z => f z * J z) 0 volume := by
  classical
  let FM : ComplexModel n → ℂ := fun z => f z * ∏ j, z j ^ d j
  have htest : FM =ᶠ[𝓝 (0 : ComplexModel n)] (fun z => K z * ∏ j, z j ^ (b j + d j)) := by
    filter_upwards [hf] with z hz
    dsimp only [FM]
    rw [hz, mul_assoc, ← Finset.prod_mul_distrib]
    simp only [pow_add]
  have hmon := HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
    (fun j => b j + d j) (fun j => (a j : ℝ)) hc hK htest hη hthreshold
  have hactualWeight : MultiplierIntegrableAt w c FM 0 volume :=
    hmon.congr hw.symm EventuallyEq.rfl
  have hunit : MultiplierIntegrableAt w c (fun z => L z * FM z) 0 volume :=
    (ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff hL hL0).mpr hactualWeight
  have hactual : (fun z => f z * J z) =ᶠ[𝓝 (0 : ComplexModel n)] (fun z => L z * FM z) := by
    filter_upwards [hJ] with z hz
    rw [hz]
    dsimp only [FM]
    ring
  exact hunit.congr EventuallyEq.rfl hactual.symm

end SGPT.PSH.OriginalStrictSNCIntegral


namespace SGPT.PSH.OriginalStrictSNCIntegral

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences FirstPass.HolomorphicMaps DivisorialChangeOfVariables
  DemaillyApproximantDivisorialLelong SquaredLogLelongSourceNormalization
  SGPT.PSH.OriginalTruncationFamilies SGPT.PSH.SamePointSNC
  SGPT.PSH.SamePointWholePrimeReader
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

/-- The original fixed nonzero test, source weight and ONE original uniform
all-prime inequality manufacture a full truncation family, an actual whole-source
model and actual SAME-chart Jacobian-weighted integrals at EVERY original fibre
point. No model/family/coordinate/integrability certificate is incoming. -/
theorem exists_original_models_with_all_fibre_weighted_integrals
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hAll : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
      (π : Y → X) (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
      (V : Set Y) (hV : IsClosedConnectedSubmanifold (m + 1) V m) (_hx : x ∈ π '' V),
      ENNReal.ofReal (1 + ε) *
        (⨅ z ∈ V, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) ≤
          ENNReal.ofReal (((LocalFibreReader.fibreOrder hπ V x F hF).toNat +
            IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hV : ℕ) : ℝ))
    {p : ℕ} (hp : 0 < p) (q : ℝ) (hq : 0 < q) (hqε : q < 1 + ε) (N : ℕ) :
    ∃ (s : ℕ) (Q : Fin s → X → ℂ),
      (∀ i, HolomorphicAt (m + 1) (Q i) x) ∧
      (∀ H : X → ℂ,
        (RestrictedIdealExtension.sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
          (IdealWeightPowers.idealPow (GermIdealOrder.pointIdeal (m + 1) x) N)).mem x H ↔
          IsInSpanAt (n := m + 1) (· ∈ range Q) x H) ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y)
        (_ : ChartedSpace (ComplexModel (m + 1)) Y) (_ : IsComplexManifold (m + 1) Y)
        (π : Y → X)
        (_hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π),
        IsProperMap π ∧ Function.Surjective π ∧
        ∀ y : Y, π y = x →
          ∃ Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y).val y),
            Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target ∧
            Φ.toFun ((complexChartAt (n := m + 1) y).val y) = 0 ∧
            MultiplierIntegrableAt
              (fun z => generatorLog Q (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z))))
              (q / (p : ℝ))
              (fun z => F (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z))) *
                complexJacobian (fun w => (complexChartAt (n := m + 1) (π y)).val
                  (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w)))) z)
              0 volume := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 < q / (p : ℝ) := div_pos hq hpr
  obtain ⟨_hzero, s, Q, hQ, hQfull, _C, _hC, _hdom,
      Y, tY, cY, mY, π, D, E, hseq, hπ, hproper, hsurj, _hpull,
      hE, hsupport, hpoint, hDgen, hfuture⟩ :=
    exists_original_point_principalization_with_full_family hφ x hp N
  let _ := tY
  let _ := cY
  let _ := mY
  refine ⟨s, Q, hQ, hQfull, Y, tY, cY, mY, π, hπ, hproper, hsurj, ?_⟩
  intro y hyx
  have hQpull (i : Fin s) : HolomorphicAt (m + 1) (fun z => Q i (π z)) y := by
    have hi : HolomorphicAt (m + 1) (Q i) (π y) := by rw [hyx]; exact hQ i
    exact hi.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hfullPull (H : Y → ℂ) : D.ideal.mem y H ↔
      IsInSpanAt (n := m + 1) (· ∈ range fun i z => Q i (π z)) y H := by
    simpa only [Function.comp_def] using hDgen y hyx H
  obtain ⟨_S, Φ, hsrc, h0, _hcard, _hinj, _hflat,
      a, d, η, R, L, hL, hR, hη, hweight, hL0, hJac, htests⟩ :=
    exists_same_point_snc_data_with_actual_prime_thresholds
      hseq hπ hE D hsupport x hpoint y hyx (fun i z => Q i (π z)) hQpull hfullPull
  obtain ⟨b, K, hK, hfactor, _hnot, hactive⟩ := htests F hF hFnon
  have hthreshold (j : Fin (m + 1)) :
      (q / (p : ℝ)) * (a j : ℝ) < ((b j + d j : ℕ) : ℝ) + 1 := by
    by_cases haj : a j = 0
    · simpa only [haj, Nat.cast_zero, mul_zero] using
        (by positivity : (0 : ℝ) < ((b j + d j : ℕ) : ℝ) + 1)
    · obtain ⟨V, hV, _hdim, hyV, hcenter, hflatV, _hfinite, hbound⟩ :=
        hactive j (Nat.pos_of_ne_zero haj)
      have hreader := whole_prime_generatorLog_reader_eq_coordinate
        hπ.1 x V hcenter y hyV Φ hsrc h0 j hflatV Q hQ a η R hR hη hweight
      have hrawSame :
          (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => generatorLog Q (π w)) z) ≤
            ENNReal.ofReal (p : ℝ) *
              ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (φ ∘ π) z := by
        have h := hfuture V.carrier hcenter
        have hQcomp : generatorLog (fun i z => Q i (π z)) =
            (fun z => generatorLog Q (π z)) := by
          funext z
          rfl
        rw [hQcomp] at h
        simpa only [Function.comp_def] using h
      rw [hreader, iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)] at hrawSame
      have hprime := hAll Y π hπ V.carrier hV ⟨y, hyV, hyx⟩
      have hstrict : (q / (p : ℝ)) * (a j : ℝ) <
          (((LocalFibreReader.fibreOrder hπ V.carrier x F hF).toNat +
            IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hV : ℕ) : ℝ) :=
        strict_threshold_of_extended_prime_bounds hp (Nat.pos_of_ne_zero haj) hε hqε
          (⨅ z ∈ V.carrier, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) hrawSame hprime
      exact hstrict.trans_le (by exact_mod_cast hbound)
  have hball : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ ball 0 R :=
    isOpen_ball.mem_nhds (mem_ball_self hR)
  have hηnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ContinuousAt η z :=
    hball.mono fun z hz => hη z hz
  have hweightnear :
      (fun z => generatorLog Q (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun z))))
        =ᶠ[𝓝 (0 : ComplexModel (m + 1))] (fun z =>
          (∑ j, ((2 * (a j : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) := by
    filter_upwards [hball] with z hz
    simpa only [generatorLog, generatorVector] using hweight z hz
  refine ⟨Φ, hsrc, h0, ?_⟩
  exact multiplierIntegral_of_actual_coordinate_forms a b d hc _ _ _ K L η
    hK hL hL0 hηnear hweightnear hfactor hJac hthreshold

end SGPT.PSH.OriginalStrictSNCIntegral


namespace SGPT.PSH.OriginalTruncationDescent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.HolomorphicMaps FirstPass.BlowupSequences DivisorialChangeOfVariables
  DemaillyApproximantDivisorialLelong SquaredLogLelongSourceNormalization
  SGPT.PSH.OriginalStrictSNCIntegral
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

private theorem generatorLog_quasiPsh_of_near_holomorphic
    {n s : ℕ} {p : ComplexModel n} (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    QuasiPlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hUsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hG)
  have hgen : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hpU, fun i z hz => (hUsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    (plurisubharmonicAt_scaled_generatorLog hgen (show (0 : ℝ) < 1 by norm_num)).quasiPlurisubharmonicAt

private theorem preferred_jacobian_integral_of_adapted
    {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p)
    (g : ComplexModel n → ComplexModel n)
    (hg : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ g z)
    (w : ComplexModel n → EReal) (hw : QuasiPlurisubharmonicAt w p)
    (f : ComplexModel n → ℂ) (c : ℝ)
    (hint : MultiplierIntegrableAt (fun z => w (Φ.invFun z)) c
      (fun z => f (Φ.invFun z) * complexJacobian (g ∘ Φ.invFun) z) (Φ.toFun p) volume) :
    MultiplierIntegrableAt w c (fun z => f z * complexJacobian g z) p volume := by
  have hq : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have ht : Tendsto Φ.invFun (𝓝 (Φ.toFun p)) (𝓝 p) := by
    have h := (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hq)).continuousAt.tendsto
    simpa only [Φ.left_inv p Φ.center_mem_source] using h
  obtain ⟨_hJto, hJinv, _hJto0, hJinv0⟩ :=
    LocalHolomorphicMultiplierGermCovariance.jacobian_units_of_local_holomorphic_equiv Φ
  have hchain : complexJacobian (g ∘ Φ.invFun) =ᶠ[𝓝 (Φ.toFun p)]
      (fun z => complexJacobian g (Φ.invFun z) * complexJacobian Φ.invFun z) := by
    filter_upwards [ht.eventually hg, Φ.isOpen_target.mem_nhds hq] with z hgz hz
    have hIz := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
    simp only [complexJacobian]
    rw [fderiv_comp z hgz hIz, ContinuousLinearMap.det]
    change LinearMap.det ((fderiv ℂ g (Φ.invFun z)).toLinearMap.comp
      (fderiv ℂ Φ.invFun z).toLinearMap) = _
    exact LinearMap.det_comp _ _
  have htest : (fun z => f (Φ.invFun z) * complexJacobian (g ∘ Φ.invFun) z)
      =ᶠ[𝓝 (Φ.toFun p)] (fun z => complexJacobian Φ.invFun z *
        (f (Φ.invFun z) * complexJacobian g (Φ.invFun z))) := by
    filter_upwards [hchain] with z hz
    rw [hz]
    ring
  have hplain : MultiplierIntegrableAt (fun z => w (Φ.invFun z)) c
      (fun z => f (Φ.invFun z) * complexJacobian g (Φ.invFun z)) (Φ.toFun p) volume :=
    (ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff
      (φ := fun z => w (Φ.invFun z)) (c := c)
      (f := fun z => f (Φ.invFun z) * complexJacobian g (Φ.invFun z)) hJinv hJinv0).mp
        (hint.congr EventuallyEq.rfl htest)
  exact (LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    Φ (f := fun z => f z * complexJacobian g z) hw).mp hplain

end SGPT.PSH.OriginalTruncationDescent


namespace SGPT.PSH.OriginalTruncationDescent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.HolomorphicMaps FirstPass.BlowupSequences DivisorialChangeOfVariables
  DemaillyApproximantDivisorialLelong SquaredLogLelongSourceNormalization
  SGPT.PSH.OriginalStrictSNCIntegral
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

/-- Original uniform prime bounds produce original point-truncation multiplier
membership for the SAME fixed nonzero test, with no incoming model, family,
coordinate, covariance or integrability certificates. -/
theorem exists_original_truncation_family_with_multiplier_membership
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hAll : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
      (π : Y → X) (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
      (V : Set Y) (hV : IsClosedConnectedSubmanifold (m + 1) V m) (_hx : x ∈ π '' V),
      ENNReal.ofReal (1 + ε) *
        (⨅ z ∈ V, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) ≤
          ENNReal.ofReal (((LocalFibreReader.fibreOrder hπ V x F hF).toNat +
            IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hV : ℕ) : ℝ))
    {p : ℕ} (hp : 0 < p) (q : ℝ) (hq : 0 < q) (hqε : q < 1 + ε) (N : ℕ) :
    ∃ (s : ℕ) (Q : Fin s → X → ℂ),
      (∀ i, HolomorphicAt (m + 1) (Q i) x) ∧
      (∀ H : X → ℂ,
        (RestrictedIdealExtension.sumIdeal (multiplierIdeal (n := m + 1) (p : ℝ) φ)
          (IdealWeightPowers.idealPow (GermIdealOrder.pointIdeal (m + 1) x) N)).mem x H ↔
          IsInSpanAt (n := m + 1) (· ∈ range Q) x H) ∧
      (multiplierIdeal (n := m + 1) (q / (p : ℝ)) (generatorLog Q)).mem x F := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 < q / (p : ℝ) := div_pos hq hpr
  obtain ⟨s, Q, hQ, hQfull, Y, tY, cY, mY, π, hπ, _hproper, _hsurj, hAllInt⟩ :=
    exists_original_models_with_all_fibre_weighted_integrals
      hφ x F hF hFnon hε hAll hp q hq hqε N
  let _ := tY
  let _ := cY
  let _ := mY
  refine ⟨s, Q, hQ, hQfull, hF, ?_⟩
  let d := complexChartAt (n := m + 1) x
  let W := chartFunction (generatorLog Q) d
  let fBase := fun z => F (d.val.symm z)
  have hQBase (i : Fin s) : ∀ᶠ z in 𝓝 (d.val x),
      DifferentiableAt ℂ (fun z => Q i (d.val.symm z)) z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source x) (hQ i)
  have hW : QuasiPlurisubharmonicAt W (d.val x) := by
    have h := generatorLog_quasiPsh_of_near_holomorphic
      (fun i z => Q i (d.val.symm z)) hQBase
    have heq : generatorLog (fun i z => Q i (d.val.symm z)) = W := by
      funext z
      rfl
    rw [heq] at h
    exact h
  have hfBase : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ fBase z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source x) hF
  apply (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x hc hW hfBase).mpr
  intro y hyx
  let e := complexChartAt (n := m + 1) y
  let g := coordinateMap π e d
  let wY := fun z => generatorLog Q (π (e.val.symm z))
  let fY := fun z => F (π (e.val.symm z))
  have hQpull (i : Fin s) : HolomorphicAt (m + 1) (fun z => Q i (π z)) y := by
    have hi : HolomorphicAt (m + 1) (Q i) (π y) := by rw [hyx]; exact hQ i
    exact hi.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hQY (i : Fin s) : ∀ᶠ z in 𝓝 (e.val y),
      DifferentiableAt ℂ (fun z => Q i (π (e.val.symm z))) z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source y) (hQpull i)
  have hwY : QuasiPlurisubharmonicAt wY (e.val y) := by
    have h := generatorLog_quasiPsh_of_near_holomorphic
      (fun i z => Q i (π (e.val.symm z))) hQY
    have heq : generatorLog (fun i z => Q i (π (e.val.symm z))) = wY := by
      funext z
      rfl
    rw [heq] at h
    exact h
  have hpD : e.val y ∈ coordinateDomain π e d := by
    apply mem_coordinateDomain (mem_complexChartAt_source y)
    rw [hyx]
    exact mem_complexChartAt_source x
  have hDomain : ∀ᶠ z in 𝓝 (e.val y), z ∈ coordinateDomain π e d :=
    (coordinateDomain_isOpen hπ.1 e d).mem_nhds hpD
  have hg : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ g z :=
    hDomain.mono fun z hz => (coordinateMap_contDiffAt hπ.1 e d hz).differentiableAt (by simp)
  obtain ⟨Φ, _hsrc, h0, hint⟩ := hAllInt y hyx
  have hmapEq : (g ∘ Φ.invFun) =
      (fun w => (complexChartAt (n := m + 1) (π y)).val
        (π ((complexChartAt (n := m + 1) y).val.symm (Φ.invFun w)))) := by
    funext w
    simp only [g, e, d, coordinateMap, Function.comp_apply, hyx]
  have hAdapt : MultiplierIntegrableAt (fun z => wY (Φ.invFun z)) (q / (p : ℝ))
      (fun z => fY (Φ.invFun z) * complexJacobian (g ∘ Φ.invFun) z)
      (Φ.toFun (e.val y)) volume := by
    simpa only [hmapEq, wY, fY, e, h0] using hint
  have hPref := preferred_jacobian_integral_of_adapted Φ g hg wY hwY fY (q / (p : ℝ)) hAdapt
  have hround : ∀ᶠ z in 𝓝 (e.val y), d.val.symm (g z) = π (e.val.symm z) := by
    filter_upwards [hDomain] with z hz
    change d.val.symm (d.val (π (e.val.symm z))) = π (e.val.symm z)
    exact d.val.left_inv hz.2
  have hWeight : wY =ᶠ[𝓝 (e.val y)] (fun z => W (g z)) := by
    filter_upwards [hround] with z hz
    change generatorLog Q (π (e.val.symm z)) = generatorLog Q (d.val.symm (g z))
    rw [hz]
  have hTest : (fun z => fY z * complexJacobian g z) =ᶠ[𝓝 (e.val y)]
      (fun z => fBase (g z) * complexJacobian g z) := by
    filter_upwards [hround] with z hz
    change F (π (e.val.symm z)) * complexJacobian g z =
      F (d.val.symm (g z)) * complexJacobian g z
    rw [hz]
  exact hPref.congr hWeight hTest

end SGPT.PSH.OriginalTruncationDescent


namespace SGPT.PSH.OriginalTruncationDescent

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences FirstPass.HolomorphicMaps HolomorphicGermReducednessBridge
  DemaillyApproximantDivisorialLelong SquaredLogLelongSourceNormalization
  SGPT.PSH.OriginalTruncationFamilies
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

private theorem original_holomorphic_adapted {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {F : X → ℂ} (hF : HolomorphicAt n F x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z := by
  have hs := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => F) F).mp
      (InvertibleIdealQuotient.isInSpanAt_self ⟨0, rfl⟩ hF)
  exact hs.1.mono fun _ hz => hz.differentiableAt

/-- Independently named ORIGINAL nonzero-germ valuative converse. The SAME
original φ,x,F and ONE original uniform all-prime bound internally produce
all model/family/order/integral stages and return original multiplier membership.
Printed ord_E/C04 and the unrestricted quotient identification remain separate. -/
theorem mem_original_multiplierIdeal_of_uniform_all_prime_bounds
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hAll : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
      (π : Y → X) (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
      (V : Set Y) (hV : IsClosedConnectedSubmanifold (m + 1) V m) (_hx : x ∈ π '' V),
      ENNReal.ofReal (1 + ε) *
        (⨅ z ∈ V, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) ≤
          ENNReal.ofReal (((LocalFibreReader.fibreOrder hπ V x F hF).toNat +
            IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hV : ℕ) : ℝ)) :
    (multiplierIdeal (n := m + 1) 1 φ).mem x F := by
  classical
  let q₁ := 1 + 2 * ε / 3
  let q₂ := 1 + ε / 3
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hq₁ : 0 < q₁ := by dsimp [q₁]; linarith
  have hq₂ : 0 < q₂ := by dsimp [q₂]; linarith
  have hq₁ε : q₁ < 1 + ε := by dsimp [q₁]; linarith
  have hq₂q₁ : q₂ < q₁ := by dsimp [q₁, q₂]; linarith
  have hq₂eq : 1 + δ = q₂ := rfl
  obtain ⟨p, hpbig⟩ := exists_nat_gt (max (2 * (1 + δ) / δ) 1)
  have hpr : (0 : ℝ) < p := lt_trans zero_lt_one ((le_max_right _ _).trans_lt hpbig)
  have hp : 0 < p := by exact_mod_cast hpr
  have hpbound : 2 * ((1 : ℝ) * (1 + δ)) / δ ≤ (p : ℝ) := by
    simpa only [one_mul] using ((le_max_left _ _).trans_lt hpbig).le
  obtain ⟨s, G, hG, hfull, _C, _hC, _hdom, hreverse, _htrunc⟩ :=
    exists_original_full_family_before_all_point_truncations hφ x hp
  let e := complexChartAt (n := m + 1) x
  obtain ⟨Φ, _hsrc, h0⟩ := NormalCrossings.exists_centred_coordinates (n := m + 1) x
  let T : ComplexModel (m + 1) → X := fun z => e.val.symm (Φ.invFun z)
  let GT : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (T z)
  let FT : ComplexModel (m + 1) → ℂ := fun z => F (T z)
  have hGT (i : Fin s) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (GT i) z := original_holomorphic_adapted x Φ h0 (hG i)
  have hqq : q₂ / p < q₁ / p := (div_lt_div_iff_of_pos_right hpr).mpr hq₂q₁
  have hintGT : MultiplierIntegrableAt (generatorLog GT) (q₂ / p) FT 0 volume := by
    apply FiniteFamilyStrictTruncationStability.multiplierIntegrableAt_of_all_truncations
      GT hGT (div_pos hq₂ hpr) hqq
    intro N
    obtain ⟨t, Q, hQ, hQfull, hQtarget⟩ :=
      exists_original_truncation_family_with_multiplier_membership
        hφ x F hF hFnon hε hAll hp q₁ hq₁ hq₁ε N
    let QT : Fin t → ComplexModel (m + 1) → ℂ := fun i z => Q i (T z)
    have hQT (i : Fin t) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
        DifferentiableAt ℂ (QT i) z := original_holomorphic_adapted x Φ h0 (hQ i)
    refine ⟨t, QT, hQT, ?_, ?_⟩
    · intro i
      have hQmem := (hQfull (Q i)).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hQ i))
      obtain ⟨_hQi, _hGi, hm⟩ :=
        ManifoldPointTruncationCoordinateMembership.mem_coordinate_truncation_of_original_membership
          x Φ h0 (multiplierIdeal (n := m + 1) p φ) G hG hfull N hQmem
      exact hm
    · let QP : Fin t → ComplexModel (m + 1) → ℂ := fun i z => Q i (e.val.symm z)
      have hQP (i : Fin t) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (QP i) z :=
        MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
          (mem_complexChartAt_source x) (hQ i)
      have hpsh := generatorLog_quasiPsh_of_near_holomorphic QP hQP
      have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
        Φ (f := fun z => F (e.val.symm z)) (c := q₁ / p) hpsh
      have hweq : (fun z => generatorLog QP (Φ.invFun z)) = generatorLog QT := by
        funext z
        simp only [generatorLog_eq_log_sum]
        rfl
      have hintP : MultiplierIntegrableAt (generatorLog QP) (q₁ / p)
          (fun z => F (e.val.symm z)) (e.val x) volume := by
        convert hQtarget.2 using 1
        funext z
        simp only [chartFunction, generatorLog_eq_log_sum]
        rfl
      have h := hcov.mpr hintP
      simpa only [h0, hweq] using h
  let GP : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (e.val.symm z)
  have hGP (i : Fin s) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (GP i) z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source x) (hG i)
  have hpsh := generatorLog_quasiPsh_of_near_holomorphic GP hGP
  have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    Φ (f := fun z => F (e.val.symm z)) (c := q₂ / p) hpsh
  have hweq : (fun z => generatorLog GP (Φ.invFun z)) = generatorLog GT := by
    funext z
    simp only [generatorLog_eq_log_sum]
    rfl
  have hintGP : MultiplierIntegrableAt (generatorLog GP) (q₂ / p)
      (fun z => F (e.val.symm z)) (e.val x) volume := by
    apply hcov.mp
    simpa only [h0, hweq] using hintGT
  have hintG : (multiplierIdeal (n := m + 1) ((1 : ℝ) * (1 + δ) / p) (generatorLog G)).mem x F := by
    refine ⟨hF, ?_⟩
    rw [one_mul, hq₂eq]
    convert hintGP using 1
    funext z
    simp only [chartFunction, generatorLog_eq_log_sum]
    rfl
  exact hreverse 1 δ zero_lt_one hδ hpbound F hintG

end SGPT.PSH.OriginalTruncationDescent


namespace SGPT.PSH.ActualGermValuative

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci SquaredLogLelongSourceNormalization
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- An ACTUAL colimit stalk element internally supplies an original local
holomorphic representative on the SAME manifold. -/
theorem exists_original_representative (x : X) (g : actualComplexStructureStalk (n := n) x) :
    ∃ (F : X → ℂ) (hF : HolomorphicAt n F x), actualOriginalFunctionGerm x F hF = g := by
  obtain ⟨U, hxU, s, hs⟩ := (actualComplexStructureSheaf (n := n) X).presheaf.exists_germ_eq g
  refine ⟨sectionExtension U s, sectionExtension_holomorphicAt U s x hxU, ?_⟩
  rw [actualOriginalFunctionGerm_eq_section U x hxU s _ _ EventuallyEq.rfl]
  exact hs

/-- Literal original colimit germ equality reflects to an ACTUAL original
neighbourhood equality, and conversely; no germ-equality certificate is assumed. -/
theorem original_germ_eq_iff_eventuallyEq (x : X) (F G : X → ℂ)
    (hF : HolomorphicAt n F x) (hG : HolomorphicAt n G x) :
    actualOriginalFunctionGerm x F hF = actualOriginalFunctionGerm x G hG ↔ F =ᶠ[𝓝 x] G := by
  constructor
  · intro h
    have hchart := congrArg (actualStalkChartEquiv (n := n) x) h
    rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart] at hchart
    dsimp only [chartTranslatedGerm, HironakaHolomorphicJetRankLoci.translatedGerm] at hchart
    have heq := HolGerm.mk_eq_mk_iff.mp hchart
    exact original_eventuallyEq_of_preferred_chart_eventuallyEq x F G heq
  · intro h
    apply (actualStalkChartEquiv (n := n) x).injective
    rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
    exact chartTranslatedGerm_congr_original x F G hF hG h

private theorem original_zero_germ (x : X) :
    actualOriginalFunctionGerm x (fun _ : X => (0 : ℂ)) (holomorphicAt_const (n := n) 0) = 0 := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualOriginalFunctionGerm_chart, map_zero]
  rfl

private def originalRepresentativeData (x : X) (g : actualComplexStructureStalk (n := n) x) :
    Σ F : X → ℂ, {hF : HolomorphicAt n F x // actualOriginalFunctionGerm x F hF = g} :=
  Classical.choice (by
    obtain ⟨F, hF, hg⟩ := exists_original_representative x g
    exact ⟨⟨F, hF, hg⟩⟩)

private theorem representative_frequently_nonzero (x : X)
    {g : actualComplexStructureStalk (n := n) x} (hg : g ≠ 0)
    (F : X → ℂ) (hF : HolomorphicAt n F x) (hFg : actualOriginalFunctionGerm x F hF = g) :
    ∃ᶠ z in 𝓝 x, F z ≠ 0 := by
  by_contra hnon
  have hzero : F =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    change ∀ᶠ z in 𝓝 x, F z = 0
    simpa only [Filter.Frequently, not_not, not_ne_iff] using hnon
  exact hg (hFg.symm.trans
    (((original_germ_eq_iff_eventuallyEq x F _ hF (holomorphicAt_const (n := n) 0)).mpr hzero).trans
      (original_zero_germ x)))

/-- The finite cast retains infinity using the native ENat map; no default
finite or real value is assigned to an infinite original order. -/
def extendedOrderValue (B : ℕ∞) : ℝ≥0∞ := B.map (fun k : ℕ => (k : NNReal))

private theorem extendedOrderValue_finite_add {B : ℕ∞} (hB : B ≠ ⊤) (A : ℕ) :
    extendedOrderValue B + (A : ℝ≥0∞) = ENNReal.ofReal (((B.toNat + A : ℕ) : ℝ)) := by
  have hext : extendedOrderValue B = (B.toNat : ℝ≥0∞) := by
    conv_lhs => rw [← ENat.natCast_toNat hB]
    rfl
  rw [hext, ENNReal.ofReal_natCast, Nat.cast_add]

end SGPT.PSH.ActualGermValuative

namespace SGPT.PSH.ActualGermValuative

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences HironakaSmoothCentreRealDomainActualSheafStalk
  SquaredLogLelongSourceNormalization
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

variable {m : ℕ} {X Y : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X}

/-- The actual original colimit germ's COMPLETE whole-fibre/flattening order.
Its choice independence is proved below from actual original germ identities. -/
def actualGermFibreOrder
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) (g : actualComplexStructureStalk (n := m + 1) x) : ℕ∞ :=
  LocalFibreReader.fibreOrder hπ E x
    (originalRepresentativeData x g).1 (originalRepresentativeData x g).2.val

/-- The actual germ reader equals the genuine full-fibre reader of EVERY
original local holomorphic representative, not just the chosen one. -/
theorem actualGermFibreOrder_eq_original
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) (g : actualComplexStructureStalk (n := m + 1) x)
    (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x) (hFg : actualOriginalFunctionGerm x F hF = g) :
    actualGermFibreOrder hπ E x g = LocalFibreReader.fibreOrder hπ E x F hF := by
  apply LocalFibreReader.fibreOrder_congr
  exact (original_germ_eq_iff_eventuallyEq x _ F _ hF).mp
    ((originalRepresentativeData x g).2.property.trans hFg.symm)

/-- A literal ZERO actual stalk has genuinely infinite order on every actual
fibre. Empty fibres are included; no infinity readback occurs. -/
theorem actualGermFibreOrder_zero
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (x : X) : actualGermFibreOrder hπ E x 0 = ⊤ := by
  rw [actualGermFibreOrder_eq_original hπ E x 0 (fun _ => 0) (holomorphicAt_const 0)
    (original_zero_germ x)]
  exact LocalFibreReader.fibreOrder_eq_top_of_zero hπ E x _ _ EventuallyEq.rfl

/-- Actual nonzero stalk and original centre membership manufacture finiteness
BEFORE all finite conversions; no finite-order certificate is incoming. -/
theorem actualGermFibreOrder_ne_top
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (hE : IsClosedConnectedSubmanifold (m + 1) E m) (x : X) (hx : x ∈ π '' E)
    (g : actualComplexStructureStalk (n := m + 1) x) (hg : g ≠ 0) :
    actualGermFibreOrder hπ E x g ≠ ⊤ := by
  obtain ⟨F, hF, hFg⟩ := exists_original_representative x g
  rw [actualGermFibreOrder_eq_original hπ E x g F hF hFg]
  exact LocalFibreReader.fibreOrder_ne_top hπ hE hx F hF
    (representative_frequently_nonzero x hg F hF hFg)

/-- ONE fixed epsilon, before all genuine modifications/primes, stated on the
LITERAL original stalk and in the precise independently named squared-log
convention. Infinite original order remains infinite on the right. -/
def ActualGermUniformPrimeBound (φ : X → EReal) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) (ε : ℝ) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (π : Y → X) (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (hE : IsClosedConnectedSubmanifold (m + 1) E m) (_hx : x ∈ π '' E),
    ENNReal.ofReal (1 + ε) *
      (⨅ z ∈ E, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) ≤
      extendedOrderValue (actualGermFibreOrder hπ E x g) +
        (IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℝ≥0∞)

/-- ZERO actual germ satisfies the actual extended condition for EVERY epsilon,
including infinite weight readers; it never becomes a finite zero-order test. -/
theorem actualGermUniformPrimeBound_zero (φ : X → EReal) (x : X) (ε : ℝ) :
    ActualGermUniformPrimeBound (m := m) φ x 0 ε := by
  intro Y _ _ _ π hπ E hE _hx
  rw [actualGermFibreOrder_zero]
  change _ ≤ ⊤ + _
  simp only [top_add, le_top]

end SGPT.PSH.ActualGermValuative


namespace SGPT.PSH.ActualGermValuative

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences HironakaSmoothCentreRealDomainActualSheafStalk
  SquaredLogLelongSourceNormalization SGPT.PSH.OriginalTruncationDescent
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- The actual colimit-germ producer: no original representative or nonzero-germ
premise is incoming. ONE original extended all-prime condition internally gives
actual whole multiplier-stalk membership and membership of EVERY original local
representative. The genuine zero/infinity branch is retained, not read back. -/
theorem original_stalk_multiplier_membership
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (g : actualComplexStructureStalk (n := m + 1) x)
    {ε : ℝ} (hε : 0 < ε) (hAll : ActualGermUniformPrimeBound (m := m) φ x g ε) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x ∧
      ∀ (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x),
        actualOriginalFunctionGerm x F hF = g →
          (multiplierIdeal (n := m + 1) 1 φ).mem x F := by
  classical
  by_cases hg : g = 0
  · subst g
    have hzeroMem : (multiplierIdeal (n := m + 1) 1 φ).mem x (fun _ : X => (0 : ℂ)) :=
      ⟨holomorphicAt_const (n := m + 1) 0,
        multiplierIntegrableAt_zero (chartFunction φ (complexChartAt (n := m + 1) x))
          zero_lt_one ((complexChartAt (n := m + 1) x).val x) volume⟩
    refine ⟨Ideal.zero_mem _, ?_⟩
    intro F hF hFg
    have hFzero : F =ᶠ[𝓝 x] (fun _ : X => (0 : ℂ)) :=
      (original_germ_eq_iff_eventuallyEq x F _ hF (holomorphicAt_const (n := m + 1) 0)).mp
        (hFg.trans (original_zero_germ x).symm)
    exact MultiplierIdealProductComparison.mem_multiplierIdeal_congr hzeroMem hFzero.symm
  · obtain ⟨F, hF, hFg⟩ := exists_original_representative x g
    have hFnon := representative_frequently_nonzero x hg F hF hFg
    have hOriginal : ∀ (Y : Type) [TopologicalSpace Y]
        [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
        (π : Y → X) (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
        (E : Set Y) (hE : IsClosedConnectedSubmanifold (m + 1) E m) (_hx : x ∈ π '' E),
        ENNReal.ofReal (1 + ε) *
          (⨅ z ∈ E, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) ≤
            ENNReal.ofReal (((LocalFibreReader.fibreOrder hπ E x F hF).toNat +
              IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℕ) : ℝ) := by
      intro Y _ _ _ π hπ E hE hx
      have hfinite := LocalFibreReader.fibreOrder_ne_top hπ hE hx F hF hFnon
      have h := hAll Y π hπ E hE hx
      rw [actualGermFibreOrder_eq_original hπ E x g F hF hFg,
        extendedOrderValue_finite_add hfinite] at h
      exact h
    have hmem := mem_original_multiplierIdeal_of_uniform_all_prime_bounds
      hφ x F hF hFnon hε hOriginal
    refine ⟨Ideal.subset_span ⟨F, hF, hmem, hFg.symm⟩, ?_⟩
    intro G hG hGg
    have hFG : F =ᶠ[𝓝 x] G :=
      (original_germ_eq_iff_eventuallyEq x F G hF hG).mp (hFg.trans hGg.symm)
    exact MultiplierIdealProductComparison.mem_multiplierIdeal_congr hmem hFG

end SGPT.PSH.ActualGermValuative


namespace SGPT.PSH.ActualGermValuative

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci FixedGermNormalOrder DemaillyApproximantDivisorialLelong
  SquaredLogLelongSourceNormalization
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

/-- Actual WHOLE multiplier-stalk ideal membership internally gives an actual
original holomorphic multiplier representative, using the proved coherence and
WHOLE chart/actual colimit dictionaries, not an incoming reflection certificate. -/
theorem exists_original_multiplier_representative
    {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (g : actualComplexStructureStalk (n := m + 1) x)
    (hg : g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x) :
    ∃ (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x),
      actualOriginalFunctionGerm x F hF = g ∧ (multiplierIdeal (n := m + 1) 1 φ).mem x F := by
  obtain ⟨F, hF, hFg⟩ := exists_original_representative x g
  have hFstalk : actualOriginalFunctionGerm x F hF ∈
      actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x := by rw [hFg]; exact hg
  have hmap := Ideal.mem_map_of_mem (actualStalkChartEquiv (n := m + 1) x).toRingHom hFstalk
  rw [map_actualWholeSheafStalkIdeal] at hmap
  change actualStalkChartEquiv x (actualOriginalFunctionGerm x F hF) ∈
    wholeChartStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x x (mem_chart_source _ x) at hmap
  rw [actualOriginalFunctionGerm_chart] at hmap
  have hcoh := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    (Nat.zero_lt_succ m) hφ (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨U, _hU, hxU, _s, _G, hsrc, _hG, hcolumns⟩ :=
    exists_coherent_whole_stalk_original_columns (multiplierIdeal (n := m + 1) 1 φ) hcoh x
  obtain ⟨_hGT, hbridge, hwhole⟩ := hcolumns x hxU
  rw [hwhole] at hmap
  exact ⟨F, hF, hFg, (hbridge F hF).mpr hmap⟩

/-- The COMPLETE actual full-fibre/flattening infimum is attained, by actual
centre membership, smooth flattenings at EVERY fibrepoint, and extended-natural
discreteness. Neither compactness nor an incoming minimum/order certificate. -/
private theorem exists_actual_fibre_order_realizer
    {m : ℕ} {X Y : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (E : Set Y) (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (x : X) (hx : x ∈ π '' E) (F : X → ℂ) (hF : HolomorphicAt (m + 1) F x) :
    ∃ (y : Y) (_hy : y ∈ E) (hyx : π y = x) (Φ : DivisorFlattening (m := m) E y),
      LocalFibreReader.fibreOrder hπ E x F hF =
        pullbackNormalOrder hπ Φ F (by rw [hyx]; exact hF) := by
  classical
  let J := {y : Y // y ∈ E ∧ π y = x}
  have : Nonempty J := by
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy, hyx⟩⟩
  have (y : J) : Nonempty (DivisorFlattening (m := m) E y.val) :=
    DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y.val y.property.1)
  let orders (y : J) (Φ : DivisorFlattening (m := m) E y.val) : ℕ∞ :=
    pullbackNormalOrder hπ Φ F (by rw [y.property.2]; exact hF)
  obtain ⟨y, hy⟩ := ENat.exists_eq_iInf (fun y : J => ⨅ Φ, orders y Φ)
  obtain ⟨Φ, hΦ⟩ := ENat.exists_eq_iInf (orders y)
  refine ⟨y.val, y.property.1, y.property.2, Φ, ?_⟩
  change (⨅ y : J, ⨅ Φ, orders y Φ) = orders y Φ
  exact hy.symm.trans hΦ.symm

private theorem squared_strict_bound_of_raw_two {α : ℝ} (S : ℝ≥0∞) (M : ℕ)
    (h : ENNReal.ofReal α * (2 * S) < ENNReal.ofReal (2 * (M : ℝ))) :
    ENNReal.ofReal α * S < (M : ℝ≥0∞) := by
  have hL : ENNReal.ofReal α * (2 * S) = 2 * (ENNReal.ofReal α * S) := by ac_rfl
  have hR : ENNReal.ofReal (2 * (M : ℝ)) = (2 : ℝ≥0∞) * (M : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  rw [hL, hR] at h
  exact (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).mp h

/-- ONE original strong-openness margin, BEFORE ALL genuine whole-source
modifications and primes, bounds the COMPLETE original fibre/flattening order.
Every local bound and actual discrete minimum is produced internally. -/
theorem exists_uniform_original_entire_fibre_bound
    {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    {x : X} {F : X → ℂ} (hint : (multiplierIdeal (n := m + 1) 1 φ).mem x F)
    (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Y : Type) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
      (π : Y → X) (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
      (E : Set Y) (hE : IsClosedConnectedSubmanifold (m + 1) E m) (_hx : x ∈ π '' E),
      ENNReal.ofReal (1 + ε) *
        (⨅ z ∈ E, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) <
        extendedOrderValue (LocalFibreReader.fibreOrder hπ E x F hint.1) +
          (IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℝ≥0∞) := by
  obtain ⟨ε, hε, hmodels⟩ :=
    UniformLocalCanonicalNecessity.exists_uniform_canonical_local_bound hφ hint hFnon
  refine ⟨ε, hε, ?_⟩
  intro Y _ _ _ π hπ E hE hx
  obtain ⟨y, _hy, hyx, Φ, hmin⟩ := exists_actual_fibre_order_realizer hπ E hE x hx F hint.1
  obtain ⟨b, hb, hbound⟩ := hmodels Y π hπ E hE y hyx Φ
  have hB : LocalFibreReader.fibreOrder hπ E x F hint.1 = (b : ℕ∞) := hmin.trans hb
  rw [iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)] at hbound
  simp only [mul_one] at hbound
  have hs := squared_strict_bound_of_raw_two _ _ hbound
  rw [hB]
  change ENNReal.ofReal (1 + ε) *
    (⨅ z ∈ E, squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) <
      (b : ℝ≥0∞) + (IntrinsicJacobianCoefficient.representedLogDiscrepancy hπ hE : ℝ≥0∞)
  rw [← Nat.cast_add]
  exact hs

end SGPT.PSH.ActualGermValuative


namespace SGPT.PSH.ActualGermValuative

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  FirstPass.BlowupSequences HironakaSmoothCentreRealDomainActualSheafStalk
open Set Filter
open scoped Topology Manifold ENNReal ContDiff

/-- Actual ORIGINAL multiplier-stalk membership manufactures ONE epsilon BEFORE
ALL whole-source modifications/primes and the ENTIRE original fibre. Actual
representatives, original membership reflection, local bounds, complete-infimum
attainment and exact squared normalization are all produced internally. The
actual zero/infinity branch uses no finite/real readback; no compactness,
prime-bound/local-agreement/output certificate is an additional premise. -/
theorem exists_uniform_all_prime_bound_of_original_stalk_membership
    {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (x : X) (g : actualComplexStructureStalk (n := m + 1) x)
    (hg : g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x) :
    ∃ ε : ℝ, 0 < ε ∧ ActualGermUniformPrimeBound (m := m) φ x g ε := by
  by_cases hzero : g = 0
  · subst g
    exact ⟨1, zero_lt_one, actualGermUniformPrimeBound_zero (m := m) φ x 1⟩
  · obtain ⟨F, hF, hFg, hmem⟩ := exists_original_multiplier_representative hφ x g hg
    have hFnon := representative_frequently_nonzero x hzero F hF hFg
    obtain ⟨ε, hε, hfull⟩ := exists_uniform_original_entire_fibre_bound hφ hmem hFnon
    refine ⟨ε, hε, ?_⟩
    intro Y _ _ _ π hπ E hE hx
    rw [actualGermFibreOrder_eq_original hπ E x g F hF hFg]
    exact (hfull Y π hπ E hE hx).le

end SGPT.PSH.ActualGermValuative
