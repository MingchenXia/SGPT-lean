import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.OriginalPositiveCurrentThetaRepresentation

set_option autoImplicit false

/-! A specified genuine smooth class of the ORIGINAL full current supplies
its actual scalar reading internally. Original full positivity then supplies
one genuine theta-PSH potential with equality of the SAME original current.
The complete mathematical statements and ENTIRE proofs precede this source.
No incoming scalar decomposition, overlap law or representation certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  CurrentBottChernClass CurrentSmoothBottChernChoiceIndependence
  FiniteScalarDistributionGluing FiniteGlobalCurrentSmoothLocalDensity
  ThetaPotentialCurrentBottChernClass LelongPoincareDivisor
  OriginalPositiveCurrentThetaRepresentation XiaoCompatibleGlobalPotential
  NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem compatible_add
    (R S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) (hS : ScalarFamilyCompatible S) :
    ScalarFamilyCompatible (fun e => R e + S e) := by
  intro e f η ψ hrel
  change R e (TestFunction.monoCLM ℝ η) + S e (TestFunction.monoCLM ℝ η) =
    R f (TestFunction.monoCLM ℝ ψ) + S f (TestFunction.monoCLM ℝ ψ)
  rw [hR e f η ψ hrel,hS e f η ψ hrel]

private theorem ddC_add {U : Opens (ComplexModel n)} (R S : 𝓓'(U, ℝ)) :
    ddC (R + S) = ddC R + ddC S := map_add ddCLM R S

private theorem smooth_reading_of_geometric_ddC
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (θ σ : ClosedRealOneOneForm n M) (h : M → ℝ) (hh : ChartSmooth (n := n) h)
    (heq : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      σ.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    (e : ComplexChart n M) :
    smoothFormDistribution b σ.val e = smoothFormDistribution b θ.val e +
      ddC (regularDistribution b.addHaar (fun z => h (e.val.symm z))
        ((hh e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet)) := by
  rw [ddC_regular_eq_regularForm b.addHaar (hh e)]
  ext v φ
  rw [AlternatingMap.add_apply,add_apply,smoothFormDistribution_apply,
    smoothFormDistribution_apply,regularFormDistribution_apply]
  have hiθ : Integrable (fun z => φ z • θ.val.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b θ.val e)
  have hid : Integrable
      (fun z => φ z • smoothDDC (fun y => h (e.val.symm y)) z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((LogWeightFactorization.smoothDDC_contDiffOn (chartTarget e).isOpen (hh e)).continuousOn.locallyIntegrableOn
        (chartTarget e).isOpen.measurableSet)
  change (∫ z, φ z • σ.val.coeff e z ∂b.addHaar) v =
    ((∫ z, φ z • θ.val.coeff e z ∂b.addHaar) +
      (∫ z, φ z • smoothDDC (fun y => h (e.val.symm y)) z ∂b.addHaar)) v
  rw [← integral_add hiθ hid]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ e.val.target
  · rw [heq e z hz,smul_add]
  · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (φ.tsupport_subset ht))
    rw [hφ,zero_smul,zero_smul,zero_smul,add_zero]

variable [CompactSpace M]

/-- The actual original class equality itself supplies the full native scalar
reading in the specified background; the distribution/compatibility are outputs. -/
theorem exists_scalar_reading_of_class_eq
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (hn : 0 < n) (T : ClosedOneOneCurrent (M := M) b hn)
    (θ : ClosedRealOneOneForm n M)
    (hclass : bottChernClass b hn T = RealBottChern.ofRepresentative θ) :
    ∃ S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ),
      ScalarFamilyCompatible S ∧ ∀ e,
        T.val.coefficients b e = smoothFormDistribution b θ.val e + ddC (S e) := by
  obtain ⟨σ,R,hR,hread,_hunique⟩ :=
    exists_unique_smooth_class_of_closed_current b hn T.val T.property.1 T.property.2
  have hc : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative σ :=
    hclass.symm.trans (bottChernClass_eq_of_native_reading b hn T σ R hR hread)
  obtain ⟨h,hh,heq⟩ := (RealBottChern.ofRepresentative_eq_iff θ σ).mp hc
  let hL (e : ComplexChart n M) :
      LocallyIntegrableOn (fun z => h (e.val.symm z)) (chartTarget e) b.addHaar :=
    (hh e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet
  let H := fun e => regularDistribution b.addHaar (fun z => h (e.val.symm z)) (hL e)
  have hH : ScalarFamilyCompatible H := scalarFamilyCompatible_regular b.addHaar h hL
  refine ⟨fun e => R e + H e,compatible_add R H hR hH,?_⟩
  intro e
  rw [hread e,smooth_reading_of_geometric_ddC b θ σ h hh heq e,ddC_add]
  dsimp only [H]
  abel

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X]

/-- Genuine class membership and original FULL positivity internally produce
the prescribed theta potential, with equality in the original full current space. -/
theorem exists_theta_representation_of_class_eq
    (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (θ : ClosedRealOneOneForm (m + 1) X) (hT : IsFullPositive T.val)
    (hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T =
      RealBottChern.ofRepresentative θ) :
    ∃ (u : X → EReal) (hu : IsThetaPshPotential θ.val u),
      T.val = thetaPotentialCurrent θ.val u hu ∧
      ∀ e : ComplexChart (m + 1) X,
        (∀ᵐ z ∂(canonicalBasis (m + 1)).addHaar.restrict (chartTarget e),
          chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) ∧
        ∃ hL : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
          (chartTarget e) (canonicalBasis (m + 1)).addHaar,
          T.val.coefficients (canonicalBasis (m + 1)) e =
            smoothFormDistribution (canonicalBasis (m + 1)) θ.val e +
            ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
              (fun z => (chartFunction u e z).toReal) hL) := by
  obtain ⟨S,hS,hread⟩ := exists_scalar_reading_of_class_eq
    (canonicalBasis (m + 1)) (Nat.succ_pos m) T θ hclass
  have hlocal := isLocallyThetaPshDistribution_of_original_full_positive T.val hT θ S hread
  obtain ⟨u,hu,hchart⟩ := exists_isThetaPshPotential_of_isCoordinateCompatible
    (canonicalBasis (m + 1)).addHaar S
    (isCoordinateCompatible_of_scalarFamilyCompatible S hS) hlocal
  refine ⟨u,hu,?_,?_⟩
  · apply globalCurrent_ext (canonicalBasis (m + 1))
    intro e
    rw [thetaPotentialCurrent,GlobalCurrent.coefficients_add,
      coefficients_smoothGlobalCurrent,GlobalCurrentPotentials.globalDDC_coefficients,hread e]
    obtain ⟨_hfin,_hL,heq⟩ := hchart e
    change smoothFormDistribution (canonicalBasis (m + 1)) θ.val e + ddC (S e) =
      smoothFormDistribution (canonicalBasis (m + 1)) θ.val e +
        ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
          (fun z => (chartFunction u e z).toReal) _)
    rw [heq]
  · intro e
    obtain ⟨hfin,hL,heq⟩ := hchart e
    exact ⟨hfin,hL,(hread e).trans (congrArg
      (fun A => smoothFormDistribution (canonicalBasis (m + 1)) θ.val e + ddC A) heq)⟩

end SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
