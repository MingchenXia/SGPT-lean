import SGPT.Foundations.Analysis.Pending.CurrentSmoothBottChernChoiceIndependence

set_option autoImplicit false

/-! A genuine real-linear smooth Bott--Chern class map for the original
signed closed type-(1,1) current subspace, in the fixed original normalization.
Full BP statements and ENTIRE proofs precede this source. No incoming class,
scalar potential, finite mass, positivity or global continuity certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  FiniteScalarDistributionGluing CurrentSmoothBottChernChoiceIndependence
  OpenSmoothFormDistributionReflection

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

/-- The actual original signed currents with their closedness and type, no
potential or class field. The real-degree bound is genuine. -/
def closedOneOneSubmodule : Submodule ℝ (GlobalCurrent n M (degreeTwo hn)) where
  carrier := {T | T.IsClosed b ∧ T.IsTypeOneOne b hn}
  zero_mem' := by
    refine ⟨GlobalCurrent.isClosed_zero b, ?_⟩
    intro e v w
    rw [GlobalCurrent.coefficients_zero]
    rfl
  add_mem' := fun hT hU => ⟨hT.1.add b hU.1, hT.2.add b hU.2⟩
  smul_mem' := fun c _ hT => ⟨hT.1.smul b c, hT.2.smul b c⟩

/-- Elements of the natural original closed type-(1,1) subspace. -/
abbrev ClosedOneOneCurrent := ↥(closedOneOneSubmodule (M := M) b hn)

private theorem ddC_zero {V : Opens (ComplexModel n)} :
    ddC (0 : 𝓓'(V, ℝ)) = 0 := by
  ext v : 1
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv,ddC_apply]
  simp

private theorem ddC_add {V : Opens (ComplexModel n)} (R S : 𝓓'(V, ℝ)) :
    ddC (R + S) = ddC R + ddC S := by
  ext v : 1
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv,AlternatingMap.add_apply,ddC_apply,ddC_apply,ddC_apply]
  simp only [map_add,smul_sub,smul_add]
  abel

private theorem ddC_smul {V : Opens (ComplexModel n)} (c : ℝ) (R : 𝓓'(V, ℝ)) :
    ddC (c • R) = c • ddC R := by
  ext v : 1
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv,AlternatingMap.smul_apply,ddC_apply,ddC_apply]
  ext φ
  simp only [map_smul,smul_sub,_root_.smul_apply,sub_apply,smul_eq_mul]
  ring

omit [IsComplexManifold n M] in
private theorem compatible_add
    (R S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) (hS : ScalarFamilyCompatible S) :
    ScalarFamilyCompatible (fun e => R e + S e) := by
  intro e f η θ hrel
  change R e (TestFunction.monoCLM ℝ η) + S e (TestFunction.monoCLM ℝ η) =
    R f (TestFunction.monoCLM ℝ θ) + S f (TestFunction.monoCLM ℝ θ)
  rw [hR e f η θ hrel,hS e f η θ hrel]

omit [IsComplexManifold n M] in
private theorem compatible_smul
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) (c : ℝ) :
    ScalarFamilyCompatible (fun e => c • R e) := by
  intro e f η θ hrel
  change c * R e (TestFunction.monoCLM ℝ η) = c * R f (TestFunction.monoCLM ℝ θ)
  rw [hR e f η θ hrel]

private theorem smoothFormDistribution_add (σ τ : ClosedRealOneOneForm n M)
    (e : ComplexChart n M) :
    smoothFormDistribution b (σ + τ).val e =
      smoothFormDistribution b σ.val e + smoothFormDistribution b τ.val e := by
  ext v φ
  have hσ : Integrable (fun z => φ z • σ.val.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b σ.val e)
  have hτ : Integrable (fun z => φ z • τ.val.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b τ.val e)
  rw [AlternatingMap.add_apply,add_apply,smoothFormDistribution_apply,
    smoothFormDistribution_apply,smoothFormDistribution_apply]
  simp only [ClosedRealOneOneForm.coeff_add,smul_add]
  rw [integral_add hσ hτ]
  rfl

private theorem smoothFormDistribution_smul (σ : ClosedRealOneOneForm n M)
    (c : ℝ) (e : ComplexChart n M) :
    smoothFormDistribution b (c • σ).val e = c • smoothFormDistribution b σ.val e := by
  ext v φ
  rw [AlternatingMap.smul_apply,_root_.smul_apply,smoothFormDistribution_apply,
    smoothFormDistribution_apply]
  simp only [ClosedRealOneOneForm.coeff_smul]
  have hfun : (fun z => φ z • (c • σ.val.coeff e z)) =
      (fun z => c • (φ z • σ.val.coeff e z)) := by
    funext z
    exact smul_comm _ _ _
  rw [hfun,integral_smul]
  rfl

private theorem coefficients_smooth (σ : ClosedRealOneOneForm n M)
    (e : ComplexChart n M) :
    (GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val).coefficients b e =
      smoothFormDistribution b σ.val e := by
  change fromLocalCurrent b (degreeTwo hn)
    (toLocalCurrent b (degreeTwo hn) (smoothFormDistribution b σ.val e)) = _
  exact CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) _

/-- The ORIGINAL smooth global current has internally proved closedness and
full type(1,1), using actual open-domain form/test integrals. -/
def smoothClosedCurrent (σ : ClosedRealOneOneForm n M) : ClosedOneOneCurrent (M := M) b hn := by
  refine ⟨GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val, ?_, ?_⟩
  · intro e
    rw [coefficients_smooth]
    exact (isClosed_regularForm_iff b.addHaar (σ.val.coeff e) (σ.val.smooth e)).mpr
      (σ.property.1 e)
  · intro e v w
    rw [coefficients_smooth]
    ext φ
    rw [smoothFormDistribution_apply,smoothFormDistribution_apply]
    have hi : Integrable (fun z => φ z • σ.val.coeff e z) b.addHaar :=
      φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
        (smoothForm_coeff_locallyIntegrable b σ.val e)
    change (formEvaluationCLM ![Complex.I • v,Complex.I • w])
        (∫ z, φ z • σ.val.coeff e z ∂b.addHaar) =
      (formEvaluationCLM ![v,w]) (∫ z, φ z • σ.val.coeff e z ∂b.addHaar)
    rw [← (formEvaluationCLM ![Complex.I • v,Complex.I • w]).integral_comp_comm hi,
      ← (formEvaluationCLM ![v,w]).integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [map_smul,formEvaluationCLM_apply]
    by_cases hz : z ∈ e.val.target
    · rw [σ.property.2 e z hz v w]
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (φ.tsupport_subset ht))
      rw [hφ,zero_smul,zero_smul]

variable [CompactSpace M]

private def chosenSmoothRepresentative (T : ClosedOneOneCurrent (M := M) b hn) :
    ClosedRealOneOneForm n M :=
  Classical.choose (exists_unique_smooth_class_of_closed_current b hn T.val
    T.property.1 T.property.2)

private theorem chosen_reading (T : ClosedOneOneCurrent (M := M) b hn) :
    ∃ R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ),
      ScalarFamilyCompatible R ∧ ∀ e,
        T.val.coefficients b e =
          smoothFormDistribution b (chosenSmoothRepresentative b hn T).val e + ddC (R e) := by
  obtain ⟨R,hR,hread,_hunique⟩ :=
    Classical.choose_spec (exists_unique_smooth_class_of_closed_current b hn T.val
      T.property.1 T.property.2)
  exact ⟨R,hR,hread⟩

/-- The class is selected from ORIGINAL T, not from an incoming class or
representation certificate. Its independence is proved on every native reading. -/
def bottChernClass (T : ClosedOneOneCurrent (M := M) b hn) : RealBottChern n M :=
  RealBottChern.ofRepresentative (chosenSmoothRepresentative b hn T)

/-- Any actual full native scalar reading gives the SAME class-map value. -/
theorem bottChernClass_eq_of_native_reading (T : ClosedOneOneCurrent (M := M) b hn)
    (σ : ClosedRealOneOneForm n M)
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R)
    (hread : ∀ e, T.val.coefficients b e = smoothFormDistribution b σ.val e + ddC (R e)) :
    bottChernClass b hn T = RealBottChern.ofRepresentative σ := by
  obtain ⟨S,hS,hSread,hunique⟩ :=
    Classical.choose_spec (exists_unique_smooth_class_of_closed_current b hn T.val
      T.property.1 T.property.2)
  exact hunique σ R hR hread

private theorem bottChernClass_add (T U : ClosedOneOneCurrent (M := M) b hn) :
    bottChernClass b hn (T + U) = bottChernClass b hn T + bottChernClass b hn U := by
  obtain ⟨R,hR,hreadR⟩ := chosen_reading b hn T
  obtain ⟨S,hS,hreadS⟩ := chosen_reading b hn U
  let σ := chosenSmoothRepresentative b hn T
  let τ := chosenSmoothRepresentative b hn U
  have hread (e : ComplexChart n M) :
      (T + U).val.coefficients b e = smoothFormDistribution b (σ + τ).val e +
        ddC (R e + S e) := by
    change (T.val + U.val).coefficients b e = _
    rw [GlobalCurrent.coefficients_add,hreadR e,hreadS e,
      smoothFormDistribution_add,ddC_add]
    abel
  rw [bottChernClass_eq_of_native_reading b hn (T + U) (σ + τ)
    (fun e => R e + S e) (compatible_add R S hR hS) hread]
  exact RealBottChern.ofRepresentative_add σ τ

private theorem bottChernClass_smul (T : ClosedOneOneCurrent (M := M) b hn) (c : ℝ) :
    bottChernClass b hn (c • T) = c • bottChernClass b hn T := by
  obtain ⟨R,hR,hreadR⟩ := chosen_reading b hn T
  let σ := chosenSmoothRepresentative b hn T
  have hread (e : ComplexChart n M) :
      (c • T).val.coefficients b e = smoothFormDistribution b (c • σ).val e +
        ddC (c • R e) := by
    change (c • T.val).coefficients b e = _
    rw [GlobalCurrent.coefficients_smul,hreadR e,
      smoothFormDistribution_smul,ddC_smul,smul_add]
  rw [bottChernClass_eq_of_native_reading b hn (c • T) (c • σ)
    (fun e => c • R e) (compatible_smul R hR c) hread]
  exact RealBottChern.ofRepresentative_smul c σ

/-- The actual original closed-current to smooth Bott--Chern map is REAL LINEAR. -/
def bottChernClassLinearMap : ClosedOneOneCurrent (M := M) b hn →ₗ[ℝ] RealBottChern n M where
  toFun := bottChernClass b hn
  map_add' := bottChernClass_add b hn
  map_smul' c T := bottChernClass_smul b hn T c

/-- On the ORIGINAL smooth global current the class map is exactly the
existing smooth representative quotient map, without incoming current proofs. -/
theorem bottChernClass_smoothClosedCurrent (σ : ClosedRealOneOneForm n M) :
    bottChernClass b hn (smoothClosedCurrent b hn σ) = RealBottChern.ofRepresentative σ := by
  apply bottChernClass_eq_of_native_reading b hn (smoothClosedCurrent b hn σ) σ
    (fun _ => 0)
  · intro e f η θ hrel
    rfl
  · intro e
    change (GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val).coefficients b e = _
    rw [coefficients_smooth,ddC_zero,add_zero]

end SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
