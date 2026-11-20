import SGPT.Foundations.Analysis.Pending.NaturalHermitianMusicalInverse

/-! # Actual positive dual metrics and full original covector tensor transport -/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianDualMetric

open FirstPass NaturalHermitianMetricCoefficients NaturalHermitianRiemannianBundle
  NaturalHermitianMusicalInverse

variable {n : ℕ}

local instance dualNormedAddCommGroup : NormedAddCommGroup (ComplexModel n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance dualNormedSpace : NormedSpace ℝ (ComplexModel n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance bidualNormedAddCommGroup : NormedAddCommGroup ((ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bidualNormedSpace : NormedSpace ℝ ((ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Genuine continuous linear evaluation/composition conversion to the dual bilinear metric. -/
def dualMetricCLM : ((ComplexModel n →L[ℝ] ℝ) →L[ℝ] ComplexModel n) →L[ℝ]
    (ComplexModel n →L[ℝ] ℝ) →L[ℝ] (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ (ComplexModel n →L[ℝ] ℝ) (ComplexModel n)
    ((ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.apply ℝ ℝ)

/-- Literal actual covector evaluation, for every actual input inverse operator. -/
theorem dualMetricCLM_apply (K : (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ComplexModel n)
    (α β : ComplexModel n →L[ℝ] ℝ) : dualMetricCLM K α β = β (K α) := rfl

/-- Original Hermitian positivity and symmetry internally imply genuine dual positivity and symmetry. -/
theorem dualMetric_symm_positive {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) :
    (∀ α β : ComplexModel n →L[ℝ] ℝ,
      dualMetricCLM (associatedMetricCLM a).inverse α β =
        dualMetricCLM (associatedMetricCLM a).inverse β α) ∧
    ∀ α : ComplexModel n →L[ℝ] ℝ, α ≠ 0 →
      0 < dualMetricCLM (associatedMetricCLM a).inverse α α := by
  obtain ⟨hleft, -⟩ := metric_inverse_identities hp
  refine ⟨?_, ?_⟩
  · intro α β
    simp only [dualMetricCLM_apply]
    calc
      β ((associatedMetricCLM a).inverse α) =
          associatedMetricCLM a ((associatedMetricCLM a).inverse β)
            ((associatedMetricCLM a).inverse α) :=
        (congrArg (fun L : ComplexModel n →L[ℝ] ℝ =>
          L ((associatedMetricCLM a).inverse α)) (hleft β)).symm
      _ = associatedMetricCLM a ((associatedMetricCLM a).inverse α)
          ((associatedMetricCLM a).inverse β) := by
        simp only [associatedMetricCLM_apply]
        exact associatedMetric_symm hJ _ _
      _ = α ((associatedMetricCLM a).inverse β) :=
        congrArg (fun L : ComplexModel n →L[ℝ] ℝ =>
          L ((associatedMetricCLM a).inverse β)) (hleft α)
  · intro α hα
    have hu : (associatedMetricCLM a).inverse α ≠ 0 := by
      intro hu
      have h := hleft α
      rw [hu, map_zero] at h
      exact hα h.symm
    have h := congrArg (fun L : ComplexModel n →L[ℝ] ℝ =>
      L ((associatedMetricCLM a).inverse α)) (hleft α)
    rw [dualMetricCLM_apply, ← h, associatedMetricCLM_apply]
    exact hp _ hu

/-- Vector tensor transport and strict positivity genuinely produce inverse covector transport. -/
theorem metric_musical_transport {a b : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (C : ComplexModel n →L[ℝ] ComplexModel n)
    (htransport : ∀ u v : ComplexModel n,
      associatedMetricCLM a u v = associatedMetricCLM b (C u) (C v))
    (α : ComplexModel n →L[ℝ] ℝ) :
    C ((associatedMetricCLM a).inverse (α.comp C)) = (associatedMetricCLM b).inverse α := by
  have hker : C.ker = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    change C u = 0 at hu
    change u = 0
    by_contra hne
    have hzero : associatedMetricCLM a u u = 0 := by
      rw [htransport u u, hu]
      simp
    exact (ha u hne).ne' (by
      simpa only [associatedMetricCLM_apply, associatedMetric] using hzero)
  have hsurj : Function.Surjective C :=
    (LinearMap.injective_iff_surjective (f := C.toLinearMap)).mp (LinearMap.ker_eq_bot.mp hker)
  let u := (associatedMetricCLM a).inverse (α.comp C)
  have hBu : associatedMetricCLM a u = α.comp C := (metric_inverse_identities ha).1 _
  have hBCu : associatedMetricCLM b (C u) = α := by
    apply ContinuousLinearMap.ext
    intro t
    obtain ⟨v, rfl⟩ := hsurj t
    calc
      associatedMetricCLM b (C u) (C v) = associatedMetricCLM a u v := (htransport u v).symm
      _ = α (C v) := congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L v) hBu
  exact ((metric_inverse_identities hb).2 (C u)).symm.trans
    (congrArg (fun L : ComplexModel n →L[ℝ] ℝ => (associatedMetricCLM b).inverse L) hBCu)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Actual dual metric coefficients in the original operator norm and coordinates. -/
def dualMetricCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) : (ComplexModel n →L[ℝ] ℝ) →L[ℝ]
      (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ :=
  dualMetricCLM (inverseMetricCoefficients w e z)

/-- Full operator norm smoothness of the genuine original dual metric field. -/
theorem dualMetricCoefficients_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) : ContDiffOn ℝ ∞ (dualMetricCoefficients w e) e.val.target := by
  apply ContDiff.comp_contDiffOn ?_ (inverseMetricCoefficients_smooth w hw e)
  exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ComplexModel n)
    (F := (ComplexModel n →L[ℝ] ℝ) →L[ℝ] (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ)
    (by exact dualMetricCLM (n := n))

/-- Full genuine original covector tensor compatibility derived internally from original vector geometry. -/
theorem dualMetricCoefficients_transport (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source)
    (α β : ComplexModel n →L[ℝ] ℝ) :
    dualMetricCoefficients w e z (α.comp (chartTransitionDerivative e f z))
        (β.comp (chartTransitionDerivative e f z)) =
      dualMetricCoefficients w f (chartTransition e f z) α β := by
  have hzf : chartTransition e f z ∈ f.val.target := f.val.map_source hz.2
  have h := metric_musical_transport (hw e z hz.1).2 (hw f (chartTransition e f z) hzf).2
    (chartTransitionDerivative e f z) ((metric_coefficients_data w hw).2.2 e f z hz) α
  exact congrArg β h

/-- Original Hermitian data alone supplies all smooth positive compatible dual coefficients. -/
theorem exists_smooth_compatible_positive_dual_metric (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) :
    ∃ D : ComplexChart n M → ComplexModel n →
        (ComplexModel n →L[ℝ] ℝ) →L[ℝ] (ComplexModel n →L[ℝ] ℝ) →L[ℝ] ℝ,
      (∀ e z α β, D e z α β = β (inverseMetricCoefficients w e z α)) ∧
      (∀ e, ContDiffOn ℝ ∞ (D e) e.val.target) ∧
      (∀ e z, z ∈ e.val.target →
        (∀ α β, D e z α β = D e z β α) ∧
        ∀ α : ComplexModel n →L[ℝ] ℝ, α ≠ 0 → 0 < D e z α α) ∧
      ∀ e f z, z ∈ (chartTransition e f).source → ∀ α β : ComplexModel n →L[ℝ] ℝ,
        D e z (α.comp (chartTransitionDerivative e f z))
          (β.comp (chartTransitionDerivative e f z)) = D f (chartTransition e f z) α β := by
  refine ⟨dualMetricCoefficients w, ?_, dualMetricCoefficients_smooth w hw, ?_, ?_⟩
  · intro e z α β
    exact dualMetricCLM_apply _ _ _
  · intro e z hz
    exact dualMetric_symm_positive (hw e z hz).1 (hw e z hz).2
  · intro e f z hz α β
    exact dualMetricCoefficients_transport w hw e f z hz α β

end SGPT.Foundations.Analysis.Pending.NaturalHermitianDualMetric
