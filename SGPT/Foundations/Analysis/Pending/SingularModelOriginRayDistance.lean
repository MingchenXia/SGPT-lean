import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayDistance

set_option autoImplicit false

/-!
# The actual metric in the original singular-model ray domain

Xia SGPT PDF0175 Theorem 4.3.4, on the genuine model-origin source
ray predicate. Actual native construction produces initial E1, true
positive-time readers transport the convergent defining radial distance,
and actual native metric laws give the genuine original source laws.
No bounded model, normalization, finite-limit or metric certificate is
assumed. Source slice separation is asserted on nonnegative times only.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelOriginRayDistance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays SingularModelGeodesicRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
private theorem model_origin_reader_eq (omega : KahlerBackground n M)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ)
    {t : ℝ} (ht : 0 ≤ t) :
    (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ).rawCurve t = ℓ t := by
  change ℓ (max t 0) = ℓ t
  rw [max_eq_left ht]

/-- Actual source construction and convergent positive-time reader ratios identify the existing source ray distance with the existing native reader distance. -/
theorem rayD1_eq_native_readers (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayFromModel θ φ hφ ℓ') :
    rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ
      (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ).rawCurve
      (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ').rawCurve := by
  let L := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ
  let K := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ'
  have h0 : L.rawCurve 0 = K.rawCurve 0 :=
    (model_origin_reader_eq omega hℓ le_rfl).trans
      (hℓ.2.trans (hℓ'.2.symm.trans (model_origin_reader_eq omega hℓ' le_rfl).symm))
  obtain ⟨m, _, hT, _, hm⟩ := SingularModelGeodesicRayDistance.exists_tendsto_rayD1 omega L K h0
  have hs : Tendsto (fun t : ℝ => ((relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t : ℝ) : EReal))
      atTop (𝓝 (m : EReal)) := by
    refine EReal.tendsto_coe.mpr (hT.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [model_origin_reader_eq omega hℓ ht.le, model_origin_reader_eq omega hℓ' ht.le]
  exact hs.limUnder_eq.trans hm.symm

/-- The actual defining radial distance has all source metric laws on genuine model-origin full singularity-order E1 rays, with no bounded-model restriction. -/
theorem rayD1_isMetric_of_model_origin (omega : KahlerBackground n M) :
    (∀ ℓ ℓ' : ℝ → M → EReal,
      IsFiniteEnergyRayFromModel θ φ hφ ℓ → IsFiniteEnergyRayFromModel θ φ hφ ℓ' →
      0 ≤ rayD1 θ φ hφ ℓ ℓ' ∧ rayD1 θ φ hφ ℓ ℓ' < ⊤) ∧
    (∀ ℓ : ℝ → M → EReal, IsFiniteEnergyRayFromModel θ φ hφ ℓ → rayD1 θ φ hφ ℓ ℓ = 0) ∧
    (∀ ℓ ℓ' : ℝ → M → EReal, rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ ℓ' ℓ) ∧
    (∀ ℓ ℓ' ℓ'' : ℝ → M → EReal,
      IsFiniteEnergyRayFromModel θ φ hφ ℓ → IsFiniteEnergyRayFromModel θ φ hφ ℓ' →
      IsFiniteEnergyRayFromModel θ φ hφ ℓ'' →
      rayD1 θ φ hφ ℓ ℓ'' ≤ rayD1 θ φ hφ ℓ ℓ' + rayD1 θ φ hφ ℓ' ℓ'') ∧
    (∀ ℓ ℓ' : ℝ → M → EReal,
      IsFiniteEnergyRayFromModel θ φ hφ ℓ → IsFiniteEnergyRayFromModel θ φ hφ ℓ' →
      rayD1 θ φ hφ ℓ ℓ' = 0 → ∀ t : ℝ, 0 ≤ t → ℓ t = ℓ' t) := by
  have hi {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) :
      (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ).rawCurve 0 = φ :=
    (model_origin_reader_eq omega hℓ le_rfl).trans hℓ.2
  have hlaws := SingularModelGeodesicRayDistance.rayD1_isMetric
    (θ := θ) (φ := φ) (hφ := hφ) omega φ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ ℓ' hℓ hℓ'
    rw [rayD1_eq_native_readers omega hℓ hℓ']
    exact hlaws.1 _ _ (hi hℓ) (hi hℓ')
  · intro ℓ hℓ
    rw [rayD1_eq_native_readers omega hℓ hℓ]
    exact hlaws.2.1 _
  · intro ℓ ℓ'
    unfold rayD1
    congr 1
    funext t
    rw [relativeD1_comm]
  · intro ℓ ℓ' ℓ'' hℓ hℓ' hℓ''
    rw [rayD1_eq_native_readers omega hℓ hℓ'', rayD1_eq_native_readers omega hℓ hℓ',
      rayD1_eq_native_readers omega hℓ' hℓ'']
    exact hlaws.2.2.2.1 _ _ _ (hi hℓ) (hi hℓ') (hi hℓ'')
  · intro ℓ ℓ' hℓ hℓ' hz t ht
    rw [rayD1_eq_native_readers omega hℓ hℓ'] at hz
    have he := hlaws.2.2.2.2 _ _ (hi hℓ) (hi hℓ') hz t ht
    rw [model_origin_reader_eq omega hℓ ht, model_origin_reader_eq omega hℓ' ht] at he
    exact he

end

end SGPT.Foundations.Analysis.Pending.SingularModelOriginRayDistance
