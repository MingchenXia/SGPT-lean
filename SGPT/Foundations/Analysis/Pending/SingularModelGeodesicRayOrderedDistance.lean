import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayDistance
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayEnergy

set_option autoImplicit false

/-!
# Actual ordered radial distance for singular-model rays

Xia SGPT PDF0175 Proposition 4.3.6, identity (4.38). Actual ordered
distance and actual ray energy linearity produce the convergent defining
distance ratio. Actual native radial energies are finite real slopes.
The genuine source construction and true eventual reader identities
recover the original model-origin source domain internally. No bounded
model, target affinity, radial identity or limit certificate is assumed.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayOrderedDistance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays SingularModelGeodesicRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual native ray energy and actual ordered distances give the defining radial distance as the difference of actual radial energies, even for different finite-energy initial slices. -/
theorem rayD1_eq_radialEnergy_sub (omega : KahlerBackground n M)
    (L K : ModelFiniteEnergyGeodesicRay θ φ hφ)
    (hle : ∀ t : ℝ, 0 ≤ t → L.rawCurve t ≤ K.rawCurve t) :
    rayD1 θ φ hφ L.rawCurve K.rawCurve =
      radialEnergy θ φ hφ K.rawCurve - radialEnergy θ φ hφ L.rawCurve := by
  let e0 := (energy θ φ hφ (L.rawCurve 0)).toReal
  let e0' := (energy θ φ hφ (K.rawCurve 0)).toReal
  let m := (energy θ φ hφ (L.rawCurve 1)).toReal - e0
  let m' := (energy θ φ hφ (K.rawCurve 1)).toReal - e0'
  have hlim : Tendsto (fun t : ℝ => (e0' - e0) / t + (m' - m)) atTop (𝓝 (m' - m)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).add_const (m' - m)
  have hT : Tendsto (fun t : ℝ => ((relativeD1 θ φ hφ
      (L.rawCurve t) (K.rawCurve t) / t : ℝ) : EReal)) atTop (𝓝 ((m' - m : ℝ) : EReal)) := by
    refine EReal.tendsto_coe.mpr (hlim.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [relativeD1_eq_sub_of_le (L.finiteEnergy_rawCurve t).1.plurisubharmonic (hle t ht.le),
      SingularModelGeodesicRayEnergy.toReal_energy_ray omega K ht.le,
      SingularModelGeodesicRayEnergy.toReal_energy_ray omega L ht.le]
    dsimp [e0, e0', m, m']
    field_simp
    ring
  rw [rayD1, hT.limUnder_eq,
    SingularModelGeodesicRayEnergy.radialEnergy_eq omega L,
    SingularModelGeodesicRayEnergy.radialEnergy_eq omega K, ← EReal.coe_sub]

omit [ConnectedSpace M] in
private theorem model_origin_reader_eq (omega : KahlerBackground n M)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ)
    {t : ℝ} (ht : 0 ≤ t) :
    (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ).rawCurve t = ℓ t := by
  change ℓ (max t 0) = ℓ t
  rw [max_eq_left ht]

/-- Genuine source rays from an arbitrary singular model satisfy the original defining identity (4.38); the actual native rays and all source/native limit transports are produced internally. -/
theorem rayD1_eq_radialEnergy_sub_of_model_origin (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayFromModel θ φ hφ ℓ')
    (hle : ∀ t : ℝ, 0 ≤ t → ℓ t ≤ ℓ' t) :
    rayD1 θ φ hφ ℓ ℓ' = radialEnergy θ φ hφ ℓ' - radialEnergy θ φ hφ ℓ := by
  let L := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ
  let K := ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hℓ'
  have h0 : L.rawCurve 0 = K.rawCurve 0 :=
    (model_origin_reader_eq omega hℓ le_rfl).trans
      (hℓ.2.trans (hℓ'.2.symm.trans (model_origin_reader_eq omega hℓ' le_rfl).symm))
  have horder : ∀ t : ℝ, 0 ≤ t → L.rawCurve t ≤ K.rawCurve t := by
    intro t ht
    rw [model_origin_reader_eq omega hℓ ht, model_origin_reader_eq omega hℓ' ht]
    exact hle t ht
  obtain ⟨m, _, hT, _, hm⟩ := SingularModelGeodesicRayDistance.exists_tendsto_rayD1 omega L K h0
  have hsourceT : Tendsto (fun t : ℝ => ((relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t : ℝ) : EReal))
      atTop (𝓝 (m : EReal)) := by
    refine EReal.tendsto_coe.mpr (hT.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [model_origin_reader_eq omega hℓ ht.le, model_origin_reader_eq omega hℓ' ht.le]
  have hdist : rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ L.rawCurve K.rawCurve :=
    hsourceT.limUnder_eq.trans hm.symm
  have hrad {η : ℝ → M → EReal} (hη : IsFiniteEnergyRayFromModel θ φ hφ η) :
      radialEnergy θ φ hφ η = radialEnergy θ φ hφ
        (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hη).rawCurve := by
    have h := SingularModelGeodesicRayEnergy.tendsto_radialEnergy omega
      (ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega hη)
    have hs := h.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [model_origin_reader_eq omega hη ht.le])
    exact hs.limUnder_eq.trans h.limUnder_eq.symm
  rw [hdist, rayD1_eq_radialEnergy_sub omega L K horder, hrad hℓ, hrad hℓ']

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayOrderedDistance
