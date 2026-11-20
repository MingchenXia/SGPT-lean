import SGPT.Foundations.Analysis.Pending.SingularModelSourceRayInitialEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayDistance

set_option autoImplicit false

/-!
# Actual radial metric in the full original positive-time E1 ray domain

Xia SGPT PDF0174--0175. Initial E1 is genuinely produced from the
original positive-time E1 source contract. The actual native geometry,
finite defining radial limit and true source reader identities then give
convexity, ratio monotonicity and all original source metric laws at any
fixed initial potential. There is no bounded reference, normalization,
model-origin, initial-E1, linear-growth or target-limit premise.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelSourceRayDistance

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays SingularModelGeodesicRays
  SingularModelSourceRayInitialEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual source distance between any two genuine positive-time E1 rays is convex on the entire nonnegative time half-line, with initial E1 internally produced. -/
theorem convexOn_relativeD1_rays (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') :
    ConvexOn ℝ (Ici 0) (fun t => relativeD1 θ φ hφ (ℓ t) (ℓ' t)) := by
  have h := SingularModelGeodesicRayMetricGeometry.convexOn_relativeD1_rays omega
    (nativeRay omega hℓ) (nativeRay omega hℓ')
  refine ⟨h.1, fun x hx y hy p q hp hq hpq => ?_⟩
  have hz : 0 ≤ p * x + q * y := add_nonneg (mul_nonneg hp hx) (mul_nonneg hq hy)
  have hi := h.2 hx hy hp hq hpq
  simp only [smul_eq_mul] at hi ⊢
  rwa [nativeRay_reader_eq omega hℓ hz, nativeRay_reader_eq omega hℓ' hz,
    nativeRay_reader_eq omega hℓ hx, nativeRay_reader_eq omega hℓ' hx,
    nativeRay_reader_eq omega hℓ hy, nativeRay_reader_eq omega hℓ' hy] at hi

/-- Actual source common initial equality and true native reader geometry give actual positive-time ratio monotonicity for an arbitrary initial slice. -/
theorem relativeD1_rays_div_mono (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (h0 : ℓ 0 = ℓ' 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    relativeD1 θ φ hφ (ℓ s) (ℓ' s) / s ≤ relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t := by
  have hzero : (nativeRay omega hℓ).rawCurve 0 = (nativeRay omega hℓ').rawCurve 0 :=
    (nativeRay_reader_eq omega hℓ le_rfl).trans
      (h0.trans (nativeRay_reader_eq omega hℓ' le_rfl).symm)
  have hi := SingularModelGeodesicRayMetricGeometry.relativeD1_rays_div_mono omega
    (nativeRay omega hℓ) (nativeRay omega hℓ') hzero hs hst
  rwa [nativeRay_reader_eq omega hℓ hs.le, nativeRay_reader_eq omega hℓ' hs.le,
    nativeRay_reader_eq omega hℓ (hs.le.trans hst),
    nativeRay_reader_eq omega hℓ' (hs.le.trans hst)] at hi

/-- Actual source rays with any common initial slice have a genuinely finite real defining radial limit and its actual positive-time supremum bounds. -/
theorem exists_tendsto_rayD1 (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (h0 : ℓ 0 = ℓ' 0) :
    ∃ m : ℝ, 0 ≤ m ∧
      Tendsto (fun t : ℝ => relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t) atTop (𝓝 m) ∧
      (∀ t : ℝ, 0 < t → relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t ≤ m) ∧
      rayD1 θ φ hφ ℓ ℓ' = (m : EReal) := by
  have hzero : (nativeRay omega hℓ).rawCurve 0 = (nativeRay omega hℓ').rawCurve 0 :=
    (nativeRay_reader_eq omega hℓ le_rfl).trans
      (h0.trans (nativeRay_reader_eq omega hℓ' le_rfl).symm)
  obtain ⟨m, hm, hT, hle, _⟩ := SingularModelGeodesicRayDistance.exists_tendsto_rayD1 omega
    (nativeRay omega hℓ) (nativeRay omega hℓ') hzero
  have hs : Tendsto (fun t : ℝ => relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t) atTop (𝓝 m) := by
    refine hT.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [nativeRay_reader_eq omega hℓ ht.le, nativeRay_reader_eq omega hℓ' ht.le]
  refine ⟨m, hm, hs, ?_, (EReal.tendsto_coe.mpr hs).limUnder_eq⟩
  intro t ht
  have hi := hle t ht
  rwa [nativeRay_reader_eq omega hℓ ht.le, nativeRay_reader_eq omega hℓ' ht.le] at hi

/-- The actual original source ray distance equals the actual defining radial distance of the internally produced genuine native readers. -/
theorem rayD1_eq_native_readers (omega : KahlerBackground n M)
    {ℓ ℓ' : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (h0 : ℓ 0 = ℓ' 0) :
    rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ
      (nativeRay omega hℓ).rawCurve (nativeRay omega hℓ').rawCurve := by
  obtain ⟨m, _, hT, _, he⟩ := exists_tendsto_rayD1 omega hℓ hℓ' h0
  have hN : Tendsto (fun t : ℝ => relativeD1 θ φ hφ
      ((nativeRay omega hℓ).rawCurve t) ((nativeRay omega hℓ').rawCurve t) / t)
      atTop (𝓝 m) := by
    refine hT.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [nativeRay_reader_eq omega hℓ ht.le, nativeRay_reader_eq omega hℓ' ht.le]
  exact he.trans (EReal.tendsto_coe.mpr hN).limUnder_eq.symm

/-- All original source radial metric laws hold for genuine positive-time E1 rays at an arbitrary fixed initial potential; actual initial finite energy is internally produced. -/
theorem rayD1_isMetric (omega : KahlerBackground n M) (p : M → EReal) :
    (∀ ℓ ℓ' : ℝ → M → EReal,
      IsFiniteEnergyRayPreceq θ φ hφ ℓ → IsFiniteEnergyRayPreceq θ φ hφ ℓ' →
      ℓ 0 = p → ℓ' 0 = p →
      0 ≤ rayD1 θ φ hφ ℓ ℓ' ∧ rayD1 θ φ hφ ℓ ℓ' < ⊤) ∧
    (∀ ℓ : ℝ → M → EReal, IsFiniteEnergyRayPreceq θ φ hφ ℓ → rayD1 θ φ hφ ℓ ℓ = 0) ∧
    (∀ ℓ ℓ' : ℝ → M → EReal, rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ ℓ' ℓ) ∧
    (∀ ℓ ℓ' ℓ'' : ℝ → M → EReal,
      IsFiniteEnergyRayPreceq θ φ hφ ℓ → IsFiniteEnergyRayPreceq θ φ hφ ℓ' →
      IsFiniteEnergyRayPreceq θ φ hφ ℓ'' → ℓ 0 = p → ℓ' 0 = p → ℓ'' 0 = p →
      rayD1 θ φ hφ ℓ ℓ'' ≤ rayD1 θ φ hφ ℓ ℓ' + rayD1 θ φ hφ ℓ' ℓ'') ∧
    (∀ ℓ ℓ' : ℝ → M → EReal,
      IsFiniteEnergyRayPreceq θ φ hφ ℓ → IsFiniteEnergyRayPreceq θ φ hφ ℓ' →
      ℓ 0 = p → ℓ' 0 = p → rayD1 θ φ hφ ℓ ℓ' = 0 →
      ∀ t : ℝ, 0 ≤ t → ℓ t = ℓ' t) := by
  have hi {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) (h0 : ℓ 0 = p) :
      (nativeRay omega hℓ).rawCurve 0 = p := (nativeRay_reader_eq omega hℓ le_rfl).trans h0
  have hlaws := SingularModelGeodesicRayDistance.rayD1_isMetric
    (θ := θ) (φ := φ) (hφ := hφ) omega p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ ℓ' hℓ hℓ' h0 h0'
    rw [rayD1_eq_native_readers omega hℓ hℓ' (h0.trans h0'.symm)]
    exact hlaws.1 _ _ (hi hℓ h0) (hi hℓ' h0')
  · intro ℓ hℓ
    rw [rayD1_eq_native_readers omega hℓ hℓ rfl]
    exact hlaws.2.1 _
  · intro ℓ ℓ'
    unfold rayD1
    congr 1
    funext t
    rw [relativeD1_comm]
  · intro ℓ ℓ' ℓ'' hℓ hℓ' hℓ'' h0 h0' h0''
    rw [rayD1_eq_native_readers omega hℓ hℓ'' (h0.trans h0''.symm),
      rayD1_eq_native_readers omega hℓ hℓ' (h0.trans h0'.symm),
      rayD1_eq_native_readers omega hℓ' hℓ'' (h0'.trans h0''.symm)]
    exact hlaws.2.2.2.1 _ _ _ (hi hℓ h0) (hi hℓ' h0') (hi hℓ'' h0'')
  · intro ℓ ℓ' hℓ hℓ' h0 h0' hz t ht
    rw [rayD1_eq_native_readers omega hℓ hℓ' (h0.trans h0'.symm)] at hz
    have he := hlaws.2.2.2.2 _ _ (hi hℓ h0) (hi hℓ' h0') hz t ht
    rwa [nativeRay_reader_eq omega hℓ ht, nativeRay_reader_eq omega hℓ' ht] at he

end

end SGPT.Foundations.Analysis.Pending.SingularModelSourceRayDistance
