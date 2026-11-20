import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace

set_option autoImplicit false

/-!
# Actual native Darvas rooftop continuity and closed pointwise order

Xia SGPT PDF0165 Lemma 4.3.4, equation (4.23), on the actual E1 subtype.
Actual one-slot rooftop contraction gives joint Lipschitz continuity.
Its native metric limit identity then produces closedness of the actual
pointwise order, as used on PDF0166 in the tail-rooftop completeness route.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasRooftopContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual genuine finite-energy rooftop as an operation on its actual subtype. -/
def finiteEnergyRooftop (omega : KahlerBackground n M)
    (u v : ModelFiniteEnergyPotential θ φ hφ) : ModelFiniteEnergyPotential θ φ hφ :=
  ⟨rooftop θ u.val v.val, relativeFiniteEnergyPreceq_rooftop omega u.property v.property⟩

/-- The actual source joint rooftop distance estimate on the native metric subtype. -/
theorem dist_rooftop_le_add_dist (omega : KahlerBackground n M)
    (u v u' v' : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    dist (finiteEnergyRooftop omega u v) (finiteEnergyRooftop omega u' v') ≤
      dist u u' + dist v v' := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  have hfirst : dist (finiteEnergyRooftop omega u v) (finiteEnergyRooftop omega u' v) ≤ dist u u' :=
    SingularModelDarvasContraction.relativeD1_rooftop_le omega u.property u'.property v.property
  have hsecond : dist (finiteEnergyRooftop omega u' v) (finiteEnergyRooftop omega u' v') ≤ dist v v' := by
    change relativeD1 θ φ hφ (rooftop θ u'.val v.val) (rooftop θ u'.val v'.val) ≤
      relativeD1 θ φ hφ v.val v'.val
    rw [rooftop_comm θ u'.val v.val, rooftop_comm θ u'.val v'.val]
    exact SingularModelDarvasContraction.relativeD1_rooftop_le omega v.property v'.property u'.property
  exact (dist_triangle _ (finiteEnergyRooftop omega u' v) _).trans
    (add_le_add hfirst hsecond)

/-- Actual rooftop is two-Lipschitz for the native maximum product metric. -/
theorem finiteEnergyRooftop_lipschitzWith (omega : KahlerBackground n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    LipschitzWith 2 (fun p : ModelFiniteEnergyPotential θ φ hφ × ModelFiniteEnergyPotential θ φ hφ =>
      finiteEnergyRooftop omega p.1 p.2) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_ofNat, Prod.dist_eq]
  have h := dist_rooftop_le_add_dist omega p.1 p.2 q.1 q.2
  have h1 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have h2 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  linarith

/-- Actual joint rooftop continuity explicitly uses the native Darvas topology. -/
theorem finiteEnergyRooftop_continuous (omega : KahlerBackground n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Continuous (fun p : ModelFiniteEnergyPotential θ φ hφ × ModelFiniteEnergyPotential θ φ hφ =>
      finiteEnergyRooftop omega p.1 p.2) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  exact (finiteEnergyRooftop_lipschitzWith (θ := θ) (φ := φ) (hφ := hφ) omega).continuous

/-- Actual pointwise order is closed under genuine native Darvas limits along any nontrivial filter. -/
theorem le_of_tendsto_of_eventually_le {I : Type*} {F : Filter I} [NeBot F]
    (omega : KahlerBackground n M)
    {ui vi : I → ModelFiniteEnergyPotential θ φ hφ}
    {u v : ModelFiniteEnergyPotential θ φ hφ} :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui F (𝓝 u) → Tendsto vi F (𝓝 v) →
      (∀ᶠ i in F, (ui i).val ≤ (vi i).val) → u.val ≤ v.val := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hu hv hle
  have hroof := ((finiteEnergyRooftop_continuous (θ := θ) (φ := φ) (hφ := hφ) omega).tendsto (u, v)).comp
    (hu.prodMk_nhds hv)
  have hleft : Tendsto (fun i => finiteEnergyRooftop omega (ui i) (vi i)) F (𝓝 u) :=
    hu.congr' (by
      filter_upwards [hle] with i hi
      apply Subtype.ext
      exact (rooftop_eq_left_of_le (ui i).property.1.plurisubharmonic hi).symm)
  have heq : finiteEnergyRooftop omega u v = u := tendsto_nhds_unique hroof hleft
  have hval := congrArg Subtype.val heq
  exact hval.symm ▸ rooftop_le_right u.property.1.plurisubharmonic v.property.1.plurisubharmonic

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasRooftopContinuity
