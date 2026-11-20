import SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-! # The actual original differential/codifferential graph-energy Hilbert space
All eight complete mathematical proofs precede this SOURCE. The literal
joint smooth graph is closed internally; actual smooth adjoint tests prove
that its first projection is injective. Original smooth topologies remain.
-/

noncomputable section

open Set Filter WithLp
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianGraphEnergy

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianKahlerVolumeCalibration NaturalHermitianCodifferential
  NaturalOriginalGradedExteriorProduct ProductTestForms

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The literal three-element index of the original joint graph. -/
inductive GraphSlot
  | base | derivative | coderivative
  deriving DecidableEq

instance : Fintype GraphSlot where
  elems := {.base, .derivative, .coderivative}
  complete i := by cases i <;> simp

def graphDegree (q : ℕ) : GraphSlot → ℕ
  | .base => q
  | .derivative => q + 1
  | .coderivative => q - 1

/-- The actual finite heterogeneous L² product of the original Hilbert completions. -/
abbrev GraphSpace (w : KahlerBackground n M) (q : ℕ) :=
  PiLp 2 (fun i : GraphSlot => HilbertFormL2 w.form.val w.isKahler.1 (graphDegree q i))

/-- The literal original differential/codifferential graph, with no supplied operator witness. -/
def smoothGraph (w : KahlerBackground n M) (α : SmoothRealForm n M q) : GraphSpace w q :=
  toLp 2 (fun
    | .base => toHilbertFormL2 w.form.val w.isKahler.1 α
    | .derivative => toHilbertFormL2 w.form.val w.isKahler.1 α.exteriorDerivative
    | .coderivative => toHilbertFormL2 w.form.val w.isKahler.1
        (coderivativeForm w.form.val w.isKahler.1 q α))

/-- Original targetwise operator linearity becomes literal linearity in the genuine Hilbert graph. -/
def smoothGraphLinear (w : KahlerBackground n M) (q : ℕ) :
    SmoothRealForm n M q →ₗ[ℝ] GraphSpace w q where
  toFun := smoothGraph w
  map_add' α β := by
    ext i
    cases i with
    | base => exact (toHilbertFormL2Linear w.form.val w.isKahler.1 q).map_add α β
    | derivative =>
      change toHilbertFormL2 _ _ (α + β).exteriorDerivative = _
      rw [(toHilbertFormL2_eq_iff _ _ _ _).mpr
        (exteriorDerivative_add_geometricallyEq α β)]
      exact (toHilbertFormL2Linear w.form.val w.isKahler.1 (q + 1)).map_add _ _
    | coderivative =>
      change toHilbertFormL2 _ _ (coderivativeForm _ _ q (α + β)) = _
      rw [(toHilbertFormL2_eq_iff _ _ _ _).mpr
        (coderivativeForm_add_geometricallyEq w.form.val w.isKahler.1 q α β)]
      exact (toHilbertFormL2Linear w.form.val w.isKahler.1 (q - 1)).map_add _ _
  map_smul' c α := by
    ext i
    cases i with
    | base => exact (toHilbertFormL2Linear w.form.val w.isKahler.1 q).map_smul c α
    | derivative =>
      change toHilbertFormL2 _ _ (c • α).exteriorDerivative = _
      rw [exteriorDerivative_const_smul]
      exact (toHilbertFormL2Linear w.form.val w.isKahler.1 (q + 1)).map_smul _ _
    | coderivative =>
      change toHilbertFormL2 _ _ (coderivativeForm _ _ q (c • α)) = _
      rw [(toHilbertFormL2_eq_iff _ _ _ _).mpr
        (coderivativeForm_smul_geometricallyEq w.form.val w.isKahler.1 q c α)]
      exact (toHilbertFormL2Linear w.form.val w.isKahler.1 (q - 1)).map_smul _ _

theorem smoothGraphLinear_apply (w : KahlerBackground n M) (α : SmoothRealForm n M q) :
    smoothGraphLinear w q α = smoothGraph w α := rfl

private theorem graph_inner (w : KahlerBackground n M) (x y : GraphSpace w q) :
    inner ℝ x y = inner ℝ (x .base) (y .base) +
      inner ℝ (x .derivative) (y .derivative) +
      inner ℝ (x .coderivative) (y .coderivative) := by
  have hu : (Finset.univ : Finset GraphSlot) =
      {.base, .derivative, .coderivative} := by
    ext i
    cases i <;> simp
  rw [PiLp.inner_apply, hu]
  simp [Finset.sum_insert, add_assoc]

theorem smoothGraph_inner (w : KahlerBackground n M) (α β : SmoothRealForm n M q) :
    inner ℝ (smoothGraph w α) (smoothGraph w β) =
      integralPair w.form.val w.isKahler.1 α β +
      integralPair w.form.val w.isKahler.1 α.exteriorDerivative β.exteriorDerivative +
      integralPair w.form.val w.isKahler.1
        (coderivativeForm w.form.val w.isKahler.1 q α)
        (coderivativeForm w.form.val w.isKahler.1 q β) := by
  rw [graph_inner]
  change inner ℝ (toHilbertFormL2 _ _ α) (toHilbertFormL2 _ _ β) +
    inner ℝ (toHilbertFormL2 _ _ α.exteriorDerivative)
      (toHilbertFormL2 _ _ β.exteriorDerivative) +
    inner ℝ (toHilbertFormL2 _ _ (coderivativeForm _ _ q α))
      (toHilbertFormL2 _ _ (coderivativeForm _ _ q β)) = _
  rw [hilbert_inner, hilbert_inner, hilbert_inner]

theorem smoothGraph_norm_sq (w : KahlerBackground n M) (α : SmoothRealForm n M q) :
    ‖smoothGraph w α‖ ^ 2 =
      integralPair w.form.val w.isKahler.1 α α +
      integralPair w.form.val w.isKahler.1 α.exteriorDerivative α.exteriorDerivative +
      integralPair w.form.val w.isKahler.1
        (coderivativeForm w.form.val w.isKahler.1 q α)
        (coderivativeForm w.form.val w.isKahler.1 q α) := by
  rw [← real_inner_self_eq_norm_sq, smoothGraph_inner]

theorem smoothGraph_eq_iff (w : KahlerBackground n M) (α β : SmoothRealForm n M q) :
    smoothGraph w α = smoothGraph w β ↔ α.GeometricallyEq β := by
  constructor
  · intro h
    exact (toHilbertFormL2_eq_iff _ _ _ _).mp (congrArg (fun x : GraphSpace w q => x .base) h)
  · intro h
    ext i
    cases i with
    | base => exact (toHilbertFormL2_eq_iff _ _ _ _).mpr h
    | derivative => exact (toHilbertFormL2_eq_iff _ _ _ _).mpr h.exteriorDerivative
    | coderivative =>
      exact (toHilbertFormL2_eq_iff _ _ _ _).mpr
        (coderivativeForm_geometricallyEq w.form.val w.isKahler.1 q h)

theorem smoothGraph_eq_zero_iff (w : KahlerBackground n M) (α : SmoothRealForm n M q) :
    smoothGraph w α = 0 ↔ α.GeometricallyEq 0 := by
  rw [← (smoothGraphLinear w q).map_zero]
  exact smoothGraph_eq_iff w α 0

/-- The actual range of the original smooth joint graph. -/
def smoothGraphRange (w : KahlerBackground n M) (q : ℕ) : Submodule ℝ (GraphSpace w q) :=
  (smoothGraphLinear w q).range

/-- The literal closed graph-energy submodule, constructed internally. -/
def graphEnergySubmodule (w : KahlerBackground n M) (q : ℕ) : Submodule ℝ (GraphSpace w q) :=
  (smoothGraphRange w q).topologicalClosure

/-- The native Hilbert subtype of the actual internally closed graph. -/
abbrev GraphEnergy (w : KahlerBackground n M) (q : ℕ) := graphEnergySubmodule w q

theorem graphEnergy_complete (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace (GraphEnergy w q) := by
  change CompleteSpace ((smoothGraphRange w q).topologicalClosure)
  infer_instance

/-- The genuine original smooth core in the constructed energy space. -/
def smoothEnergyLinear (w : KahlerBackground n M) (q : ℕ) :
    SmoothRealForm n M q →ₗ[ℝ] GraphEnergy w q :=
  (smoothGraphLinear w q).codRestrict (graphEnergySubmodule w q)
    (fun α => (smoothGraphRange w q).le_topologicalClosure ⟨α, rfl⟩)

/-- The actual bounded native coordinate projection on the closed energy subtype. -/
def energyProjection (w : KahlerBackground n M) (q : ℕ) (i : GraphSlot) :
    GraphEnergy w q →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 (graphDegree q i) :=
  (PiLp.proj 2 _ i).comp (graphEnergySubmodule w q).subtypeL

abbrev energyInclusion (w : KahlerBackground n M) (q : ℕ) := energyProjection w q .base
abbrev energyDerivative (w : KahlerBackground n M) (q : ℕ) := energyProjection w q .derivative
abbrev energyCoderivative (w : KahlerBackground n M) (q : ℕ) := energyProjection w q .coderivative

theorem energyProjection_norm_le (w : KahlerBackground n M) (u : GraphEnergy w q) (i : GraphSlot) :
    ‖energyProjection w q i u‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val i

theorem energy_inner (w : KahlerBackground n M) (u v : GraphEnergy w q) :
    inner ℝ u v = inner ℝ (energyInclusion w q u) (energyInclusion w q v) +
      inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
      inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) :=
  graph_inner w u.val v.val

theorem energyInclusion_smooth (w : KahlerBackground n M) (α : SmoothRealForm n M q) :
    energyInclusion w q (smoothEnergyLinear w q α) =
      toHilbertFormL2 w.form.val w.isKahler.1 α := rfl

theorem energyDerivative_smooth (w : KahlerBackground n M) (α : SmoothRealForm n M q) :
    energyDerivative w q (smoothEnergyLinear w q α) =
      toHilbertFormL2 w.form.val w.isKahler.1 α.exteriorDerivative := rfl

theorem energyCoderivative_smooth (w : KahlerBackground n M) (α : SmoothRealForm n M q) :
    energyCoderivative w q (smoothEnergyLinear w q α) =
      toHilbertFormL2 w.form.val w.isKahler.1 (coderivativeForm w.form.val w.isKahler.1 q α) := rfl

/-- The genuine original derivative adjoint identity extends by an actual closed scalar equal-locus. -/
theorem energyDerivative_adjoint (w : KahlerBackground n M) (u : GraphEnergy w q)
    (β : SmoothRealForm n M (q + 1)) :
    inner ℝ (energyDerivative w q u) (toHilbertFormL2 w.form.val w.isKahler.1 β) =
      inner ℝ (energyInclusion w q u)
        (toHilbertFormL2 w.form.val w.isKahler.1
          (castSmoothForm (show (q + 1) - 1 = q by omega)
            (coderivativeForm w.form.val w.isKahler.1 (q + 1) β))) := by
  let b := toHilbertFormL2 w.form.val w.isKahler.1 β
  let c := toHilbertFormL2 w.form.val w.isKahler.1
    (castSmoothForm (show (q + 1) - 1 = q by omega)
      (coderivativeForm w.form.val w.isKahler.1 (q + 1) β))
  let E : Set (GraphSpace w q) := {x | inner ℝ (x .derivative) b = inner ℝ (x .base) c}
  have hE : IsClosed E := isClosed_eq
    ((PiLp.proj (𝕜 := ℝ) 2
      (fun i : GraphSlot => HilbertFormL2 w.form.val w.isKahler.1 (graphDegree q i)) GraphSlot.derivative).continuous.inner (𝕜 := ℝ) continuous_const)
    ((PiLp.proj (𝕜 := ℝ) 2
      (fun i : GraphSlot => HilbertFormL2 w.form.val w.isKahler.1 (graphDegree q i)) GraphSlot.base).continuous.inner (𝕜 := ℝ) continuous_const)
  have hrange : (smoothGraphRange w q : Set (GraphSpace w q)) ⊆ E := by
    rintro x ⟨α, rfl⟩
    exact hilbert_smooth_image_formal_adjoint w q α β
  exact closure_minimal hrange hE u.property

/-- The genuine positive-degree original codifferential adjoint tests extend to the actual closure. -/
theorem energyCoderivative_adjoint (w : KahlerBackground n M) (p : ℕ)
    (u : GraphEnergy w (p + 1)) (γ : SmoothRealForm n M p) :
    inner ℝ (energyCoderivative w (p + 1) u) (toHilbertFormL2 w.form.val w.isKahler.1 γ) =
      inner ℝ (energyInclusion w (p + 1) u)
        (toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative) := by
  let b := toHilbertFormL2 w.form.val w.isKahler.1 γ
  let c := toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative
  let E : Set (GraphSpace w (p + 1)) :=
    {x | inner ℝ (x .coderivative) b = inner ℝ (x .base) c}
  have hE : IsClosed E := isClosed_eq
    ((PiLp.proj (𝕜 := ℝ) 2
      (fun i : GraphSlot => HilbertFormL2 w.form.val w.isKahler.1 (graphDegree (p + 1) i)) GraphSlot.coderivative).continuous.inner (𝕜 := ℝ) continuous_const)
    ((PiLp.proj (𝕜 := ℝ) 2
      (fun i : GraphSlot => HilbertFormL2 w.form.val w.isKahler.1 (graphDegree (p + 1) i)) GraphSlot.base).continuous.inner (𝕜 := ℝ) continuous_const)
  have hrange : (smoothGraphRange w (p + 1) : Set (GraphSpace w (p + 1))) ⊆ E := by
    rintro x ⟨β, rfl⟩
    have hadj := hilbert_smooth_image_formal_adjoint w p γ β
    change inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative)
      (toHilbertFormL2 w.form.val w.isKahler.1 β) =
      inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 γ)
        (toHilbertFormL2 w.form.val w.isKahler.1
          (coderivativeForm w.form.val w.isKahler.1 (p + 1) β)) at hadj
    change inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1
      (coderivativeForm w.form.val w.isKahler.1 (p + 1) β))
      (toHilbertFormL2 w.form.val w.isKahler.1 γ) =
      inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 β)
        (toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative)
    calc
      inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1
          (coderivativeForm w.form.val w.isKahler.1 (p + 1) β))
          (toHilbertFormL2 w.form.val w.isKahler.1 γ) =
          inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 γ)
            (toHilbertFormL2 w.form.val w.isKahler.1
              (coderivativeForm w.form.val w.isKahler.1 (p + 1) β)) :=
        real_inner_comm (toHilbertFormL2 w.form.val w.isKahler.1 γ)
          (toHilbertFormL2 w.form.val w.isKahler.1
            (coderivativeForm w.form.val w.isKahler.1 (p + 1) β))
      _ = inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative)
          (toHilbertFormL2 w.form.val w.isKahler.1 β) := hadj.symm
      _ = inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 β)
          (toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative) :=
        real_inner_comm (toHilbertFormL2 w.form.val w.isKahler.1 β)
          (toHilbertFormL2 w.form.val w.isKahler.1 γ.exteriorDerivative)
  exact closure_minimal hrange hE u.property

/-- The entire constructed zero-degree last projection vanishes by the actual defining branch. -/
theorem energyCoderivative_zero_degree (w : KahlerBackground n M) (u : GraphEnergy w 0) :
    energyCoderivative w 0 u = 0 := by
  let E : Set (GraphSpace w 0) := {x | x .coderivative = 0}
  have hE : IsClosed E := isClosed_eq
    (PiLp.proj (𝕜 := ℝ) 2 _ GraphSlot.coderivative).continuous continuous_const
  have hrange : (smoothGraphRange w 0 : Set (GraphSpace w 0)) ⊆ E := by
    rintro x ⟨α, rfl⟩
    change toHilbertFormL2 w.form.val w.isKahler.1
      (coderivativeForm w.form.val w.isKahler.1 0 α) = 0
    simp only [coderivativeForm]
    exact (toHilbertFormL2Linear w.form.val w.isKahler.1 0).map_zero
  exact closure_minimal hrange hE u.property

private theorem energy_eq_zero_of_inclusion_eq_zero (w : KahlerBackground n M)
    (u : GraphEnergy w q) (hu : energyInclusion w q u = 0) : u = 0 := by
  have hd : energyDerivative w q u = 0 := by
    let H := HilbertFormL2 w.form.val w.isKahler.1 (q + 1)
    have hcont : Continuous (fun y : H => inner ℝ (energyDerivative w q u) y) :=
      (continuous_const : Continuous (fun _ : H => energyDerivative w q u)).inner
        (𝕜 := ℝ) (continuous_id : Continuous (fun y : H => y))
    have horth : ∀ y : H, inner ℝ (energyDerivative w q u) y = 0 := by
      intro y
      exact (toHilbertFormL2_denseRange w.form.val w.isKahler.1 (q + 1)).induction_on
        (p := fun z => inner ℝ (energyDerivative w q u) z = 0) y
        (isClosed_eq hcont continuous_const)
        (fun β => by
          have hadj := energyDerivative_adjoint w u β
          rw [hu, inner_zero_left] at hadj
          exact hadj)
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp (horth (energyDerivative w q u))
  have hc : energyCoderivative w q u = 0 := by
    cases q with
    | zero => exact energyCoderivative_zero_degree w u
    | succ p =>
      let H := HilbertFormL2 w.form.val w.isKahler.1 p
      have hcont : Continuous (fun y : H => inner ℝ (energyCoderivative w (p + 1) u) y) :=
        (continuous_const : Continuous (fun _ : H => energyCoderivative w (p + 1) u)).inner
          (𝕜 := ℝ) (continuous_id : Continuous (fun y : H => y))
      have horth : ∀ y : H, inner ℝ (energyCoderivative w (p + 1) u) y = 0 := by
        intro y
        exact (toHilbertFormL2_denseRange w.form.val w.isKahler.1 p).induction_on
          (p := fun z => inner ℝ (energyCoderivative w (p + 1) u) z = 0) y
          (isClosed_eq hcont continuous_const)
          (fun γ => by
            have hadj := energyCoderivative_adjoint w p u γ
            rw [hu, inner_zero_left] at hadj
            exact hadj)
      exact (inner_self_eq_zero (𝕜 := ℝ)).mp (horth (energyCoderivative w (p + 1) u))
  apply Subtype.ext
  ext i
  cases i with
  | base => exact hu
  | derivative => exact hd
  | coderivative => exact hc

/-- Genuine joint closability is a theorem of the actual closed smooth graph, not a premise. -/
theorem energyInclusion_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (energyInclusion w q) := by
  intro u v h
  apply sub_eq_zero.mp
  apply energy_eq_zero_of_inclusion_eq_zero w
  rw [map_sub, h, sub_self]

/-- The actual original smooth joint graph has dense image in its internally constructed closure. -/
theorem smoothEnergy_denseRange (w : KahlerBackground n M) (q : ℕ) :
    DenseRange (smoothEnergyLinear w q) := by
  change Dense (range (smoothEnergyLinear w q))
  rw [Subtype.dense_iff]
  have himage : (Subtype.val : GraphEnergy w q → GraphSpace w q) ''
      range (smoothEnergyLinear w q) = range (smoothGraph w) := by
    ext x
    constructor
    · rintro ⟨y, ⟨α, rfl⟩, rfl⟩
      exact ⟨α, rfl⟩
    · rintro ⟨α, rfl⟩
      exact ⟨smoothEnergyLinear w q α, ⟨α, rfl⟩, rfl⟩
  intro x hx
  change x ∈ closure (range (smoothGraph w)) at hx
  exact (congrArg closure himage).symm ▸ hx

/-- The actual graph inclusion has dense range in the original Hilbert space. -/
theorem energyInclusion_denseRange (w : KahlerBackground n M) (q : ℕ) :
    DenseRange (energyInclusion w q) := by
  apply (toHilbertFormL2_denseRange w.form.val w.isKahler.1 q).mono
  rintro x ⟨α, rfl⟩
  exact ⟨smoothEnergyLinear w q α, rfl⟩

/-- Genuine original smooth approximants are internally produced in the actual graph norm. -/
theorem exists_original_smooth_approximants (w : KahlerBackground n M) (u : GraphEnergy w q) :
    ∃ α : ℕ → SmoothRealForm n M q,
      Tendsto (fun j => smoothEnergyLinear w q (α j)) atTop (𝓝 u) ∧
      Tendsto (fun j => toHilbertFormL2 w.form.val w.isKahler.1 (α j))
        atTop (𝓝 (energyInclusion w q u)) ∧
      Tendsto (fun j => toHilbertFormL2 w.form.val w.isKahler.1 (α j).exteriorDerivative)
        atTop (𝓝 (energyDerivative w q u)) ∧
      Tendsto (fun j => toHilbertFormL2 w.form.val w.isKahler.1
        (coderivativeForm w.form.val w.isKahler.1 q (α j)))
        atTop (𝓝 (energyCoderivative w q u)) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (smoothEnergy_denseRange w q u)
  choose α hα using hv
  have hJ : Tendsto (fun j => smoothEnergyLinear w q (α j)) atTop (𝓝 u) := by
    simpa only [hα] using hlim
  refine ⟨α, hJ, ?_, ?_, ?_⟩
  · exact ((energyInclusion w q).continuous.tendsto u).comp hJ
  · exact ((energyDerivative w q).continuous.tendsto u).comp hJ
  · exact ((energyCoderivative w q).continuous.tendsto u).comp hJ

end SGPT.Foundations.Analysis.Pending.NaturalHermitianGraphEnergy
