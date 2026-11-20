import SGPT.Hodge.ConeTopology
import SGPT.Okounkov.TranscendentalVolumeConcavityContinuity

/-!
# The positive cones of `H^{1,1}(X, ℝ)` and the continuity of the volume

Blueprint `claude-hodge` (lane HODGE-TOP, package `HodgeTopology`), nodes
`claude-hodge:prop-kahler-cone-open`, `claude-hodge:prop-nef-cone-closed`,
`claude-hodge:prop-psef-cone-closed`, `claude-hodge:prop-volume-usc`; Xia, *Foundations of
pluripotential theory*, q07, `prop:cohomology-cone-topology`.  Used without proof in Xia,
*Singularities in global pluripotential theory*, `chap:bdiv` (`lma:volbdivnet`, `thm:DT`,
`cor:mn_level_nefb`).

Let `X` be a compact connected Kähler manifold.  `H^{1,1}(X, ℝ)` carries its Euclidean topology
(`SGPT.BDivisor.euclideanTopology`), which is TN's quotient `C⁰` topology
(`SGPT.Hodge.classC0Topology_eq_euclideanTopology`).  We prove, first for the quotient `C⁰`
topology and then for the Euclidean topology:

* the **Kähler cone is open** (`isOpen_actualKahlerCone`; the Kähler forms are `C⁰`-open,
  `isOpen_setOf_isKahler`, and the quotient map is open);
* the **nef cone is closed** (`isClosed_setOf_classNef`; it is the closure of the Kähler cone,
  TN `mem_closure_kahlerCone_iff_classNef`);
* the **pseudo-effective cone is closed** (`isClosed_setOf_classPseudoeffective`: a limit `α` of
  pseudo-effective classes has `α + ε{ω}` pseudo-effective for all `ε > 0`, hence is
  pseudo-effective by the weak compactness of positive currents,
  `SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_of_forall_add_smul`);
* the **volume is continuous** on `H^{1,1}(X, ℝ)` (`continuous_sourceClassVolume`, from
  `SGPT.Okounkov.TranscendentalVolumeConcavity.volumeContinuity`), hence upper semicontinuous on
  the pseudo-effective cone, and the big cone is open (`isOpen_bigCone`);
* **domination of nearby classes**: if `α_i → α` and `θ ∈ α`, then for every `ε > 0`, eventually
  `α_i` has a representative `η_i` with `‖η_i - θ‖_{C⁰} < ε`, so that
  `-ε ω ≤ η_i - θ ≤ ε ω` and `α_i ≤ α + ε{ω}` in the pseudo-effective order
  (`eventually_exists_formC0_lt`, `eventually_classPseudoeffective_add_smul_sub`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ENNReal

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
  SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
  SGPT.Okounkov.TranscendentalVolumeConcavity

section C0

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- **Kähler forms form a `C⁰`-open set** of closed real `(1,1)`-forms: a Kähler form `κ`
dominates `ω / A`, and a form `C⁰`-closer than `1/(2A)` to `κ` dominates `ω/(2A)`. -/
theorem isOpen_setOf_isKahler (w : KahlerBackground n M) :
    IsOpen[formC0Topology w] {θ : ClosedRealOneOneForm n M | θ.val.IsKahler} := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  rw [isOpen_iff_mem_nhds]
  intro κ hκ
  obtain ⟨A, hA, hdom⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul ⟨κ, hκ⟩ (-w.form)
  have hδ : 0 < 1 / (2 * A) := by positivity
  filter_upwards [(isOpen_formC0Seminorm_ball w κ (1 / (2 * A))).mem_nhds
    ((formC0Seminorm w).mem_ball_self hδ)] with η hη
  have hη' : formC0Seminorm w (κ - η) < 1 / (2 * A) := by
    rw [← neg_sub, map_neg_eq_map]
    exact (formC0Seminorm w).mem_ball.mp hη
  have hsemi := isSemipositive_sub_add_smul_of_formC0_lt w η κ hη'
  refine ⟨fun e z hz => ⟨η.property.2 e z hz, fun v hv => ?_⟩, η.property.1⟩
  have h1 := hsemi e z hz v
  have h2 := hdom e z hz v
  have h3 := (w.isKahler.1 e z hz).2 v hv
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at h1 h2
  have hw : 0 < w.form.val.coeff e z ![v, Complex.I • v] := h3
  have : (1 / (2 * A)) * w.form.val.coeff e z ![v, Complex.I • v] <
      (1 / A) * w.form.val.coeff e z ![v, Complex.I • v] := by
    apply mul_lt_mul_of_pos_right _ hw
    rw [div_lt_div_iff₀ (by positivity) hA]
    linarith
  have hκv : (1 / A) * w.form.val.coeff e z ![v, Complex.I • v] ≤
      κ.val.coeff e z ![v, Complex.I • v] := by
    rw [one_div, inv_mul_le_iff₀ hA]
    linarith
  linarith

/-- **The Kähler cone is open** for the quotient `C⁰` topology. -/
theorem isOpen_actualKahlerCone_classC0 (w : KahlerBackground n M) :
    IsOpen[classC0Topology w] (actualKahlerCone : Set (RealBottChern n M)) := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  exact (isOpenQuotientMap_ofRepresentative w).isOpenMap _ (isOpen_setOf_isKahler w)

/-- **The nef cone is closed** for the quotient `C⁰` topology: it is the closure of the Kähler
cone (TN `mem_closure_kahlerCone_iff_classNef`; the topology does not depend on the background). -/
theorem isClosed_setOf_classNef_classC0 (w w' : KahlerBackground n M) :
    IsClosed[classC0Topology w] {α : RealBottChern n M | ClassNefWithRespectTo w' α} := by
  have h : {α : RealBottChern n M | ClassNefWithRespectTo w' α} =
      @closure (RealBottChern n M) (classC0Topology w') actualKahlerCone := by
    ext α
    exact (mem_closure_kahlerCone_iff_classNef w' α).symm
  rw [h, classC0Topology_eq_of_background w w']
  exact @isClosed_closure _ (classC0Topology w') _

/-- **Nearby classes have `C⁰`-nearby representatives**: if `α_i → α` for the quotient `C⁰`
topology and `θ ∈ α`, then for every `ε > 0`, eventually `α_i` has a representative `η` with
`‖η - θ‖_{C⁰} < ε`. -/
theorem eventually_exists_formC0_lt_classC0 (w : KahlerBackground n M) {ι : Type*}
    {l : Filter ι} {α : ι → RealBottChern n M} {θ : ClosedRealOneOneForm n M}
    (h : Tendsto α l (@nhds _ (classC0Topology w) (RealBottChern.ofRepresentative θ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ η : ClosedRealOneOneForm n M,
      RealBottChern.ofRepresentative η = α i ∧ formC0Seminorm w (η - θ) < ε := by
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formC0Topology w
  let : TopologicalSpace (RealBottChern n M) := classC0Topology w
  rw [← (isOpenQuotientMap_ofRepresentative w).map_nhds_eq θ] at h
  have hball : (formC0Seminorm w).ball θ ε ∈ 𝓝 θ :=
    (isOpen_formC0Seminorm_ball w θ ε).mem_nhds ((formC0Seminorm w).mem_ball_self hε)
  filter_upwards [h (image_mem_map hball)] with i hi
  obtain ⟨η, hη, hηi⟩ := hi
  exact ⟨η, hηi, (formC0Seminorm w).mem_ball.mp hη⟩

omit [CompactSpace M] in
/-- A pseudo-effective class plus the class of a semipositive form is pseudo-effective. -/
theorem classPseudoeffective_add_ofRepresentative {α : RealBottChern n M}
    (hα : ClassPseudoeffectiveViaPotentials α) {σ : ClosedRealOneOneForm n M}
    (hσ : σ.val.IsSemipositive) :
    ClassPseudoeffectiveViaPotentials (α + RealBottChern.ofRepresentative σ) := by
  induction α using Quotient.inductionOn with
  | h θ =>
  obtain ⟨u, hu⟩ := hα
  exact ⟨u, LocalPotentials.isThetaPshPotential_add_of_semipositive hu hσ⟩

end C0

section C0Succ

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- **The pseudo-effective cone is closed** for the quotient `C⁰` topology. If `α = {θ}` is in
its closure, then for `ε > 0` some pseudo-effective `{η}` has `‖η - θ‖_{C⁰} < ε`, so
`α + ε{ω} = {η} + {θ - η + εω}` with `θ - η + εω ≥ 0` is pseudo-effective; hence `α` is
pseudo-effective (weak compactness of closed positive currents). -/
theorem isClosed_setOf_classPseudoeffective_classC0 (w : KahlerBackground (m + 1) X) :
    IsClosed[classC0Topology w]
      {α : RealBottChern (m + 1) X | ClassPseudoeffectiveViaPotentials α} := by
  let : TopologicalSpace (ClosedRealOneOneForm (m + 1) X) := formC0Topology w
  let : TopologicalSpace (RealBottChern (m + 1) X) := classC0Topology w
  rw [← closure_subset_iff_isClosed]
  intro α hα
  obtain ⟨θ, rfl⟩ : ∃ θ, RealBottChern.ofRepresentative θ = α :=
    ⟨Quotient.out α, Quotient.out_eq α⟩
  show ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ)
  apply classPseudoeffective_of_forall_add_smul w (RealBottChern.ofRepresentative θ)
  intro ε hε
  have hopen : IsOpen (RealBottChern.ofRepresentative '' (formC0Seminorm w).ball θ ε) :=
    (isOpenQuotientMap_ofRepresentative w).isOpenMap _ (isOpen_formC0Seminorm_ball w θ ε)
  obtain ⟨β, ⟨η, hη, rfl⟩, hβ⟩ := mem_closure_iff.mp hα _ hopen
    ⟨θ, (formC0Seminorm w).mem_ball_self hε, rfl⟩
  have hsemi := isSemipositive_sub_add_smul_of_formC0_lt w θ η
    ((formC0Seminorm w).mem_ball.mp hη)
  have hβ' : ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative η) := hβ
  have hsum := classPseudoeffective_add_ofRepresentative hβ' hsemi
  have he : RealBottChern.ofRepresentative η + RealBottChern.ofRepresentative (θ - η + ε • w.form) =
      RealBottChern.ofRepresentative θ + ε • RealBottChern.ofRepresentative w.form := by
    rw [← RealBottChern.ofRepresentative_smul, ← RealBottChern.ofRepresentative_add,
      ← RealBottChern.ofRepresentative_add]
    congr 1
    abel
  rwa [he] at hsum

end C0Succ

/-! ### The Euclidean topology -/

section Euclidean

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]

/-- **The Kähler cone is open** in the Euclidean topology of `H^{1,1}(X, ℝ)`
(`claude-hodge:prop-kahler-cone-open`), for every compact connected complex manifold (it is
empty if `X` carries no Kähler form). -/
theorem isOpen_actualKahlerCone :
    IsOpen[SGPT.BDivisor.euclideanTopology (RealBottChern n M)]
      (actualKahlerCone : Set (RealBottChern n M)) := by
  rcases (actualKahlerCone : Set (RealBottChern n M)).eq_empty_or_nonempty with h | ⟨_, κ, hκ, -⟩
  · rw [h]
    exact @isOpen_empty _ (SGPT.BDivisor.euclideanTopology _)
  · rw [← classC0Topology_eq_euclideanTopology ⟨κ, hκ⟩]
    exact isOpen_actualKahlerCone_classC0 ⟨κ, hκ⟩

/-- **The nef cone is closed** in the Euclidean topology (`claude-hodge:prop-nef-cone-closed`). -/
theorem isClosed_setOf_classNef (w : KahlerBackground n M) :
    IsClosed[SGPT.BDivisor.euclideanTopology (RealBottChern n M)]
      {α : RealBottChern n M | ClassNefWithRespectTo w α} := by
  rw [← classC0Topology_eq_euclideanTopology w]
  exact isClosed_setOf_classNef_classC0 w w

/-- Euclidean convergence of classes gives `C⁰`-close representatives: if `α_i → α` and
`θ ∈ α`, then for every `ε > 0`, eventually `α_i = {η}` with `‖η - θ‖_{C⁰} < ε`. -/
theorem eventually_exists_formC0_lt (w : KahlerBackground n M) {ι : Type*}
    {l : Filter ι} {α : ι → RealBottChern n M} {θ : ClosedRealOneOneForm n M}
    (h : Tendsto α l (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern n M))
      (RealBottChern.ofRepresentative θ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ η : ClosedRealOneOneForm n M,
      RealBottChern.ofRepresentative η = α i ∧ formC0Seminorm w (η - θ) < ε := by
  rw [← classC0Topology_eq_euclideanTopology w] at h
  exact eventually_exists_formC0_lt_classC0 w h hε

/-- **Domination of nearby classes**: if `α_i → α` (Euclidean topology), then for every `ε > 0`,
eventually `α + ε{ω} - α_i` and `α_i - α + ε{ω}` contain smooth semipositive forms. -/
theorem eventually_exists_semipositive_of_tendsto (w : KahlerBackground n M) {ι : Type*}
    {l : Filter ι} {α : ι → RealBottChern n M} {β : RealBottChern n M}
    (h : Tendsto α l (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern n M)) β))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, (∃ σ : ClosedRealOneOneForm n M, σ.val.IsSemipositive ∧
        RealBottChern.ofRepresentative σ =
          β + ε • RealBottChern.ofRepresentative w.form - α i) ∧
      (∃ σ : ClosedRealOneOneForm n M, σ.val.IsSemipositive ∧
        RealBottChern.ofRepresentative σ =
          α i - β + ε • RealBottChern.ofRepresentative w.form) := by
  obtain ⟨θ, rfl⟩ : ∃ θ, RealBottChern.ofRepresentative θ = β :=
    ⟨Quotient.out β, Quotient.out_eq β⟩
  filter_upwards [eventually_exists_formC0_lt w h hε] with i hi
  obtain ⟨η, hηi, hη⟩ := hi
  have hη' : formC0Seminorm w (θ - η) < ε := by
    rw [← neg_sub, map_neg_eq_map]
    exact hη
  refine ⟨⟨θ - η + ε • w.form, isSemipositive_sub_add_smul_of_formC0_lt w θ η hη, ?_⟩,
    ⟨η - θ + ε • w.form, isSemipositive_sub_add_smul_of_formC0_lt w η θ hη', ?_⟩⟩
  · rw [← hηi, sub_eq_add_neg θ η, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
      RealBottChern.ofRepresentative_smul]
    abel
  · rw [← hηi, sub_eq_add_neg η θ, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
      RealBottChern.ofRepresentative_smul]
    abel

end Euclidean

section EuclideanSucc

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **The pseudo-effective cone is closed** in the Euclidean topology of `H^{1,1}(X, ℝ)`
(`claude-hodge:prop-psef-cone-closed`), `X` compact connected Kähler. -/
theorem isClosed_setOf_classPseudoeffective (w : KahlerBackground (m + 1) X) :
    IsClosed[SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)]
      {α : RealBottChern (m + 1) X | ClassPseudoeffectiveViaPotentials α} := by
  rw [← classC0Topology_eq_euclideanTopology w]
  exact isClosed_setOf_classPseudoeffective_classC0 w

/-- **Domination in the pseudo-effective order**: if `α_i → α` (Euclidean topology), then for
every `ε > 0`, eventually `α_i ≤ α + ε{ω}` and `α - ε{ω} ≤ α_i`. -/
theorem eventually_classPseudoeffective_add_smul_sub (w : KahlerBackground (m + 1) X)
    {ι : Type*} {l : Filter ι} {α : ι → RealBottChern (m + 1) X} {β : RealBottChern (m + 1) X}
    (h : Tendsto α l (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)) β))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ClassPseudoeffectiveViaPotentials
        (β + ε • RealBottChern.ofRepresentative w.form - α i) ∧
      ClassPseudoeffectiveViaPotentials
        (α i - β + ε • RealBottChern.ofRepresentative w.form) := by
  filter_upwards [eventually_exists_semipositive_of_tendsto w h hε] with i hi
  obtain ⟨⟨σ, hσ, hσc⟩, ⟨σ', hσ', hσ'c⟩⟩ := hi
  refine ⟨?_, ?_⟩
  · rw [← hσc]
    exact ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ⟩
  · rw [← hσ'c]
    exact ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff σ').mpr hσ'⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- **The volume is continuous** on `H^{1,1}(X, ℝ)` with its Euclidean topology
(`claude-hodge:prop-volume-usc`; Boucksom).  In particular it is upper semicontinuous on the
(closed) pseudo-effective cone. -/
theorem continuous_sourceClassVolume (w : KahlerBackground (m + 1) X) :
    Continuous[SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X), inferInstance]
      (SGPT.PSH.VariableComplexAtlas.sourceClassVolume (n := m + 1) (M := X)) := by
  rw [← classC0Topology_eq_euclideanTopology w]
  exact volumeContinuity w

/-- The volume of a limit is the limit of the volumes (Euclidean topology). -/
theorem tendsto_sourceClassVolume (w : KahlerBackground (m + 1) X) {ι : Type*}
    {l : Filter ι} {α : ι → RealBottChern (m + 1) X} {β : RealBottChern (m + 1) X}
    (h : Tendsto α l (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)) β)) :
    Tendsto (fun i => SGPT.PSH.VariableComplexAtlas.sourceClassVolume (α i)) l
      (𝓝 (SGPT.PSH.VariableComplexAtlas.sourceClassVolume β)) := by
  let : TopologicalSpace (RealBottChern (m + 1) X) :=
    SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)
  exact ((continuous_sourceClassVolume w).tendsto β).comp h

/-- **The big cone is open** in the Euclidean topology. -/
theorem isOpen_bigCone (w : KahlerBackground (m + 1) X) :
    IsOpen[SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)] (bigCone (m := m) X) := by
  rw [← classC0Topology_eq_euclideanTopology w]
  exact SGPT.Okounkov.TranscendentalVolumeConcavity.isOpen_bigCone w w

end EuclideanSucc

end SGPT.Hodge
