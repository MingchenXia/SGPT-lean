import SGPT.PSH.HermitianExtremalGlobalPoleUnion
import SGPT.PSH.HermitianExtremalChartSublevels
import SGPT.Foundations.Analysis.FirstPass.ManifoldPluripolar

/-!
# Actual finite coordinate pole covers

Original manifold local pluripolarity supplies nontrivial local PSH
witnesses. Shrinking gives a standardized buffered coordinate ball;
subtracting its actual compact upper bound makes the witness nonpositive.
The original PSH local L1 theorem proves that the shrunken witness is
still nontrivial. Compactness then selects finitely many of these genuine
coordinate neighborhoods.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Original local witness with fixed explicit geometric buffers. No
global pole or analytic capacity conclusion is stored in this datum. -/
structure LocalPoleBall (S : Set M) where
  e : ComplexChart (m + 1) M
  center : ComplexModel (m + 1)
  radius : ℝ
  potential : ComplexModel (m + 1) → EReal
  radius_pos : 0 < radius
  target_buffer : closedBall center (32 * radius) ⊆ e.val.target
  plurisubharmonic : PlurisubharmonicOn potential (ball center (32 * radius))
  nontrivial : ∃ z ∈ ball center (32 * radius), potential z ≠ ⊥
  nonpositive : ∀ z ∈ ball center (32 * radius), potential z ≤ 0
  contains_poles : ∀ x ∈ chartBall e center radius, x ∈ S → potential (e.val x) = ⊥

namespace LocalPoleBall

def domain {S : Set M} (B : LocalPoleBall (m := m) S) : Set M :=
  chartBall B.e B.center B.radius

def poleSet {S : Set M} (B : LocalPoleBall (m := m) S) : Set M :=
  B.domain ∩ {x | B.potential (B.e.val x) = ⊥}

omit [IsComplexManifold (m + 1) M] in
theorem isOpen_domain {S : Set M} (B : LocalPoleBall (m := m) S) : IsOpen B.domain :=
  chartBall_isOpen B.e B.center B.radius

omit [IsComplexManifold (m + 1) M] in
theorem subset_poleSet {S : Set M} (B : LocalPoleBall (m := m) S) : S ∩ B.domain ⊆ B.poleSet :=
  fun x hx => ⟨hx.2, B.contains_poles x hx.2 hx.1⟩

end LocalPoleBall

/-- Local nontriviality is preserved on a shrunken ball by actual PSH
almost-everywhere finiteness; it is not an additional witness assumption. -/
theorem exists_localPoleBall (S : Set M) (hS : ManifoldLocallyPluripolar (n := m + 1) S)
    (x : M) : ∃ B : LocalPoleBall (m := m) S, x ∈ B.domain := by
  let e : ComplexChart (m + 1) M := complexChartAt x
  have hxsource : x ∈ e.val.source := mem_complexChartAt_source x
  have hxtarget : e.val x ∈ e.val.target := e.val.map_source hxsource
  obtain ⟨V, u, hV, hxV, hVconn, hu, hne, hpole⟩ := hS e (e.val x) hxtarget
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp (hV.inter e.val.open_target)
    (e.val x) ⟨hxV, hxtarget⟩
  let r : ℝ := δ / 128
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hbuffer : closedBall (e.val x) (64 * r) ⊆ V ∩ e.val.target :=
    (closedBall_subset_ball (by dsimp only [r]; linarith)).trans hδball
  have h32 : closedBall (e.val x) (32 * r) ⊆ V ∩ e.val.target :=
    (closedBall_subset_closedBall (by linarith)).trans hbuffer
  have h32V : ball (e.val x) (32 * r) ⊆ V := ball_subset_closedBall.trans
    (h32.trans inter_subset_left)
  obtain ⟨C, _, hC⟩ := hu.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall (e.val x) (32 * r)) (h32.trans inter_subset_left)
  have hfinite : ∀ᵐ z ∂volume.restrict (ball (e.val x) (32 * r)), u z ≠ ⊤ ∧ u z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset h32V (hu.ae_finite volume hVconn hne)
  have hpos : 0 < volume (ball (e.val x) (32 * r)) :=
    measure_ball_pos volume _ (by positivity)
  obtain ⟨b, hb, hbu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' hfinite
  let ψ : ComplexModel (m + 1) → EReal := fun z => u z + ((-C : ℝ) : EReal)
  have hψ : PlurisubharmonicOn ψ (ball (e.val x) (32 * r)) :=
    (hu.mono h32V).add (fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top (-C)) z)
  have hψnonpos : ∀ z ∈ ball (e.val x) (32 * r), ψ z ≤ 0 := by
    intro z hz
    calc ψ z ≤ (C : EReal) + ((-C : ℝ) : EReal) :=
        add_le_add (hC z (ball_subset_closedBall hz)) le_rfl
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  let B : LocalPoleBall (m := m) S := {
    e := e
    center := e.val x
    radius := r
    potential := ψ
    radius_pos := hr
    target_buffer := h32.trans inter_subset_right
    plurisubharmonic := hψ
    nontrivial := ⟨b, hb, EReal.add_ne_bot_iff.mpr ⟨hbu.2, EReal.coe_ne_bot (-C)⟩⟩
    nonpositive := hψnonpos
    contains_poles := by
      intro y hy hyS
      have hyV : e.val y ∈ V := h32V (ball_subset_ball (by linarith) hy.2)
      have hval : u (e.val y) = ⊥ := hpole (e.val y) hyV
        ⟨e.val.map_source hy.1, by simpa only [mem_preimage, e.val.left_inv hy.1] using hyS⟩
      change u (e.val y) + ((-C : ℝ) : EReal) = ⊥
      rw [hval, EReal.bot_add] }
  exact ⟨B, hxsource, mem_ball_self hr⟩

variable [CompactSpace M]

/-- Compactness selects a finite cover of genuine buffered coordinate
pole witnesses from the original local pluripolarity predicate. -/
theorem exists_finite_localPoleBall_cover (S : Set M)
    (hS : ManifoldLocallyPluripolar (n := m + 1) S) :
    ∃ B : M → LocalPoleBall (m := m) S, ∃ t : Finset M,
      ∀ x : M, ∃ i ∈ t, x ∈ (B i).domain := by
  classical
  choose B hB using exists_localPoleBall S hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (B i).domain) (fun i => (B i).isOpen_domain)
    (fun x _ => mem_iUnion.mpr ⟨x, hB x⟩)
  refine ⟨B, t, fun x => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hit, hxi⟩ := mem_iUnion.mp hi
  exact ⟨i, hit, hxi⟩

variable [ConnectedSpace M]

/-- Countable index types, in particular any actual finite selected
coordinate cover, reduce to the proved original-potential series theorem.
This is only union closure: each input is a genuine global witness. -/
theorem exists_pole_iUnion_countable_of_quasiPsh_poles
    (ω : Background (m + 1) M) {ι : Type*} [Countable ι] (A : ι → Set M)
    (hA : ∀ i, ∃ u : M → EReal, IsGlobalQuasiPshPotential (n := m + 1) u ∧
      ∀ x ∈ A i, u x = ⊥) :
    ∃ q : M → EReal, IsHermitianPSH ω q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ ⋃ i, A i, q x = ⊥ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    refine ⟨fun _ => 0, isHermitianPSH_zero ω, fun _ => le_rfl, fun x hx => ?_⟩
    obtain ⟨i, _⟩ := mem_iUnion.mp hx
    exact isEmptyElim i
  | inr hne =>
    obtain ⟨f, hf⟩ := exists_surjective_nat ι
    obtain ⟨q, hq, hq0, hpole⟩ := exists_pole_iUnion_of_quasiPsh_poles ω
      (fun j => A (f j)) (fun j => hA (f j))
    refine ⟨q, hq, hq0, fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := hf i
    exact hpole x (mem_iUnion.mpr ⟨j, hi⟩)

end SGPT.PSH.HermitianExtremal
