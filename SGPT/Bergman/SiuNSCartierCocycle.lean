import SGPT.PSH.NativeCartierGeneratorUnits
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! The actual holomorphic scalar cocycle of the original invertible
Cartier ideal, including all singular zeros of its defining functions. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Original generating presentations of the full invertible ideal. -/
structure CartierAtlas (D : EffectiveDivisor n X) where
  dom : X → Set X
  open_dom : ∀ i, IsOpen (dom i)
  mem_dom : ∀ i, i ∈ dom i
  gen : X → X → ℂ
  hol : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (gen i) (dom i)
  dense : ∀ i W, IsOpen W → W ⊆ dom i → W.Nonempty → ∃ y ∈ W, gen i y ≠ 0
  generates : ∀ i y, y ∈ dom i → ∀ f,
    D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = gen i) y f

/-- The actual divisor supplies its own full generating cover. -/
def cartierAtlas (D : EffectiveDivisor n X) : CartierAtlas D := by
  choose U hU hx g hg hn hgen using D.isInvertible
  exact ⟨U, hU, hx, g, hg, hn, hgen⟩

namespace CartierAtlas
variable {D : EffectiveDivisor n X} (A : CartierAtlas D)

omit [IsComplexManifold n X] in
/-- Cancellation at a zero of a defining function uses its actual dense
nonzero locus and continuity of the two candidate transition coefficients. -/
theorem unit_value_unique (i : X) {p : X} (hp : p ∈ A.dom i)
    {u v : X → ℂ} (hu : ContinuousAt u p) (hv : ContinuousAt v p)
    (heq : (fun y => A.gen i y * u y) =ᶠ[𝓝 p] fun y => A.gen i y * v y) : u p = v p := by
  by_contra hne
  have hnear : ∀ᶠ y in 𝓝 p, u y ≠ v y := (hu.sub hv).eventually_ne (sub_ne_zero.mpr hne)
    |>.mono (fun _ h => sub_ne_zero.mp h)
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp
    (heq.and (hnear.and (A.open_dom i |>.mem_nhds hp)))
  obtain ⟨y, hyW, hgy⟩ := A.dense i W hW (fun y hy => (hWsub hy).2.2) ⟨p, hpW⟩
  exact (hWsub hyW).2.1 (mul_left_cancel₀ hgy (hWsub hyW).1)

/-- Actual Cartier germs supply a native holomorphic unit at every overlap
point, including where both original generators vanish. -/
theorem exists_unit (i j : X) {p : X} (hp : p ∈ A.dom i ∩ A.dom j) :
    ∃ u : X → ℂ, HolomorphicAt n u p ∧ u p ≠ 0 ∧
      (∀ᶠ y in 𝓝 p, u y ≠ 0) ∧ A.gen j =ᶠ[𝓝 p] fun y => A.gen i y * u y :=
  SGPT.PSH.exists_native_cartier_generator_unit D p (A.gen j) (A.gen i)
    (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn (A.open_dom j) (A.hol j) hp.2)
    (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn (A.open_dom i) (A.hol i) hp.1)
    (A.generates j p hp.2) (A.generates i p hp.1)

/-- The genuine transition, extended by one outside the actual overlap. -/
def transition (i j p : X) : ℂ := by
  classical
  exact if hp : p ∈ A.dom i ∩ A.dom j then (A.exists_unit i j hp).choose p else 1

theorem transition_ne_zero (i j : X) {p : X} (hp : p ∈ A.dom i ∩ A.dom j) :
    A.transition i j p ≠ 0 := by
  rw [transition, dif_pos hp]
  exact (A.exists_unit i j hp).choose_spec.2.1

/-- Every local holomorphic transition candidate agrees at the original
point with the globally defined transition. -/
theorem transition_eq_unit (i j : X) {p : X} (hp : p ∈ A.dom i ∩ A.dom j)
    {u : X → ℂ} (hu : HolomorphicAt n u p)
    (heq : A.gen j =ᶠ[𝓝 p] fun y => A.gen i y * u y) : A.transition i j p = u p := by
  rw [transition, dif_pos hp]
  obtain ⟨hv, _, _, hveq⟩ := (A.exists_unit i j hp).choose_spec
  exact A.unit_value_unique i hp.1 hv.continuousAt hu.continuousAt (hveq.symm.trans heq)

/-- Local uniqueness glues the actual germ units to a holomorphic function
on the entire overlap; smoothness is proved, never assumed of the choice. -/
theorem transition_eventuallyEq_unit (i j : X) {p : X}
    (hp : p ∈ A.dom i ∩ A.dom j) {u : X → ℂ} (hu : HolomorphicAt n u p)
    (heq : A.gen j =ᶠ[𝓝 p] fun y => A.gen i y * u y) :
    A.transition i j =ᶠ[𝓝 p] u := by
  have hgen : ∀ᶠ y in 𝓝 p, A.gen j =ᶠ[𝓝 y] fun t => A.gen i t * u t :=
    heq.eventually_nhds
  have hhol : ∀ᶠ y in 𝓝 p, HolomorphicAt n u y := hu.eventually
  filter_upwards [(A.open_dom i |>.inter (A.open_dom j)).mem_nhds hp, hgen, hhol]
    with y hy hyeq hyhol
  exact A.transition_eq_unit i j hy hyhol hyeq

theorem transition_holomorphicAt (i j : X) {p : X} (hp : p ∈ A.dom i ∩ A.dom j) :
    HolomorphicAt n (A.transition i j) p := by
  obtain ⟨u, hu, _, _, heq⟩ := A.exists_unit i j hp
  exact hu.congr (A.transition_eventuallyEq_unit i j hp hu heq).symm

theorem transition_contMDiffOn (i j : X) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (A.transition i j) (A.dom i ∩ A.dom j) := by
  intro p hp
  exact (contMDiffAt_of_eventually_mdifferentiableAt (A.transition_holomorphicAt i j hp)).contMDiffWithinAt

/-- The actual transition coefficients multiply the original defining
functions, on the entire overlap and not only off their zeros. -/
theorem generator_transition (i j : X) {p : X} (hp : p ∈ A.dom i ∩ A.dom j) :
    A.gen j p = A.gen i p * A.transition i j p := by
  obtain ⟨u, hu, _, _, heq⟩ := A.exists_unit i j hp
  rw [A.transition_eq_unit i j hp hu heq]
  exact heq.self_of_nhds

theorem transition_self (i : X) {p : X} (hp : p ∈ A.dom i) : A.transition i i p = 1 := by
  apply A.transition_eq_unit i i ⟨hp, hp⟩ (holomorphicAt_const 1)
  filter_upwards [] with y
  simp

/-- The full original Cartier ideal enforces the actual cocycle law,
including at the divisor; no cocycle is an additional premise. -/
theorem transition_mul (i j k : X) {p : X}
    (hi : p ∈ A.dom i) (hj : p ∈ A.dom j) (hk : p ∈ A.dom k) :
    A.transition i j p * A.transition j k p = A.transition i k p := by
  obtain ⟨u, hu, _, _, hueq⟩ := A.exists_unit i j ⟨hi, hj⟩
  obtain ⟨v, hv, _, _, hveq⟩ := A.exists_unit j k ⟨hj, hk⟩
  have heq : A.gen k =ᶠ[𝓝 p] fun y => A.gen i y * (u y * v y) := by
    filter_upwards [hueq, hveq] with y hy hjy
    rw [hjy, hy, mul_assoc]
  rw [A.transition_eq_unit i j ⟨hi, hj⟩ hu hueq,
    A.transition_eq_unit j k ⟨hj, hk⟩ hv hveq,
    A.transition_eq_unit i k ⟨hi, hk⟩ (hu.mul hv) heq]

end CartierAtlas
end SGPT.BDivisor.NSKodaira
