import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

set_option autoImplicit false

/-!
# The rooftop envelope in dimension zero

Every statement of Xia's Section 2.4 that this workspace proves carries `0 < n`,
because Xia's Lemma 2.4.1, the nullity of `nK({theta})`, the balayage lemma and
the existence of the envelope as a genuine potential all do.  The *targets* of
Section 3.1 carry no dimension hypothesis, so the degenerate case has to be
proved rather than excluded.  This module does that, once, for the rooftop
obstacle `min {phi, psi}`.

In dimension `0` the model `ComplexModel 0 = EuclideanSpace ℂ (Fin 0)` is a
single point, and three things collapse at once.

* **Every affine disc is a point.**  So `circleDeficit u x v r C` is the
  integral of the constant `C - u x` over `Ioc 0 (2 pi)`, and the disc submean
  inequality of `HasDiscSubmeanOn` holds with equality, for *every*
  extended-real function.  Together with upper semicontinuity (automatic on a
  subsingleton) and `u != top`, every function avoiding `top` is
  plurisubharmonic.
* **`M` is discrete.**  A chart is injective on its open source and its target
  is a subsingleton, so the source of the chart at `x` is `{x}`; hence `{x}` is
  open.  Consequently `LocallyNondegenerate u` is equivalent to `u x != bot` for
  every `x`.
* **Hence `min {phi, psi}` is itself a `theta`-PSH potential**, being neither
  `top` (it is `<= phi`) nor `bot` (it is one of two values, both finite by the
  previous point).  The rooftop envelope of a genuine potential is that
  potential, so `P_theta(min {phi, psi}) = min {phi, psi}` and the non-contact
  set `{w != phi} cap {w != psi}` is **empty**.

Nothing here is analytic; no capacity, no bigness, no Kähler background.  The
consumer is `Pending.RooftopContactConcentration`, whose interface is stated
without `0 < n`: its positive-dimensional half is
`Pending.RooftopMinConcentration`, and its `n = 0` half is the last theorem
below.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopDimZero

open FirstPass
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

/-! ### Plurisubharmonicity over a subsingleton model -/

section SubsingletonModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Subsingleton E]

/-- Over a subsingleton model every affine disc degenerates to its centre, so the
angular integral of the deficit is `2 pi` times the deficit at the centre and the
submean inequality holds with equality — for an arbitrary extended-real
function. -/
theorem hasDiscSubmeanOn_of_subsingleton (u : E → EReal) (U : Set E) :
    HasDiscSubmeanOn u U := by
  intro x v r _ _ C _
  have hconst : ∀ t : ℝ, x + circleMap 0 r t • v = x := fun _ => Subsingleton.elim _ _
  have hint : circleDeficit u x v r C
      = ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal := by
    unfold circleDeficit
    simp only [hconst]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  rw [hint]

omit [NormedSpace ℂ E] in
/-- Over a subsingleton model every function is upper semicontinuous: the
neighbourhood filter sees only the point itself. -/
theorem upperSemicontinuousOn_of_subsingleton (u : E → EReal) (U : Set E) :
    UpperSemicontinuousOn u U := by
  intro x _ y hy
  exact Filter.Eventually.of_forall fun z => by rw [Subsingleton.elim z x]; exact hy

/-- Over a subsingleton model the disc criterion holds for every function that
avoids `top`. -/
theorem discPshOn_of_subsingleton {u : E → EReal} (hu : ∀ x, u x ≠ ⊤) (U : Set E) :
    DiscPshOn u U :=
  ⟨fun x _ => hu x, upperSemicontinuousOn_of_subsingleton u U,
    hasDiscSubmeanOn_of_subsingleton u U⟩

/-- Over a subsingleton model every function avoiding `top` is
plurisubharmonic. -/
theorem plurisubharmonicOn_of_subsingleton {u : E → EReal} (hu : ∀ x, u x ≠ ⊤)
    (U : Set E) : PlurisubharmonicOn u U :=
  fun x _ => ⟨univ, isOpen_univ, mem_univ x, discPshOn_of_subsingleton hu univ⟩

end SubsingletonModel

/-! ### Zero-dimensional complex manifolds -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A zero-dimensional complex manifold is discrete.**  The chart at `x` is
injective on its open source and lands in a subsingleton, so that source is
`{x}`. -/
theorem isOpen_singleton_of_dim_zero (hn : n = 0) (x : M) : IsOpen ({x} : Set M) := by
  subst hn
  have hsub : (chartAt (ComplexModel 0) x).source ⊆ {x} := fun y hy =>
    (chartAt (ComplexModel 0) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
  have hsup : ({x} : Set M) ⊆ (chartAt (ComplexModel 0) x).source :=
    singleton_subset_iff.mpr (mem_chart_source _ x)
  have hEq : (chartAt (ComplexModel 0) x).source = ({x} : Set M) :=
    Subset.antisymm hsub hsup
  rw [← hEq]
  exact (chartAt (ComplexModel 0) x).open_source

/-- In dimension `0` a locally nondegenerate function is finite at every point:
`{x}` is a neighbourhood of `x`. -/
theorem ne_bot_of_locallyNondegenerate_of_dim_zero (hn : n = 0) {u : M → EReal}
    (hu : LocallyNondegenerate u) (x : M) : u x ≠ ⊥ := by
  obtain ⟨y, hy, hne⟩ := hu x {x} (isOpen_singleton_of_dim_zero hn x) rfl
  rw [mem_singleton_iff] at hy
  subst hy
  exact hne

omit [IsComplexManifold n M] in
/-- A function that is nowhere `bot` is locally nondegenerate, in any
dimension. -/
theorem locallyNondegenerate_of_ne_bot {u : M → EReal} (hu : ∀ x, u x ≠ ⊥) :
    LocallyNondegenerate u := fun x _ _ hx => ⟨x, hx, hu x⟩

/-- **In dimension `0` every function avoiding `top` is `theta`-PSH**, as soon as
`theta` has smooth local potentials at all.  The local model is a point, so the
sum of the chart representative and a smooth local potential is automatically
plurisubharmonic. -/
theorem thetaPlurisubharmonic_of_dim_zero (hn : n = 0) {theta : SmoothRealForm n M 2}
    (hlp : HasSmoothLocalPotentials theta) {u : M → EReal} (hu : ∀ x, u x ≠ ⊤) :
    ThetaPlurisubharmonic theta u := by
  subst hn
  intro e z hz
  obtain ⟨W, rho, hzW, hrho⟩ := hlp e z hz
  refine ⟨W, rho, hzW, hrho, plurisubharmonicOn_of_subsingleton ?_ W⟩
  intro y
  have hy : chartFunction u e y ≠ ⊤ := hu _
  rcases eq_or_ne (chartFunction u e y) ⊥ with hb | hb
  · rw [hb, EReal.bot_add]
    exact bot_ne_top
  · lift chartFunction u e y to ℝ using ⟨hy, hb⟩ with a ha
    rw [← EReal.coe_add]
    exact EReal.coe_ne_top _

/-- **In dimension `0` every function that is nowhere `top` and nowhere `bot` is
a `theta`-PSH potential.** -/
theorem isThetaPshPotential_of_dim_zero (hn : n = 0) {theta : SmoothRealForm n M 2}
    (hlp : HasSmoothLocalPotentials theta) {u : M → EReal}
    (htop : ∀ x, u x ≠ ⊤) (hbot : ∀ x, u x ≠ ⊥) :
    IsThetaPshPotential theta u :=
  ⟨thetaPlurisubharmonic_of_dim_zero hn hlp htop, locallyNondegenerate_of_ne_bot hbot⟩

/-- **In dimension `0` the minimum of two `theta`-PSH potentials is again one.**
This is what fails in positive dimension and is the whole reason the rooftop
envelope is needed there. -/
theorem isThetaPshPotential_min_of_dim_zero (hn : n = 0) {theta : SmoothRealForm n M 2}
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta phi)
    (hpsi : IsThetaPshPotential theta psi) :
    IsThetaPshPotential theta (fun x => min (phi x) (psi x)) := by
  refine isThetaPshPotential_of_dim_zero hn hphi.1.hasSmoothLocalPotentials
    (fun x => ?_) (fun x => ?_)
  · exact ne_top_of_le_ne_top (hphi.1.quasiPlurisubharmonic.ne_top x) (min_le_left _ _)
  · rcases min_cases (phi x) (psi x) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact ne_bot_of_locallyNondegenerate_of_dim_zero hn hphi.2 x
    · rw [h]
      exact ne_bot_of_locallyNondegenerate_of_dim_zero hn hpsi.2 x

/-- **In dimension `0` the rooftop is the obstacle**: `P_theta(min {phi, psi})
= min {phi, psi}`. -/
theorem rooftopEnvelope_min_eq_of_dim_zero (hn : n = 0) {theta : SmoothRealForm n M 2}
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta phi)
    (hpsi : IsThetaPshPotential theta psi) :
    rooftopEnvelope theta (fun x => min (phi x) (psi x)) = fun x => min (phi x) (psi x) := by
  refine le_antisymm ?_ (self_le_rooftopEnvelope (isThetaPshPotential_min_of_dim_zero hn hphi hpsi))
  have hfun : (fun x : M => min (phi x) (psi x + ((0 : ℝ) : EReal))) =
      fun x : M => min (phi x) (psi x) := by
    funext x
    simp
  have h := rooftopEnvelope_min_add_const_le_obstacles hphi.1 hpsi.1 0
  rw [hfun] at h
  intro x
  exact le_min (h.1 x) (by simpa using h.2 x)

/-! ### Theorem 2.4.4 at the rooftop obstacle, in dimension zero -/

section Measure

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)) at the
obstacle `min {phi, psi}`, in dimension `0`.**  The non-contact set is empty,
because the rooftop *is* the obstacle: this is the degenerate half of
`Pending.RooftopContactConcentration.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero`,
whose positive-dimensional half is `Pending.RooftopMinConcentration`.

No measure theory is used beyond `measure_empty`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_of_dim_zero
    (hn : n = 0) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) hw
      {x | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
        rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} = 0 := by
  have heq := rooftopEnvelope_min_eq_of_dim_zero hn hphi hpsi
  have hempty : {x : M | rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ phi x ∧
      rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x ≠ psi x} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    intro h1
    have hx : rooftopEnvelope theta.val (fun y => min (phi y) (psi y)) x =
        min (phi x) (psi x) := congrFun heq x
    rw [hx] at h1 ⊢
    rcases min_cases (phi x) (psi x) with ⟨h, _⟩ | ⟨h, _⟩
    · exact absurd h h1
    · exact h
  rw [hempty]
  exact measure_empty

end Measure

end

end SGPT.Foundations.Analysis.Pending.RooftopDimZero
