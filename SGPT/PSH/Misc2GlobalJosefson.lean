import SGPT.PSH.SourceGlobalPluripolarPole
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure

/-!
# The global Josefson theorem on every compact Kähler manifold

Source `thm:gloJosefson` (chapter *Plurisubharmonic functions*): on a compact complex manifold
`X`, every pluripolar set `E` lies in the pole set of a quasi-plurisubharmonic function.

`SGPT.PSH.GlobalPluripolarPole.source_exists_nonpositive_global_pluripolar_pole` proves this for
compact **connected** Kähler manifolds (through the outer capacity of the Kähler form). This file
removes the connectedness assumption: a compact complex manifold is locally connected, its
connected components `C` are clopen, compact, connected complex manifolds, the Kähler form,
pluripolarity and theta-plurisubharmonicity restrict to them
(`SGPT.Foundations.Analysis.Pending.OpensRestriction`, `...OpensRestrictionMeasure`), and the
nonpositive pole potentials of the components glue to one potential on `X`, since the
theta-PSH condition and local nondegeneracy are local and the components are open.

## Main results

* `exists_native_nonpositive_pole`: the native statement (a nonpositive `ω`-psh potential with
  poles on `S`) on every compact Kähler manifold.
* `source_exists_nonpositive_global_pluripolar_pole_compact`: `thm:gloJosefson` for every
  compact Kähler manifold, in the source predicates (`ω`-PSH, quasi-PSH, `≤ 0`, `= -∞` on `S`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Misc2GlobalJosefson

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  SGPT.PSH.VariableComplexAtlas
open OpensRestriction OpensRestrictionMeasure
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A chosen point of a connected component. -/
def rep (c : ConnectedComponents M) : M := Quotient.out (s := connectedComponentSetoid M) c

theorem coe_rep (c : ConnectedComponents M) : ((rep c : M) : ConnectedComponents M) = c :=
  Quotient.out_eq (s := connectedComponentSetoid M) c

theorem mem_connectedComponent_rep_iff (c : ConnectedComponents M) (y : M) :
    y ∈ connectedComponent (rep c) ↔ (y : ConnectedComponents M) = c := by
  rw [← ConnectedComponents.coe_eq_coe', coe_rep]

theorem mem_connectedComponent_rep (y : M) :
    y ∈ connectedComponent (rep (y : ConnectedComponents M)) :=
  (mem_connectedComponent_rep_iff _ y).mpr rfl

variable [CompactSpace M]

/-- **`thm:gloJosefson` on compact Kähler manifolds, native form.** On a compact (not
necessarily connected) Kähler manifold, every pluripolar set lies in the pole set of a
nonpositive `ω`-psh potential. -/
theorem exists_native_nonpositive_pole (omega : KahlerBackground n M) {S : Set M}
    (hS : ManifoldLocallyPluripolar (n := n) S) :
    ∃ q : M → EReal, IsThetaPshPotential omega.form.val q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ S, q x = ⊥ := by
  classical
  have : LocallyConnectedSpace M := OpensRestrictionMeasure.locallyConnectedSpace n M
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hempty := PluripolarOuterCapacity.eq_empty_of_manifoldLocallyPluripolar_dim_zero hS
    exact ⟨fun _ => 0, PluripolarCapacityDichotomy.isThetaPshPotential_zero omega,
      fun _ => le_rfl, fun x hx => False.elim (by rw [hempty] at hx; exact hx)⟩
  -- a nonpositive pole potential on each connected component
  have hcomp : ∀ c : ConnectedComponents M, ∃ u : componentOpens (rep c) → EReal,
      IsThetaPshPotential (restrictKahler (componentOpens (rep c)) omega).form.val u ∧
        (∀ y, u y ≤ 0) ∧ ∀ y : componentOpens (rep c), (y : M) ∈ S → u y = ⊥ := by
    intro c
    borelize ↥(componentOpens (rep c))
    have hSU : ManifoldLocallyPluripolar (n := n)
        (Subtype.val ⁻¹' S : Set (componentOpens (rep c))) :=
      manifoldLocallyPluripolar_preimage_val hS
    obtain ⟨u, hu, hpoles⟩ :=
      KahlerVolumePositive.exists_isThetaPshPotential_poles_of_outerCapacityZero' hn
        (restrictKahler (componentOpens (rep c)) omega)
        (PluripolarOuterCapacity.outerCapacityZero_of_manifoldLocallyPluripolar
          (restrictKahler (componentOpens (rep c)) omega) hSU)
    obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
    refine ⟨fun y => u y - (C : EReal), hu.sub_const C, sub_const_nonpositive_of_le hC, ?_⟩
    intro y hy
    change u y - (C : EReal) = ⊥
    rw [hpoles y hy, sub_eq_add_neg, EReal.bot_add]
  choose u hu hu0 hupoles using hcomp
  -- the glued potential
  let q : M → EReal := fun y =>
    u (y : ConnectedComponents M) ⟨y, mem_connectedComponent_rep y⟩
  have hq : ∀ (c : ConnectedComponents M) (y : componentOpens (rep c)), q y = u c y := by
    rintro c ⟨y, hy⟩
    have hc : (y : ConnectedComponents M) = c := (mem_connectedComponent_rep_iff c y).mp hy
    subst hc
    rfl
  have hpsh : ThetaPlurisubharmonic omega.form.val q := by
    intro e z hz
    have hrestr : ThetaPlurisubharmonic
        (SmoothRealForm.pullback (contMDiff_val (componentOpens
          (rep ((e.val.symm z : M) : ConnectedComponents M)))) omega.form.val)
        (fun y : componentOpens (rep ((e.val.symm z : M) : ConnectedComponents M)) => q y) := by
      have hfun : (fun y : componentOpens (rep ((e.val.symm z : M) : ConnectedComponents M)) =>
          q y) = u ((e.val.symm z : M) : ConnectedComponents M) :=
        funext (hq _)
      rw [hfun]
      exact (hu _).1
    exact thetaPlurisubharmonicOn_of_restrict hrestr e z hz
      (mem_connectedComponent_rep (e.val.symm z))
  have hnd : LocallyNondegenerate q := by
    intro x V hV hxV
    obtain ⟨y, hyV, hy⟩ := (hu (x : ConnectedComponents M)).2
      ⟨x, mem_connectedComponent_rep x⟩ (Subtype.val ⁻¹' V)
      (hV.preimage continuous_subtype_val) hxV
    exact ⟨y, hyV, by rw [hq _ y]; exact hy⟩
  refine ⟨q, ⟨hpsh, hnd⟩, fun x => ?_, fun x hx => ?_⟩
  · exact hu0 _ _
  · exact hupoles _ ⟨x, mem_connectedComponent_rep x⟩ hx

/-- **Source `thm:gloJosefson` for every compact Kähler manifold** (no connectedness): for a
pluripolar set `S` (`def:pluripolarsets`) there is a nonpositive quasi-plurisubharmonic (indeed
`ω`-plurisubharmonic) function `q` on `X` with `q|_S ≡ -∞`. -/
theorem source_exists_nonpositive_global_pluripolar_pole_compact
    (omega : KahlerBackground n M) {S : Set M}
    (hS : (ofFixedModel n M).LocallyPluripolar S) :
    ∃ q : M → EReal,
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas omega.form) q ∧
      (ofFixedModel n M).IsQPSH q ∧ (∀ x, q x ≤ 0) ∧ ∀ x ∈ S, q x = ⊥ := by
  have hSNative : ManifoldLocallyPluripolar (n := n) S := by
    intro e
    exact hS.in_chart e
  have hback : atlasClosedFormToNative (nativeClosedFormToAtlas omega.form) = omega.form := by
    rcases omega.form with ⟨wForm, hwForm⟩
    cases wForm
    rfl
  have source {q : M → EReal} (hq : IsThetaPshPotential omega.form.val q) :
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas omega.form) q := by
    apply (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas omega.form) q).mpr
    simpa only [hback] using hq
  obtain ⟨q, hq, hq0, hpoles⟩ := exists_native_nonpositive_pole omega hSNative
  have hqSource := source hq
  exact ⟨q, hqSource, ⟨_, hqSource⟩, hq0, hpoles⟩

end SGPT.PSH.Misc2GlobalJosefson
