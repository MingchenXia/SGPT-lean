import SGPT.PSH.SourceTestCurveGeneralSup
import SGPT.PSH.SourceTestCurveMassContinuity
import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.Choquet
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Separation.Hausdorff

/-! # Countably many original test curves suffice

Existing original-index Choquet selection produces actual finite subsets.
Countable original carriers retain cofinal real cutoffs. Genuine mass
continuity and positive diagonal P-equivalence give whole-curve rigidity.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Actual mass continuity upgrades genuine rational-slice equality to whole-curve equality. -/
theorem SourceTestCurve.eq_of_order_and_rational_at_eq
    (omega : KahlerBackground n M) (Γ Δ : SourceTestCurve θ)
    (hmax : Γ.max = Δ.max) (hle : SourceTestCurvePOrder Γ Δ)
    (hq : ∀ q : ℚ, (q : ℝ) < Γ.max →
      sourceTestCurveAt Γ.toSourceTestCurvePredata q =
        sourceTestCurveAt Δ.toSourceTestCurvePredata q) : Γ = Δ := by
  have hmassRat : EqOn (sourceTestCurveRealMassAt omega Γ)
      (sourceTestCurveRealMassAt omega Δ)
      (Iio Γ.max ∩ range ((↑) : ℚ → ℝ)) := by
    rintro _ ⟨hr, q, rfl⟩
    have hs : (q : ℝ) < Δ.max := hr.trans_le hmax.le
    have hp := hq q hr
    rw [sourceTestCurveAt_of_lt _ hr, sourceTestCurveAt_of_lt _ hs] at hp
    rw [sourceTestCurveRealMassAt_of_lt omega Γ hr,
      sourceTestCurveRealMassAt_of_lt omega Δ hs]
    simp only [hp]
  have hmass : EqOn (sourceTestCurveRealMassAt omega Γ)
      (sourceTestCurveRealMassAt omega Δ) (Iio Γ.max) :=
    hmassRat.of_subset_closure
      (fun r hr => (sourceTestCurveRealMassAt_continuousAt omega Γ hr).continuousWithinAt)
      (fun r hr => (sourceTestCurveRealMassAt_continuousAt omega Δ
        (hr.trans_le hmax.le)).continuousWithinAt)
      inter_subset_left
      ((Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).open_subset_closure_inter isOpen_Iio)
  apply SourceTestCurvePOrder.antisymm omega hle
  refine ⟨hmax.ge, fun r hr => ?_⟩
  have hs : r < Γ.max := hr.trans_le hmax.ge
  have heq := hmass hs
  rw [sourceTestCurveRealMassAt_of_lt omega Γ hs,
    sourceTestCurveRealMassAt_of_lt omega Δ hr] at heq
  have hactual := congrArg ENNReal.ofReal heq
  rw [ENNReal.ofReal_toReal (Γ.mass_lt_top omega ⟨r, hs⟩).ne,
    ENNReal.ofReal_toReal (Δ.mass_lt_top omega ⟨r, hr⟩).ne] at hactual
  exact ((sourcePEquivalent_iff_diagonalMass_eq_of_positive omega
    (Γ.thetaPSH ⟨r, hs⟩) (Δ.thetaPSH ⟨r, hr⟩)
    (Γ.mass_positive omega ⟨r, hs⟩) (Δ.mass_positive omega ⟨r, hr⟩)
    (hle.slice_le r hs)).mpr hactual).2

omit [BorelSpace M] [ConnectedSpace M] in
/-- The actual original subfamily inherits the given finite real cutoff bound. -/
theorem sourceTestCurveRestrictedFamily_bddAbove {I : Type*}
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) (J : Set I) :
    BddAbove (range fun j : J => (Γ j.val).max) := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact hC (mem_range_self j.val)

/-- The actual general supremum of an original subfamily is intrinsically below the full one. -/
theorem SourceTestCurve.generalSup_restrict_le {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) (J : Set I) [Nonempty J] :
    SourceTestCurvePOrder
      (SourceTestCurve.generalSup omega (fun j : J => Γ j.val)
        (sourceTestCurveRestrictedFamily_bddAbove Γ hb J))
      (SourceTestCurve.generalSup omega Γ hb) := by
  apply SourceTestCurve.generalSup_le
  intro j
  exact SourceTestCurve.le_generalSup omega Γ hb j.val

/-- An actual finite set of included original inputs lies below the restricted supremum. -/
theorem SourceTestCurve.finiteJoin_le_generalSup_restrict {I : Type*}
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) (J : Set I) [Nonempty J]
    (s : Finset I) (hs : s.Nonempty) (hsub : ∀ i ∈ s, i ∈ J) :
    SourceTestCurvePOrder (SourceTestCurve.finiteJoin omega Γ s hs)
      (SourceTestCurve.generalSup omega (fun j : J => Γ j.val)
        (sourceTestCurveRestrictedFamily_bddAbove Γ hb J)) := by
  apply (SourceTestCurve.finiteJoin_le_iff omega Γ s hs _).mpr
  intro i hi
  exact SourceTestCurve.le_generalSup omega (fun j : J => Γ j.val)
    (sourceTestCurveRestrictedFamily_bddAbove Γ hb J) ⟨i, hsub i hi⟩

/-- Genuine rational-cofinal original cutoffs force equality of the actual supremum cutoffs. -/
theorem SourceTestCurve.generalSup_restrict_max_eq {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) (J : Set I) [Nonempty J]
    (hcofinal : ∀ q : ℚ, (q : ℝ) < sourceTestCurveSupCutoff Γ →
      ∃ i ∈ J, (q : ℝ) < (Γ i).max) :
    (SourceTestCurve.generalSup omega (fun j : J => Γ j.val)
      (sourceTestCurveRestrictedFamily_bddAbove Γ hb J)).max =
      (SourceTestCurve.generalSup omega Γ hb).max := by
  apply le_antisymm (SourceTestCurve.generalSup_restrict_le omega Γ hb J).cutoff_le
  by_contra hn
  obtain ⟨q, hlow, hhigh⟩ := exists_rat_btwn (lt_of_not_ge hn)
  obtain ⟨i, hi, hqi⟩ := hcofinal q (by
    simpa only [SourceTestCurve.generalSup_max] using hhigh)
  have hcut := (SourceTestCurve.le_generalSup omega (fun j : J => Γ j.val)
    (sourceTestCurveRestrictedFamily_bddAbove Γ hb J) ⟨i, hi⟩).cutoff_le
  exact (not_lt_of_ge hlow.le) (hqi.trans_le hcut)

/-- Existing original-index Choquet selection on the actual whole finite-join extensions. -/
theorem sourceTestCurveFiniteJoin_countable_at_selection {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ) :
    ∃ S : ℚ → Set (SourceTestCurveFiniteIndex I),
      (∀ q, (S q).Countable ∧ (S q).Nonempty) ∧
      ∀ q : ℚ,
        uscRegularization (⨆ F : S q, sourceTestCurveAt
          (sourceTestCurveFiniteJoinFamily omega Γ F.val).toSourceTestCurvePredata q) =
        sourceTestCurveSupPotential (sourceTestCurveFiniteJoinFamily omega Γ) q := by
  classical
  have h (q : ℚ) := SGPT.PSH.exists_countable_indices_uscSup_eq
    (fun F : SourceTestCurveFiniteIndex I => sourceTestCurveAt
      (sourceTestCurveFiniteJoinFamily omega Γ F).toSourceTestCurvePredata q)
  choose S hSc hSn hSel using h
  refine ⟨S, fun q => ⟨hSc q, hSn q⟩, ?_⟩
  intro q
  have hL : (⨆ F : S q, sourceTestCurveAt
      (sourceTestCurveFiniteJoinFamily omega Γ F.val).toSourceTestCurvePredata q) =
      fun x => ⨆ F : S q, sourceTestCurveAt
        (sourceTestCurveFiniteJoinFamily omega Γ F.val).toSourceTestCurvePredata q x := by
    funext x
    exact iSup_apply
  have hR : (⨆ F : SourceTestCurveFiniteIndex I, sourceTestCurveAt
      (sourceTestCurveFiniteJoinFamily omega Γ F).toSourceTestCurvePredata q) =
      fun x => ⨆ F : SourceTestCurveFiniteIndex I, sourceTestCurveAt
        (sourceTestCurveFiniteJoinFamily omega Γ F).toSourceTestCurvePredata q x := by
    funext x
    exact iSup_apply
  unfold sourceTestCurveSupPotential
  rw [hL, hR]
  exact hSel q

omit [BorelSpace M] [ConnectedSpace M] in
/-- A genuine countable original carrier contains all selected finite sets and cofinal cutoffs. -/
theorem sourceTestCurveChoquet_countable_carrier {I : Type*} [Nonempty I]
    (Γ : I → SourceTestCurve θ) (S : ℚ → Set (SourceTestCurveFiniteIndex I))
    (hS : ∀ q, (S q).Countable) :
    ∃ J : Set I, J.Countable ∧ J.Nonempty ∧
      (∀ q, ∀ F ∈ S q, ∀ i ∈ F.val, i ∈ J) ∧
      (∀ q : ℚ, (q : ℝ) < sourceTestCurveSupCutoff Γ →
        ∃ i ∈ J, (q : ℝ) < (Γ i).max) := by
  classical
  let K := {q : ℚ // (q : ℝ) < sourceTestCurveSupCutoff Γ}
  have hcof (q : K) : ∃ i, (q.val : ℝ) < (Γ i).max :=
    sourceTestCurveSupCutoff_exists Γ q.property
  choose c hc using hcof
  let A : Set I := ⋃ q : ℚ, ⋃ F ∈ S q, (F.val : Set I)
  let J : Set I := insert (Classical.arbitrary I) (A ∪ range c)
  have hAc : A.Countable := countable_iUnion fun q =>
    (hS q).biUnion fun F _ => F.val.finite_toSet.countable
  refine ⟨J, (hAc.union (countable_range c)).insert _,
    ⟨Classical.arbitrary I, Or.inl rfl⟩, ?_, ?_⟩
  · intro q F hF i hi
    apply mem_insert_of_mem
    apply Or.inl
    exact mem_iUnion.mpr ⟨q, mem_iUnion₂.mpr ⟨F, hF, hi⟩⟩
  · intro q hq
    refine ⟨c ⟨q, hq⟩, mem_insert_of_mem _ (Or.inr (mem_range_self _)), hc ⟨q, hq⟩⟩

/-- Genuine selected whole-extension suprema and cofinal original cutoffs give actual rational slices. -/
theorem SourceTestCurve.generalSup_restrict_rational_at_eq {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max))
    (S : ℚ → Set (SourceTestCurveFiniteIndex I)) (J : Set I) [Nonempty J]
    (hsel : ∀ q : ℚ,
      uscRegularization (⨆ F : S q, sourceTestCurveAt
        (sourceTestCurveFiniteJoinFamily omega Γ F.val).toSourceTestCurvePredata q) =
        sourceTestCurveSupPotential (sourceTestCurveFiniteJoinFamily omega Γ) q)
    (hsub : ∀ q, ∀ F ∈ S q, ∀ i ∈ F.val, i ∈ J)
    (hcofinal : ∀ q : ℚ, (q : ℝ) < sourceTestCurveSupCutoff Γ →
      ∃ i ∈ J, (q : ℝ) < (Γ i).max)
    (q : ℚ) (hq : (q : ℝ) < (SourceTestCurve.generalSup omega Γ hb).max) :
    sourceTestCurveAt (SourceTestCurve.generalSup omega (fun j : J => Γ j.val)
      (sourceTestCurveRestrictedFamily_bddAbove Γ hb J)).toSourceTestCurvePredata q =
      sourceTestCurveAt (SourceTestCurve.generalSup omega Γ hb).toSourceTestCurvePredata q := by
  let R := SourceTestCurve.generalSup omega (fun j : J => Γ j.val)
    (sourceTestCurveRestrictedFamily_bddAbove Γ hb J)
  let T := SourceTestCurve.generalSup omega Γ hb
  have hmax : R.max = T.max := SourceTestCurve.generalSup_restrict_max_eq omega Γ hb J hcofinal
  have hs : (q : ℝ) < R.max := by rw [hmax]; exact hq
  have hRT : SourceTestCurvePOrder R T := SourceTestCurve.generalSup_restrict_le omega Γ hb J
  change sourceTestCurveAt R.toSourceTestCurvePredata q =
    sourceTestCurveAt T.toSourceTestCurvePredata q
  rw [sourceTestCurveAt_of_lt _ hs, sourceTestCurveAt_of_lt _ hq]
  apply le_antisymm
  · exact (sourceTestCurvePOrder_iff omega R T).mp hRT |>.2 q hs
  · change sourceTestCurveSupPotential (sourceTestCurveFiniteJoinFamily omega Γ) q ≤
      R.potential ⟨q, hs⟩
    rw [← hsel q]
    apply uscRegularization_le
      (R.native_thetaPSH ⟨q, hs⟩).1.quasiPlurisubharmonic.upperSemicontinuous
    apply iSup_le
    intro F
    have hF := SourceTestCurve.finiteJoin_le_generalSup_restrict omega Γ hb J
      F.val.val F.val.property (hsub q F.val F.property)
    have h := (sourceTestCurvePOrder_iff_extension omega _ R).mp hF q
    intro x
    simpa only [sourceTestCurveFiniteJoinFamily,
      sourceTestCurveAt_of_lt R.toSourceTestCurvePredata hs] using h x

/-- Whole original prop:testcurvChoquet: actual nonempty countable ORIGINAL indices and curve equality. -/
theorem source_test_curve_choquet_whole {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    ∃ (J : Set I) (hJ : J.Nonempty), J.Countable ∧
      (letI : Nonempty J := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
       SourceTestCurve.generalSup omega (fun j : J => Γ j.val)
         (sourceTestCurveRestrictedFamily_bddAbove Γ hb J)) =
        SourceTestCurve.generalSup omega Γ hb := by
  classical
  obtain ⟨S, hS, hsel⟩ := sourceTestCurveFiniteJoin_countable_at_selection omega Γ
  obtain ⟨J, hJc, hJn, hsub, hcofinal⟩ :=
    sourceTestCurveChoquet_countable_carrier Γ S (fun q => (hS q).1)
  refine ⟨J, hJn, hJc, ?_⟩
  let : Nonempty J := ⟨⟨hJn.choose, hJn.choose_spec⟩⟩
  have hmax := SourceTestCurve.generalSup_restrict_max_eq omega Γ hb J hcofinal
  apply SourceTestCurve.eq_of_order_and_rational_at_eq omega _ _ hmax
    (SourceTestCurve.generalSup_restrict_le omega Γ hb J)
  intro q hq
  exact SourceTestCurve.generalSup_restrict_rational_at_eq omega Γ hb S J hsel hsub
    hcofinal q (by simpa only [hmax] using hq)

end SGPT.PSH.VariableComplexAtlas
