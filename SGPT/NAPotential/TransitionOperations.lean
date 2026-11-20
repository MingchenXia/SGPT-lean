import SGPT.PSH.SourceTestCurveGeneralLaws
import SGPT.PSH.SourceTestCurveDecreasingProjection
import SGPT.PSH.SourceTestCurveGeneralScaling

/-! # Transitions of positive `𝓘`-model test curves commute with the lattice operations

The transition maps `P_{θ+ω}[•]_𝓘` of the inverse system defining `PSH^NA(X, θ)`
(`def:NApotential:L24`) are the existing all-competitor `𝓘`-envelope transitions
`sourceIModelTestCurveTransition`.  On positive `𝓘`-model test curves the `𝓘`-envelope of
every slice equals its `P`-envelope (the slices are `𝓘`-good, `ex:ImodelIgood`), so a
transition is the existing semipositive `P`-projection followed by an identification of the
whole background.  Combined with the existing compatibility of the `P`-projection with the
binary join (`lma:testcurlorPthetapomega`), the general supremum (`lma:testcursupcompatible`)
and the decreasing infimum (`lma:testcurinfcompatible`), this shows that the transitions
commute with these three operations on positive `𝓘`-model test curves.  These are the facts
behind the book's sentences "It follows from `lma:testcurlorPthetapomega` that
`Γ ∨ Γ' ∈ PSH^NA(X, θ)`", and the analogous ones for `uscsup` and `inf`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {α β θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The added form `β - α` of the transition from background `α` to background `β`. -/
def sourceNATransitionForm (α β : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    AtlasClosedRealOneOneForm (ofFixedModel n M) :=
  nativeClosedFormToAtlas (atlasClosedFormToNative β - atlasClosedFormToNative α)

theorem sourceNATransitionForm_semipositive
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive) :
    (atlasClosedFormToNative (sourceNATransitionForm α β)).val.IsSemipositive := by
  simpa only [sourceNATransitionForm, sourceNativeAtlasForm_roundTrip] using hαβ

/-- Adding the transition form to `α` gives the entire atlas form `β`. -/
theorem sourceNATransitionForm_add (α β : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    α.add (sourceNATransitionForm α β) = β := by
  apply Function.LeftInverse.injective (fun θ ↦ sourceAtlasNativeForm_roundTrip θ)
  simp only [sourceNATransitionForm, sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip]
  abel

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- On a positive `𝓘`-model test curve, the `𝓘`-envelope transition is the semipositive
`P`-projection by the difference form, transported to the target background. -/
theorem sourceIModelTestCurveTransition_val_eq_projection (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : SourcePositiveIModelTestCurve α) :
    (sourceIModelTestCurveTransition omega hαβ G).val =
      (G.val.semipositiveProjection omega (sourceNATransitionForm α β)
        (sourceNATransitionForm_semipositive hαβ)).castBackground
        (sourceNATransitionForm_add α β) := by
  apply SourceTestCurve.ext_of_max_potential
  · rw [sourceIModelTestCurveTransition_max, SourceTestCurve.castBackground_max,
      SourceTestCurve.semipositiveProjection_max]
  · intro r hr hs
    have hrG : r < G.val.max := by
      rwa [sourceIModelTestCurveTransition_max] at hr
    rw [sourceIModelTestCurveTransition_potential omega hαβ G r hrG hr,
      SourceTestCurve.castBackground_potential (G.val.semipositiveProjection omega
        (sourceNATransitionForm α β) (sourceNATransitionForm_semipositive hαβ)) _ r hrG hs]
    change sourceIEnvelope β (G.val.potential ⟨r, hrG⟩) =
      sourceSingularityEnvelope (α.add (sourceNATransitionForm α β)) (G.val.potential ⟨r, hrG⟩)
    have hi : sourceIModel α (G.val.potential ⟨r, hrG⟩) :=
      (sourceIModel_iff_native α _).mpr
        (((sourceIModelTestCurvesPositive_iff_slices omega G.val).mp G.property) ⟨r, hrG⟩)
    have h := (sourceIModel_transition_envelope_and_mass omega hαβ hi
      (G.val.mass_positive omega ⟨r, hrG⟩)).1
    rw [sourceNATransitionForm_add]
    exact h.symm

omit [BorelSpace M] [ConnectedSpace M] in
/-- Equal curves have equal slices at every common parameter. -/
theorem sourceTestCurve_potential_congr {C D : SourceTestCurve α} (h : C = D)
    (r : ℝ) (hr : r < C.max) (hs : r < D.max) :
    C.potential ⟨r, hr⟩ = D.potential ⟨r, hs⟩ := by
  cases h
  rfl

/-! ### The binary join -/

/-- The Kähler form passed to the join is a proof resource only. -/
theorem SourceTestCurve.join_ambient_independent (omega omega' : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) : Γ.join omega Δ = Γ.join omega' Δ := rfl

/-- The join commutes with the identification of equal backgrounds. -/
theorem SourceTestCurve.castBackground_join (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve α) (h : α = β) :
    (Γ.join omega Δ).castBackground h = (Γ.castBackground h).join omega (Δ.castBackground h) := by
  cases h
  rfl

/-- The book's join `Γ ∨ Γ'` (`def:testcurlor`) of two positive `𝓘`-model test curves,
again a positive `𝓘`-model test curve (`cor:testcurvlorprop`). -/
def SourcePositiveIModelTestCurve.join (omega : KahlerBackground n M)
    (G H : SourcePositiveIModelTestCurve α) : SourcePositiveIModelTestCurve α :=
  ⟨G.val.join omega H.val,
    SourceTestCurve.join_mem_iModelPositive omega G.val H.val G.property H.property⟩

theorem SourcePositiveIModelTestCurve.join_val (omega : KahlerBackground n M)
    (G H : SourcePositiveIModelTestCurve α) : (G.join omega H).val = G.val.join omega H.val :=
  rfl

theorem SourcePositiveIModelTestCurve.join_ambient_independent
    (omega omega' : KahlerBackground n M) (G H : SourcePositiveIModelTestCurve α) :
    G.join omega H = G.join omega' H := rfl

theorem SourcePositiveIModelTestCurve.castBackground_join (omega : KahlerBackground n M)
    (G H : SourcePositiveIModelTestCurve α) (h : α = β) :
    (G.join omega H).castBackground h = (G.castBackground h).join omega (H.castBackground h) := by
  cases h
  rfl

/-- Transitions commute with the binary join of positive `𝓘`-model test curves. -/
theorem sourceIModelTestCurveTransition_join (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G H : SourcePositiveIModelTestCurve α) :
    sourceIModelTestCurveTransition omega hαβ (G.join omega H) =
      (sourceIModelTestCurveTransition omega hαβ G).join omega
        (sourceIModelTestCurveTransition omega hαβ H) := by
  apply Subtype.ext
  rw [SourcePositiveIModelTestCurve.join_val, sourceIModelTestCurveTransition_val_eq_projection,
    sourceIModelTestCurveTransition_val_eq_projection,
    sourceIModelTestCurveTransition_val_eq_projection, SourcePositiveIModelTestCurve.join_val,
    source_test_curve_join_semipositive_projection_compatible, SourceTestCurve.castBackground_join]

theorem SourcePositiveIModelTestCurve.join_comm (omega : KahlerBackground n M)
    (G H : SourcePositiveIModelTestCurve α) : G.join omega H = H.join omega G :=
  Subtype.ext (G.val.join_comm omega H.val)

theorem SourcePositiveIModelTestCurve.join_assoc (omega : KahlerBackground n M)
    (G H K : SourcePositiveIModelTestCurve α) :
    (G.join omega H).join omega K = G.join omega (H.join omega K) :=
  Subtype.ext (G.val.join_assoc omega H.val K.val)

/-! ### The general (usc) supremum -/

/-- The Kähler form passed to the general supremum is a proof resource only. -/
theorem SourceTestCurve.generalSup_ambient_independent {I : Type*} [Nonempty I]
    (omega omega' : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    SourceTestCurve.generalSup omega Γ hb = SourceTestCurve.generalSup omega' Γ hb :=
  SourceTestCurvePOrder.antisymm omega
    (SourceTestCurve.generalSup_le omega Γ hb _
      (fun i => SourceTestCurve.le_generalSup omega' Γ hb i))
    (SourceTestCurve.generalSup_le omega' Γ hb _
      (fun i => SourceTestCurve.le_generalSup omega Γ hb i))

/-- The general supremum depends only on the family, not on the proof of boundedness. -/
theorem SourceTestCurve.generalSup_congr {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) {Γ Γ' : I → SourceTestCurve θ} (h : Γ = Γ')
    (hb : BddAbove (range fun i => (Γ i).max)) (hb' : BddAbove (range fun i => (Γ' i).max)) :
    SourceTestCurve.generalSup omega Γ hb = SourceTestCurve.generalSup omega Γ' hb' := by
  subst h
  rfl

omit [BorelSpace M] [ConnectedSpace M] in
/-- A cutoff bound for a family transported to an equal background. -/
theorem sourceTestCurveCastFamily_bddAbove {I : Type*} (Γ : I → SourceTestCurve α)
    (h : α = β) (hb : BddAbove (range fun i => (Γ i).max)) :
    BddAbove (range fun i => ((Γ i).castBackground h).max) := by
  simpa only [SourceTestCurve.castBackground_max] using hb

/-- The general supremum commutes with the identification of equal backgrounds. -/
theorem SourceTestCurve.castBackground_generalSup {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve α) (h : α = β)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    (SourceTestCurve.generalSup omega Γ hb).castBackground h =
      SourceTestCurve.generalSup omega (fun i => (Γ i).castBackground h)
        (sourceTestCurveCastFamily_bddAbove Γ h hb) := by
  cases h
  rfl

/-- The book's usc supremum (`def:testcurvsupsgeneral`) of a family of positive `𝓘`-model test
curves with bounded cutoffs, again a positive `𝓘`-model test curve. -/
def SourcePositiveIModelTestCurve.generalSup {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (G : I → SourcePositiveIModelTestCurve α)
    (hb : BddAbove (range fun i => (G i).val.max)) : SourcePositiveIModelTestCurve α :=
  ⟨SourceTestCurve.generalSup omega (fun i => (G i).val) hb,
    SourceTestCurve.generalSup_mem_iModelPositive omega _ hb (fun i => (G i).property)⟩

theorem SourcePositiveIModelTestCurve.generalSup_val {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (G : I → SourcePositiveIModelTestCurve α)
    (hb : BddAbove (range fun i => (G i).val.max)) :
    (SourcePositiveIModelTestCurve.generalSup omega G hb).val =
      SourceTestCurve.generalSup omega (fun i => (G i).val) hb := rfl

theorem SourcePositiveIModelTestCurve.generalSup_ambient_independent {I : Type*} [Nonempty I]
    (omega omega' : KahlerBackground n M) (G : I → SourcePositiveIModelTestCurve α)
    (hb : BddAbove (range fun i => (G i).val.max)) :
    SourcePositiveIModelTestCurve.generalSup omega G hb =
      SourcePositiveIModelTestCurve.generalSup omega' G hb :=
  Subtype.ext (SourceTestCurve.generalSup_ambient_independent omega omega' _ hb)

theorem SourcePositiveIModelTestCurve.generalSup_congr {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) {G G' : I → SourcePositiveIModelTestCurve α} (h : G = G')
    (hb : BddAbove (range fun i => (G i).val.max))
    (hb' : BddAbove (range fun i => (G' i).val.max)) :
    SourcePositiveIModelTestCurve.generalSup omega G hb =
      SourcePositiveIModelTestCurve.generalSup omega G' hb' := by
  subst h
  rfl

omit [BorelSpace M] [ConnectedSpace M] in
/-- A cutoff bound for a family of positive curves transported to an equal background. -/
theorem sourcePositiveIModelTestCurveCastFamily_bddAbove {I : Type*}
    (G : I → SourcePositiveIModelTestCurve α) (h : α = β)
    (hb : BddAbove (range fun i => (G i).val.max)) :
    BddAbove (range fun i => ((G i).castBackground h).val.max) := by
  simpa only [SourcePositiveIModelTestCurve.castBackground_max] using hb

/-- The usc supremum of positive curves commutes with the identification of equal backgrounds. -/
theorem SourcePositiveIModelTestCurve.castBackground_generalSup {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (G : I → SourcePositiveIModelTestCurve α) (h : α = β)
    (hb : BddAbove (range fun i => (G i).val.max)) :
    (SourcePositiveIModelTestCurve.generalSup omega G hb).castBackground h =
      SourcePositiveIModelTestCurve.generalSup omega (fun i => (G i).castBackground h)
        (sourcePositiveIModelTestCurveCastFamily_bddAbove G h hb) := by
  cases h
  rfl

/-- Positive rescaling commutes with the usc supremum of positive curves
(the supremum clause of `prop:resclacompat`). -/
theorem SourcePositiveIModelTestCurve.generalSup_positiveScale {I : Type*} [Nonempty I]
    (omega omega' : KahlerBackground n M) (G : I → SourcePositiveIModelTestCurve α)
    (hb : BddAbove (range fun i => (G i).val.max)) {c : ℝ} (hc : 0 < c) :
    (SourcePositiveIModelTestCurve.generalSup omega G hb).positiveScale omega' hc =
      SourcePositiveIModelTestCurve.generalSup omega (fun i => (G i).positiveScale omega' hc)
        (sourceTestCurvePositiveScaledFamily_bddAbove (fun i => (G i).val) hb hc) :=
  Subtype.ext (SourceTestCurve.generalSup_positiveScale omega (fun i => (G i).val) hb hc)

/-- Transitions keep the cutoffs, hence keep a cutoff bound. -/
theorem sourceIModelTestCurveTransition_family_bddAbove {I : Type*}
    (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : I → SourcePositiveIModelTestCurve α) (hb : BddAbove (range fun i => (G i).val.max)) :
    BddAbove (range fun i => (sourceIModelTestCurveTransition omega hαβ (G i)).val.max) := by
  simpa only [sourceIModelTestCurveTransition_max] using hb

/-- Transitions commute with the usc supremum of positive `𝓘`-model test curves.  The target
family is any family agreeing with the transitioned one. -/
theorem sourceIModelTestCurveTransition_generalSup {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : I → SourcePositiveIModelTestCurve α) (hb : BddAbove (range fun i => (G i).val.max))
    (H : I → SourcePositiveIModelTestCurve β)
    (hH : ∀ i, sourceIModelTestCurveTransition omega hαβ (G i) = H i)
    (hb' : BddAbove (range fun i => (H i).val.max)) :
    sourceIModelTestCurveTransition omega hαβ (SourcePositiveIModelTestCurve.generalSup omega G hb) =
      SourcePositiveIModelTestCurve.generalSup omega H hb' := by
  apply Subtype.ext
  rw [sourceIModelTestCurveTransition_val_eq_projection,
    SourcePositiveIModelTestCurve.generalSup_val, SourcePositiveIModelTestCurve.generalSup_val,
    source_test_curve_generalSup_semipositive_projection_compatible,
    SourceTestCurve.castBackground_generalSup]
  apply SourceTestCurve.generalSup_congr
  funext i
  rw [← hH i, sourceIModelTestCurveTransition_val_eq_projection]

/-! ### The decreasing infimum -/

section DecreasingInf

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- The decreasing infimum depends only on the family, not on the proofs of its hypotheses. -/
theorem SourceTestCurve.decreasingInf_congr (omega : KahlerBackground n M)
    {Γ Γ' : I → SourceTestCurve θ} (h : Γ = Γ')
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb)
    (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ' j) (Γ' i))
    (hb' : BddBelow (range fun i => (Γ' i).max)) (hm' : SourceTestCurveInfMassCondition Γ' hb') :
    SourceTestCurve.decreasingInf omega Γ ha hb hm =
      SourceTestCurve.decreasingInf omega Γ' ha' hb' hm' := by
  subst h
  rfl

/-- The Kähler form passed to the decreasing infimum is a proof resource only. -/
theorem SourceTestCurve.decreasingInf_ambient_independent (omega omega' : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb) :
    SourceTestCurve.decreasingInf omega Γ ha hb hm =
      SourceTestCurve.decreasingInf omega' Γ ha hb hm := rfl

/-- The decreasing infimum commutes with the identification of equal backgrounds. -/
theorem SourceTestCurve.castBackground_decreasingInf (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve α) (h : α = β)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb)
    (Γ' : I → SourceTestCurve β) (hΓ : ∀ i, (Γ i).castBackground h = Γ' i)
    (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ' j) (Γ' i))
    (hb' : BddBelow (range fun i => (Γ' i).max)) (hm' : SourceTestCurveInfMassCondition Γ' hb') :
    (SourceTestCurve.decreasingInf omega Γ ha hb hm).castBackground h =
      SourceTestCurve.decreasingInf omega Γ' ha' hb' hm' := by
  cases h
  have : Γ = Γ' := funext hΓ
  subst this
  rfl

/-- The book's infimum of a decreasing net (`def:testcurinf`) of positive `𝓘`-model test curves,
again a positive `𝓘`-model test curve (`prop:inftcistc`). -/
def SourcePositiveIModelTestCurve.decreasingInf (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb) :
    SourcePositiveIModelTestCurve α :=
  ⟨SourceTestCurve.decreasingInf omega (fun i => (G i).val) ha hb hm,
    (source_test_curve_decreasing_inf_whole omega _ ha hb hm).2 (fun i => (G i).property)⟩

theorem SourcePositiveIModelTestCurve.decreasingInf_val (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb) :
    (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val =
      SourceTestCurve.decreasingInf omega (fun i => (G i).val) ha hb hm := rfl

theorem SourcePositiveIModelTestCurve.decreasingInf_ambient_independent
    (omega omega' : KahlerBackground n M) (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb) :
    SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm =
      SourcePositiveIModelTestCurve.decreasingInf omega' G ha hb hm := rfl

theorem SourcePositiveIModelTestCurve.decreasingInf_congr (omega : KahlerBackground n M)
    {G G' : I → SourcePositiveIModelTestCurve α} (h : G = G')
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb)
    (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (G' j).val (G' i).val)
    (hb' : BddBelow (range fun i => (G' i).val.max))
    (hm' : SourceTestCurveInfMassCondition (fun i => (G' i).val) hb') :
    SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm =
      SourcePositiveIModelTestCurve.decreasingInf omega G' ha' hb' hm' := by
  subst h
  rfl

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- The uniform positive mass condition survives every transition: transitions preserve the
mass of positive `𝓘`-model slices in the larger background, which dominates the old mass. -/
theorem sourceIModelTestCurveTransition_family_massCondition (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : I → SourcePositiveIModelTestCurve α)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb)
    (H : I → SourcePositiveIModelTestCurve β)
    (hH : ∀ i, sourceIModelTestCurveTransition omega hαβ (G i) = H i)
    (hb' : BddBelow (range fun i => (H i).val.max)) :
    SourceTestCurveInfMassCondition (fun i => (H i).val) hb' := by
  obtain ⟨r, hr⟩ := hm
  have hmax (i : I) : (H i).val.max = (G i).val.max := by
    rw [← hH i, sourceIModelTestCurveTransition_max]
  have hcut : sourceTestCurveInfCutoff (fun i => (H i).val) =
      sourceTestCurveInfCutoff (fun i => (G i).val) := by
    unfold sourceTestCurveInfCutoff
    simp only [hmax]
  refine ⟨⟨r.val, by rw [hcut]; exact r.property⟩, hr.trans_le ?_⟩
  apply iInf_mono
  intro i
  have hri : r.val < (G i).val.max :=
    r.property.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)
  have hrH : r.val < (H i).val.max := by rw [hmax]; exact hri
  have hi : sourceIModel α ((G i).val.potential ⟨r.val, hri⟩) :=
    (sourceIModel_iff_native α _).mpr
      (((sourceIModelTestCurvesPositive_iff_slices omega (G i).val).mp (G i).property)
        ⟨r.val, hri⟩)
  have hpos := (G i).val.mass_positive omega ⟨r.val, hri⟩
  have hmono := sourcePotentialMass_mono_background hαβ hi.1
  have heq := (sourceIModel_transition_envelope_and_mass omega hαβ hi hpos).2
  have hT : r.val < (sourceIModelTestCurveTransition omega hαβ (G i)).val.max := by
    rw [sourceIModelTestCurveTransition_max]; exact hri
  have hpot : (H i).val.potential ⟨r.val, hrH⟩ =
      sourceIEnvelope β ((G i).val.potential ⟨r.val, hri⟩) :=
    (sourceTestCurve_potential_congr (congrArg Subtype.val (hH i)) r.val hT hrH).symm.trans
      (sourceIModelTestCurveTransition_potential omega hαβ (G i) r.val hri hT)
  calc sourcePotentialNonPluripolarMeasure α ((G i).val.potential ⟨r.val, hri⟩)
        ((G i).val.thetaPSH _) univ
      ≤ sourcePotentialNonPluripolarMeasure β ((G i).val.potential ⟨r.val, hri⟩)
          (sourceThetaPSH_of_semipositive_difference hαβ hi.1) univ := hmono
    _ = sourcePotentialNonPluripolarMeasure β (sourceIEnvelope β ((G i).val.potential ⟨r.val, hri⟩))
          (isThetaPSH_sourceIEnvelope (sourceThetaPSH_of_semipositive_difference hαβ hi.1)) univ :=
        heq.symm
    _ = sourcePotentialNonPluripolarMeasure β ((H i).val.potential ⟨r.val, hrH⟩)
          ((H i).val.thetaPSH _) univ := sourcePotentialMass_congr hpot.symm _ _

/-- Transitions commute with the decreasing infimum of positive `𝓘`-model test curves. -/
theorem sourceIModelTestCurveTransition_decreasingInf (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb)
    (H : I → SourcePositiveIModelTestCurve β)
    (hH : ∀ i, sourceIModelTestCurveTransition omega hαβ (G i) = H i)
    (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (H j).val (H i).val)
    (hb' : BddBelow (range fun i => (H i).val.max))
    (hm' : SourceTestCurveInfMassCondition (fun i => (H i).val) hb') :
    sourceIModelTestCurveTransition omega hαβ
        (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm) =
      SourcePositiveIModelTestCurve.decreasingInf omega H ha' hb' hm' := by
  have hHv : (fun i => (H i).val) = fun i =>
      ((G i).val.semipositiveProjection omega (sourceNATransitionForm α β)
        (sourceNATransitionForm_semipositive hαβ)).castBackground
        (sourceNATransitionForm_add α β) := by
    funext i
    rw [← hH i, sourceIModelTestCurveTransition_val_eq_projection]
  apply Subtype.ext
  rw [sourceIModelTestCurveTransition_val_eq_projection,
    SourcePositiveIModelTestCurve.decreasingInf_val, SourcePositiveIModelTestCurve.decreasingInf_val,
    source_test_curve_decreasingInf_semipositive_projection_compatible]
  apply SourceTestCurve.castBackground_decreasingInf
  intro i
  exact (congrFun hHv i).symm

end DecreasingInf

end SGPT.PSH.VariableComplexAtlas
