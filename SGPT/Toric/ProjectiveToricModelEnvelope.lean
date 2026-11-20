import SGPT.Toric.ProjectiveToricRooftop
import SGPT.Toric.ProjectiveToricConstants
import SGPT.Toric.ProjectiveToricNewtonGeometry
import SGPT.PSH.SourceEnvelopeRooftop
import SGPT.Toric.ToricEnvelopeClosure
import SGPT.Foundations.Analysis.Pending.SmoothPotentialDomination

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- A finite shift preserves every original smooth local-potential test and
the original non-bottom witnesses, in every actual chart dimension. -/
theorem IsThetaPSH.add_const {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) (C : ℝ) :
    A.IsThetaPSH θ (fun x ↦ u x + (C : EReal)) := by
  refine ⟨fun x ↦ EReal.add_ne_top (hu.1 x) (EReal.coe_ne_top C), ?_⟩
  intro U g hg
  have hp := hu.2 U g hg
  apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
  constructor
  · intro i
    have hc : PlurisubharmonicOn (fun _ : ComplexModel (A.dimension i) ↦ (C : EReal))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
      fun z _ ↦ plurisubharmonicAt_const C (EReal.coe_ne_top C) z
    have hh := (hp.chartPlurisubharmonic i).add hc
    intro z hz
    apply (hh z hz).congr
    exact Eventually.of_forall fun y ↦
      add_right_comm (u ((A.chart i).symm y)) (g ((A.chart i).symm y) : EReal) (C : EReal)
  · intro x hx O hO hxO
    obtain ⟨y, hy, hfin⟩ := hp.locallyNondegenerate hg.1 x hx O hO hxO
    refine ⟨y, hy, ?_⟩
    change (u y + (C : EReal)) + (g y : EReal) ≠ ⊥
    rw [add_right_comm]
    exact EReal.add_ne_bot_iff.mpr ⟨hfin, EReal.coe_ne_bot C⟩

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.Toric

open Set Filter SGPT.Convex SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical

/-- The actual positive FS chart potentials supply all original universal
source theta-PSH tests for zero on the same quotient projective line. -/
theorem isThetaPSH_projectiveZero :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm
      (fun _ : Projectivization ℂ (Fin 2 → ℂ) ↦ (0 : EReal)) := by
  apply isThetaPSH_global_from_relative (fun _ ↦ projectiveFSPotential)
    (fun _ ↦ contDiff_projectiveFSPotential.contDiffOn) (fun _ _ _ ↦ rfl) ?_
    (fun _ ↦ by simp) ?_
  · intro i
    change Bool at i
    have hnn : ∀ z ∈ (univ : Set (ComplexModel 1)), ∀ v,
        0 ≤ smoothDDC projectiveFSPotential z ![v, Complex.I • v] := by
      intro z _ v
      by_cases hv : v = 0
      · subst v
        simp
      · exact (projectiveFSForm_strictlyPositive i z hv).le
    have hp := Pending.SmoothPotentialDomination.plurisubharmonicOn_coe_of_smoothDDC_nonneg
      isOpen_univ contDiff_projectiveFSPotential.contDiffOn hnn
    intro z _
    change ComplexModel 1 at z
    change PlurisubharmonicAt (fun z : ComplexModel 1 ↦
      (0 : EReal) + (projectiveFSPotential z : EReal)) z
    simpa only [zero_add] using hp z (mem_univ z)
  · intro x _ O _ hxO
    exact ⟨x, ⟨mem_univ x, hxO⟩, by simp⟩

private theorem modelEnvelope_legendre_closedProper
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) :
    projectiveToricLegendre u ∈ ClosedProperOnBody projectiveMomentInterval := by
  exact conjugate_mem_closedProperOnBody_of_mem_growthClass
    (innerₗ (EuclideanSpace ℝ (Fin 1))) isCompact_projectiveMomentInterval
    convex_projectiveMomentInterval (projectiveToricCorrectedDescent_mem_growthClass hu hiu)

/-- Every actual finite shift produces a genuine common minorant from the
closed-proper inverse; the rooftop is non-bottom and has its literal full dual. -/
theorem projectiveToricLegendre_shifted_rooftop
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (C : ℝ) :
    let R := thetaRooftop projectiveFSForm (fun p ↦ u p + (C : EReal)) 0
    R ≠ ⊥ ∧ projectiveLineAtlas.IsThetaPSH projectiveFSForm R ∧
      ProjectiveCircleInvariant R ∧ projectiveToricLegendre R =
        fun m ↦ max (projectiveToricLegendre (fun _ ↦ 0) m)
          (projectiveToricLegendre u m - (C : EReal)) := by
  let us := fun p ↦ u p + (C : EReal)
  have hus : projectiveLineAtlas.IsThetaPSH projectiveFSForm us := hu.add_const C
  have his : ProjectiveCircleInvariant us := fun a ha p ↦ congrArg
    (fun b : EReal ↦ b + (C : EReal)) (hiu a ha p)
  have hi0 : ProjectiveCircleInvariant (fun _ ↦ (0 : EReal)) := fun _ _ _ ↦ rfl
  have hGs := modelEnvelope_legendre_closedProper hus his
  have hG0 := modelEnvelope_legendre_closedProper isThetaPSH_projectiveZero hi0
  let K := fun m ↦ max (projectiveToricLegendre (fun _ ↦ 0) m)
    (projectiveToricLegendre us m)
  have hc : IsClosedConvex K := by
    let f : Bool → EuclideanSpace ℝ (Fin 1) → EReal := fun b ↦
      if b then projectiveToricLegendre us else projectiveToricLegendre (fun _ ↦ 0)
    have hf : ∀ b, IsClosedConvex (f b) := by
      intro b
      cases b
      · exact Or.inr (Or.inr ⟨hG0.1, hG0.2.1⟩)
      · exact Or.inr (Or.inr ⟨hGs.1, hGs.2.1⟩)
    have heq : convexSup f = K := by
      funext y
      simp [convexSup, f, K, iSup_bool_eq, max_comm]
    rw [← heq]
    exact isClosedConvex_convexSup hf
  obtain ⟨m, hm⟩ := hGs.1.2.1
  have hmP : m ∈ projectiveMomentInterval := by
    by_contra h
    have ht := hGs.2.2 m h
    change projectiveToricLegendre us m < ⊤ at hm
    rw [ht] at hm
    exact lt_irrefl _ hm
  have hG0finite : projectiveToricLegendre (fun _ ↦ 0) m < ⊤ := by
    have hmP' : m 0 ∈ Icc (0 : ℝ) 1 := hmP
    rw [projectiveToricLegendre_zero, projectiveLineEntropy_eq, if_pos hmP']
    exact EReal.coe_lt_top _
  have hK : K ∈ ClosedProperOnBody projectiveMomentInterval := by
    refine ⟨⟨isConvex_of_isClosedConvex hc, ⟨m, max_lt_iff.mpr ⟨hG0finite, hm⟩⟩, ?_⟩,
      lowerSemicontinuous_of_isClosedConvex hc, ?_⟩
    · intro y
      exact ne_of_gt ((bot_lt_iff_ne_bot.mpr (hG0.1.2.2 y)).trans_le (le_max_left _ _))
    · intro y hy
      simp [K, hG0.2.2 y hy]
  let w := projectiveToricEquivClosedProper.symm ⟨K, hK⟩
  have hw := w.property.1
  have hiw := w.property.2
  have hwG : projectiveToricLegendre w.val = K := by
    calc
      _ = (projectiveToricEquivClosedProper w).val :=
        (projectiveToricEquivClosedProper_apply w).symm
      _ = K := congrArg Subtype.val (projectiveToricEquivClosedProper.apply_symm_apply ⟨K, hK⟩)
  have hw0 : w.val ≤ (fun _ ↦ 0) :=
    (projectiveThetaPSH_le_iff_legendre hw isThetaPSH_projectiveZero hiw hi0).mpr
      (fun y ↦ by rw [hwG]; exact le_max_left _ _)
  have hws : w.val ≤ us :=
    (projectiveThetaPSH_le_iff_legendre hw hus hiw his).mpr
      (fun y ↦ by rw [hwG]; exact le_max_right _ _)
  let R := thetaRooftop projectiveFSForm us 0
  have hnonbot : R ≠ ⊥ := by
    let p := OnePoint.equivProjectivization ℂ (0 : ℂ)
    obtain ⟨y, _hy, hfin⟩ := hw.locallyNondegenerate p (mem_univ p)
      univ isOpen_univ (mem_univ p)
    intro hR
    apply hfin
    have hle := le_thetaRooftop hw hws hw0 y
    change w.val y ≤ R y at hle
    rw [hR] at hle
    exact le_bot_iff.mp hle
  have hR := isThetaPSH_projective_thetaRooftop hus isThetaPSH_projectiveZero hnonbot
  refine ⟨hnonbot, hR, projectiveCircleInvariant_thetaRooftop his hi0, ?_⟩
  change projectiveToricLegendre (thetaRooftop projectiveFSForm us (fun _ ↦ 0)) = _
  rw [projectiveToricLegendre_thetaRooftop hus isThetaPSH_projectiveZero his hi0 hnonbot]
  have hshift : projectiveToricLegendre us =
      fun m ↦ projectiveToricLegendre u m - (C : EReal) :=
    projectiveToricLegendre_add_const u C
  rw [hshift]
  funext y
  exact max_comm _ _

/-- Actual compact USC supplies a source competitor, so the independent
ALL-source singularity envelope really belongs to the original theta class. -/
theorem isThetaPSH_projectiveSourceEnvelope
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    projectiveLineAtlas.IsThetaPSH projectiveFSForm
        (sourceSingularityEnvelope projectiveFSForm u) ∧
      sourceSingularityEnvelope projectiveFSForm u ≤ 0 := by
  obtain ⟨B, hB⟩ := exists_upper_bound_projectiveThetaPSH hu
  have hn : Nonempty (sourceSingularityCompetitors projectiveFSForm u) := by
    refine ⟨⟨fun p ↦ u p + ((-B : ℝ) : EReal), hu.add_const (-B), ?_, ?_⟩⟩
    · intro p
      change u p + ((-B : ℝ) : EReal) ≤ (0 : EReal)
      have h := add_le_add (hB p) (le_refl ((-B : ℝ) : EReal))
      simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
    · exact (singularityLE_iff_exists_real _ _).mpr ⟨-B, fun _ ↦ le_rfl⟩
  exact ⟨isThetaPSH_sourceSingularityEnvelope_of_nonempty hn,
    sourceSingularityEnvelope_le_zero projectiveFSForm u⟩


/-- The actual all-real infimum closes precisely on the genuine Newton body;
properness, closedness and reversed family conjugation are produced internally. -/
theorem projectiveModelDual_mem_closedProper
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) :
    let g := fun m : EuclideanSpace ℝ (Fin 1) ↦ projectiveLineEntropyReal (m 0)
    let K := fun C : ℝ ↦ fun m ↦ max (projectiveToricLegendre (fun _ ↦ 0) m)
      (projectiveToricLegendre u m - (C : EReal))
    let G := realReferenceOnDomain g (projectiveToricNewtonBody u)
    convexClosure (fun m ↦ ⨅ C : ℝ, K C m) = G ∧
      G ∈ ClosedProperOnBody projectiveMomentInterval ∧
      conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip G =
        fun x ↦ ⨆ C : ℝ, conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip (K C) x := by
  classical
  let g := fun m : EuclideanSpace ℝ (Fin 1) ↦ projectiveLineEntropyReal (m 0)
  let D := effectiveDomain (projectiveToricLegendre u)
  let K := fun C : ℝ ↦ fun m ↦ max (projectiveToricLegendre (fun _ ↦ 0) m)
    (projectiveToricLegendre u m - (C : EReal))
  let f := fun m ↦ ⨅ C : ℝ, K C m
  let G := realReferenceOnDomain g (projectiveToricNewtonBody u)
  have hGu := modelEnvelope_legendre_closedProper hu hiu
  have hi0 : ProjectiveCircleInvariant (fun _ ↦ (0 : EReal)) := fun _ _ _ ↦ rfl
  have hG0 := modelEnvelope_legendre_closedProper isThetaPSH_projectiveZero hi0
  have hD : D ⊆ projectiveMomentInterval := by
    intro m hm
    by_contra hmP
    exact (ne_of_lt hm) (hGu.2.2 m hmP)
  have href (m : EuclideanSpace ℝ (Fin 1)) (hm : m ∈ projectiveMomentInterval) :
      projectiveToricLegendre (fun _ ↦ 0) m = (g m : EReal) := by
    have hm' : m 0 ∈ Icc (0 : ℝ) 1 := hm
    rw [projectiveToricLegendre_zero, projectiveLineEntropy_eq, if_pos hm']
    congr 1
    exact (projectiveLineEntropyReal_eq (m 0)).symm
  have hraw : f = realReferenceOnDomain g D := by
    funext m
    by_cases hmP : m ∈ projectiveMomentInterval
    · change (⨅ C : ℝ, max (projectiveToricLegendre (fun _ ↦ 0) m)
        (projectiveToricLegendre u m - (C : EReal))) = _
      rw [href m hmP]
      exact congrFun (iInf_max_sub_realReference g (projectiveToricLegendre u)) m
    · have hmD : m ∉ D := fun hm ↦ hmP (hD hm)
      simp [f, K, hG0.2.2 m hmP, hGu.2.2 m hmP,
        realReferenceOnDomain, hmD]
  have hepi : epigraph f = epigraph (projectiveToricLegendre (fun _ ↦ 0)) ∩
      (D ×ˢ (univ : Set ℝ)) := by
    ext p
    by_cases hp : p.1 ∈ D
    · rw [hraw]
      simp [epigraph, realReferenceOnDomain, hp, href p.1 (hD hp)]
    · rw [hraw]
      simp [epigraph, realReferenceOnDomain, hp]
  have hfc : IsConvex f := by
    change Convex ℝ (epigraph f)
    rw [hepi]
    exact hG0.1.1.inter ((convex_effectiveDomain hGu.1.1).prod convex_univ)
  have hfnobot : ∀ m, f m ≠ ⊥ := by
    rw [hraw]
    intro m
    by_cases hm : m ∈ D <;> simp [realReferenceOnDomain, hm]
  have hfp : IsProper f := by
    obtain ⟨m, hm⟩ := hGu.1.2.1
    refine ⟨hfc, ⟨m, ?_⟩, hfnobot⟩
    change f m < ⊤
    rw [hraw]
    simp [realReferenceOnDomain, hm, D]
  have hg : Continuous g := by
    exact (continuous_facetEntropyReal projectiveLineFacets projectiveLineOffsets).comp
      (by fun_prop)
  have heq : convexClosure f = G := by
    rw [convexClosure_of_forall_ne_bot hfnobot, hraw,
      regularization_realReferenceOnDomain g D hg.continuousOn]
    rfl
  have hGP : G ∈ ClosedProperOnBody projectiveMomentInterval := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← heq]
      exact isProper_convexClosure_of_isProper hfp
    · rw [← heq]
      exact lowerSemicontinuous_convexClosure f
    · intro m hm
      have hmΔ : m ∉ projectiveToricNewtonBody u :=
        fun hmΔ ↦ hm ((projectiveToricNewtonBody_properties hu hiu).2.2.2 hmΔ)
      simp [G, realReferenceOnDomain, hmΔ]
  refine ⟨heq, hGP, ?_⟩
  change conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip G =
    fun x ↦ ⨆ C : ℝ, conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip (K C) x
  rw [← heq, conjugate_convexClosure]
  exact conjugate_iInf (innerₗ (EuclideanSpace ℝ (Fin 1))).flip K


private theorem modelEnvelope_conjugate_rooftop
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (C : ℝ) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin 1))).flip
      (fun m ↦ max (projectiveToricLegendre (fun _ ↦ 0) m)
        (projectiveToricLegendre u m - (C : EReal))) =
      projectiveToricCorrectedDescent
        (thetaRooftop projectiveFSForm (fun p ↦ u p + (C : EReal)) 0) := by
  obtain ⟨_hnb, hR, hiR, hG⟩ := projectiveToricLegendre_shifted_rooftop hu hiu C
  have hf := projectiveToricCorrectedDescent_mem_growthClass hR hiR
  rw [← hG]
  exact (biconjugate_eq_convexClosure_of_isContPerfPair
    (innerₗ (EuclideanSpace ℝ (Fin 1))) hf.1.1).trans
      (convexClosure_eq_self_of_isClosedConvex (isClosedConvex_of_mem_growthClass _
        isCompact_projectiveMomentInterval nonempty_projectiveMomentInterval hf))

private theorem modelEnvelope_continuousAt_offPotential
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : Continuous f)
    {p : Projectivization ℂ (Fin 2 → ℂ)} (hp : p ∉ projectiveToricBoundary) :
    ContinuousAt (projectiveToricOffPotential f) p := by
  let e := projectiveModelChart false
  have hs : p ∈ e.source := projectiveToricBoundary_compl_subset_finite_source hp
  have hz : e p ∈ complexTorus 1 := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
  have he : ContinuousAt e p := e.continuousAt hs
  have ht : ContinuousAt tropicalization (e p) := by
    apply (PiLp.continuous_toLp 2 _).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    have hnorm : ContinuousAt (fun z : ComplexModel 1 ↦ ‖z i‖) (e p) :=
      (PiLp.continuous_apply 2 _ i).continuousAt.norm
    exact continuousAt_const.mul
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr (hz i))).comp
        (f := fun z : ComplexModel 1 ↦ ‖z i‖) hnorm)
  have hreal : ContinuousAt
      (fun q ↦ f (tropicalization (e q)) - projectiveFSPotential (e q)) p :=
    (hf.continuousAt.comp (ht.comp he)).sub
      (contDiff_projectiveFSPotential.continuous.continuousAt.comp he)
  exact continuous_coe_real_ereal.continuousAt.comp hreal

/-- The independent ALL-source envelope equals the actual inverse of the
manufactured closed-proper Newton-domain reference, including both boundary points. -/
theorem projectiveSourceEnvelope_eq_modelInverse
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) :
    let G := realReferenceOnDomain
      (fun m : EuclideanSpace ℝ (Fin 1) ↦ projectiveLineEntropyReal (m 0))
      (projectiveToricNewtonBody u)
    ∃ hG : G ∈ ClosedProperOnBody projectiveMomentInterval,
      sourceSingularityEnvelope projectiveFSForm u =
        (projectiveToricEquivClosedProper.symm ⟨G, hG⟩).val := by
  classical
  let B := innerₗ (EuclideanSpace ℝ (Fin 1))
  let G := realReferenceOnDomain
    (fun m : EuclideanSpace ℝ (Fin 1) ↦ projectiveLineEntropyReal (m 0))
    (projectiveToricNewtonBody u)
  let K := fun C : ℝ ↦ fun m ↦ max (projectiveToricLegendre (fun _ ↦ 0) m)
    (projectiveToricLegendre u m - (C : EReal))
  let R := fun C : ℝ ↦ thetaRooftop projectiveFSForm (fun p ↦ u p + (C : EReal)) 0
  obtain ⟨_hcl, hG, hsup⟩ := projectiveModelDual_mem_closedProper hu hiu
  have hgrowth : conjugate B.flip G ∈ GrowthClass B projectiveMomentInterval :=
    conjugate_mem_growthClass_of_mem_closedProperOnBody B isCompact_projectiveMomentInterval hG
  let f := growthToRealConvex B isCompact_projectiveMomentInterval
    nonempty_projectiveMomentInterval ⟨conjugate B.flip G, hgrowth⟩
  have hcoe : (fun x ↦ (f.val x : EReal)) = conjugate B.flip G :=
    funext (coe_growthToRealConvex B isCompact_projectiveMomentInterval
      nonempty_projectiveMomentInterval ⟨conjugate B.flip G, hgrowth⟩)
  have hf : f.val ∈ RealGrowthClass B projectiveMomentInterval := by
    refine ⟨f.property, ?_⟩
    rw [hcoe]
    exact hgrowth.2
  have hR (C : ℝ) := projectiveToricLegendre_shifted_rooftop hu hiu C
  have hsum : (fun x ↦ ⨆ C : ℝ, projectiveToricCorrectedDescent (R C) x) =
      fun x ↦ (f.val x : EReal) := by
    rw [hcoe]
    rw [hsup]
    funext x
    apply iSup_congr
    intro C
    exact congrFun (modelEnvelope_conjugate_rooftop hu hiu C).symm x
  have hraw : EqOn (fun p ↦ ⨆ C : ℝ, R C p)
      (projectiveToricOffPotential f.val) projectiveToricBoundaryᶜ := by
    intro p hp
    let e := projectiveModelChart false
    let z := e p
    have hs : p ∈ e.source := projectiveToricBoundary_compl_subset_finite_source hp
    have hz : z ∈ complexTorus 1 := projectiveFiniteCoordinate_mem_torus_of_off_boundary hp
    have hcorrect : (⨆ C : ℝ, R C p) + (projectiveFSPotential z : EReal) =
        (f.val (tropicalization z) : EReal) := by
      calc
        _ = ⨆ C : ℝ, R C p + (projectiveFSPotential z : EReal) :=
          (iSup_add_coe (fun C : ℝ ↦ R C p) (projectiveFSPotential z)).symm
        _ = ⨆ C : ℝ, projectiveToricCorrectedDescent (R C) (tropicalization z) := by
          apply iSup_congr
          intro C
          have h := projectiveToricCorrectedDescent_tropicalPullback (hR C).2.2.1 hz
          change projectiveToricCorrectedDescent (R C) (tropicalization z) =
            R C (e.symm z) + (projectiveFSPotential z : EReal) at h
          rw [e.left_inv hs] at h
          exact h.symm
        _ = _ := congrFun hsum (tropicalization z)
    have heq := congrArg (fun q : EReal ↦ q + ((-projectiveFSPotential z : ℝ) : EReal)) hcorrect
    have hcancel := corrected_add_sub (⨆ C : ℝ, R C p) (projectiveFSPotential z) 0
    simp only [zero_sub, EReal.coe_zero, add_zero] at hcancel
    rw [hcancel, ← EReal.coe_add] at heq
    change (⨆ C : ℝ, R C p) =
      ((f.val (tropicalization z) - projectiveFSPotential z : ℝ) : EReal)
    simpa only [sub_eq_add_neg] using heq
  have hfiniteContinuous : Continuous f.val :=
    continuousOn_univ.mp (f.property.continuousOn isOpen_univ)
  have hoff : EqOn (sourceSingularityEnvelope projectiveFSForm u)
      (projectiveToricOffPotential f.val) projectiveToricBoundaryᶜ := by
    intro p hp
    rw [sourceSingularityEnvelope_eq_uscSup_thetaRooftop]
    change uscRegularization (fun q ↦ ⨆ C : ℝ, R C q) p = _
    apply le_antisymm
    · apply uscRegularization_le_of_eventually_le
        (modelEnvelope_continuousAt_offPotential hfiniteContinuous hp).upperSemicontinuousAt
      filter_upwards [isClosed_projectiveToricBoundary.isOpen_compl.mem_nhds hp] with q hq
      exact (hraw hq).le
    · rw [← hraw hp]
      change (⨆ C : ℝ, R C p) ≤ uscRegularization (fun q ↦ ⨆ C : ℝ, R C q) p
      exact le_uscRegularization (fun q ↦ ⨆ C : ℝ, R C q) p
  have henvelope := (isThetaPSH_projectiveSourceEnvelope hu).1
  have hwhole : sourceSingularityEnvelope projectiveFSForm u = projectiveToricExtension f.val hf :=
    (Classical.choose_spec (existsUnique_projectiveToricExtension hf)).2
      _ ⟨henvelope, hoff⟩
  refine ⟨hG, ?_⟩
  change sourceSingularityEnvelope projectiveFSForm u =
    projectiveToricExtension f.val hf
  exact hwhole

/-- Circle invariance is inherited from the produced genuine inverse on the
whole quotient, rather than imposed on the ALL-source competitor family. -/
theorem projectiveSourceEnvelope_circleInvariant
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) :
    ProjectiveCircleInvariant (sourceSingularityEnvelope projectiveFSForm u) := by
  obtain ⟨hG, heq⟩ := projectiveSourceEnvelope_eq_modelInverse hu hiu
  rw [heq]
  exact (projectiveToricEquivClosedProper.symm _).property.2

/-- Literal original G_P-envelope formula, with genuine Newton-domain closure
and the actual original reference transform, retaining all infinite values. -/
theorem projectiveToricLegendre_sourceSingularityEnvelope
    {u : Projectivization ℂ (Fin 2 → ℂ) → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hiu : ProjectiveCircleInvariant u) (m : EuclideanSpace ℝ (Fin 1)) :
    projectiveToricLegendre (sourceSingularityEnvelope projectiveFSForm u) m =
      if m ∈ projectiveToricNewtonBody u then projectiveToricLegendre (fun _ ↦ 0) m else ⊤ := by
  classical
  obtain ⟨hG, heq⟩ := projectiveSourceEnvelope_eq_modelInverse hu hiu
  let G := realReferenceOnDomain
    (fun m : EuclideanSpace ℝ (Fin 1) ↦ projectiveLineEntropyReal (m 0))
    (projectiveToricNewtonBody u)
  let w := projectiveToricEquivClosedProper.symm ⟨G, hG⟩
  have hread : projectiveToricLegendre w.val = G := by
    calc
      _ = (projectiveToricEquivClosedProper w).val :=
        (projectiveToricEquivClosedProper_apply w).symm
      _ = G := congrArg Subtype.val
        (projectiveToricEquivClosedProper.apply_symm_apply ⟨G, hG⟩)
  rw [heq]
  change projectiveToricLegendre w.val m = _
  rw [hread]
  by_cases hm : m ∈ projectiveToricNewtonBody u
  · have hmP := (projectiveToricNewtonBody_properties hu hiu).2.2.2 hm
    have hmP' : m 0 ∈ Icc (0 : ℝ) 1 := hmP
    rw [if_pos hm, projectiveToricLegendre_zero, projectiveLineEntropy_eq, if_pos hmP']
    simp [G, realReferenceOnDomain, hm, projectiveLineEntropyReal_eq]
  · simp [G, realReferenceOnDomain, hm]

end SGPT.Toric
