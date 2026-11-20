import SGPT.Foundations.Analysis.Pending.FiniteHolomorphicFamilyLocalPrincipalization
import SGPT.Foundations.Analysis.Pending.FiniteFamilyTruncationModificationTransport
import SGPT.Foundations.Analysis.Pending.AdmissiblePrincipalizationAnalyticModification
import SGPT.Foundations.Analysis.Pending.FiniteGermIdealPullbackGenerators
import SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus
import SGPT.Foundations.Analysis.Pending.PointPowerTruncationZeroTest

set_option autoImplicit false

/-! # Strict truncation stability for every complete original finite holomorphic family -/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteFamilyStrictTruncationStability

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  NormalCrossings HironakaAdmissibleSequence HolomorphicGermReducednessBridge

noncomputable section

private theorem integrable_zero_dimension {s : ℕ}
    (G : Fin s → ComplexModel 0 → ℂ)
    (hne : ∃ i, ∃ᶠ z in 𝓝 (0 : ComplexModel 0), G i z ≠ 0)
    {q : ℝ} (hq : 0 < q) (F : ComplexModel 0 → ℂ) :
    MultiplierIntegrableAt (generatorLog G) q F 0 volume := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨z, hz⟩ := hi.exists
  have hGi : G i 0 ≠ 0 := by simpa only [Subsingleton.elim z 0] using hz
  have hbot : generatorLog G 0 ≠ ⊥ := fun h =>
    hGi ((generatorLog_eq_bot_iff G 0).mp h i)
  have htop := generatorLog_ne_top G 0
  have hval (z : ComplexModel 0) : generatorLog G z = ((generatorLog G 0).toReal : EReal) := by
    rw [Subsingleton.elim z 0]
    exact (EReal.coe_toReal htop hbot).symm
  have hF : F = fun _ => F 0 := by
    funext z
    exact congrArg F (Subsingleton.elim z 0)
  have hdens : multiplierDensity (generatorLog G) q F = fun _ =>
      ENNReal.ofReal (‖F 0‖ ^ 2) * ENNReal.ofReal (Real.exp (-(q * (generatorLog G 0).toReal))) := by
    funext z
    have hFz : F z = F 0 := congrArg F (Subsingleton.elim z 0)
    simp only [multiplierDensity, hval z, hFz, multiplierWeight_coe]
  refine ⟨hq, ball 0 1, isOpen_ball, mem_ball_self one_pos, ?_, ?_, ?_⟩
  · rw [hF]
    exact differentiableOn_const (F 0)
  · rw [hdens]
    exact aemeasurable_const
  · rw [hdens, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) measure_ball_lt_top

private theorem nonzero_family_positive_dimension {m s : ℕ}
    (G : Fin s → ComplexModel (m + 1) → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (G i) z)
    (hne : ∃ i, ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), G i z ≠ 0)
    {q q' : ℝ} (hq' : 0 < q') (hqq' : q' < q) {F : ComplexModel (m + 1) → ℂ}
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel (m + 1) → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) ⊔
        (Ideal.span (Set.range fun j : Fin (m + 1) => HolGerm.mk
          (fun z : ComplexModel (m + 1) => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt (generatorLog G) q' F 0 volume := by
  classical
  obtain ⟨B, h0B, _hBconn, hGB, I, hgenI, hIcoh, U, hU0, _hUc,
      Y, hYt, hYc, hYm, π, D, E, hadm, hpb, hE, hsupp, hZ, _hiso⟩ :=
    FiniteHolomorphicFamilyLocalPrincipalization.exists_principalization_of_nonzero_family_germ
      G hG hne
  let b₀ : B := ⟨0, h0B⟩
  let x₀ : U := ⟨b₀, hU0 (by rfl)⟩
  let gB : Fin s → B → ℂ := fun i b => G i b.val
  let gU : Fin s → U → ℂ := fun i z => G i z.val.val
  let Iu : GermIdeal (m + 1) U := GermIdeal.pullback (m := m + 1) (Subtype.val : U → B) I
  have hBhol (i : Fin s) (b : B) : HolomorphicAt (m + 1) (gB i) b := by
    apply Eventually.of_forall
    intro z
    apply (mdifferentiableAt_comp_val_iff B).mpr
    simpa only [mdifferentiableAt_iff_differentiableAt] using hGB i z.val z.property
  have hUhol (i : Fin s) (z : U) : HolomorphicAt (m + 1) (gU i) z :=
    (hBhol i z.val).comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)
  have hgenU (z : U) (g : U → ℂ) : Iu.mem z g ↔
      IsInSpanAt (n := m + 1) (· ∈ Set.range gU) z g :=
    FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt) I gB
      (fun i => hBhol i z.val) (hgenI z.val) g
  have hcohU : Iu.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hIcoh
  have hZU : Iu.zeroLocus = (Subtype.val : U → B) ⁻¹' I.zeroLocus :=
    BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hIcoh
  have hadmU : IsAdmissibleBlowupSequence (m + 1) U [] Iu.zeroLocus Y π E := by
    simpa only [hZU] using hadm
  have hsuppU : D.support = π ⁻¹' Iu.zeroLocus := by
    simpa only [hZU] using hZ
  have hπ := AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    hcohU hadmU D hsuppU
  have hfull (y : Y) (g : Y → ℂ) : D.ideal.mem y g ↔
      IsInSpanAt (n := m + 1) (· ∈ Set.range fun i => gU i ∘ π) y g := by
    have h := FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun _ => hπ.1.contMDiffAt) Iu gU
      (fun i => hUhol i (π y)) (hgenU (π y)) g
    simpa only [Iu, hpb] using h
  let d := complexChartAt (n := m + 1) x₀
  have hchart (z : U) : d.val z = z.val.val := by
    change (chartAt (ComplexModel (m + 1)) (0 : ComplexModel (m + 1))) z.val.val = z.val.val
    rw [chartAt_self_eq]
    rfl
  have hcenter : d.val x₀ = 0 := hchart x₀
  let Φ : LocalHolomorphicEquivAt (n := m + 1) (d.val x₀) := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := id
    invFun := id
    toFun_holomorphic := differentiable_id.differentiableOn
    invFun_holomorphic := differentiable_id.differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun _ _ => rfl
    right_inv := fun _ _ => rfl }
  have hΦ0 : Φ.toFun (d.val x₀) = 0 := hcenter
  let A : Fin s → ComplexModel (m + 1) → ℂ := fun i z => gU i (d.val.symm (Φ.invFun z))
  have hfamily (i : Fin s) : A i =ᶠ[𝓝 (0 : ComplexModel (m + 1))] G i := by
    have hdt : (0 : ComplexModel (m + 1)) ∈ d.val.target := by
      rw [← hcenter]
      exact d.val.map_source (mem_complexChartAt_source x₀)
    filter_upwards [d.val.open_target.mem_nhds hdt] with z hz
    change G i (d.val.symm z).val.val = G i z
    exact congrArg (G i) ((hchart (d.val.symm z)).symm.trans (d.val.right_inv hz))
  have hGA (i : Fin s) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (A i) z := by
    have h := DerivativeIdeal.eventually_differentiableAt_comp_symm d
      (mem_complexChartAt_source x₀) (hUhol i x₀)
    simpa only [hcenter, A, Φ, id_eq, Function.comp_def] using h
  have hspan : Ideal.span (Set.range fun i => HolGerm.mk (A i) (hGA i)) =
      Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) := by
    have hmk : (fun i => HolGerm.mk (A i) (hGA i)) =
        (fun i => HolGerm.mk (G i) (hG i)) := by
      funext i
      exact HolGerm.mk_eq_mk_iff.mpr (hfamily i)
    rw [hmk]
  have hintA : MultiplierIntegrableAt (generatorLog A) q' F 0 volume := by
    apply FiniteFamilyTruncationModificationTransport.multiplierIntegrableAt_of_all_truncations_of_modification
      hπ x₀ Φ hΦ0 gU (fun i => hUhol i x₀) D E hE hsupp
      (fun y _ => hfull y) hq' hqq'
    intro N
    obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
    refine ⟨r, Q, hQ, ?_, hint⟩
    intro i
    change HolGerm.mk (Q i) (hQ i) ∈
      Ideal.span (Set.range fun j => HolGerm.mk (A j) (hGA j)) ⊔
        (Ideal.span (Set.range fun j : Fin (m + 1) => HolGerm.mk
          (fun z : ComplexModel (m + 1) => z j) (eventually_differentiableAt_coordinate j))) ^ N
    rw [hspan]
    exact hmem i
  apply hintA.congr ?_ EventuallyEq.rfl
  filter_upwards [eventually_all.mpr hfamily] with z hz
  simp only [generatorLog_eq_log_sum]
  exact congrArg (fun t : ℝ => ENNReal.log (ENNReal.ofReal t))
    (Finset.sum_congr rfl fun i _ => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hz i))

/-- Every original family, including the zero ideal and dimension zero,
supplies strict analytic stability from its actual all-power source integrals. -/
theorem multiplierIntegrableAt_of_all_truncations {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    {q q' : ℝ} (hq' : 0 < q') (hqq' : q' < q) {F : ComplexModel n → ℂ}
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) ⊔
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt (generatorLog G) q' F 0 volume := by
  classical
  by_cases hzero : ∀ i, G i =ᶠ[𝓝 (0 : ComplexModel n)] (fun _ => (0 : ℂ))
  · have hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) = ⊥ := by
      apply le_antisymm ?_ bot_le
      rw [Ideal.span_le]
      rintro g ⟨i, rfl⟩
      have hg : HolGerm.mk (G i) (hG i) = 0 :=
        (HolGerm.mk_eq_mk_iff.mpr (hzero i)).trans HolGerm.mk_zero
      change HolGerm.mk (G i) (hG i) ∈ (⊥ : Ideal (HolGerm (ComplexModel n)))
      rw [hg]
      exact Ideal.zero_mem ⊥
    apply PointPowerTruncationZeroTest.multiplierIntegrableAt_of_all_point_power_integrals
      (generatorLog G) hq'
    intro N
    obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
    exact ⟨r, Q, hQ, fun i => by simpa only [hspan, bot_sup_eq] using hmem i, hint⟩
  · have hne : ∃ i, ∃ᶠ z in 𝓝 (0 : ComplexModel n), G i z ≠ 0 := by
      obtain ⟨i, hi⟩ := not_forall.mp hzero
      refine ⟨i, ?_⟩
      change ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n), ¬ G i z ≠ 0
      intro hn
      exact hi (hn.mono fun _ hz => not_ne_iff.mp hz)
    cases n with
    | zero => exact integrable_zero_dimension G hne hq' F
    | succ m => exact nonzero_family_positive_dimension G hG hne hq' hqq' htrunc

end
end SGPT.Foundations.Analysis.Pending.FiniteFamilyStrictTruncationStability
