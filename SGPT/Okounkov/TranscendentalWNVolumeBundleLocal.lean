import SGPT.Okounkov.TranscendentalWNVolumeBundlePotential
import SGPT.Okounkov.TranscendentalWNVolumeGlobalExcInput
import SGPT.Okounkov.TranscendentalWNLegendreReduction
import SGPT.Okounkov.TranscendentalWNLegendreSmooth
import SGPT.Okounkov.TranscendentalWNVolumeExcInvolution
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity

/-!
# Local tools for the bundle Legendre identity (package WN-VF4)

Blueprint `claude-tok-wn-vf4`, nodes `tok-wn-vf4:measure-coordinates`,
`tok-wn-vf4:inverse-legendre-data`; source WN21 §3 (Theorem 3.5 and the involution property of the
partial Legendre transform).

* `globalMixedMeasure_image_eq` (**the global non-pluripolar measure in local holomorphic
  coordinates**): let `Λ : O → V` be injective on an open `O ⊆ ℂᵏ` and, near every point of
  `O`, the inverse of an atlas chart of `V` on whose image a fixed smooth `ρ` is a local potential
  of `Θ`, with `φ ∘ Λ + ρ = u`.  Then `⟨(Θ + dd^c φ)ᵏ⟩(Λ(S)) = ⟨(dd^c u)ᵏ⟩(S)` for every Borel
  `S ⊆ O` (countable cover by chart patches, `globalMixedMeasure_restrict_patch`, locality and
  congruence of the local truncation limit).
* `isLegendreMAData_inverseLegendre`: the inverse partial Legendre transform
  `u(z, τ) = sup_{t ∈ [0, c]} (v_t(z) + t log |τ|²)` of a concave family of psh functions,
  locally bounded for each `t` and locally uniformly bounded above, satisfies the hypotheses of
  WN21 Theorem 3.3 (`IsLegendreMAData`) with empty exceptional set; its partial Legendre
  transform is `v_t` for `t ∈ (0, c)` (WN-VF3's involution lemma).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality


/-! ### The diagonal truncation limit, including dimension `0` -/

section Diagonal

open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending.MongeAmpere

/-- The diagonal mixed truncation limit is the truncation limit, in positive dimension or for a
function without poles on `Ω` (in dimension `0` both are the empty Bedford–Taylor measure, the
truncation limit restricted to the finite locus). -/
theorem mixedTruncationLimitMeasure_diagonal_of {n : ℕ} {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → EReal} (hv : PlurisubharmonicOn v Ω)
    (hfin : 0 < n ∨ ∀ z ∈ Ω, v z ≠ ⊥) :
    mixedTruncationLimitMeasure Ω (fun _ => v) (fun _ => hv) =
      MongeAmpere.truncationLimitMeasure Ω v hv := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hfin' : ∀ z ∈ Ω, v z ≠ ⊥ := hfin.resolve_left (lt_irrefl 0)
    set mu0 := mixedTruncationMeasure Ω (fun _ => v) (fun _ => hv) 0 with hmu0
    have hmix : ∀ k, mixedTruncationMeasure Ω (fun _ => v) (fun _ => hv) k = mu0 := by
      intro k
      rw [mixedTruncationMeasure_zero_dim Ω _ _ (mixedTruncationReal (fun _ => v) 0)
          (mixedTruncationReal_isLocallyBounded (fun _ => hv) 0) k, hmu0,
        mixedTruncationMeasure_zero_dim Ω _ _ (mixedTruncationReal (fun _ => v) 0)
          (mixedTruncationReal_isLocallyBounded (fun _ => hv) 0) 0]
    have htr : ∀ k, MongeAmpere.truncationMeasure Ω v hv k =
        mu0.restrict (strictTruncationLocus Ω v k) := by
      intro k
      unfold MongeAmpere.truncationMeasure
      rw [← canonicalMixedBedfordTaylorMeasure_diagonal, hmu0,
        mixedTruncationMeasure_zero_dim Ω _ _ (fun _ => truncationReal v k)
          (fun _ => truncationReal_isLocallyBoundedPshOn hv k) 0]
    apply Measure.ext
    intro s hs
    rw [mixedTruncationLimitMeasure_apply, MongeAmpere.truncationLimitMeasure_apply]
    simp_rw [hmix, htr, Measure.restrict_apply hs]
    rw [ciSup_const, ← Monotone.measure_iUnion]
    · have hU : (⋃ k, s ∩ strictTruncationLocus Ω v k) = s ∩ Ω := by
        ext z
        simp only [mem_iUnion, mem_inter_iff, strictTruncationLocus, mem_ofPred_eq]
        constructor
        · rintro ⟨k, hz, hzΩ, -⟩
          exact ⟨hz, hzΩ⟩
        · rintro ⟨hz, hzΩ⟩
          have hne := hfin' z hzΩ
          have hlt : (⊥ : EReal) < v z := bot_lt_iff_ne_bot.mpr hne
          obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
          obtain ⟨k, hk⟩ := exists_nat_gt (-r)
          refine ⟨k, hz, hzΩ, lt_trans ?_ hr⟩
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
      rw [hU, ← measure_inter_add_sdiff s Ω.isOpen.measurableSet]
      have h0 : mu0 (s \ Ω) = 0 := by
        refine measure_mono_null (fun z hz => hz.2) ?_
        rw [hmu0, mixedTruncationMeasure_zero_dim Ω _ _ (mixedTruncationReal (fun _ => v) 0)
          (mixedTruncationReal_isLocallyBounded (fun _ => hv) 0) 0]
        exact canonicalMixedBedfordTaylorMeasure_compl Ω _ _
      rw [h0, add_zero]
    · intro i j hij z hz
      refine ⟨hz.1, hz.2.1, lt_of_le_of_lt ?_ hz.2.2⟩
      exact EReal.coe_le_coe_iff.mpr (by simp only [neg_le_neg_iff, Nat.cast_le]; exact hij)
  · exact mixedTruncationLimitMeasure_diagonal hn hv

end Diagonal

/-! ### The global measure in local holomorphic coordinates -/

section Coordinates

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]

omit [IsComplexManifold k V] [CompactSpace V] in
/-- The inverse image of a measurable set inside a chart target is measurable. -/
theorem measurableSet_chart_symm_image (e : ComplexChart k V) {S : Set (ComplexModel k)}
    (hS : MeasurableSet S) (hSt : S ⊆ e.val.target) : MeasurableSet (e.val.symm '' S) := by
  rw [e.val.symm_image_eq_source_inter_preimage hSt]
  exact SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
    e.val.open_source.measurableSet e.val.continuousOn hS

/-- **`tok-wn-vf4:measure-coordinates`**: the global non-pluripolar measure in local holomorphic
coordinates `Λ`, which are locally inverses of atlas charts carrying a fixed local potential. -/
theorem globalMixedMeasure_image_eq {Θ : ClosedRealOneOneForm k V} {φ : V → EReal}
    (hφ : ThetaPlurisubharmonic Θ.val φ) (O : Opens (ComplexModel k)) (Λ : ComplexModel k → V)
    (hinj : InjOn Λ O) (ρ : ComplexModel k → ℝ) (u : ComplexModel k → EReal)
    (hu : PlurisubharmonicOn u O)
    (hloc : ∀ v ∈ O, ∃ (e : ComplexChart k V) (G : Set (ComplexModel k)), IsOpen G ∧ v ∈ G ∧
      G ⊆ O ∧ G ⊆ e.val.target ∧ (∀ z ∈ G, e.val.symm z = Λ z) ∧
      IsSmoothLocalPotential Θ.val e G ρ ∧ ∀ z ∈ G, φ (Λ z) + (ρ z : EReal) = u z)
    (hk : 0 < k ∨ ∀ z ∈ O, u z ≠ ⊥)
    {S : Set (ComplexModel k)} (hS : MeasurableSet S) (hSO : S ⊆ O) :
    MeasurableSet (Λ '' S) ∧
      globalMixedMeasure (fun _ : Fin k => Θ) (fun _ => φ) (fun _ => hφ) (Λ '' S) =
        MongeAmpere.truncationLimitMeasure O u hu S := by
  classical
  set ν := globalMixedMeasure (fun _ : Fin k => Θ) (fun _ => φ) (fun _ => hφ) with hν
  set μO := MongeAmpere.truncationLimitMeasure O u hu with hμO
  rcases eq_empty_or_nonempty (O : Set (ComplexModel k)) with hO | hO
  · have hS0 : S = ∅ := subset_eq_empty hSO hO
    subst hS0
    simp
  choose e G hG hvG hGO hGt hGΛ hρ hGu using hloc
  set s : O → Set (ComplexModel k) := fun v => G v.1 v.2 with hsdef
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable s fun v => hG v.1 v.2
  have hUO : (⋃ v, s v) = (O : Set (ComplexModel k)) := by
    apply subset_antisymm
    · exact iUnion_subset fun v => hGO v.1 v.2
    · intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, hvG z hz⟩
  have hTne : T.Nonempty := by
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    have : (⋃ v ∈ T, s v) = ∅ := by rw [hT]; simp
    rw [hTU, hUO] at this
    exact hO.ne_empty this
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  set Gn : ℕ → Set (ComplexModel k) := fun n => s (f n) with hGn
  have hcov : (⋃ n, Gn n) = (O : Set (ComplexModel k)) := by
    rw [← hUO, ← hTU, hf]
    ext z
    simp [Gn]
  set H : ℕ → Set (ComplexModel k) := disjointed Gn with hH
  have hHm : ∀ n, MeasurableSet (H n) :=
    MeasurableSet.disjointed fun n => (hG (f n).1 (f n).2).measurableSet
  have hHdisj : Pairwise (Function.onFun Disjoint H) := disjoint_disjointed _
  have hHG : ∀ n, H n ⊆ Gn n := disjointed_subset _
  have hHcov : (⋃ n, H n) = (O : Set (ComplexModel k)) := by rw [hH, iUnion_disjointed, hcov]
  set Sn : ℕ → Set (ComplexModel k) := fun n => S ∩ H n with hSn
  have hSnm : ∀ n, MeasurableSet (Sn n) := fun n => hS.inter (hHm n)
  have hSnG : ∀ n, Sn n ⊆ Gn n := fun n => inter_subset_right.trans (hHG n)
  have hSU : S = ⋃ n, Sn n := by
    rw [← inter_iUnion, hHcov, inter_eq_left.mpr hSO]
  -- the patches
  let P : ℕ → Patch (fun _ : Fin k => Θ) (fun _ => φ) := fun n =>
    { chart := e (f n).1 (f n).2
      domain := ⟨Gn n, hG (f n).1 (f n).2⟩
      domain_le_target := hGt (f n).1 (f n).2
      potential := fun _ => ρ
      localPotential := fun _ => hρ (f n).1 (f n).2
      plurisubharmonic := fun _ =>
        ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hφ _
          (hρ (f n).1 (f n).2) }
  -- the images of the pieces
  have himg : ∀ n, Λ '' Sn n = (e (f n).1 (f n).2).val.symm '' Sn n := by
    intro n
    refine image_congr fun z hz => ?_
    exact (hGΛ (f n).1 (f n).2 z (hSnG n hz)).symm
  have himgm : ∀ n, MeasurableSet (Λ '' Sn n) := by
    intro n
    rw [himg n]
    exact measurableSet_chart_symm_image _ (hSnm n) ((hSnG n).trans (hGt _ _))
  have hpiece : ∀ n, ν (Λ '' Sn n) = μO (Sn n) := by
    intro n
    set en := e (f n).1 (f n).2
    have hsrc : Λ '' Sn n ⊆ ((P n).source : Set V) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzG := hSnG n hz
      rw [← hGΛ _ _ z hzG]
      refine ⟨en.val.map_target (hGt _ _ hzG), ?_⟩
      change en.val (en.val.symm z) ∈ Gn n
      rw [en.val.right_inv (hGt _ _ hzG)]
      exact hzG
    have h1 : ν (Λ '' Sn n) = patchMeasure (P n) (Λ '' Sn n) := by
      rw [← globalMixedMeasure_restrict_patch (fun _ => hφ) (P n),
        Measure.restrict_apply' (P n).source.isOpen.measurableSet, inter_eq_left.mpr hsrc]
    have hpre : (Gn n) ∩ en.val.symm ⁻¹' (Λ '' Sn n) = Sn n := by
      ext z
      constructor
      · rintro ⟨hzG, z', hz', hzz'⟩
        rw [hGΛ _ _ z hzG] at hzz'
        have := hinj (hGO _ _ (hSnG n hz')) (hGO _ _ hzG) hzz'
        rw [← this]
        exact hz'
      · intro hz
        exact ⟨hSnG n hz, z, hz, (hGΛ _ _ z (hSnG n hz)).symm⟩
    have hvG' : PlurisubharmonicOn (fun z => chartFunction φ en z + (ρ z : EReal)) (Gn n) :=
      ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hφ _
        (hρ (f n).1 (f n).2)
    have huG : PlurisubharmonicOn u (Gn n) := hu.mono (hGO _ _)
    have hdiag := mixedTruncationLimitMeasure_diagonal_of
      (Ω := ⟨Gn n, hG (f n).1 (f n).2⟩) hvG' (hk.imp id fun h z hz => by
        change φ (en.val.symm z) + (ρ z : EReal) ≠ ⊥
        rw [hGΛ _ _ z hz, hGu _ _ z hz]
        exact h z (hGO _ _ hz))
    have hcongr := truncationLimitMeasure_congr (Ω := ⟨Gn n, hG (f n).1 (f n).2⟩) hvG' huG
      (fun z hz => by
        change φ (en.val.symm z) + (ρ z : EReal) = u z
        rw [hGΛ _ _ z hz]
        exact hGu _ _ z hz)
    have hres := MongeAmpere.truncationLimitMeasure_restrict_open
      (Ω := O) (U := ⟨Gn n, hG (f n).1 (f n).2⟩) (hGO _ _) hu huG
    rw [h1, patchMeasure, Patch.pushMeasure_apply]
    change MixedNonPluripolar.mixedTruncationLimitMeasure ⟨Gn n, hG (f n).1 (f n).2⟩
      (fun _ => fun z => chartFunction φ en z + (ρ z : EReal)) (fun _ => hvG') _ = _
    rw [hdiag, hcongr]
    change MongeAmpere.truncationLimitMeasure _ u huG ((Gn n) ∩ en.val.symm ⁻¹' (Λ '' Sn n)) = _
    rw [hpre, ← hres, Measure.restrict_apply (hSnm n)]
    exact congrArg _ (inter_eq_left.mpr (hSnG n))
  have hdisj : Pairwise (Function.onFun Disjoint fun n => Λ '' Sn n) := by
    intro i j hij
    rw [Function.onFun, disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
    have hzO : z ∈ (O : Set (ComplexModel k)) := hSO hz.1
    have hz'O : z' ∈ (O : Set (ComplexModel k)) := hSO hz'.1
    have := hinj hz'O hzO hzz'
    subst this
    exact disjoint_left.mp (hHdisj hij) hz.2 hz'.2
  have himgU : Λ '' S = ⋃ n, Λ '' Sn n := by
    conv_lhs => rw [hSU]
    exact image_iUnion
  refine ⟨himgU ▸ MeasurableSet.iUnion himgm, ?_⟩
  rw [himgU, measure_iUnion hdisj himgm]
  simp_rw [hpiece]
  rw [← measure_iUnion (fun i j hij => ((hHdisj hij).mono inter_subset_right inter_subset_right))
    hSnm, ← hSU]

end Coordinates

/-! ### The inverse Legendre transform satisfies the hypotheses of WN21 Theorem 3.3 -/

section Inverse

variable {m : ℕ}

theorem locallyPluripolarOn_empty (U : Set (ComplexModel m)) :
    LocallyPluripolarOn (∅ : Set (ComplexModel m)) U := by
  intro x _
  refine ⟨univ, fun _ => (0 : EReal), isOpen_univ, mem_univ x, isPreconnected_univ,
    fun y _ => plurisubharmonicAt_const (0 : EReal) EReal.zero_ne_top y, ⟨x, mem_univ x, ?_⟩,
    fun y _ hy => absurd hy (notMem_empty y)⟩
  exact EReal.zero_ne_bot

/-- `u(z, τ) - t log |τ|² ≥ v_t(z)` for `t ∈ [0, c]`. -/
theorem le_partialLegendre_inverseLegendre {X : Type*} (v : ℝ → X → EReal) {c t : ℝ}
    (ht : t ∈ Icc 0 c) (z : X) : v t z ≤ partialLegendre (inverseLegendre v 0 c) t z := by
  refine le_iInf fun τ => ?_
  have h1 : v t z + ((t * logNormSq τ : ℝ) : EReal) ≤ inverseLegendre v 0 c z τ :=
    le_iSup₂ (f := fun lam (_ : lam ∈ Icc 0 c) => v lam z + ((lam * logNormSq τ : ℝ) : EReal))
      t ht
  have h2 := EReal.sub_le_sub h1 (le_refl (((t * logNormSq τ : ℝ) : EReal)))
  rwa [ereal_add_coe_sub_coe] at h2

/-- `û_t(z) ≤ u(z, 1) = sup_s v_s(z)`. -/
theorem partialLegendre_inverseLegendre_le {X : Type*} (v : ℝ → X → EReal) (c t : ℝ) (z : X)
    {C : ℝ} (hC : ∀ s ∈ Icc 0 c, v s z ≤ (C : EReal)) :
    partialLegendre (inverseLegendre v 0 c) t z ≤ (C : EReal) := by
  have h1 : (1 : ℂ) ≠ 0 := one_ne_zero
  refine (iInf_le _ (⟨1, h1⟩ : puncturedPlane)).trans ?_
  have hl : logNormSq (1 : ℂ) = 0 := by simp [logNormSq]
  simp only [inverseLegendre, hl, mul_zero, EReal.coe_zero, add_zero, sub_zero]
  exact iSup₂_le hC

/-- **`tok-wn-vf4:inverse-legendre-data`**: the inverse partial Legendre transform of a concave
family of psh functions satisfies the hypotheses of WN21 Theorem 3.3 with empty exceptional set. -/
theorem isLegendreMAData_inverseLegendre {Ω : Opens (ComplexModel m)}
    {v : ℝ → ComplexModel m → EReal} {c : ℝ} (hc : 0 < c)
    (hpsh : ∀ t ∈ Icc 0 c, PlurisubharmonicOn (v t) Ω)
    (hconc : ∀ z ∈ Ω, IsConcaveFamilyAt v (Icc 0 c) z)
    (hbdd : ∀ t ∈ Icc 0 c, ∀ z ∈ Ω, ∃ C : ℝ, ∀ᶠ w in 𝓝 z,
      ((-C : ℝ) : EReal) ≤ v t w ∧ v t w ≤ (C : EReal))
    (hup : ∀ z ∈ Ω, ∃ C : ℝ, ∀ᶠ w in 𝓝 z, ∀ t ∈ Icc 0 c, v t w ≤ (C : EReal)) :
    IsLegendreMAData Ω (inverseLegendre v 0 c) 0 c ∅ where
  psh := plurisubharmonicOn_inverseLegendre Ω.isOpen le_rfl hc le_rfl hpsh hconc hbdd
  circleInvariant := by
    intro z τ σ hτσ
    simp only [inverseLegendre, logNormSq, hτσ]
  le := hc.le
  eq_bot_of_notMem := by
    intro lam hlam z hz
    obtain ⟨C, hC⟩ := hup z hz
    exact partialLegendre_inverseLegendre_eq_bot (C := C) (fun s hs => hC.self_of_nhds s hs) hlam
  pluripolar := locallyPluripolarOn_empty _
  locallyBounded := by
    intro t ht z hz
    obtain ⟨C₁, hC₁⟩ := hbdd t ht z hz.1
    obtain ⟨C₂, hC₂⟩ := hup z hz.1
    refine ⟨max C₁ C₂, ?_⟩
    filter_upwards [hC₁, hC₂] with w hw1 hw2
    constructor
    · refine le_trans ?_ ((hw1.1).trans (le_partialLegendre_inverseLegendre v ht w))
      exact EReal.coe_le_coe_iff.mpr (by simp)
    · exact (partialLegendre_inverseLegendre_le v c t w hw2).trans
        (EReal.coe_le_coe_iff.mpr (le_max_right _ _))

/-- The partial Legendre transform of the inverse transform is `v_t` on `(0, c)`. -/
theorem partialLegendre_inverseLegendre_eq {Ω : Opens (ComplexModel m)}
    {v : ℝ → ComplexModel m → EReal} {c : ℝ}
    (hconc : ∀ z ∈ Ω, IsConcaveFamilyAt v (Icc 0 c) z)
    (hbdd : ∀ t ∈ Icc 0 c, ∀ z ∈ Ω, ∃ C : ℝ, ∀ᶠ w in 𝓝 z,
      ((-C : ℝ) : EReal) ≤ v t w ∧ v t w ≤ (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo 0 c) {z : ComplexModel m} (hz : z ∈ Ω) :
    partialLegendre (inverseLegendre v 0 c) t z = v t z := by
  refine partialLegendre_inverseLegendre (hconc z hz) (fun s hs => ?_) ht
  obtain ⟨C, hC⟩ := hbdd s hs z hz
  have h := hC.self_of_nhds
  exact ⟨ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h.1, ne_top_of_le_ne_top (EReal.coe_ne_top _) h.2⟩

end Inverse

end SGPT.Okounkov.TranscendentalWN
