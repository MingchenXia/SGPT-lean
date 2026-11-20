import SGPT.NPP.CodexC11OriginalHermitianMatrix
import SGPT.Envelopes.DNTC11Density

/-!
# `IsCOneOneBar` functions have bounded complex Hessian densities

Lane NPP-PROMOTE (`claude-npp-codex`, node `npp-codex:c11-gluing`), completing the Codex unit
U2-C11-DENSITY.  The library has two `C^{1,1̄}` classes of quasi-psh type:

* WN-REG's `IsCOneOneBar f` (`SGPT.Okounkov.TranscendentalWNReg`): `f` continuous and, in every
  holomorphic chart, the distributional complex Hessian of `f ∘ e⁻¹` is locally bounded
  (`|∫ g ∂_v∂̄_v φ| ≤ C |v|² ‖φ‖_{L¹}` for tests supported in a compact subset of the target);
* S53's `DNTC11.HasBoundedComplexHessian f`: `f` continuous and, in every chart, `f ∘ e⁻¹` has a
  measurable, pointwise Hermitian, locally essentially bounded density `h` of its distributional
  complex Hessian on the whole chart target (`IsBoundedHessianDensityOn`).

The library proves `HasBoundedComplexHessian → IsCOneOneBar` (`HasBoundedComplexHessian.isCOneOneBar`).
The Codex drafts (`SGPT.NPP.CodexC11*`) construct, around every point of a chart target, a ball
with bounded measurable real/imaginary component densities of the complex Hessian, Hermitian almost
everywhere (`exists_original_hermitian_matrix_density`; Riesz–Markov–Kakutani and Radon–Nikodym
for the directional Levi distributions, then polarization).  Here these local densities are
turned into one density on the chart target:

* `isBoundedHessianDensityOn_ball_of_isCOneOneBar`: the Codex components, redefined on a null set
  to be Hermitian everywhere, are a bounded density on the ball;
* `exists_isBoundedHessianDensityOn_of_local`: **gluing** — bounded densities on the members of an
  open cover of an open `U ⊆ ℂⁿ` glue to one on `U` (countable subcover, first-index selection,
  almost-everywhere uniqueness `IsBoundedHessianDensityOn.ae_eq` on overlaps, a smooth partition
  of unity for the Levi identity);
* `IsCOneOneBar.hasBoundedComplexHessian` and `isCOneOneBar_iff_hasBoundedComplexHessian`: the two
  classes coincide in every dimension.

Hence every DNT statement proved for `HasBoundedComplexHessian` obstacles (lanes S48/S53/NPP-DNT)
holds verbatim for `IsCOneOneBar` obstacles.  (Neither class is the book's `C^{1,1̄}(X)` for
`n ≥ 2`, which is `LapClass.HasBoundedMetricLaplacian`; for that class see lane CZ-LP's
`SGPT.Envelopes.LapClass3`.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff Distributions ENNReal Manifold

namespace SGPT.NPP.CodexDNT

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11
open SGPT.NPP.Codex.C11OriginalHermitianMatrix

variable {n : ℕ}

/-! ### Algebra of the Hermitian form -/

/-- `Q_A(v) = ∑_{p,q} (Re c_{pq} Re A_{pq} - Im c_{pq} Im A_{pq})`, `c_{pq} = v_p \bar v_q`. -/
theorem hermQuad_eq_sum (A : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    hermQuad A v = ∑ p, ∑ q, ((v p * star (v q)).re * (A p q).re -
      (v p * star (v q)).im * (A p q).im) := by
  simp only [hermQuad, sesqForm, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Complex.mul_re, Complex.mul_im]
  ring

/-- The Levi form of a finite sum of `C²` functions. -/
theorem leviForm_finset_sum {ι : Type*} (s : Finset ι) {u : ι → ComplexModel n → ℝ}
    (hu : ∀ i ∈ s, ContDiff ℝ 2 (u i)) (z v : ComplexModel n) :
    leviForm (fun y => ∑ i ∈ s, u i y) z v = ∑ i ∈ s, leviForm (u i) z v := by
  have h2 : (iteratedFDeriv ℝ 2 (fun y => ∑ i ∈ s, u i y) z) =
      ∑ i ∈ s, iteratedFDeriv ℝ 2 (u i) z :=
    by rw [congrFun (iteratedFDeriv_sum (fun i hi => hu i hi)) z, Finset.sum_apply]
  simp only [leviForm, realHessian, h2, _root_.sum_apply, ← Finset.sum_add_distrib,
    Finset.sum_div]

/-! ### Changing a bounded density on a null set -/

/-- A bounded density may be changed on a null set, keeping it Hermitian and measurable. -/
theorem IsBoundedHessianDensityOn.congr_ae {g : ComplexModel n → ℝ}
    {h h' : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hg : IsBoundedHessianDensityOn g h U) (hherm : ∀ z, (h' z).IsHermitian)
    (hmeas : ∀ i j, Measurable fun z => h' z i j) (heq : ∀ᵐ z ∂volume.restrict U, h' z = h z) :
    IsBoundedHessianDensityOn g h' U where
  isOpen := hg.isOpen
  continuousOn := hg.continuousOn
  isHermitian := hherm
  measurable := hmeas
  bounded K hK hKU := by
    obtain ⟨C, hC⟩ := hg.bounded K hK hKU
    refine ⟨C, ?_⟩
    filter_upwards [hC, ae_restrict_of_ae_restrict_of_subset hKU heq] with z hz hz'
    rw [hz']
    exact hz
  levi φ hφ hφc hφU v := by
    rw [hg.levi φ hφ hφc hφU v]
    have heq' : ∀ᵐ z, z ∈ U → h' z = h z := (ae_restrict_iff' hg.isOpen.measurableSet).mp heq
    refine integral_congr_ae ?_
    filter_upwards [heq'] with z hz
    by_cases hzU : z ∈ U
    · rw [hz hzU]
    · have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzU (hφU h)
      simp [h0]

/-! ### Gluing bounded densities along an open cover -/

/-- The empty open set carries every density. -/
theorem isBoundedHessianDensityOn_empty (g : ComplexModel n → ℝ) :
    IsBoundedHessianDensityOn g 0 (∅ : Set (ComplexModel n)) where
  isOpen := isOpen_empty
  continuousOn := continuousOn_empty _
  isHermitian _ := Matrix.isHermitian_zero
  measurable _ _ := measurable_const
  bounded K _ hK := ⟨0, by
    rw [subset_empty_iff.mp hK, Measure.restrict_empty]
    simp⟩
  levi φ _ _ hφU v := by
    have h0 : ∀ z, φ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun h => hφU h
    simp [leviForm, realHessian, show (φ : ComplexModel n → ℝ) = 0 from funext h0]

/-- **Gluing of bounded complex Hessian densities.**  If every point of the open set `U ⊆ ℂⁿ` has
an open neighbourhood in `U` carrying a bounded density of the complex Hessian of `g`, then `g`
has a bounded density on `U`. -/
theorem exists_isBoundedHessianDensityOn_of_local {g : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hloc : ∀ z ∈ U, ∃ B : Set (ComplexModel n), IsOpen B ∧ z ∈ B ∧ B ⊆ U ∧
      ∃ h, IsBoundedHessianDensityOn g h B) :
    ∃ h, IsBoundedHessianDensityOn g h U := by
  classical
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · subst hU0
    exact ⟨0, isBoundedHessianDensityOn_empty g⟩
  choose B hBo hzB hBU H hH using hloc
  -- a countable subcover, enumerated by `ℕ`
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : U => B z.1 z.2) fun z => hBo z.1 z.2
  have hcov : ∀ z ∈ U, ∃ t ∈ T, z ∈ B t.1 t.2 := by
    intro z hz
    have : z ∈ ⋃ t : U, B t.1 t.2 := mem_iUnion.mpr ⟨⟨z, hz⟩, hzB z hz⟩
    rw [← hTU] at this
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp this
    exact ⟨t, ht, hzt⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hUne
    obtain ⟨t, ht, -⟩ := hcov z hz
    exact ⟨t, ht⟩
  obtain ⟨s, hs⟩ := hTc.exists_eq_range hTne
  set Bk : ℕ → Set (ComplexModel n) := fun k => B (s k).1 (s k).2 with hBk
  set Hk : ℕ → ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun k => H (s k).1 (s k).2 with hHk
  have hBko : ∀ k, IsOpen (Bk k) := fun k => hBo _ _
  have hBkU : ∀ k, Bk k ⊆ U := fun k => hBU _ _
  have hHkd : ∀ k, IsBoundedHessianDensityOn g (Hk k) (Bk k) := fun k => hH _ _
  have hcovk : ∀ z ∈ U, ∃ k, z ∈ Bk k := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := hcov z hz
    rw [hs] at ht
    obtain ⟨k, rfl⟩ := ht
    exact ⟨k, hzt⟩
  -- first-index selection
  have hex : ∀ z, ∃ k, z ∈ Bk k ∨ z ∉ U := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨k, hk⟩ := hcovk z hz
      exact ⟨k, Or.inl hk⟩
    · exact ⟨0, Or.inr hz⟩
  set h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun z => Hk (Nat.find (hex z)) z with hhdef
  have hmeas : ∀ i j, Measurable fun z => h z i j := fun i j =>
    Measurable.find (f := fun k z => Hk k z i j) (p := fun k z => z ∈ Bk k ∨ z ∉ U)
      (fun k => (hHkd k).measurable i j)
      (fun k => ((hBko k).measurableSet.union hU.measurableSet.compl)) hex
  have hherm : ∀ z, (h z).IsHermitian := fun z => (hHkd _).isHermitian z
  -- on each member of the subcover, `h` agrees with the local density almost everywhere
  have hagree : ∀ k, ∀ᵐ z ∂volume.restrict (Bk k), h z = Hk k z := by
    intro k
    have hpair : ∀ l, ∀ᵐ z, z ∈ Bk l ∩ Bk k → Hk l z = Hk k z := fun l =>
      (ae_restrict_iff' ((hBko l).inter (hBko k)).measurableSet).mp
        (IsBoundedHessianDensityOn.ae_eq ((hHkd l).mono ((hBko l).inter (hBko k))
          inter_subset_left) ((hHkd k).mono ((hBko l).inter (hBko k)) inter_subset_right))
    have hall : ∀ᵐ z, ∀ l, z ∈ Bk l ∩ Bk k → Hk l z = Hk k z := ae_all_iff.mpr hpair
    refine (ae_restrict_iff' (hBko k).measurableSet).mpr ?_
    filter_upwards [hall] with z hz hzk
    have hspec := Nat.find_spec (hex z)
    have hmem : z ∈ Bk (Nat.find (hex z)) := hspec.resolve_right fun h => h (hBkU k hzk)
    exact hz _ ⟨hmem, hzk⟩
  have hloc' : ∀ k, IsBoundedHessianDensityOn g h (Bk k) := fun k =>
    IsBoundedHessianDensityOn.congr_ae (hHkd k) hherm hmeas (hagree k)
  refine ⟨h, ?_⟩
  exact
  { isOpen := hU
    continuousOn := by
      intro z hz
      obtain ⟨k, hk⟩ := hcovk z hz
      exact ((hloc' k).continuousOn z hk).mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds ((hBko k).mem_nhds hk))
    isHermitian := hherm
    measurable := hmeas
    bounded := by
      intro K hK hKU
      -- around each point of `K`, a closed ball inside a member of the subcover
      have hball : ∀ z ∈ K, ∃ ρ > 0, ∃ k, closedBall z ρ ⊆ Bk k := by
        intro z hz
        obtain ⟨k, hk⟩ := hcovk z (hKU hz)
        obtain ⟨ε, hε, hεk⟩ := Metric.isOpen_iff.mp (hBko k) z hk
        exact ⟨ε / 2, by positivity, k, (closedBall_subset_ball (by linarith)).trans hεk⟩
      choose! ρ hρ kk hkk using hball
      obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun z => ball z (ρ z))
        fun z hz => ball_mem_nhds z (hρ z hz)
      have hbd : ∀ z ∈ t, ∃ C, ∀ᵐ y ∂volume.restrict (closedBall z (ρ z)), ∀ i j,
          ‖h y i j‖ ≤ C := fun z hz =>
        (hloc' (kk z)).bounded _ (isCompact_closedBall _ _) (hkk z (htK z hz))
      choose! C hC using hbd
      refine ⟨∑ z ∈ t, |C z|, ?_⟩
      have hae : ∀ᵐ y, ∀ z ∈ t, y ∈ closedBall z (ρ z) → ∀ i j, ‖h y i j‖ ≤ C z := by
        rw [Filter.eventually_all_finset]
        intro z hz
        exact (ae_restrict_iff' measurableSet_closedBall).mp (hC z hz)
      refine (ae_restrict_iff' hK.measurableSet).mpr ?_
      filter_upwards [hae] with y hy hyK i j
      obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (hcover hyK)
      refine (hy z hzt (ball_subset_closedBall hyz) i j).trans ?_
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |C z|)
        (fun _ _ => abs_nonneg _) hzt)
    levi := by
      intro φ hφ hφc hφU v
      -- a smooth partition of unity on `tsupport φ` subordinate to the subcover
      obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
        (I := 𝓘(ℝ, ComplexModel n)) (isClosed_tsupport φ) Bk hBko (by
          intro z hz
          obtain ⟨k, hk⟩ := hcovk z (hφU hz)
          exact mem_iUnion.mpr ⟨k, hk⟩)
      have hfin := ρ.locallyFinite.finite_nonempty_inter_compact hφc
      set I := hfin.toFinset with hIdef
      set ψ : ℕ → ComplexModel n → ℝ := fun k z => ρ k z * φ z with hψdef
      have hψs : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k => (ρ k).contMDiff.contDiff.mul hφ
      have hψc : ∀ k, HasCompactSupport (ψ k) := fun k => hφc.mul_left
      have hψU : ∀ k, tsupport (ψ k) ⊆ Bk k := fun k =>
        (tsupport_mul_subset_left (f := fun z => ρ k z) (g := φ)).trans (hρ k)
      have hsum : φ = fun z => ∑ k ∈ I, ψ k z := by
        funext z
        simp only [hψdef]
        by_cases hz : z ∈ tsupport φ
        · have hsupport : Function.support (fun k => ρ k z) ⊆ (I : Set ℕ) := by
            intro k hk
            exact hfin.mem_toFinset.mpr ⟨z, hk, hz⟩
          have hs1 : ∑ k ∈ I, ρ k z = 1 :=
            (finsum_eq_finsetSum_of_support_subset (fun k => ρ k z) hsupport).symm.trans
              (ρ.sum_eq_one hz)
          rw [← Finset.sum_mul, hs1, one_mul]
        · have hz0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
          simp only [hz0, mul_zero, Finset.sum_const_zero]
      have h2 : ∀ k ∈ I, ContDiff ℝ 2 (ψ k) := fun k _ =>
        (hψs k).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      calc ∫ z, g z * leviForm φ z v
          = ∫ z, ∑ k ∈ I, g z * leviForm (ψ k) z v := by
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only
            conv_lhs => rw [hsum]
            rw [leviForm_finset_sum I h2, Finset.mul_sum]
        _ = ∑ k ∈ I, ∫ z, g z * leviForm (ψ k) z v :=
            integral_finsetSum _ fun k _ =>
              (hloc' k).integrable_mul_leviForm (hψs k) (hψc k) (hψU k) v
        _ = ∑ k ∈ I, ∫ z, hermQuad (h z) v * ψ k z :=
            Finset.sum_congr rfl fun k _ => (hloc' k).levi _ (hψs k) (hψc k) (hψU k) v
        _ = ∫ z, ∑ k ∈ I, hermQuad (h z) v * ψ k z :=
            (integral_finsetSum _ fun k _ =>
              (hloc' k).integrable_hermQuad_mul (hψs k).continuous (hψc k) (hψU k) v).symm
        _ = ∫ z, hermQuad (h z) v * φ z := by
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only
            rw [← Finset.mul_sum]
            conv_rhs => rw [hsum] }

/-! ### The Codex local densities as bounded densities on a ball -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Bounded density on a chart ball** (from the Codex components): for `f ∈ IsCOneOneBar`, a
chart `e` and `z₀` in its target, there is a ball around `z₀` in the target on which `f ∘ e⁻¹` has
a bounded density of its complex Hessian. -/
theorem exists_isBoundedHessianDensityOn_ball_of_isCOneOneBar {f : M → ℝ}
    (hf : IsCOneOneBar (N := n) f) (e : ComplexChart n M) {z₀ : ComplexModel n}
    (hz₀ : z₀ ∈ e.val.target) :
    ∃ r > 0, ball z₀ r ⊆ e.val.target ∧
      ∃ h, IsBoundedHessianDensityOn (fun z => f (e.val.symm z)) h (ball z₀ r) := by
  classical
  obtain ⟨r, hr, htarget, R, I, BR, BI, hd, ht, hherm⟩ :=
    exists_original_hermitian_matrix_density hf e hz₀
  let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
  have hΩt : (Ω : Set (ComplexModel n)) ⊆ e.val.target :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans htarget
  set A : Ω → Matrix (Fin n) (Fin n) ℂ :=
    fun z j k => (R j k z : ℂ) + Complex.I * (I j k z : ℂ) with hAdef
  have hAm : ∀ j k, Measurable fun z => A z j k := fun j k => by
    have h1 := (hd j k).1
    have h2 := (hd j k).2.1
    simp only [hAdef]
    fun_prop
  have hHset : MeasurableSet {z : Ω | (A z).IsHermitian} := by
    have : {z : Ω | (A z).IsHermitian} = ⋂ j, ⋂ k, {z | star (A z k j) = A z j k} := by
      ext z
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h j k => congrFun (congrFun h j) k, fun h => Matrix.ext fun j k => h j k⟩
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
      measurableSet_eq_fun (continuous_star.measurable.comp (hAm k j)) (hAm j k)
  set A' : Ω → Matrix (Fin n) (Fin n) ℂ := fun z => if (A z).IsHermitian then A z else 0
    with hA'def
  set h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ :=
    fun z => if hz : z ∈ Ω then A' ⟨z, hz⟩ else 0 with hhdef
  have hA'm : ∀ j k, Measurable fun z : Ω => A' z j k := by
    intro j k
    have : (fun z : Ω => A' z j k) = fun z => if (A z).IsHermitian then A z j k else 0 := by
      funext z
      simp only [hA'def]
      split_ifs <;> rfl
    rw [this]
    exact Measurable.ite hHset (hAm j k) measurable_const
  have hhm : ∀ j k, Measurable fun z => h z j k := by
    intro j k
    have : (fun z => h z j k) = fun z => if hz : z ∈ Ω then A' ⟨z, hz⟩ j k else 0 := by
      funext z
      simp only [hhdef]
      split_ifs <;> rfl
    rw [this]
    exact Measurable.dite (hA'm j k) measurable_const Ω.isOpen.measurableSet
  have hhherm : ∀ z, (h z).IsHermitian := by
    intro z
    simp only [hhdef, hA'def]
    split_ifs with h1 h2
    · exact h2
    · exact Matrix.isHermitian_zero
    · exact Matrix.isHermitian_zero
  -- almost everywhere on the ball, `h` is the Codex matrix
  have hae : ∀ᵐ z ∂volume.restrict (Ω : Set (ComplexModel n)),
      ∀ hz : z ∈ Ω, h z = A ⟨z, hz⟩ := by
    refine (ae_restrict_iff_subtype Ω.isOpen.measurableSet).mpr ?_
    filter_upwards [hherm] with z hz hz'
    simp only [hhdef, dif_pos hz', hA'def]
    exact if_pos hz
  have hbdR : ∀ j k, ∀ᵐ z ∂volume.restrict (Ω : Set (ComplexModel n)),
      ∀ hz : z ∈ Ω, |R j k ⟨z, hz⟩| ≤ BR j k := fun j k =>
    (ae_restrict_iff_subtype Ω.isOpen.measurableSet).mpr
      ((hd j k).2.2.1.mono fun z hz _ => hz)
  have hbdI : ∀ j k, ∀ᵐ z ∂volume.restrict (Ω : Set (ComplexModel n)),
      ∀ hz : z ∈ Ω, |I j k ⟨z, hz⟩| ≤ BI j k := fun j k =>
    (ae_restrict_iff_subtype Ω.isOpen.measurableSet).mpr
      ((hd j k).2.2.2.mono fun z hz _ => hz)
  have hg : ContinuousOn (fun z => f (e.val.symm z)) (ball z₀ r) :=
    hf.1.comp_continuousOn (e.val.continuousOn_symm.mono hΩt)
  -- the finite reference measure on the ball
  let ξ : Measure Ω := volume.comap Subtype.val
  have : IsFiniteMeasure ξ := ⟨by
    have h : ξ univ ≤ volume (Subtype.val '' (univ : Set Ω)) :=
      Measure.comap_apply_le _ _ nullMeasurableSet_univ
    rw [image_univ, Subtype.range_coe] at h
    exact h.trans_lt ((measure_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)))).trans_lt
        (isCompact_closedBall z₀ (2 * r)).measure_lt_top)⟩
  have hAre : ∀ z j k, (A z j k).re = R j k z := fun z j k => by simp [hAdef]
  have hAim : ∀ z j k, (A z j k).im = I j k z := fun z j k => by simp [hAdef]
  refine ⟨r, hr, hΩt, h, ?_⟩
  exact
  { isOpen := isOpen_ball
    continuousOn := hg
    isHermitian := hhherm
    measurable := hhm
    bounded := by
      intro K hK hKU
      refine ⟨∑ j, ∑ k, (|BR j k| + |BI j k|), ?_⟩
      have hall : ∀ᵐ z ∂volume.restrict (Ω : Set (ComplexModel n)), ∀ j k,
          (∀ hz : z ∈ Ω, h z = A ⟨z, hz⟩) ∧ (∀ hz : z ∈ Ω, |R j k ⟨z, hz⟩| ≤ BR j k) ∧
            ∀ hz : z ∈ Ω, |I j k ⟨z, hz⟩| ≤ BI j k := by
        simp only [ae_all_iff]
        intro j k
        filter_upwards [hae, hbdR j k, hbdI j k] with z h1 h2 h3 using ⟨h1, h2, h3⟩
      refine (ae_restrict_iff' hK.measurableSet).mpr ?_
      filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).mp hall] with z hz hzK i j
      have hzΩ : z ∈ Ω := hKU hzK
      obtain ⟨h1, h2, h3⟩ := hz hzΩ i j
      rw [h1 hzΩ]
      have hb : ‖A ⟨z, hzΩ⟩ i j‖ ≤ |BR i j| + |BI i j| := by
        simp only [hAdef]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [Complex.norm_real, Real.norm_eq_abs]
          exact (h2 hzΩ).trans (le_abs_self _)
        · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          exact (h3 hzΩ).trans (le_abs_self _)
      refine hb.trans ?_
      refine (Finset.single_le_sum (f := fun k => |BR i k| + |BI i k|)
        (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
      exact Finset.single_le_sum (f := fun j => ∑ k, (|BR j k| + |BI j k|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
    levi := by
      intro φ hφ hφc hφU v
      let ψ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hφc, hφU⟩
      have hψφ : (ψ : ComplexModel n → ℝ) = φ := rfl
      have hgl : LocallyIntegrableOn (fun z => f (e.val.symm z)) Ω volume :=
        hg.locallyIntegrableOn Ω.isOpen.measurableSet
      have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have hre : ∀ p q z, (complexHessian φ z p q).re =
          (leviForm φ z (polVec p q 0) - leviForm φ z (polVec p q 1)) / 4 := by
        intro p q z
        rw [complexHessian_eq_polarize hφ2.contDiffAt]
        simp only [polarize, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
      have him : ∀ p q z, (complexHessian φ z p q).im =
          (leviForm φ z (polVec p q 2) - leviForm φ z (polVec p q 3)) / 4 := by
        intro p q z
        rw [complexHessian_eq_polarize hφ2.contDiffAt]
        simp only [polarize, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
      have hint_re : ∀ p q, Integrable fun z => f (e.val.symm z) * (complexHessian φ z p q).re := by
        intro p q
        have h0 := integrable_mul_leviForm_testFunction hgl ψ (polVec p q 0)
        have h1 := integrable_mul_leviForm_testFunction hgl ψ (polVec p q 1)
        refine ((h0.sub h1).div_const 4).congr (Eventually.of_forall fun z => ?_)
        simp only [Pi.sub_apply, hψφ, hre]
        ring
      have hint_im : ∀ p q, Integrable fun z => f (e.val.symm z) * (complexHessian φ z p q).im := by
        intro p q
        have h0 := integrable_mul_leviForm_testFunction hgl ψ (polVec p q 2)
        have h1 := integrable_mul_leviForm_testFunction hgl ψ (polVec p q 3)
        refine ((h0.sub h1).div_const 4).congr (Eventually.of_forall fun z => ?_)
        simp only [Pi.sub_apply, hψφ, him]
        ring
      have hφint : Integrable (fun z : Ω => φ z) ξ :=
        (integrableOn_iff_comap_subtypeVal Ω.isOpen.measurableSet).mp
          (hφ.continuous.integrable_of_hasCompactSupport hφc).integrableOn
      have hint_R : ∀ p q, Integrable (fun z : Ω => φ z * R p q z) ξ := fun p q =>
        hφint.mul_bdd (hd p q).1.aestronglyMeasurable
          (by simpa only [Real.norm_eq_abs] using (hd p q).2.2.1)
      have hint_I : ∀ p q, Integrable (fun z : Ω => φ z * I p q z) ξ := fun p q =>
        hφint.mul_bdd (hd p q).2.1.aestronglyMeasurable
          (by simpa only [Real.norm_eq_abs] using (hd p q).2.2.2)
      have hcoef : ∀ p q, Integrable (fun z => (v p * star (v q)).re *
          (f (e.val.symm z) * (complexHessian φ z p q).re) - (v p * star (v q)).im *
          (f (e.val.symm z) * (complexHessian φ z p q).im)) := fun p q =>
        ((hint_re p q).const_mul _).sub ((hint_im p q).const_mul _)
      have hcoef' : ∀ p q, Integrable (fun z : Ω => (v p * star (v q)).re * (φ z * R p q z) -
          (v p * star (v q)).im * (φ z * I p q z)) ξ := fun p q =>
        ((hint_R p q).const_mul _).sub ((hint_I p q).const_mul _)
      have htR : ∀ p q, (∫ z, f (e.val.symm z) * (complexHessian φ z p q).re) =
          ∫ z : Ω, φ z * R p q z ∂ξ := fun p q => (ht p q ψ).1
      have htI : ∀ p q, (∫ z, f (e.val.symm z) * (complexHessian φ z p q).im) =
          ∫ z : Ω, φ z * I p q z ∂ξ := fun p q => (ht p q ψ).2
      have hφ0 : ∀ z ∉ (Ω : Set (ComplexModel n)), φ z = 0 := fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h => hz (hφU h)
      calc ∫ z, f (e.val.symm z) * leviForm φ z v
          = ∫ z, ∑ p, ∑ q, ((v p * star (v q)).re *
              (f (e.val.symm z) * (complexHessian φ z p q).re) - (v p * star (v q)).im *
              (f (e.val.symm z) * (complexHessian φ z p q).im)) := by
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only
            rw [← hermQuad_complexHessian hφ2.contDiffAt v, hermQuad_eq_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            ring
        _ = ∑ p, ∑ q, ((v p * star (v q)).re *
              (∫ z, f (e.val.symm z) * (complexHessian φ z p q).re) - (v p * star (v q)).im *
              ∫ z, f (e.val.symm z) * (complexHessian φ z p q).im) := by
            rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hcoef p q]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [integral_finsetSum _ fun q _ => hcoef p q]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_sub ((hint_re p q).const_mul _) ((hint_im p q).const_mul _),
              integral_const_mul, integral_const_mul]
        _ = ∑ p, ∑ q, ((v p * star (v q)).re * (∫ z : Ω, φ z * R p q z ∂ξ) -
              (v p * star (v q)).im * ∫ z : Ω, φ z * I p q z ∂ξ) := by
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
            rw [htR p q, htI p q]
        _ = ∫ z : Ω, ∑ p, ∑ q, ((v p * star (v q)).re * (φ z * R p q z) -
              (v p * star (v q)).im * (φ z * I p q z)) ∂ξ := by
            rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hcoef' p q]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [integral_finsetSum _ fun q _ => hcoef' p q]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_sub ((hint_R p q).const_mul _) ((hint_I p q).const_mul _),
              integral_const_mul, integral_const_mul]
        _ = ∫ z : Ω, (fun y => hermQuad (h y) v * φ y) z ∂ξ := by
            refine integral_congr_ae ?_
            filter_upwards [hherm] with z hz
            have hzh : h z = A z := by
              simp only [hhdef, dif_pos z.2, hA'def]
              exact if_pos hz
            simp only [hzh, hermQuad_eq_sum, hAre, hAim, Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
            ring
        _ = ∫ z in (Ω : Set (ComplexModel n)), hermQuad (h z) v * φ z :=
            integral_subtype_comap (μ := volume) Ω.isOpen.measurableSet
              (fun y => hermQuad (h y) v * φ y)
        _ = ∫ z, hermQuad (h z) v * φ z :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
              rw [hφ0 z hz, mul_zero] }

/-! ### The two `C^{1,1̄}` classes of quasi-psh type coincide -/

/-- **`IsCOneOneBar` functions have bounded complex Hessian densities** in every chart (glued from
the Codex chart-ball densities). -/
theorem IsCOneOneBar.hasBoundedComplexHessian {f : M → ℝ} (hf : IsCOneOneBar (N := n) f) :
    HasBoundedComplexHessian (n := n) f := by
  refine ⟨hf.1, fun e => exists_isBoundedHessianDensityOn_of_local e.val.open_target ?_⟩
  intro z hz
  obtain ⟨r, hr, hrt, h, hh⟩ := exists_isBoundedHessianDensityOn_ball_of_isCOneOneBar hf e hz
  exact ⟨ball z r, isOpen_ball, mem_ball_self hr, hrt, h, hh⟩

/-- **The classes `IsCOneOneBar` (WN-REG) and `HasBoundedComplexHessian` (S53) coincide** in every
dimension. -/
theorem isCOneOneBar_iff_hasBoundedComplexHessian {f : M → ℝ} :
    IsCOneOneBar (N := n) f ↔ HasBoundedComplexHessian (n := n) f :=
  ⟨IsCOneOneBar.hasBoundedComplexHessian, HasBoundedComplexHessian.isCOneOneBar⟩

end SGPT.NPP.CodexDNT
