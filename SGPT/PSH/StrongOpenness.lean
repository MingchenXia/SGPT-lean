import SGPT.PSH.AtlasAE
import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- The original local PSH predicate gives the actual zero-background record;
the smooth local potential and nondegeneracy are already proved producers. -/
theorem ManifoldPSH.isThetaPshPotential_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} (hu : ManifoldPSH (n := n) u) :
    IsThetaPshPotential (0 : ClosedRealOneOneForm n M).val u := by
  refine ⟨?_, hu.locallyNondegenerate⟩
  intro e z hz
  refine ⟨e.val.target, fun _ => 0, hz,
    FirstPass.LocalPotentials.localPotential_zero e e.val.open_target subset_rfl, ?_⟩
  simpa only [EReal.coe_zero, add_zero] using hu.chartPlurisubharmonic e

/-- Original almost-everywhere increasing convergence determines pointwise
order even at poles, through main's actual PSH comparison. -/
theorem increasing_psh_le_limit_of_ae
    {n : ℕ} {W : Set (ComplexModel n)} (hW : IsOpen W)
    {u : ComplexModel n → EReal} {v : ℕ → ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u W) (hv : ∀ j, PlurisubharmonicOn (v j) W)
    (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    (hae : ∀ᵐ y ∂volume.restrict W,
      Tendsto (fun j => v j y) atTop (𝓝 (u y))) :
    ∀ j, ∀ y ∈ W, v j y ≤ u y := by
  intro j y hy
  apply (hv j).le_of_ae_le hW hu.upperSemicontinuousOn volume ?_ y hy
  filter_upwards [hae, ae_restrict_mem hW.measurableSet] with z hz hzW
  exact (hmono z hzW).ge_of_tendsto hz j

/-- The regularized actual supremum is the original PSH limit at every
domain point, not merely almost everywhere. -/
theorem increasing_psh_uscSup_eq_of_ae
    {n : ℕ} {W : Set (ComplexModel n)} (hW : IsOpen W)
    {u : ComplexModel n → EReal} {v : ℕ → ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u W) (hv : ∀ j, PlurisubharmonicOn (v j) W)
    (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    (hae : ∀ᵐ y ∂volume.restrict W,
      Tendsto (fun j => v j y) atTop (𝓝 (u y))) :
    EqOn (uscSup v) u W := by
  have hle := increasing_psh_le_limit_of_ae hW hu hv hmono hae
  intro y hy
  apply le_antisymm
  · apply uscRegularization_le_of_eventually_le
    · intro a ha
      simpa only [hW.nhdsWithin_eq hy] using hu.upperSemicontinuousOn y hy a ha
    · filter_upwards [hW.mem_nhds hy] with z hz
      exact iSup_le fun j => hle j z hz
  · apply hu.le_of_ae_le hW
      ((upperSemicontinuous_uscRegularization _).upperSemicontinuousOn W) volume ?_ y hy
    filter_upwards [hae] with z hz
    exact le_of_tendsto' hz fun j => le_uscSup v j z

/-- Actual finitely many Nadel generators turn main's individual-germ
openness into one cutoff for the ENTIRE original multiplier stalk. -/
theorem increasing_psh_multiplier_stalk_stabilizes_pos
    {m : ℕ} {W : Set (ComplexModel (m + 1))} (hW : IsOpen W)
    {u : ComplexModel (m + 1) → EReal}
    {v : ℕ → ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u W) (hv : ∀ j, PlurisubharmonicOn (v j) W)
    (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    (hae : ∀ᵐ y ∂volume.restrict W,
      Tendsto (fun j => v j y) atTop (𝓝 (u y)))
    {z : ComplexModel (m + 1)} (hz : z ∈ W) {c : ℝ} (hc : 0 < c) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ f : ComplexModel (m + 1) → ℂ,
      MultiplierIntegrableAt (v j) c f z volume ↔
        MultiplierIntegrableAt u c f z volume := by
  classical
  have hle := increasing_psh_le_limit_of_ae hW hu hv hmono hae
  have hreg := increasing_psh_uscSup_eq_of_ae hW hu hv hmono hae
  have hb : FirstPass.LocallyUniformlyBoundedAbove (range v) W := by
    intro y hy
    obtain ⟨C, hC, _⟩ := EReal.exists_between_coe_real
      (lt_top_iff_ne_top.mpr (hu.discPshOn.ne_top y hy))
    refine ⟨{x | u x < (C : EReal)}, hu.upperSemicontinuousOn y hy _ hC,
      C, ?_⟩
    rintro _ ⟨j, rfl⟩ x ⟨hx, hxW⟩
    exact (hle j x hxW).trans hx.le
  let Ω : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨W, hW⟩
  obtain ⟨r, hr, N, g, _hball, hgd, hgi, hgen⟩ :=
    MultiplierIdealBergmanNadelCoherence.exists_local_generators
      (Ω := Ω) hu hc hz
  have hgz : ∀ i : Fin N, MultiplierIntegrableAt u c (g i) z volume :=
    fun i => hgi i z (mem_ball_self hr)
  have hj : ∀ i : Fin N, ∃ j, MultiplierIntegrableAt (v j) c (g i) z volume := by
    intro i
    have hgA : AnalyticAt ℂ (g i) z := HolomorphicAnalytic.analyticAt_of_differentiableOn
      isOpen_ball (hgd i) (mem_ball_self hr)
    have hgreg : MultiplierIntegrableAt (uscRegularization (⨆ j, v j)) c (g i) z volume := by
      apply (hgz i).congr ?_ (EventuallyEq.refl _ _)
      filter_upwards [hW.mem_nhds hz] with y hy
      have hfun : (⨆ j, v j) = (fun x => ⨆ j, v j x) := by
        funext x
        exact iSup_apply
      rw [hfun]
      exact (hreg hy).symm
    have hgreg' := (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mp hgreg
    have hout (j : ℕ) := QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      (v j) c (g i) z
    let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
    let _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
    obtain ⟨j, hj⟩ := increasingStrongOpenness_ofRegularRoute (m + 1) W v hW hv hmono hb z hz
      c hc (g i) hgA hgreg'
    exact ⟨j, (hout j).mpr hj⟩
  choose J hJ using hj
  let j₀ := Finset.univ.sup J
  refine ⟨j₀, ?_⟩
  intro j hj f
  have hmore (i k : ℕ) (hik : i ≤ k) : MoreSingularAt (v i) (v k) z := by
    refine ⟨0, ?_⟩
    filter_upwards [hW.mem_nhds hz] with y hy
    simpa only [EReal.coe_zero, add_zero] using hmono y hy hik
  constructor
  · intro hf
    apply multiplierIntegrableAt_of_moreSingularAt (hu z hz).quasiPlurisubharmonicAt ?_ hf
    refine ⟨0, ?_⟩
    filter_upwards [hW.mem_nhds hz] with y hy
    simpa only [EReal.coe_zero, add_zero] using hle j y hy
  · intro hf
    have hgJ : ∀ i : Fin N, MultiplierIntegrableAt (v j) c (g i) z volume := by
      intro i
      have hi : J i ≤ j := (Finset.le_sup (Finset.mem_univ i)).trans hj
      exact multiplierIntegrableAt_of_moreSingularAt (hv j z hz).quasiPlurisubharmonicAt
        (hmore (J i) j hi) (hJ i)
    obtain ⟨N', s, a, hs, ha, heq⟩ := hgen z (mem_ball_self hr) f hf
    have hsJ : ∀ i : Fin N', MultiplierIntegrableAt (v j) c (s i) z volume := by
      intro i
      obtain ⟨l, hl⟩ := hs i
      rw [← hl]
      exact hgJ l
    have hsum := MultiplierIdealBergmanNadelManifold.multiplierIntegrableAt_sum_mul hc
      (hv j z hz).quasiPlurisubharmonicAt ha hsJ
    exact hsum.congr (EventuallyEq.refl _ _) heq.symm

/-- Zero-dimensional source PSH is finite on its actual domain. Reuse main's
proved full zero-dimensional ideal instead of a second integrability proof. -/
theorem multiplierIntegrableAt_zero_of_pshOn
    {W : Set (ComplexModel 0)} {u : ComplexModel 0 → EReal}
    (hu : PSHOn u W) {z : ComplexModel 0} (hz : z ∈ W)
    {c : ℝ} (hc : 0 < c) (f : ComplexModel 0 → ℂ) :
    MultiplierIntegrableAt u c f z volume := by
  obtain ⟨y, _hy, hyfin⟩ := hu.nontrivial
  have hbot : u z ≠ ⊥ := by simpa only [Subsingleton.elim y z] using hyfin
  have htop : u z ≠ ⊤ := hu.disc.ne_top z hz
  have he : u = fun _ => ((u z).toReal : EReal) := by
    funext x
    rw [Subsingleton.elim x z]
    exact (EReal.coe_toReal htop hbot).symm
  have hq : IsGlobalQuasiPshPotential (n := 0) u := by
    rw [he]
    exact isGlobalQuasiPshPotential_const _
  have hf : f = fun _ => f z := by
    funext x
    rw [Subsingleton.elim x z]
  have hF : HolomorphicAt 0 f z := by
    rw [hf]
    exact Eventually.of_forall fun _ => mdifferentiableAt_const
  have hmem := (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
    hq hc z f).mpr hF
  have hmi := hmem.2
  change MultiplierIntegrableAt (chartFunction u (complexChartAt (n := 0) z)) c
    (fun x => f ((complexChartAt (n := 0) z).val.symm x))
    ((complexChartAt (n := 0) z).val z) volume at hmi
  have hphi : chartFunction u (complexChartAt (n := 0) z) = u := by
    funext x
    change u ((complexChartAt (n := 0) z).val.symm x) = u x
    simp [complexChartAt, chartAt_self_eq]
  rw [hphi] at hmi
  simpa [complexChartAt, chartAt_self_eq] using hmi

/-- Entire-stalk increasing strong openness in every concrete dimension,
including the source's zero-dimensional case. -/
theorem increasing_psh_multiplier_stalk_stabilizes
    {n : ℕ} {W : Set (ComplexModel n)} (hW : IsOpen W)
    {u : ComplexModel n → EReal} {v : ℕ → ComplexModel n → EReal}
    (hu : PSHOn u W) (hv : ∀ j, PSHOn (v j) W)
    (hmono : ∀ y ∈ W, Monotone fun j => v j y)
    (hae : ∀ᵐ y ∂volume.restrict W,
      Tendsto (fun j => v j y) atTop (𝓝 (u y)))
    {z : ComplexModel n} (hz : z ∈ W) {c : ℝ} (hc : 0 < c) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∀ j ≥ j₀, ∀ f : ComplexModel n → ℂ,
      MultiplierIntegrableAt (v j) c f z volume ↔
        MultiplierIntegrableAt u c f z volume := by
  cases n with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    intro j _ f
    exact ⟨fun _ => multiplierIntegrableAt_zero_of_pshOn hu hz hc f,
      fun _ => multiplierIntegrableAt_zero_of_pshOn (hv j) hz hc f⟩
  | succ m =>
    obtain ⟨j₀, hj₀⟩ := increasing_psh_multiplier_stalk_stabilizes_pos hW
      (hu.disc.plurisubharmonicOn hW) (fun j => (hv j).disc.plurisubharmonicOn hW)
      hmono hae hz hc
    exact ⟨max j₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun j hj => hj₀ j ((le_max_left _ _).trans hj)⟩

/-- Source `thm:strongopen` on the full variable-dimensional atlas: every
actual chart has one cutoff for all germs at the original point. -/
theorem VariableComplexAtlas.IsPSH.multiplier_stalk_stabilizes
    {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}
    {u : X → EReal} {v : ℕ → X → EReal}
    (hu : A.IsPSH u) (hv : ∀ j, A.IsPSH (v j)) (hmono : Monotone v)
    (hae : ∀ i : A.Index, ∀ᵐ z ∂volume.restrict (A.chart i).target,
      Tendsto (fun j => A.coordinate (v j) i z) atTop (𝓝 (A.coordinate u i z)))
    (i : A.Index) {x : X} (hx : x ∈ (A.chart i).source) {c : ℝ} (hc : 0 < c) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∀ j ≥ j₀, ∀ f : ComplexModel (A.dimension i) → ℂ,
      MultiplierIntegrableAt (A.coordinate (v j) i) c f (A.chart i x) volume ↔
        MultiplierIntegrableAt (A.coordinate u i) c f (A.chart i x) volume := by
  have hz := (A.chart i).map_source hx
  have hup : PSHOn (A.coordinate u i) (A.chart i).target :=
    ⟨(hu.chartPlurisubharmonic i).discPshOn,
      LocallyNondegenerate.exists_coordinate_ne_bot hu.locallyNondegenerate
        (A.chart i) (A.chart i).open_target subset_rfl hz⟩
  have hvp (j : ℕ) : PSHOn (A.coordinate (v j) i) (A.chart i).target :=
    ⟨((hv j).chartPlurisubharmonic i).discPshOn,
      LocallyNondegenerate.exists_coordinate_ne_bot (hv j).locallyNondegenerate
        (A.chart i) (A.chart i).open_target subset_rfl hz⟩
  exact increasing_psh_multiplier_stalk_stabilizes (A.chart i).open_target hup hvp
    (fun z _ j k hjk => hmono hjk ((A.chart i).symm z)) (hae i) hz hc

/-- The original native multiplier ideal has one eventually stable ENTIRE
stalk. No compactness, connectedness, positive dimension or finite atlas. -/
theorem ManifoldPSH.multiplier_stalk_stabilizes
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} {v : ℕ → M → EReal}
    (hu : ManifoldPSH (n := n) u) (hv : ∀ j, ManifoldPSH (n := n) (v j))
    (hmono : Monotone v)
    (hae : ∀ e : ComplexChart n M, ∀ᵐ z ∂volume.restrict e.val.target,
      Tendsto (fun j => chartFunction (v j) e z) atTop (𝓝 (chartFunction u e z)))
    (x : M) {c : ℝ} (hc : 0 < c) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∀ j ≥ j₀, ∀ F : M → ℂ,
      (multiplierIdeal (n := n) c (v j)).mem x F ↔
        (multiplierIdeal (n := n) c u).mem x F := by
  let A := VariableComplexAtlas.ofFixedModel n M
  have huA : A.IsPSH u := (VariableComplexAtlas.ofFixedModel_isPSH_iff n M u).mpr hu
  have hvA (j : ℕ) : A.IsPSH (v j) :=
    (VariableComplexAtlas.ofFixedModel_isPSH_iff n M (v j)).mpr (hv j)
  let e := complexChartAt (n := n) x
  obtain ⟨j₀, hj₀, heq⟩ := huA.multiplier_stalk_stabilizes hvA hmono hae
    e (mem_complexChartAt_source x) hc
  refine ⟨j₀, hj₀, ?_⟩
  intro j hj F
  exact and_congr_right fun _ => heq j hj (fun z => F (e.val.symm z))

end SGPT.PSH
