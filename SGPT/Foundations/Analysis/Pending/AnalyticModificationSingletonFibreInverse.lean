import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
import SGPT.Foundations.Analysis.Pending.RiemannExtensionThin
import Mathlib.Analysis.Calculus.FDeriv.WithLp

set_option autoImplicit false

/-!
# A singleton modification fibre is unramified

Properness confines the original inverse on an analytic complement to a
bounded chart around the singleton fibre.  Actual Riemann extension of
its coordinates and density give a holomorphic left inverse germ.
Differentiating that produced germ proves bijectivity of the differential.
The exceptional witnesses may be enlarged; their codimension is not used.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationSingletonFibreInverse

open FirstPass FirstPass.BlowupSequences FirstPass.HolomorphicMaps
  AnalyticModificationLocalDiscrepancy

noncomputable section

private theorem exists_vector_extension {n : ℕ} {p : ComplexModel n} {r C : ℝ}
    {T : Set (ComplexModel n)} {f : ComplexModel n → ComplexModel n}
    {h : ComplexModel n → ℂ} (hr : 0 < r)
    (hUT : IsOpen (ball p r \ T))
    (hf : DifferentiableOn ℂ f (ball p r \ T))
    (hh : DifferentiableOn ℂ h (ball p r))
    (hne : ¬ ∀ᶠ z in 𝓝 p, h z = 0)
    (hTh : ∀ z ∈ ball p r, z ∈ T → h z = 0)
    (hC : ∀ z ∈ ball p r \ T, ‖f z‖ ≤ C) :
    ∃ F : ComplexModel n → ComplexModel n,
      ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ F z ∧ (z ∉ T → F z = f z) := by
  classical
  have hext (i : Fin n) : ∃ ρ > 0, ∃ F : ComplexModel n → ℂ,
      DifferentiableOn ℂ F (ball p ρ) ∧
        ∀ z ∈ ball p ρ \ T, F z = f z i := by
    obtain ⟨ρ, hρ, _, _, F, hF, hFe⟩ :=
      RiemannExtensionThin.exists_local_extension hUT
        ((EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn hf)
        hr subset_rfl hh hne hTh
        (fun z hz => (PiLp.norm_apply_le (f z) i).trans (hC z hz))
    exact ⟨ρ, hρ, F, hF, hFe⟩
  choose ρ hρ F hF hFe using hext
  refine ⟨fun z => WithLp.toLp 2 (fun i => F i z), ?_⟩
  have hev : ∀ᶠ z in 𝓝 p, ∀ i : Fin n,
      DifferentiableAt ℂ (F i) z ∧ (z ∉ T → F i z = f z i) := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hρ i))] with z hz
    exact ⟨(hF i).differentiableAt (isOpen_ball.mem_nhds hz), fun hzT => hFe i z ⟨hz, hzT⟩⟩
  filter_upwards [hev] with z hz
  refine ⟨(differentiableAt_piLp 2).mpr fun i => (hz i).1, ?_⟩
  intro hzT
  ext i
  exact (hz i).2 hzT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual singleton-fibre geometry internally supplies an unramified
point; no inverse or differential certificate is an input. -/
theorem not_mem_exceptionalLocus_of_unique_fibre {g : Y → X}
    (hg : IsAnalyticModification (n := n) g) (y : Y)
    (hunique : ∀ z : Y, g z = g y → z = y) : y ∉ exceptionalLocus n g := by
  classical
  obtain ⟨A, B, s, hAc, _, hAi, hBc, hBa, hBi, hpre, hs, hright, hleft⟩ := hg.2.2
  let e := complexChartAt (n := n) y
  let d := complexChartAt (n := n) (g y)
  let p := d.val (g y)
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hgd : g y ∈ d.val.source := mem_complexChartAt_source (g y)
  have hpdt : p ∈ d.val.target := d.val.map_source hgd
  let U : Set Y := e.val.source ∩ e.val ⁻¹' ball (e.val y) 1
  have hUo : IsOpen U := e.val.isOpen_inter_preimage isOpen_ball
  have hyU : y ∈ U := ⟨hye, mem_ball_self one_pos⟩
  let N : Set X := d.val.source ∩ (g '' Uᶜ)ᶜ
  have hNo : IsOpen N :=
    d.val.open_source.inter (hg.2.1.isClosedMap _ hUo.isClosed_compl).isOpen_compl
  have hgyN : g y ∈ N := by
    refine ⟨hgd, ?_⟩
    rintro ⟨z, hz, hzy⟩
    exact hz (hunique z hzy ▸ hyU)
  have hpreN : g ⁻¹' N ⊆ U := by
    intro z hz
    by_contra hzU
    exact hz.2 ⟨z, hzU, rfl⟩
  obtain ⟨P⟩ := hBa (g y)
  have hgne : ∃ i, ¬ ∀ᶠ z in 𝓝 p, P.generator i z = 0 := by
    by_contra hall
    push Not at hall
    have hzeros : ∀ᶠ z in 𝓝 p, ∀ i, P.generator i z = 0 :=
      Filter.eventually_all.mpr hall
    have hev : ∀ᶠ x in 𝓝 (g y), x ∈ B := by
      have hdc : ContinuousAt d.val (g y) := d.val.continuousAt hgd
      filter_upwards [d.val.open_source.mem_nhds hgd,
        hdc.eventually (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood),
        hdc.eventually hzeros] with x hxd hxP hxzero
      exact (P.zeroLocus hxd hxP).mpr hxzero
    have hi : g y ∈ interior B := mem_interior_iff_mem_nhds.mpr hev
    rw [hBi] at hi
    exact hi
  obtain ⟨i, hi⟩ := hgne
  let W : Set (ComplexModel n) :=
    (d.val.target ∩ d.val.symm ⁻¹' N) ∩ P.coordinateNeighborhood
  have hWo : IsOpen W :=
    (d.val.isOpen_inter_preimage_symm hNo).inter P.isOpen_coordinateNeighborhood
  have hpW : p ∈ W :=
    ⟨⟨hpdt, by change d.val.symm (d.val (g y)) ∈ N; rwa [d.val.left_inv hgd]⟩,
      P.center_mem_coordinateNeighborhood⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWo p hpW
  let T : Set (ComplexModel n) := d.val.target ∩ d.val.symm ⁻¹' B
  have hballT : ∀ z ∈ ball p r, z ∈ T ↔ d.val.symm z ∈ B :=
    fun z hz => ⟨fun hzT => hzT.2, fun hzB => ⟨(hrW hz).1.1, hzB⟩⟩
  have hTh : ∀ z ∈ ball p r, z ∈ T → P.generator i z = 0 := by
    intro z hz hzT
    have hzs : d.val.symm z ∈ d.val.source := d.val.map_target (hrW hz).1.1
    have hzP : d.val (d.val.symm z) ∈ P.coordinateNeighborhood := by
      rw [d.val.right_inv (hrW hz).1.1]
      exact (hrW hz).2
    have hzero := (P.zeroLocus hzs hzP).mp hzT.2 i
    rwa [d.val.right_inv (hrW hz).1.1] at hzero
  have hUT : IsOpen (ball p r \ T) := by
    have heq : ball p r \ T = ball p r ∩ (d.val.target ∩ d.val.symm ⁻¹' Bᶜ) := by
      ext z
      constructor
      · rintro ⟨hz, hzT⟩
        exact ⟨hz, (hrW hz).1.1, fun hzB => hzT ⟨(hrW hz).1.1, hzB⟩⟩
      · rintro ⟨hz, _, hzB⟩
        exact ⟨hz, fun hzT => hzB hzT.2⟩
    rw [heq]
    exact isOpen_ball.inter (d.val.isOpen_inter_preimage_symm hBc.isOpen_compl)
  let f : ComplexModel n → ComplexModel n := coordinateMap s d e
  have hf : DifferentiableOn ℂ f (ball p r \ T) := by
    intro z hz
    have hzdt : z ∈ d.val.target := (hrW hz.1).1.1
    have hzB : d.val.symm z ∉ B := fun hzB => hz.2 ⟨hzdt, hzB⟩
    have hsgN : g (s (d.val.symm z)) ∈ N := by
      rw [hright _ hzB]
      exact (hrW hz.1).1.2
    have hse : s (d.val.symm z) ∈ e.val.source := (hpreN hsgN).1
    have hd : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ d.val.symm z :=
      (contMDiffOn_chart_symm (n := ∞)).contMDiffAt (d.val.open_target.mem_nhds hzdt)
    have hsd : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s (d.val.symm z) :=
      hs.contMDiffAt (hBc.isOpen_compl.mem_nhds hzB)
    have he : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.val (s (d.val.symm z)) :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt (e.val.open_source.mem_nhds hse)
    exact ((he.comp z (hsd.comp z hd)).contDiffAt.differentiableAt (by simp)).differentiableWithinAt
  have hfC : ∀ z ∈ ball p r \ T, ‖f z‖ ≤ ‖e.val y‖ + 1 := by
    intro z hz
    have hzB : d.val.symm z ∉ B := (hballT z hz.1).not.mp hz.2
    have hsU : s (d.val.symm z) ∈ U := by
      apply hpreN
      change g (s (d.val.symm z)) ∈ N
      rw [hright _ hzB]
      exact (hrW hz.1).1.2
    have hdist : ‖e.val (s (d.val.symm z)) - e.val y‖ < 1 := by
      simpa only [mem_preimage, mem_ball, dist_eq_norm] using hsU.2
    have h := norm_le_insert' (e.val (s (d.val.symm z))) (e.val y)
    change ‖e.val (s (d.val.symm z))‖ ≤ ‖e.val y‖ + 1
    calc _ ≤ ‖e.val y‖ + ‖e.val (s (d.val.symm z)) - e.val y‖ := by
          simpa [norm_sub_rev, add_comm] using h
      _ ≤ ‖e.val y‖ + 1 := add_le_add le_rfl hdist.le
  obtain ⟨F, hF⟩ := exists_vector_extension hr hUT hf
    ((P.generator_holomorphic i).mono fun z hz => (hrW hz).2) hi hTh hfC
  have hFd : DifferentiableAt ℂ F p := hF.self_of_nhds.1
  obtain ⟨Q, hQsub, hQo, hpQ⟩ := _root_.mem_nhds_iff.mp hF
  let O : Set Y := e.val.source ∩ (g ⁻¹' (d.val.source ∩ d.val ⁻¹' Q))
  have hOo : IsOpen O :=
    e.val.open_source.inter ((d.val.isOpen_inter_preimage hQo).preimage hg.1.continuous)
  have hyO : y ∈ O := ⟨hye, hgd, hpQ⟩
  have hleftE : EqOn (fun z => F (d.val (g z))) e.val (O \ A) := by
    intro z hz
    have hgzB : g z ∉ B := by
      intro hzB
      apply hz.2
      rw [← hpre]
      exact hzB
    have hqT : d.val (g z) ∉ T := by
      intro hzT
      apply hgzB
      have hzB := hzT.2
      change d.val.symm (d.val (g z)) ∈ B at hzB
      rwa [d.val.left_inv hz.1.2.1] at hzB
    have heq := (hQsub hz.1.2.2).2 hqT
    change F (d.val (g z)) = e.val z
    rw [heq]
    change e.val (s (d.val.symm (d.val (g z)))) = e.val z
    rw [d.val.left_inv hz.1.2.1, hleft z hz.2]
  have hdense : O ⊆ closure (O \ A) := by
    intro z hz
    rw [mem_closure_iff_nhds]
    intro L hL
    have hopen : IsOpen (interior L ∩ O) := isOpen_interior.inter hOo
    have hz' : z ∈ interior L ∩ O := ⟨mem_interior_iff_mem_nhds.mpr hL, hz⟩
    have hnot : ¬ interior L ∩ O ⊆ A := by
      intro hsub
      have hi := interior_maximal hsub hopen hz'
      rw [hAi] at hi
      exact hi
    obtain ⟨w, ⟨hwL, hwO⟩, hwA⟩ := not_subset.mp hnot
    exact ⟨w, interior_subset hwL, hwO, hwA⟩
  have hFe : EqOn (fun z => F (d.val (g z))) e.val O := by
    apply hleftE.of_subset_closure ?_ (e.val.continuousOn.mono inter_subset_left) sdiff_subset hdense
    have hFQ : ContinuousOn F Q := fun z hz => (hQsub hz).1.continuousAt.continuousWithinAt
    exact hFQ.comp
      (d.val.continuousOn.comp hg.1.continuous.continuousOn fun z hz => hz.2.1)
      fun z hz => hz.2.2
  have hFp : F p = e.val y := hFe hyO
  let t : X → Y := fun x => e.val.symm (F (d.val x))
  have htd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) t (g y) := by
    have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d.val (g y) :=
      ((contMDiffOn_chart (n := ∞)).contMDiffAt
        (d.val.open_source.mem_nhds hgd)).mdifferentiableAt (by simp)
    have hFmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F p :=
      hFd.mdifferentiableAt
    have he : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val.symm (F p) := by
      apply ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt ?_).mdifferentiableAt (by simp)
      rw [hFp]
      exact e.val.open_target.mem_nhds (e.val.map_source hye)
    exact he.comp (g y) (hFmd.comp (g y) hd)
  have htg : (t ∘ g) =ᶠ[𝓝 y] id := by
    filter_upwards [hOo.mem_nhds hyO] with z hz
    change e.val.symm (F (d.val (g z))) = z
    have heq : F (d.val (g z)) = e.val z := hFe hz
    rw [heq, e.val.left_inv hz.1]
  have hgd' := (hg.1 y).mdifferentiableAt (by simp)
  have hder : (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) t (g y)).comp
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y) =
        ContinuousLinearMap.id ℂ (ComplexModel n) := by
    rw [← mfderiv_comp y htd hgd', htg.mfderiv_eq, mfderiv_id]
    rfl
  have hinj : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y) := by
    have hli : Function.LeftInverse
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) t (g y))
        (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y) :=
      fun v => DFunLike.congr_fun hder v
    exact hli.injective
  let L : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    { toFun := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y
      map_add' := (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y).map_add
      map_smul' := (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y).map_smul }
  have hLin : Function.Injective L := hinj
  have hbij : Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g y) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := L)).mp hLin⟩
  simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hbij

end

end SGPT.Foundations.Analysis.Pending.AnalyticModificationSingletonFibreInverse
