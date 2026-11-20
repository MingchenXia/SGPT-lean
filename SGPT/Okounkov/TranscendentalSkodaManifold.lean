import SGPT.Okounkov.TranscendentalSkodaManifoldStatement
import SGPT.Okounkov.TranscendentalSkodaTheorem
import SGPT.Foundations.Analysis.Pending.MultiplierIdeals
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon
import SGPT.Foundations.Analysis.FirstPass.AnalyticPoleSet

/-!
# Skoda's theorem for analytic singularities on a complex manifold

Blueprint node `skoda:manifold` (`claude-tok-skoda`), the manifold form of `tok:ext-skoda`
consumed by DENSITY: `manifoldSkodaStatement : ManifoldSkodaStatement`.

In the preferred chart `e` at `y`, the potential `φ ∘ e⁻¹ = log ∑ᵢ |gᵢ ∘ e⁻¹|² + R ∘ e⁻¹` has the
singularity type of `log ∑ᵢ |gᵢ ∘ e⁻¹|²` (bounded remainder), so TN's
`multiplierIntegrableAt_iff_of_sameSingularityTypeOn` identifies the multiplier ideals of `φ`
at `y` with those of `log |g ∘ e⁻¹|²` at `e y`, where `multiplierIdeal_add_eq_pow_mul` applies; the
generators `h_β` are transported between `M` and the chart.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter Set MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold

universe u

/-- **Skoda's theorem on a complex manifold** (`tok:ext-skoda`, manifold form). -/
theorem manifoldSkodaStatement : ManifoldSkodaStatement.{u} := by
  intro n M _ _ _ hn φ hφ r g U hU hg R C hRC hφeq y hy m k hm f
  set e := complexChartAt (n := n) y with he
  have hsrc : y ∈ e.val.source := mem_complexChartAt_source y
  set z₀ := e.val y with hz₀def
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hsrc
  have hleft : e.val.symm z₀ = y := e.val.left_inv hsrc
  set Ω := e.val.target ∩ e.val.symm ⁻¹' U with hΩdef
  have hΩ : IsOpen Ω := e.val.isOpen_inter_preimage_symm hU
  have hz₀Ω : z₀ ∈ Ω := ⟨hz₀t, by simp only [mem_preimage, hleft]; exact hy⟩
  set g' : Fin r → ComplexModel n → ℂ := fun i z => g i (e.val.symm z) with hg'def
  have hg' : ∀ i, DifferentiableOn ℂ (g' i) Ω := fun i =>
    differentiableOn_comp_chartSymm (n := n) y (hg i)
  have hgen : HolomorphicGeneratorsAt g' z₀ := ⟨Ω, hΩ, hz₀Ω, hg'⟩
  set φ' := chartFunction φ e with hφ'def
  -- `φ'` has the singularity type of `log |g'|²` on `Ω`
  have hval : ∀ z ∈ Ω, φ' z = generatorLog g' z + (R (e.val.symm z) : EReal) :=
    fun z hz => hφeq _ hz.2
  have hsame : SameSingularityTypeOn φ' (generatorLog g') Ω := by
    refine ⟨⟨C, fun z hz => ?_⟩, ⟨C, fun z hz => ?_⟩⟩
    · rw [hval z hz]
      gcongr
      exact (le_abs_self _).trans (hRC _ hz.2)
    · rw [hval z hz, add_assoc, ← EReal.coe_add]
      refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
      linarith [neg_abs_le (R (e.val.symm z)), hRC _ hz.2]
  have hφq : QuasiPlurisubharmonicAt φ' z₀ := hφ e z₀ hz₀t
  have hlq : QuasiPlurisubharmonicAt (generatorLog g') z₀ :=
    quasiPlurisubharmonicAt_generatorLog hgen
  have htrans : ∀ (c : ℝ) (h : ComplexModel n → ℂ),
      MultiplierIntegrableAt φ' c h z₀ volume ↔
        MultiplierIntegrableAt (generatorLog g') c h z₀ volume := fun c h =>
    Pending.multiplierIntegrableAt_iff_of_sameSingularityTypeOn hφq hlq (hΩ.mem_nhds hz₀Ω) hsame
  have hsk := multiplierIdeal_add_eq_pow_mul n r hn g' z₀ hgen m k hm
    (fun z => f (e.val.symm z))
  -- holomorphy in the chart
  have hhol : ∀ F : M → ℂ, HolomorphicAt n F y ↔
      ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => F (e.val.symm z)) z := fun F =>
    Pending.CoherentIdealColon.holomorphicAt_iff_holAt_chart (x := y) hsrc
  have hT : Tendsto e.val.symm (𝓝 z₀) (𝓝 y) := by
    have h := e.val.continuousAt_symm hz₀t
    rwa [ContinuousAt, hleft] at h
  constructor
  · rintro ⟨-, hfint⟩
    obtain ⟨h', hh', hfeq⟩ := hsk.mp ((htrans _ _).mp hfint)
    -- `h' β ∘ e` on `M`
    have hcomp : ∀ β, (fun z => h' β (e.val (e.val.symm z))) =ᶠ[𝓝 z₀] h' β := fun β =>
      Filter.eventually_of_mem (e.val.open_target.mem_nhds hz₀t) fun z hz =>
        congrArg (h' β) (e.val.right_inv hz)
    refine ⟨fun β p => h' β (e.val p), fun β => ⟨?_, ?_⟩, ?_⟩
    · rw [hhol]
      obtain ⟨-, V, hV, hz₀V, hdiff, -⟩ := hh' β
      filter_upwards [hV.mem_nhds hz₀V, e.val.open_target.mem_nhds hz₀t] with z hzV hzt
      have hev : (fun w => h' β (e.val (e.val.symm w))) =ᶠ[𝓝 z] h' β :=
        Filter.eventually_of_mem (e.val.open_target.mem_nhds hzt) fun w hw =>
          congrArg (h' β) (e.val.right_inv hw)
      exact ((hdiff z hzV).differentiableAt (hV.mem_nhds hzV)).congr_of_eventuallyEq hev
    · exact ((htrans _ _).mpr (hh' β)).congr (EventuallyEq.refl _ _) (hcomp β).symm
    · filter_upwards [e.val.open_source.mem_nhds hsrc, (e.val.continuousAt hsrc).eventually hfeq]
        with p hp hpe
      simp only [hg'def, e.val.left_inv hp] at hpe
      exact hpe
  · rintro ⟨h, hh, hfeq⟩
    have hfeq' : (fun z => f (e.val.symm z)) =ᶠ[𝓝 z₀]
        fun z => ∑ β, (∏ i, g' (β i) z) * h β (e.val.symm z) :=
      hT.eventually hfeq
    have hint : MultiplierIntegrableAt (generatorLog g') ((k + m : ℕ) : ℝ)
        (fun z => f (e.val.symm z)) z₀ volume :=
      hsk.mpr ⟨fun β z => h β (e.val.symm z), fun β => (htrans _ _).mp (hh β).2, hfeq'⟩
    refine ⟨?_, (htrans _ _).mpr hint⟩
    obtain ⟨-, V, hV, hz₀V, hdiff, -⟩ := hint
    rw [hhol]
    filter_upwards [hV.mem_nhds hz₀V] with z hz
    exact (hdiff z hz).differentiableAt (hV.mem_nhds hz)

end SGPT.Okounkov.TranscendentalSkoda
