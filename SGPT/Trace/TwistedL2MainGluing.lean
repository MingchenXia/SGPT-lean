import SGPT.Trace.TwistedL2MainLocalSection

/-!
# Gluing the actual local correction representatives

The local representatives share the original bundle-valued `G - correction`
almost everywhere. Full support upgrades this to pointwise agreement on
open overlaps, and a countable subcover transfers the a.e. identity to U.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- Genuine local adjoint-test equations produce an actual holomorphic
section equal almost everywhere on U to the original `G - correction`. -/
theorem exists_holomorphic_section_ae_difference
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (htest : ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing) :
    ∃ S : (x : X) → T.L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) T.L.Fiber S T.U ∧
      ∀ᵐ x ∂(T.μ.restrict T.U), S x = T.G x - T.correctionSection u x := by
  classical
  let c : T.U → ComplexChart n X := fun y => complexChartAt (n := n) y.val
  let e : T.U → AtlasFrame T.L := fun y => atlasFrameAt T.L y.val
  choose ρ hρ using fun y : T.U => T.volume_smooth (c y)
  choose F hF hae using fun y : T.U =>
    T.exists_localSection_ae_difference u htest (c y) (e y) (hρ y)
  have hcover : ∀ x ∈ T.U, ∃ y : T.U, x ∈ T.localSectionRegion (c y) (e y) := by
    intro x hx
    refine ⟨⟨x, hx⟩, hx, ?_, ?_⟩
    · exact mem_complexChartAt_source x
    · exact mem_atlasFrameAt_baseSet T.L x
  choose pick hpick using hcover
  let S : (x : X) → T.L.Fiber x := fun x =>
    if hx : x ∈ T.U then T.localSection (c (pick x hx)) (e (pick x hx)) (F (pick x hx)) x
    else 0
  have hkey : ∀ (y : T.U) (x : X), x ∈ T.localSectionRegion (c y) (e y) →
      S x = T.localSection (c y) (e y) (F y) x := by
    intro y x hx
    have hxU : x ∈ T.U := hx.1
    have hp := hpick x hxU
    simp only [S, dif_pos hxU]
    exact T.localSections_eq_fiber_on_overlap u (c (pick x hxU)) (c y)
      (e (pick x hxU)) (e y) (hF (pick x hxU)) (hF y)
      (hae (pick x hxU)) (hae y) ⟨hp, hx⟩
  have hcoef : ∀ (y : T.U) (x : X), x ∈ T.localSectionRegion (c y) (e y) →
      ((e y).val ⟨x, S x⟩).2 = F y ((c y).val x) := by
    intro y x hx
    let := (e y).property
    rw [hkey y x hx, localSection]
    exact congrArg Prod.snd ((e y).val.apply_mk_symm hx.2.2 (F y ((c y).val x)))
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    let y := pick x hx
    let := (e y).property
    have hreg : x ∈ T.localSectionRegion (c y) (e y) := hpick x hx
    have hregopen : IsOpen (T.localSectionRegion (c y) (e y)) :=
      T.isOpen_localSectionRegion (c y) (e y)
    have hz : (c y).val x ∈ T.pieceDomain (c y) (e y) := by
      refine ⟨⟨(c y).val.map_source hreg.2.1, ?_⟩, ?_⟩
      · simpa only [mem_preimage, (c y).val.left_inv hreg.2.1] using hreg.2.2
      · simpa only [mem_preimage, (c y).val.left_inv hreg.2.1] using hreg.1
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n))
      (e y).val S hreg.2.2]
    refine MDifferentiableAt.congr_of_eventuallyEq ?_
      (eventually_of_mem (hregopen.mem_nhds hreg) fun x' hx' => hcoef y x' hx')
    exact (((hF y).differentiableAt ((T.isOpen_pieceDomain (c y) (e y)).mem_nhds hz)).comp_mdifferentiableAt
      (mdifferentiableAt_atlas (c y).property hreg.2.1))
  · obtain ⟨J, hJcount, hJunion⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun y : T.U => T.localSectionRegion (c y) (e y))
      (fun y => T.isOpen_localSectionRegion (c y) (e y))
    let : Countable J := hJcount.to_subtype
    have hAe : ∀ y : J, ∀ᵐ x ∂(T.μ.restrict T.U),
        x ∈ T.localSectionRegion (c y.val) (e y.val) →
          S x = T.G x - T.correctionSection u x := by
      intro y
      have hy : ∀ᵐ x ∂T.μ,
          x ∈ T.localSectionRegion (c y.val) (e y.val) →
            T.localSection (c y.val) (e y.val) (F y.val) x =
              T.G x - T.correctionSection u x :=
        (ae_restrict_iff' (T.isOpen_localSectionRegion (c y.val) (e y.val)).measurableSet).mp
          (hae y.val)
      filter_upwards [hy.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hreg
      rw [hkey y.val x hreg]
      exact hx hreg
    filter_upwards [ae_all_iff.mpr hAe, ae_restrict_mem T.isOpen_U.measurableSet] with x hxall hxU
    have hxunion : x ∈ ⋃ y : T.U, T.localSectionRegion (c y) (e y) :=
      mem_iUnion.mpr ⟨pick x hxU, hpick x hxU⟩
    rw [← hJunion] at hxunion
    obtain ⟨y, hyJ, hyreg⟩ := mem_iUnion₂.mp hxunion
    exact hxall ⟨y, hyJ⟩ hyreg

end TwistedDatum
end SGPT.Trace.TwistedL2
