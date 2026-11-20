import SGPT.Foundations.Analysis.Pending.ResolvedNefPart
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

set_option autoImplicit false

/-! # The original local analytic reference internally produces its coherent ideal

The literal finite family on an actual open neighborhood generates every stalk.
Original nondegeneracy supplies every nonzero stalk, including in dimension zero.
No coherent ideal, compactness or mass hypothesis is an input.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualLocalAnalyticReferenceIdeal

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.QuasiEquisingularApproximation DivisorExponentAlong

noncomputable section

/-- Original analytic data produce the same finite-family ideal on an actual
open neighborhood, together with coherence and every nonzero stalk. -/
theorem exists_local_reference_ideal {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {φ : X → EReal} (hnd : LocallyNondegenerate φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) φ) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ (c : ℚ) (N : ℕ) (G : Fin N → U → ℂ)
      (b : U → ℝ) (C : ℝ) (I : GermIdeal n U),
      0 < c ∧ (∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i)) ∧
      (∀ y : U, |b y| ≤ C) ∧
      (∀ y : U, φ y = ((c : ℝ) : EReal) * generatorLog G y + (b y : EReal)) ∧
      (∀ y : U, ∀ F : U → ℂ,
        I.mem y F ↔ IsInSpanAt (n := n) (· ∈ Set.range G) y F) ∧
      I.IsCoherent ∧ HasAnalyticSingularitiesOfType (fun y : U => φ y) c I ∧
      ∀ y : U, IsNonzeroAlongAt Set.univ I y := by
  classical
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨c, N, f, hc, ⟨V, hV, hxV, hf⟩, b, ⟨C, _, hb⟩, heq⟩ :=
    hA e (e.val x) (e.val.map_source hx)
  have hev : ∀ᶠ z in 𝓝 (e.val x), z ∈ V ∧ |b z| ≤ C ∧
      chartFunction φ e z = ((c : ℝ) : EReal) * generatorLog f z + (b z : EReal) := by
    filter_upwards [hV.mem_nhds hxV, hb, heq] with z hz hzb hze
    exact ⟨hz, hzb, hze⟩
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hev
  let U : Opens X := ⟨e.val.source ∩ e.val ⁻¹' W, e.val.isOpen_inter_preimage hWo⟩
  have hxU : x ∈ U := ⟨hx, hxW⟩
  let G : Fin N → U → ℂ := fun i y => f i (e.val y)
  let B : U → ℝ := fun y => b (e.val y)
  let I : GermIdeal n U := ⟨fun y F => IsInSpanAt (n := n) (· ∈ Set.range G) y F⟩
  have hG : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) := by
    intro i y
    have hdi : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
        (f i) (e.val y) := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact (hf i).differentiableAt (hV.mem_nhds (hW y.2.2).1)
    exact (hdi.comp y.val (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt y.2.1)).comp y
      ((contMDiff_subtype_val (n := ∞) y).mdifferentiableAt (by simp))
  have hbound : ∀ y : U, |B y| ≤ C := fun y => (hW y.2.2).2.1
  have hformula : ∀ y : U,
      φ y = ((c : ℝ) : EReal) * generatorLog G y + (B y : EReal) := by
    intro y
    have hy := (hW y.2.2).2.2
    simpa only [chartFunction, e.val.left_inv y.2.1, generatorLog, generatorVector, G, B]
      using hy
  have hcoherent : I.IsCoherent := by
    intro y
    exact ⟨univ, isOpen_univ, mem_univ y, N, G,
      fun i => (hG i).mdifferentiableOn, fun _ _ _ => Iff.rfl⟩
  have htype : HasAnalyticSingularitiesOfType (fun y : U => φ y) c I := by
    refine ⟨(by exact_mod_cast hc), hcoherent, ?_⟩
    intro y
    exact ⟨univ, isOpen_univ, mem_univ y, N, G,
      fun i => (hG i).mdifferentiableOn, fun _ _ _ => Iff.rfl,
      B, C, fun z _ => hbound z, fun z _ => hformula z⟩
  have hndU : LocallyNondegenerate (fun y : U => φ y) := by
    intro y O hO hyO
    have hopen : IsOpen (Subtype.val '' O : Set X) :=
      U.isOpen.isOpenMap_subtype_val O hO
    obtain ⟨z, hz, hfin⟩ := hnd y (Subtype.val '' O) hopen ⟨y, hyO, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, hw, hfin⟩
  refine ⟨U, hxU, c, N, G, B, C, I, (by exact_mod_cast hc), hG, hbound,
    hformula, (fun _ _ => Iff.rfl), hcoherent, htype, ?_⟩
  exact ResolvedNefPart.isNonzeroAlongAt_of_hasAnalyticSingularitiesOfType htype hndU

end
end SGPT.Foundations.Analysis.Pending.ActualLocalAnalyticReferenceIdeal
