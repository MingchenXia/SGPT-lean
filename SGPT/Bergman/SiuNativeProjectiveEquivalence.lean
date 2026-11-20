import SGPT.Bergman.SiuNativeProjectiveNS
import SGPT.Bergman.SiuNativePositiveNS
import SGPT.Trace.BertiniSetting

/-! Both directions of actual projectivity versus an actual Kähler class
in the original real Cartier span, without any resolution construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The exact same original compact complex manifold admits an actual
native holomorphic closed projective embedding with injective mfderiv iff
its existing real Cartier span contains an actual Kähler class. -/
theorem exists_kahler_mem_neronSeveri_iff_native_projective_embedding :
    (∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
      RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X) ↔
    ∃ (N : ℕ) (f : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      X (ComplexProjectiveSpace N) ∞), Topology.IsClosedEmbedding f ∧
      ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) f p) := by
  constructor
  · rintro ⟨omega, hK, hNS⟩
    obtain ⟨G, d, hd, N, s, hgen, hhol, hemb, himm⟩ :=
      kodairaEmbedding_of_kahler_mem_neronSeveri omega hK hNS
    exact ⟨N, ⟨_, hhol⟩, hemb, himm⟩
  · rintro ⟨N, f, _, himm⟩
    exact exists_kahler_mem_neronSeveri_of_native_projective_immersion f himm

/-- The existing source-facing analytic projectivity predicate, used by
Bertini, is exactly equivalent to an actual NS_R Kähler class. This uses
the original native maps and mfderiv, without a new projectivity predicate
or a scheme algebraization assumption. -/
theorem isProjectiveManifold_iff_exists_kahler_mem_neronSeveri :
    SGPT.Trace.Bertini.IsProjectiveManifold n X ↔
      ∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
        RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X := by
  constructor
  · rintro ⟨N, f, hf, _, himm⟩
    exact exists_kahler_mem_neronSeveri_of_native_projective_immersion ⟨f, hf⟩ himm
  · intro h
    obtain ⟨N, f, hemb, himm⟩ :=
      exists_kahler_mem_neronSeveri_iff_native_projective_embedding.mp h
    exact ⟨N, f, f.contMDiff, hemb.injective, himm⟩

end SGPT.BDivisor.NSKodaira
