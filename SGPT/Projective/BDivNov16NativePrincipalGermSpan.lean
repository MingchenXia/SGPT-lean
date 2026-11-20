import SGPT.NAPotential.GAGAMult2Limit

/-! Blueprint first: BDivNov16NativePrincipalGermSpan.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.BDivNov16
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (p : M) (f : M → ℂ) (hf : HolomorphicAt n f p)

omit [IsComplexManifold n M] in
theorem nativeGerm_singleton_span_eq_principal :
    spanGerms (n := n) (· = f) p = Ideal.span {NativeHolGerm.mk f hf} := by
  unfold spanGerms
  congr 1
  ext γ
  constructor
  · rintro ⟨g,hg,rfl,rfl⟩
    rfl
  · intro hγ
    obtain rfl := Set.mem_singleton_iff.mp hγ
    exact ⟨f,hf,rfl,rfl⟩

theorem nativeGerm_principal_mem_iff_isInSpanAt (g : M → ℂ) (hg : HolomorphicAt n g p) :
    NativeHolGerm.mk g hg ∈ Ideal.span {NativeHolGerm.mk f hf} ↔ IsInSpanAt (n := n) (· = f) p g := by
  rw [← nativeGerm_singleton_span_eq_principal p f hf]
  constructor
  · exact isInSpanAt_of_mk_mem_spanGerms hg
  · intro h
    exact mk_mem_spanGerms_of_isInSpanAt (fun s hs => hs ▸ hf) h
end SGPT.Projective.BDivNov16
