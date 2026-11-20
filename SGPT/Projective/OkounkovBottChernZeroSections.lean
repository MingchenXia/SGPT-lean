import SGPT.Projective.OkounkovFlatUniformSections
import SGPT.Bergman.SiuNSMetricPotential
import SGPT.LineBundle.TMetricSections

/-! Genuine class-zero metric flattening and SAME original twisted-power sections.
Blueprint: okounkov-bott-chern-zero-sections.tex. No whole source credit yet. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.FlatTwist
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2
open SGPT.BDivisor.NSKodaira SGPT.LineBundle.TMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Actual quotient equality manufactures a genuine smooth flat metric on the SAME holomorphic bundle. -/
theorem exists_actual_flat_rescaling_of_class_zero
    (N : HermitianHolomorphicLineBundle.{0,0} n X) (hN : IsSourceSmoothHermitianMetric N)
    (θ : ClosedRealOneOneForm n X) (hθ : IsOwnFirstChernForm N θ)
    (hclass : RealBottChern.ofRepresentative θ = 0) :
    ∃ (f : X → ℝ) (hf : ChartSmooth (n:=n) f),
      IsSourceSmoothHermitianMetric (rescaleExp N f hf) ∧
      IsOwnFirstChernForm (rescaleExp N f hf) (0 : ClosedRealOneOneForm n X) := by
  obtain ⟨f,hf,heq⟩ := (RealBottChern.ofRepresentative_eq_iff θ 0).mp hclass
  exact ⟨f,hf,rescaleExp_smooth N hN f hf,
    rescale_exp_isOwnFirstChernForm N hN θ 0 hθ f hf heq⟩

/-- A SINGLE threshold BEFORE ANY class-zero original line, producing sections in the ORIGINAL fibers. -/
theorem exists_uniform_class_zero_twist_nonzero_sections [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0,0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) :
    ∃ k₀ : ℕ, 0<k₀ ∧ ∀ k : ℕ, k₀≤k →
      ∀ N : HermitianHolomorphicLineBundle.{0,0} n X, IsSourceSmoothHermitianMetric N →
      ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm N θ →
      RealBottChern.ofRepresentative θ = 0 →
      ∀ m : ℕ, 0<m → ∀ p : X,
        ∃ s : HolomorphicSections (n:=n) (twistedPower N (positivePower G (k-1)) m).Fiber,
          s p ≠ 0 := by
  obtain ⟨k₀,hk₀,huniform⟩ := exists_uniform_flat_twist_nonzero_sections G hG θG hθG hKah
  refine ⟨k₀,hk₀,?_⟩
  intro k hk N hN θ hθ hclass m hm p
  obtain ⟨f,hf,hflat,hzero⟩ := exists_actual_flat_rescaling_of_class_zero N hN θ hθ hclass
  obtain ⟨s,hs⟩ := huniform k hk (rescaleExp N f hf) hflat hzero m hm p
  let Φ := rescaleEquiv N (fun x => Real.exp (-f x))
    (Real.continuous_exp.comp (ProductTestForms.ChartSmooth.continuous hf).neg)
    (fun _ => Real.exp_pos _)
  let Ψ := FrameIdentityEquiv.twistedPowerCongr Φ
    (FrameIdentityEquiv.refl (positivePower G (k-1)).Fiber) m
  refine ⟨Ψ.symm.sectionMap s,?_⟩
  intro hzero
  change (Ψ.equiv p).symm (s p) = 0 at hzero
  exact hs ((Ψ.equiv p).symm.map_eq_zero_iff.mp hzero)

end SGPT.Okounkov.FlatTwist
