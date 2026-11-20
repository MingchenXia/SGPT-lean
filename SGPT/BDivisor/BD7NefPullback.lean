import SGPT.BDivisor.ClassPullback

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.BD7

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

universe u

variable {m : ℕ} {U V : Type u} [TopologicalSpace U] [TopologicalSpace V]
  [ChartedSpace (ComplexModel (m + 1)) U] [ChartedSpace (ComplexModel (m + 1)) V]
  [IsComplexManifold (m + 1) U] [IsComplexManifold (m + 1) V]

/-- Pullback of a nef Bott--Chern class is nef for any Kähler background on the
compact source. -/
theorem classNefWithRespectTo_pullback_bd7 [CompactSpace U] {g : U → V}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    (κU : KahlerBackground (m + 1) U) (κV : KahlerBackground (m + 1) V)
    (α : RealBottChern (m + 1) V) (hn : ClassNefWithRespectTo κV α) :
    ClassNefWithRespectTo κU (classPullback hg α) := by
  induction α using Quotient.inductionOn with
  | _ θ => exact nefWithRespectTo_pullback hg κV κU hn

end SGPT.BDivisor.BD7
