import SGPT.Toric.ToricIntegralPerturbation
import SGPT.Toric.ToricTranslatedFaceMinkowski
import SGPT.Toric.ToricStratumReferenceFace

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Pointwise Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine perturbed CURRENT'S original face, in the actual
annihilator, is N times the original CURRENT'S face plus the genuine ample
reference face. Literal metric/profile/Cartier/supporting equations produce
the identity, with arbitrary original Cartier representative and no target
body/model certificate among the inputs. -/
theorem BigToricMetric.integralKahlerPerturbation_translatedFace
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (N : ℕ) (hN : 0 < N) :
    toricStratumTranslatedFace (N • D + polytopeToricAmpleDivisor γ hs) v J
      (N • mσ + toricCartierDatum (polytopeToricAmpleDivisor γ hs) v)
      ((h.integralKahlerPerturbation N).newtonBody (fun p => ((N : ℝ) : EReal) * u p)) =
      (N : ℝ) • toricStratumTranslatedFace D v J mσ (h.newtonBody u) +
        toricStratumReferenceFace (hs := hs) v J := by
  rw [h.integralKahlerPerturbation_newtonBody N hN hu]
  exact toricStratumTranslatedFace_nsmul_add D (polytopeToricAmpleDivisor γ hs) v J mσ _ hσ
    (isToricCartierDatumAlong_vertex (polytopeToricAmpleDivisor γ hs) v J) N hN
    (h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu).2.2.2
    (by rw [toricDivisorPolytope_ampleDivisor])

end SGPT.Toric
