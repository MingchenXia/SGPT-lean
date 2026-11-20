import SGPT.Foundations.Analysis.Pending.NaturalRealPPPositiveSpanDictionary
import SGPT.Foundations.Analysis.FirstPass.FormPullback

/-!
# Genuine usual pure type for original global smooth real forms

Pure type uses the constructed unique complex extension and actual projections.
The original smooth coefficient and tensor overlap fields are retained.
Preferred-chart detection, arbitrary holomorphic pullback and geometric
quotient descent are proved, including zero dimensions and empty manifolds.
No global topology, Green operator or current cohomology dictionary is claimed.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalSmoothPurePPTransport

open SGPT.Foundations.Analysis.FirstPass
open HolomorphicMaps
open NaturalRealAlternatingComplexification NaturalRealPPSubmodule
open NaturalRealPPPositiveSpanDictionary
open scoped Manifold ContDiff

theorem isPureRealPP_compContinuousLinearMap {m n p : ℕ}
    (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ)
    (L : ComplexModel m →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v)
    (hA : IsPureRealPP p (A.toAlternatingMap.domDomCongr (finCongr (two_mul p)))) :
    IsPureRealPP p ((A.compContinuousLinearMap L).toAlternatingMap.domDomCongr
      (finCongr (two_mul p))) := by
  have he : (A.compContinuousLinearMap L).toAlternatingMap.domDomCongr
      (finCongr (two_mul p)) =
      (A.toAlternatingMap.domDomCongr (finCongr (two_mul p))).compLinearMap
        L.toLinearMap := by
    ext v
    rfl
  rw [he]
  exact isPureRealPP_compLinearMap _ L.toLinearMap hL hA

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def IsPurePP (a : SmoothRealForm n M (2 * p)) : Prop :=
  ∀ e z, z ∈ e.val.target →
    IsPureRealPP p ((a.coeff e z).toAlternatingMap.domDomCongr (finCongr (two_mul p)))

theorem isPurePP_iff_coeff_mem_formSpan (a : SmoothRealForm n M (2 * p)) :
    IsPurePP a ↔ ∀ e z, z ∈ e.val.target →
      a.coeff e z ∈ LocalProductCurrents.formSpan n p := by
  unfold IsPurePP
  exact forall_congr' fun e => forall_congr' fun z => forall_congr' fun _ =>
    (mem_formSpan_iff_pureRealPP (a.coeff e z)).symm

theorem isPurePP_one_iff_isTypeOneOne (a : SmoothRealForm n M 2) :
    IsPurePP (p := 1) a ↔ a.IsTypeOneOne := by
  unfold IsPurePP SmoothRealForm.IsTypeOneOne
  apply forall_congr'
  intro e
  apply forall_congr'
  intro z
  apply forall_congr'
  intro _
  simpa using (isOneOne_iff_pureRealPP (a.coeff e z)).symm

theorem coeff_eq_transition_pullback (a : SmoothRealForm n M (2 * p))
    (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) :
    a.coeff e z = (a.coeff f (chartTransition e f z)).compContinuousLinearMap
      (chartTransitionDerivative e f z) := by
  ext v
  exact a.compatible e f z hz v

theorem isPurePP_iff_preferred (a : SmoothRealForm n M (2 * p)) :
    IsPurePP a ↔ ∀ x : M,
      IsPureRealPP p ((a.coeff (complexChartAt (n := n) x)
        ((complexChartAt (n := n) x).val x)).toAlternatingMap.domDomCongr
          (finCongr (two_mul p))) := by
  constructor
  · intro ha x
    exact ha _ _ ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))
  · intro ha e z hz
    let x := e.val.symm z
    let f := complexChartAt (n := n) x
    have hzf : z ∈ (chartTransition e f).source :=
      ⟨hz, mem_complexChartAt_source x⟩
    rw [coeff_eq_transition_pullback a e f z hzf]
    apply isPureRealPP_compContinuousLinearMap
    · exact fun v => chartTransitionDerivative_complex_smul e f z hzf Complex.I v
    · exact ha x

variable {m : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]

theorem isPurePP_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a : SmoothRealForm n M (2 * p)} (ha : IsPurePP a) :
    IsPurePP (SmoothRealForm.pullback hf a) := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff hf a e d hzd]
  apply isPureRealPP_compContinuousLinearMap
  · exact fun v => coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  · exact ha d _ (coordinateMap_mem_target hzd)

theorem closed_purePP_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a : SmoothRealForm n M (2 * p)} (hclosed : a.IsClosed) (hpure : IsPurePP a) :
    (SmoothRealForm.pullback hf a).IsClosed ∧ IsPurePP (SmoothRealForm.pullback hf a) :=
  ⟨hclosed.pullback hf, isPurePP_pullback hf hpure⟩

theorem geometricallyEq_isPurePP_iff {a b : SmoothRealForm n M (2 * p)}
    (h : a.GeometricallyEq b) : IsPurePP a ↔ IsPurePP b := by
  unfold IsPurePP
  exact forall_congr' fun e => forall_congr' fun z => forall_congr' fun hz => by
    rw [h e hz]

def geometricIsPurePP (a : GeometricRealForm n M (2 * p)) : Prop :=
  Quotient.lift (s := SmoothRealForm.geometricSetoid) IsPurePP
    (fun _ _ h => propext (geometricallyEq_isPurePP_iff h)) a

theorem geometricIsPurePP_ofRepresentative (a : SmoothRealForm n M (2 * p)) :
    geometricIsPurePP (GeometricRealForm.ofRepresentative a) ↔ IsPurePP a :=
  Iff.rfl

def geometricPullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    GeometricRealForm n M (2 * p) → GeometricRealForm m V (2 * p) :=
  Quotient.map (SmoothRealForm.pullback hf) (fun _ _ h => h.pullback hf)

theorem geometricPullback_ofRepresentative {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M (2 * p)) :
    geometricPullback hf (GeometricRealForm.ofRepresentative a) =
      GeometricRealForm.ofRepresentative (SmoothRealForm.pullback hf a) := rfl

theorem geometricIsPurePP_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : GeometricRealForm n M (2 * p)) :
    geometricIsPurePP a → geometricIsPurePP (geometricPullback hf a) := by
  refine Quotient.inductionOn a ?_
  intro b hb
  exact isPurePP_pullback hf hb

end SGPT.Foundations.Analysis.Pending.NaturalSmoothPurePPTransport
