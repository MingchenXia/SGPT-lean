import SGPT.PSH.Basic
import SGPT.Foundations.Analysis.Pending.PshRepresentative
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents
import SGPT.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

set_option autoImplicit false

noncomputable section
namespace SGPT.PSH
open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open scoped Distributions Topology

/-- Source local integrability of the original extended values. Almost-everywhere
finiteness is retained, so an identically negative infinite function cannot be
made integrable by taking `toReal`. -/
def SourceLocallyIntegrableOn {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure E) (u : E → EReal) (U : Set E) : Prop :=
  (∀ᵐ x ∂μ.restrict U, u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
    LocallyIntegrableOn (fun x ↦ (u x).toReal) U μ

/-- Positivity of the actual complex-oriented scalar current's
normalized differential, tested on all variable strongly positive compact forms.
In dimension zero the degree-two differential is zero. -/
def HasPositiveSourceDdc : {n : ℕ} → {Ω : Opens (ComplexModel n)} → 𝓓'(Ω, ℝ) → Prop
  | 0, _, _ => True
  | _ + 1, _, T =>
      Pending.LocalProductCurrents.IsPositive
        (Pending.LocalBedfordTaylorProducts.ddc
          (Pending.ScalarLeviPositiveCurrent.scalarTopCurrent T))

/-- The original zero-dimensional degree-two differential really vanishes. -/
theorem sourceDdc_eq_zero_of_zeroDim {Ω : Opens (ComplexModel 0)} (T : 𝓓'(Ω, ℝ)) :
    LocalCurrents.ddC T = 0 := by
  ext v φ
  have hv : v = ![0, 0] := by
    funext i
    exact Subsingleton.elim _ _
  rw [hv, LocalCurrents.ddC_apply]
  simp

/-- The actual full variable-test current and scalar Levi criteria coincide.
Both directions reuse main's complete normalized transpose and gluing proofs. -/
theorem hasPositiveSourceDdc_iff_nonnegativeLevi {n : ℕ}
    {Ω : Opens (ComplexModel n)} (T : 𝓓'(Ω, ℝ)) :
    HasPositiveSourceDdc T ↔ HasNonnegativeDistributionalLevi T := by
  cases n with
  | zero =>
      constructor
      · intro _ v φ _
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        have hD : TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) (Ω := Ω) (F := ℝ) ℝ
            (0 : ComplexModel 0) = 0 := by
          rw [show (0 : ComplexModel 0) = (0 : ℝ) • (0 : ComplexModel 0) by simp,
            TestFunction.lineDerivCLM_smul]
          simp
        simp [distributionalLeviCLM_apply, hD]
      · intro _
        trivial
  | succ m =>
      exact ⟨Pending.FullPositiveScalarCurrentLeviConverse.hasNonnegativeDistributionalLevi_of_isPositive_ddc T,
        Pending.LocalPositiveCurrentGluing.isPositive_ddc_scalarTopCurrent⟩

section GeneralRepresentative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → EReal}

/-- The actual distributional representative recovers the original extended
function almost everywhere and genuinely has a source non-pole point. -/
theorem exists_pshOn_ae_eq_of_nonnegativeLevi
    (hΩ : (Ω : Set E).Nonempty) (hu : SourceLocallyIntegrableOn μ u Ω)
    (hLevi : HasNonnegativeDistributionalLevi
      (regularDistribution μ (fun x ↦ (u x).toReal) hu.2)) :
    ∃ v : E → EReal, PSHOn v Ω ∧ u =ᵐ[μ.restrict Ω] v := by
  obtain ⟨v, hvP, hvf, hvL, hvT⟩ := Pending.exists_pshRepresentative μ hLevi
  have hreal := ae_eq_of_regularDistribution_eq μ hu.2 hvL hvT
  have hae : u =ᵐ[μ.restrict Ω] v := by
    filter_upwards [hu.1, hvf, hreal] with x hux hvx hx
    rw [← EReal.coe_toReal hux.1 hux.2, ← EReal.coe_toReal hvx.1 hvx.2, hx]
  obtain ⟨x, hx, hfx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (Ω.isOpen.measure_ne_zero μ hΩ) hvf
  exact ⟨v, ⟨hvP.discPshOn, x, hx, hfx.2⟩, hae⟩

/-- Almost-everywhere agreement with an original source PSH function produces
both actual local integrability and the genuine positive Levi distribution. -/
theorem sourceLocallyIntegrableOn_nonnegativeLevi_of_ae_eq_pshOn
    (hΩ : IsPreconnected (Ω : Set E)) {v : E → EReal}
    (hv : PSHOn v Ω) (hae : u =ᵐ[μ.restrict Ω] v) :
    ∃ hu : SourceLocallyIntegrableOn μ u Ω,
      HasNonnegativeDistributionalLevi
        (regularDistribution μ (fun x ↦ (u x).toReal) hu.2) := by
  have hvP := hv.disc.plurisubharmonicOn Ω.isOpen
  have hvf := hvP.ae_finite μ hΩ hv.nontrivial
  have hvL := hvP.locallyIntegrableOn_toReal μ hΩ hv.nontrivial
  have hreal : (fun x ↦ (u x).toReal) =ᵐ[μ.restrict Ω] (fun x ↦ (v x).toReal) :=
    hae.mono (fun _ hx ↦ congrArg EReal.toReal hx)
  have huf : ∀ᵐ x ∂μ.restrict Ω, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
    filter_upwards [hvf, hae] with x hx heq
    simpa only [heq] using hx
  have huL := hvL.congr hreal.symm
  refine ⟨⟨huf, huL⟩, ?_⟩
  rw [regularDistribution_congr_ae_on huL hvL hreal]
  exact hvP.hasNonnegativeDistributionalLevi_of_locallyIntegrable hvL hvf

/-- Source uniqueness is pointwise on the original domain, including poles.
The values outside the source domain are irrelevant. -/
theorem PSHOn.eqOn_of_original_ae_eq {v w : E → EReal}
    (hv : PSHOn v Ω) (hw : PSHOn w Ω)
    (huv : u =ᵐ[μ.restrict Ω] v) (huw : u =ᵐ[μ.restrict Ω] w) : EqOn v w Ω :=
  (hv.disc.plurisubharmonicOn Ω.isOpen).eqOn_of_ae_eq
    (hw.disc.plurisubharmonicOn Ω.isOpen) Ω.isOpen μ (huv.symm.trans huw)
end GeneralRepresentative

/-- The original measurable extended function is locally integrable with a
positive normalized full `dd^c` current exactly when it agrees almost everywhere
with a source PSH function. This includes dimension zero. -/
theorem psh_distribution_rigidity {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hΩ : IsConnected (Ω : Set (ComplexModel n)))
    (_hu : Measurable (fun x : Ω ↦ u x)) (_htop : ∀ x ∈ Ω, u x ≠ ⊤) :
    (∃ hL : SourceLocallyIntegrableOn volume u Ω,
      HasPositiveSourceDdc (regularDistribution volume (fun x ↦ (u x).toReal) hL.2)) ↔
      ∃ v : ComplexModel n → EReal, PSHOn v Ω ∧ u =ᵐ[volume.restrict Ω] v := by
  constructor
  · rintro ⟨hL, hpos⟩
    exact exists_pshOn_ae_eq_of_nonnegativeLevi volume hΩ.nonempty hL
      ((hasPositiveSourceDdc_iff_nonnegativeLevi _).mp hpos)
  · rintro ⟨v, hv, hae⟩
    obtain ⟨hL, hLevi⟩ := sourceLocallyIntegrableOn_nonnegativeLevi_of_ae_eq_pshOn
      volume hΩ.isPreconnected hv hae
    exact ⟨hL, (hasPositiveSourceDdc_iff_nonnegativeLevi _).mpr hLevi⟩

end SGPT.PSH
