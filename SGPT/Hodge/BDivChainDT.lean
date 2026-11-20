import SGPT.Hodge.BDivChainDS
import SGPT.Hodge.BDivChainCartier
import SGPT.BDivisor.BlowupModel2Linear
import SGPT.Okounkov.PartialBodyVolume
import SGPT.Okounkov.PartialBodyKahler
import SGPT.Okounkov.ThetaPotentialCurrentCombinations
import SGPT.PSH.SourceIGoodAnalyticCharacterization
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic

/-!
# `𝔻(T)` is nef (`thm:DT`, first assertion)

Source `thm:DT` (chapter *The theory of b-divisors*): for a closed positive `(1,1)`-current `T`
on the connected compact Kähler manifold `X`, `𝔻(T)` is nef; moreover `vol T = vol 𝔻(T)`.

This file proves the **first assertion** (`currentBDivisor_isNef`), following the book:

* Step 1 (reduction to Kähler currents): `𝔻(T + ε_k ω)` nef for `ε_k = 1/(k+1)` implies `𝔻(T)`
  nef (`SGPT.BDivisor.currentBDivisorOn_isNef_of_forall_add`, S44).
* Step 2 (analytic singularities): `𝔻(T)` is a nef Cartier b-divisor
  (`currentBDivisor_isNefCartier_of_hasAnalyticSingularitiesOfType`, `BDivChainCartier`).
* Step 3 (Kähler currents, `currentBDivisorOn_isNef_of_isKahlerCurrentPotential`): take a
  quasi-equisingular approximation `(φ_j)` of `φ` by Kähler currents with analytic singularities
  (`SGPT.Okounkov.PartialBody.exists_isKahlerQEA`, Demailly). It converges to `P_θ[φ]_𝓘` in `d_S`
  (`QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit`), so
  `𝔻(θ_{φ_j}) → 𝔻(θ_{P[φ]_𝓘})` (`prop:dscontbdiv`, `currentBDivisor_converges_of_dS`), and
  `𝔻(θ_{P[φ]_𝓘}) = 𝔻(θ_φ)` since `φ ∼_𝓘 P[φ]_𝓘` (`prop:Iequivchar2`, via
  `currentBDivisorOn_eq_of_iEquivalent`). A limit of nef Cartier b-divisors is nef (`def:nefb`).

In Step 3 the book proves the convergence `𝔻(θ_{φ_j}) → 𝔻(θ_φ)` directly from `thm:Lelongcont`
and the finite-tail estimate; here it is deduced from `prop:dscontbdiv`, whose proof contains
exactly that argument.

The volume identity `vol T = vol 𝔻(T)` is not proved here.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- `𝔻(T)` only depends on the current. -/
theorem currentBDivisorOn_congr (S : ModelSystem (m + 1) X) {T T' : CurX} (h : T = T')
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) (hT' : SGPT.Siu.IsClosedPositiveCurrent T') :
    currentBDivisorOn S T hT = currentBDivisorOn S T' hT' := by
  subst h
  rfl

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **`thm:DT` for Kähler currents (Steps 2 and 3).** If `θ + ddᶜφ` is a Kähler current, then
`𝔻(θ + ddᶜφ)` is nef. -/
theorem currentBDivisorOn_isNef_of_isKahlerCurrentPotential (θ : ClosedRealOneOneForm (m + 1) X)
    {φ : X → EReal} (hφ : IsKahlerCurrentPotential θ φ) (hφθ : IsThetaPshPotential θ.val φ) :
    (currentBDivisorOn (ModelSystem.blowup (m + 1) X) (thetaPotentialCurrent θ.val φ hφθ)
      (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφθ)).IsNef := by
  obtain ⟨U, hU⟩ := SGPT.Okounkov.PartialBody.exists_isKahlerQEA hφ
  obtain ⟨ω₀, ε, hnat⟩ := SGPT.PSH.native_of_sourceQuasiEquisingularApproximation hU.1
  have hbig := SGPT.Okounkov.PartialBody.isBigClass_of_isKahlerCurrentPotential hφ
  have hpos := SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hφ
    hnat.target
  obtain ⟨-, hI, -, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit ω₀ θ hbig
      hnat (fun j => (hU.2 j).1.1) hpos
  -- the approximation and the `𝓘`-envelope as source potentials
  let θa := nativeClosedFormToAtlas θ
  let W : ℕ → SourceThetaPotentialL1 θa := fun j =>
    ⟨U j, (isThetaPSH_iff_nativeThetaPotential θa _).mpr (hU.2 j).1.1⟩
  let v : SourceThetaPotentialL1 θa :=
    ⟨iSingularityEnvelope θ.val φ, (isThetaPSH_iff_nativeThetaPotential θa _).mpr hI⟩
  have hsrc : Tendsto W atTop (@nhds _ (sourceSingularityTopology ω₀ θa hbig) v) :=
    (sourceSingularity_tendsto_iff_native atTop ω₀ θa hbig W v).mpr hlim
  -- `prop:dscontbdiv`: `𝔻(θ_{φ_j}) → 𝔻(θ_{P[φ]_𝓘})`
  have hconv := currentBDivisor_converges_of_dS ω₀ θa hbig atTop W v hsrc
  -- Step 2: each `𝔻(θ_{φ_j})` is nef Cartier
  have hnefj : ∀ j, (currentBDivisor (sourcePotentialCurrent θa (W j))).IsNef := by
    intro j
    obtain ⟨c, 𝔞, htype⟩ := (hU.2 j).1.2
    exact (currentBDivisor_isNefCartier_of_hasAnalyticSingularitiesOfType ω₀ θ (hU.2 j).1.1
      htype).isNef
  have hnefv := WeilBDivisorOn.IsNef.of_converges hnefj hconv
  -- `𝔻(θ_{P[φ]_𝓘}) = 𝔻(θ_φ)`
  have hTv := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hI
  have hTφ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφθ
  have hequiv := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hφθ.1.hasSmoothLocalPotentials φ hφθ
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨thetaPotentialCurrent θ.val (iSingularityEnvelope θ.val φ) hI, hTv.1, hTv.2.1⟩ =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨thetaPotentialCurrent θ.val φ hφθ, hTφ.1, hTφ.2.1⟩ := by
    exact (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hI).trans
      (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ _ hφθ).symm
  have heq := currentBDivisorOn_eq_of_iEquivalent (ModelSystem.blowup (m + 1) X) hTv hTφ hclass
    ⟨θ, θ, _, φ, hI, hφθ, rfl, rfl, hequiv.2⟩ ⟨θ, θ, φ, _, hφθ, hI, rfl, rfl, hequiv.1⟩
  rw [← heq]
  exact hnefv

/-- **`thm:DT`, first assertion: `𝔻(T)` is nef** for every closed positive `(1,1)`-current `T` on
the connected compact Kähler manifold `X` (b-divisors over the book's models). -/
theorem currentBDivisor_isNef (ω : KahlerBackground (m + 1) X)
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X) : (currentBDivisor T).IsNef := by
  obtain ⟨θ, φ, hφ, hTeq⟩ := SGPT.PSH.BookCurrent.exists_presentation T
  have hT := SGPT.Siu.isClosedPositiveCurrent_bookCurrent T
  have hTφ := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hφ
  change (currentBDivisorOn _ T.current hT).IsNef
  rw [currentBDivisorOn_congr _ hTeq hT hTφ]
  have h0 : IsThetaPshPotential ω.form.val (fun _ : X => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr ω.isSemipositive,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  apply currentBDivisorOn_isNef_of_forall_add _ hTφ ω.form h0
  intro k hk
  have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨hsm, hsmeq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul h0 hc.le
  obtain ⟨hadd, haddeq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hφ hsm
  have hcur : thetaPotentialCurrent θ.val φ hφ +
      (1 / ((k : ℝ) + 1)) • thetaPotentialCurrent ω.form.val (fun _ => 0) h0 =
      thetaPotentialCurrent (θ + (1 / ((k : ℝ) + 1)) • ω.form).val
        (fun x => φ x + ((1 / ((k : ℝ) + 1) : ℝ) : EReal) * 0) hadd := by
    rw [haddeq, hsmeq]
  rw [currentBDivisorOn_congr _ hcur hk
    (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hadd)]
  have hfun : (fun x => φ x + ((1 / ((k : ℝ) + 1) : ℝ) : EReal) * 0) = φ := by
    funext x
    rw [mul_zero, add_zero]
  have hK : IsKahlerCurrentPotential (θ + (1 / ((k : ℝ) + 1)) • ω.form)
      (fun x => φ x + ((1 / ((k : ℝ) + 1) : ℝ) : EReal) * 0) := by
    refine ⟨KahlerBackground.smul hc ω, ?_⟩
    rw [KahlerBackground.smul_form, add_sub_cancel_right, hfun]
    exact hφ
  exact currentBDivisorOn_isNef_of_isKahlerCurrentPotential _ hK hadd

end SGPT.Hodge.BDivChain
