import SGPT.Okounkov.TranscendentalLiftingApprox
import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.Okounkov.TranscendentalDensityTheorem
import SGPT.Okounkov.TranscendentalBodyBound
import SGPT.Okounkov.ModificationNativeConvergence
import SGPT.Okounkov.TranscendentalRelGen

/-!
# Lifting invariance of transcendental Okounkov bodies

Source: `thm:Okounkovtranmain` item 3 (book chapter *The theory of Okounkov bodies*), blueprint
node `tok:lifting-invariance` (chapter `claude-okounkov-transcendental`), i.e. DRWNXZ
(Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*) Proposition 4.4
("In particular").

For a proper bimeromorphic holomorphic map `π : W → X` from a compact Kähler manifold carrying
the lifting `W•` of the flag `Y•` (`IsFlagLifting F W π`, correction matrix `g`) and a
representative `θ` of a big class `ξ`, `Δ_{W•}(π^*ξ) = Δ_{Y•}(ξ) g`.

## Status: conditional on one external input

* `liftingInvarianceStatement_of_pushforwardAnalytic`: `LiftingInvarianceStatement F` from
  `TranscendentalRelGen.PushforwardAnalyticStatement` (DRWNXZ Lemma 2.8, pushforwards of
  `β + c[D]` have analytic singularities).
* `liftingInvarianceStatement_of_l2Generation` (blueprint name: `tradOkounkovBody_pullback_eq`):
  `LiftingInvarianceStatement F` from `TranscendentalRelGen.WeaklyPseudoconvexL2GenerationStatement`
  (Nadel/Hörmander `L²` generation on weakly pseudoconvex open subsets of compact Kähler manifolds,
  Demailly 2015 Corollary 5.3), through RELGEN's
  `pushforwardAnalyticStatement_of_l2Generation`. **This `L²` statement is not proved in the
  project; item 3 is therefore conditional on it**, and on nothing else: every other ingredient
  (density of gentle Kähler currents, Skoda, log resolutions, flag liftings, correction matrices,
  Blanchard/exceptional Kähler forms, the Kähler half of `lma:logsingrem`, descent of potentials,
  bigness of pullbacks) is proved.

## The proof (blueprint `tok:lifting-invariance`)

`π^*ξ` is big (`isBigClass_modification_pullback`, `claude-env:cones-modif`), so by
`tok:density` both bodies are closures of valuations of currents with analytic singularities
(`tradOkounkovBody_eq_closure_analyticCurrents`) or of gentle Kähler currents.

* `⊇` (unconditional, `image_subset_tradOkounkovBody_pullback`): for `T ∈ 𝒢(X, ξ)`,
  `π^*T ∈ 𝒜(W, π^*ξ)` and `ν_{W•}(π^*T) = ν_{Y•}(T) g`; right multiplication by `g` is continuous.
* `⊆`: for `T ∈ Ω(W, π^*ξ)`, `tok:approx-pushforward` gives `T_k ∈ 𝒜(X, ξ)` with
  `ν_{Y•}(T_k) g → ν_{W•}(T)`; `Δ_{Y•}(ξ) g` is compact, hence closed.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Topology Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalRelGen
open SGPT.Okounkov.TranscendentalDensity

variable {m : ℕ}

/-- **Pullbacks of big classes are big** (`claude-env:cones-modif`, book `prop:cones_modif2`), in
the form of `SGPT.PSH.BookCurrent.IsBig` and for a flag lifting. -/
theorem isBig_pullback {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1.1 θ)) := by
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  let : MeasurableSpace W.carrier := borel W.carrier
  have : BorelSpace W.carrier := ⟨rfl⟩
  rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass] at hbig ⊢
  exact isBigClass_modification_pullback hπ.1 F.omega W.omega θ hbig

/-- **Lifting invariance, inclusion `Δ_{Y•}(ξ) g ⊆ Δ_{W•}(π^*ξ)`** (unconditional). -/
theorem image_subset_tradOkounkovBody_pullback {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (fun x => x ᵥ* correctionMatrixReal hπ) '' tradOkounkovBody F θ ⊆
      tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) := by
  have hcont : Continuous fun x : Fin (m + 1) → ℝ => x ᵥ* correctionMatrixReal hπ :=
    continuous_id.matrix_vecMul continuous_const
  rw [tradOkounkovBody_eq_closure_image θ]
  refine (image_closure_subset_closure_image hcont).trans
    (closure_minimal ?_ (isClosed_tradOkounkovBody _))
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  rw [tradOkounkovBody_eq_closure_analyticCurrents (isBig_pullback hπ hbig)]
  refine subset_closure ⟨fun y => φ (π y),
    comp_mem_analyticCurrents hπ.1 (gentleCurrents_subset_analyticCurrents θ hφ), ?_⟩
  exact flagValuation_comp_eq_vecMul hπ hφ.1

/-- **Lifting invariance, inclusion `Δ_{W•}(π^*ξ) ⊆ Δ_{Y•}(ξ) g`**, conditional on
`PushforwardAnalyticStatement` (DRWNXZ Lemma 2.8). -/
theorem tradOkounkovBody_pullback_subset_image (hP : PushforwardAnalyticStatement.{u})
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) ⊆
      (fun x => x ᵥ* correctionMatrixReal hπ) '' tradOkounkovBody F θ := by
  have hcont : Continuous fun x : Fin (m + 1) → ℝ => x ᵥ* correctionMatrixReal hπ :=
    continuous_id.matrix_vecMul continuous_const
  have hclosed : IsClosed ((fun x => x ᵥ* correctionMatrixReal hπ) '' tradOkounkovBody F θ) :=
    ((TranscendentalBody.isCompact_tradOkounkovBody θ).image hcont).isClosed
  rw [tradOkounkovBody_eq_closure_gentleKahlerCurrents (isBig_pullback hπ hbig)]
  refine closure_minimal ?_ hclosed
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨w, φ, hφA, hφν⟩ := exists_analytic_approximation_of_gentleKahler hP hπ hψ
  have hmem : ∀ k, flagValuation F (φ k) ᵥ* correctionMatrixReal hπ ∈
      (fun x => x ᵥ* correctionMatrixReal hπ) '' tradOkounkovBody F θ := fun k =>
    ⟨flagValuation F (φ k), by
      rw [tradOkounkovBody_eq_closure_analyticCurrents hbig]
      exact subset_closure ⟨φ k, hφA k, rfl⟩, rfl⟩
  have hlim : Tendsto (fun k : ℕ => flagValuation F (φ k) ᵥ* correctionMatrixReal hπ) atTop
      (𝓝 (flagValuation W ψ)) := by
    simp only [hφν]
    have h0 : Tendsto (fun k : ℕ => ((1 : ℝ) / ((k : ℝ) + 1)) • w) atTop (𝓝 ((0 : ℝ) • w)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.smul_const w
    rw [zero_smul] at h0
    simpa using tendsto_const_nhds.add h0
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)

/-- **Lifting invariance** (`thm:Okounkovtranmain` item 3), conditional on
`PushforwardAnalyticStatement` (DRWNXZ Lemma 2.8): `Δ_{W•}(π^*ξ) = Δ_{Y•}(ξ) g`. -/
theorem liftingInvarianceStatement_of_pushforwardAnalytic (hP : PushforwardAnalyticStatement.{u})
    (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.LiftingInvarianceStatement F := by
  intro W π hπ θ hbig
  exact Subset.antisymm (tradOkounkovBody_pullback_subset_image hP hπ hbig)
    (image_subset_tradOkounkovBody_pullback hπ hbig)

/-- **Lifting invariance** (`thm:Okounkovtranmain` item 3, blueprint `tok:lifting-invariance`),
**conditional on the `L²` generation theorem** `WeaklyPseudoconvexL2GenerationStatement`
(Demailly 2015, Corollary 5.3; RELGEN's `relgen:l2-generation`), the only unproved input. -/
theorem liftingInvarianceStatement_of_l2Generation
    (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u}) (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.LiftingInvarianceStatement F :=
  liftingInvarianceStatement_of_pushforwardAnalytic
    (pushforwardAnalyticStatement_of_l2Generation hL2) F

/-- Blueprint name of `liftingInvarianceStatement_of_l2Generation`: `Δ_{W•}(π^*ξ) = Δ_{Y•}(ξ) g`
for every lifting, conditional on `WeaklyPseudoconvexL2GenerationStatement`. -/
theorem tradOkounkovBody_pullback_eq (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u})
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' tradOkounkovBody F θ :=
  liftingInvarianceStatement_of_l2Generation hL2 F W π hπ θ hbig

end SGPT.Okounkov.TranscendentalLifting
