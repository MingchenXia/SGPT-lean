import SGPT.Okounkov.TranscendentalPartialVolume
import Mathlib.Analysis.Convex.Measure

/-!
# Exhaustion of the Okounkov body by partial bodies

Source: blueprint node `tok:partial-exhaustion` (chapter `claude-okounkov-transcendental`), i.e.
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ),
Proposition 5.4, items (2) and (3) (item (1) is not needed).

For a big class `ξ = {θ}` there is a sequence `R_i ∈ Ω(ξ)`, increasing for the singularity order
(`R_i ⪯ R_{i+1}`), with

* `∫_X ⟨R_i^n⟩ → vol(ξ)`,
* `Δ(ξ) = closure ⋃_i Δ(ξ; R_i)` (and the partial bodies increase),
* `vol Δ(ξ; R_i) → vol Δ(ξ)` (Lebesgue measure).

Proof (`exists_partialOkounkovBody_exhaustion`): `ν(Ω(ξ)) ⊆ ℚⁿ` is countable
(`tok:valuation-analytic`), enumerate it as `ν(T_i)`; choose `G_i ∈ Ω(ξ)` with masses tending to
`vol(ξ)` (`tok:volume-sup`) and inductively `R_i ∈ Ω(ξ)` less singular than `R_{i-1}`, `T_i` and
`G_i` (`tok:sing-decrease` (b)). Then `ν(T_i) ∈ Δ(ξ; R_i)`, the union is dense in
`Δ(ξ) = closure ν(Ω(ξ))` (`tok:density`), the masses are squeezed between `∫⟨G_i^n⟩` and
`vol(ξ)` (monotonicity of non-pluripolar masses), and the union `U` of the increasing convex
bodies is convex with `closure U = Δ(ξ)`; the frontier of a convex set is Lebesgue null, so
`vol Δ(ξ; R_i) ↑ vol U = vol Δ(ξ)`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore
open SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `ν(Ω(ξ)) ⊆ ℚⁿ` is countable (`tok:valuation-analytic`). -/
theorem countable_image_gentleKahlerCurrents (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    (flagValuation F '' gentleKahlerCurrents θ).Countable := by
  have hsub : flagValuation F '' gentleKahlerCurrents θ ⊆
      range (fun q : Fin (m + 1) → ℚ => fun i => (q i : ℝ)) := by
    rintro _ ⟨φ, hφ, rfl⟩
    have h := TranscendentalCore.flagValuation_rational_of_analytic (m + 1) F θ φ
      (gentleCurrents_subset_analyticCurrents θ hφ.1)
    choose q _ hq using h
    exact ⟨q, funext fun i => (hq i).symm⟩
  exact (countable_range _).mono hsub

/-- The Lebesgue measure of the closure of a convex subset of `ℝⁿ` is its measure. -/
theorem volume_closure_of_convex {k : ℕ} {s : Set (Fin k → ℝ)} (hs : Convex ℝ s) :
    volume (closure s) = volume s :=
  measure_closure_of_null_frontier (hs.addHaar_frontier volume)

/-- **Volumes of an increasing exhaustion** (DRWNXZ Proposition 5.4 (3), measure-theoretic part):
for an increasing sequence of convex sets `B_i ⊆ ℝⁿ` with `closure ⋃ B_i = Δ`,
`vol B_i → vol Δ`. -/
theorem tendsto_volume_of_monotone_convex {k : ℕ} {B : ℕ → Set (Fin k → ℝ)} (hB : Monotone B)
    (hconv : ∀ i, Convex ℝ (B i)) {Δ : Set (Fin k → ℝ)} (hΔ : Δ = closure (⋃ i, B i)) :
    Tendsto (fun i => volume (B i)) atTop (𝓝 (volume Δ)) := by
  have hU : Convex ℝ (⋃ i, B i) := Directed.convex_iUnion hB.directed_le (fun i => hconv i)
  rw [hΔ, volume_closure_of_convex hU]
  exact tendsto_measure_iUnion_atTop hB

/-- **`tok:partial-exhaustion`** (DRWNXZ Proposition 5.4 (2), (3)): for a big class `ξ = {θ}`
there are `R_i ∈ Ω(ξ)` with `R_i ⪯ R_{i+1}`, `∫_X ⟨R_i^n⟩ → vol(ξ)`, increasing partial bodies
with `Δ(ξ) = closure ⋃_i Δ(ξ; R_i)`, and `vol Δ(ξ; R_i) → vol Δ(ξ)`. -/
theorem exists_partialOkounkovBody_exhaustion (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    ∃ (R : ℕ → F.carrier → EReal) (hR : ∀ i, R i ∈ gentleKahlerCurrents θ),
      (∀ i, SingularityLE (R i) (R (i + 1))) ∧
      Tendsto (fun i => diagonalPotentialMass θ (R i)
          (isThetaPshPotential_of_mem_gentleCurrents (hR i).1)) atTop
        (𝓝 (sourceClassVolume (RealBottChern.ofRepresentative θ))) ∧
      Monotone (fun i => partialOkounkovBody F θ (R i)) ∧
      tradOkounkovBody F θ = closure (⋃ i, partialOkounkovBody F θ (R i)) ∧
      Tendsto (fun i => volume (partialOkounkovBody F θ (R i))) atTop
        (𝓝 (volume (tradOkounkovBody F θ))) := by
  classical
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  set Ωs := {φ : F.carrier → EReal // φ ∈ gentleKahlerCurrents θ}
  have hne : (gentleKahlerCurrents θ).Nonempty :=
    TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  -- enumerate `ν(Ω(ξ))`
  obtain ⟨f, hf⟩ := (countable_image_gentleKahlerCurrents (F := F) θ).exists_eq_range
    (hne.image _)
  have hT : ∀ i, ∃ T : Ωs, flagValuation F T.1 = f i := by
    intro i
    have hi : f i ∈ flagValuation F '' gentleKahlerCurrents θ := by rw [hf]; exact ⟨i, rfl⟩
    obtain ⟨φ, hφ, h⟩ := hi
    exact ⟨⟨φ, hφ⟩, h⟩
  choose T hTf using hT
  -- masses tending to the volume
  set g : Ωs → ℝ≥0∞ := fun φ =>
    diagonalPotentialMass θ φ.1 (isThetaPshPotential_of_mem_gentleCurrents φ.2.1) with hg
  have hvol : sourceClassVolume (RealBottChern.ofRepresentative θ) = sSup (range g) := by
    rw [sourceClassVolume_eq_iSup_gentleKahler F.omega θ hne, sSup_range, iSup_subtype']
  obtain ⟨u, -, hu, hug⟩ := exists_seq_tendsto_sSup (S := range g)
    (by obtain ⟨φ, hφ⟩ := hne; exact ⟨_, ⟨φ, hφ⟩, rfl⟩) (OrderTop.bddAbove _)
  choose G hG using hug
  -- the joins
  have hJ : ∀ a b : Ωs, ∃ c : Ωs, SingularityLE a.1 c.1 ∧ SingularityLE b.1 c.1 := by
    intro a b
    obtain ⟨ψ, hψ, h1, h2⟩ :=
      TranscendentalBody.exists_mem_gentleKahlerCurrents_singularityLE a.2.2 b.2.2
    exact ⟨⟨ψ, hψ⟩, h1, h2⟩
  choose J hJ1 hJ2 using hJ
  let Rs : ℕ → Ωs := fun i =>
    Nat.rec (motive := fun _ => Ωs) (J (T 0) (G 0)) (fun i r => J r (J (T (i + 1)) (G (i + 1)))) i
  have hRs0 : Rs 0 = J (T 0) (G 0) := rfl
  have hRsS : ∀ i, Rs (i + 1) = J (Rs i) (J (T (i + 1)) (G (i + 1))) := fun _ => rfl
  have hTR : ∀ i, SingularityLE (T i).1 (Rs i).1 := by
    intro i
    cases i with
    | zero => rw [hRs0]; exact hJ1 _ _
    | succ i => rw [hRsS]; exact singularityLE_trans (hJ1 _ _) (hJ2 _ _)
  have hGR : ∀ i, SingularityLE (G i).1 (Rs i).1 := by
    intro i
    cases i with
    | zero => rw [hRs0]; exact hJ2 _ _
    | succ i => rw [hRsS]; exact singularityLE_trans (hJ2 _ _) (hJ2 _ _)
  have hRR : ∀ i, SingularityLE (Rs i).1 (Rs (i + 1)).1 := fun i => by rw [hRsS]; exact hJ1 _ _
  have hmono : Monotone (fun i => partialOkounkovBody F θ (Rs i).1) :=
    monotone_nat_of_le_succ fun i => partialOkounkovBody_mono θ (hRR i)
  have hcover : tradOkounkovBody F θ = closure (⋃ i, partialOkounkovBody F θ (Rs i).1) := by
    refine le_antisymm ?_ (closure_minimal
      (iUnion_subset fun i => partialOkounkovBody_subset_tradOkounkovBody θ _)
      (isClosed_tradOkounkovBody θ))
    rw [TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents hbig, hf]
    refine closure_mono ?_
    rintro _ ⟨i, rfl⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [← hTf i]
    exact flagValuation_mem_partialOkounkovBody ⟨(T i).2, hTR i⟩
  refine ⟨fun i => (Rs i).1, fun i => (Rs i).2, hRR, ?_, hmono, hcover, ?_⟩
  · -- the masses
    rw [hvol]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := u) (h := fun _ => sSup (range g))
      hu tendsto_const_nhds (fun i => ?_) (fun i => ?_)
    · rw [← hG i]
      exact diagonalPotentialMass_mono_of_kahler F.omega _ _ (hGR i)
    · exact le_sSup ⟨Rs i, rfl⟩
  · exact tendsto_volume_of_monotone_convex hmono
      (fun i => convex_partialOkounkovBody θ _) hcover

end SGPT.Okounkov.TranscendentalPartial
