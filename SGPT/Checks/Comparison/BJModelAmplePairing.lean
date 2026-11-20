import SGPT.Checks.Comparison.BJEnergySelection
import SGPT.Checks.Comparison.BJModelTruncation

/-!
# Energy pairings in ample classes from Fubini–Study positivity

Source: `chapter_NApotential.tex`, `thm:BJappseq`; Boucksom–Jonsson ([BJ22],
`references/bj22-trivval`), Example `exam:FSpsh` (`𝓗(L) ⊆ PL ∩ PSH(L)`) and Proposition
`prop:FSideal`. Lane BJ-MODEL, step R9 of `claude-bj-energy:plan`; blueprint `claude-bj-model.tex`.

`SGPT.NAPotential.BJ.AppSeq.AmpleEnergyPairing` asks that the `ω`-psh PL functions of the energy
pairing contain the truncations `max(φ, c)` of the rational GF functions `φ ∈ 𝓗^gf_ℚ(ω)`. By
`isFlagFS_truncation` these truncations are Fubini–Study functions of `ω` in the flag-ideal form
of [BJ22, `prop:FSideal`] (`IsFlagFS`). Hence it suffices that the Fubini–Study functions of `ω`
are `ω`-psh, which is [BJ22, Example `exam:FSpsh`] (a globally generated test configuration is
relatively nef). This file records the reduction:

* `ampleEnergyPairingOfFlagFS`: an energy pairing on `X^An` with trivial point `v_triv` whose
  `ω`-psh functions contain `𝓗(ω)` and whose divisorial points are charged is an
  `AmpleEnergyPairing`;
* `bjAppSeq_of_flagFS_pairings`: `thm:BJappseq` follows from `thm:pshdetbydiv`
  (`DivisorialComparison`) and the existence, in every ample rational class `ω`, of such an energy
  pairing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.NAPotential.BJModel

open AlgebraicGeometry CategoryTheory
open SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.AppSeq SGPT.NAPotential.BJEnergy

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **An energy pairing in an ample class from Fubini–Study positivity.** Let `B` be an energy
pairing on `X^An` (in the class `ω`) with trivial point `v_triv`, such that every Fubini–Study
function of `ω` ([BJ22, `prop:FSideal`]) is an `ω`-psh PL function of `B` ([BJ22,
`exam:FSpsh`]) and every divisorial point is charged. Then `B` is an energy pairing in the ample
class `ω` in the sense of `AmpleEnergyPairing`. -/
def ampleEnergyPairingOfFlagFS {ω : RationalPicardSpace X}
    (hω : NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p) {n : ℕ}
    (B : EnergyPairing (BerkovichPoint p) n) (htriv : B.triv = BerkovichPoint.trivial p)
    (hfs : ∀ φ : BerkovichPoint p → ℝ, IsFlagFS p ω φ → ∃ f ∈ B.psh, (f : BerkovichPoint p → ℝ) = φ)
    (hcharged : ∀ v ∈ divisorialSet p, B.IsCharged v) : AmpleEnergyPairing p ω where
  dim := n
  pairing := B
  triv_eq := htriv
  truncation E hE c := by
    obtain ⟨f, hf, hfφ⟩ := hfs _ (isFlagFS_truncation p hω E hE c)
    exact ⟨f, hf, fun v => congrFun hfφ v⟩
  charged := hcharged

/-- **`thm:BJappseq` from Fubini–Study positivity of energy pairings.** `thm:pshdetbydiv`
(`DivisorialComparison`) and, for every rational class `ω` with ample numerical class, an energy
pairing on `X^An` with trivial point `v_triv`, containing the Fubini–Study functions of `ω` among
its `ω`-psh functions and charging every divisorial point, imply `thm:BJappseq`. -/
theorem bjAppSeq_of_flagFS_pairings (hcomp : DivisorialComparison p)
    (hE : ∀ ω : RationalPicardSpace X,
      NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p →
        ∃ (n : ℕ) (B : EnergyPairing (BerkovichPoint p) n), B.triv = BerkovichPoint.trivial p ∧
          (∀ φ : BerkovichPoint p → ℝ, IsFlagFS p ω φ →
            ∃ f ∈ B.psh, (f : BerkovichPoint p → ℝ) = φ) ∧
          ∀ v ∈ divisorialSet p, B.IsCharged v) :
    BJAppSeqStatement.{u} p := by
  refine bjAppSeq_of_ampleEnergyPairing p hcomp fun ω hω => ?_
  obtain ⟨n, B, htriv, hfs, hcharged⟩ := hE ω hω
  exact ⟨ampleEnergyPairingOfFlagFS p hω B htriv hfs hcharged⟩

end SGPT.NAPotential.BJModel
