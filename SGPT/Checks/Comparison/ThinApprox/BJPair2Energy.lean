import SGPT.Checks.Comparison.ThinApprox.BJPair2Triv
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalAmpleCone

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# The energy pairing of an ample class with `PairTriv` and `(ω^n) > 0` discharged
(lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), §3.2. Towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

For `X` integral projective of dimension `n ≥ 1` and a rational class `ω` with ample numerical
class, `ω` is a nonnegative multiple of an ample (hence nef) line bundle
(`omega_mem_relNefCone`), `(ω^n) > 0` (`volQ_pos`) and `equ:mixedMA0` holds (`pairTriv`), so the
energy pairing of lane BJ-PAIR only depends on the two hypotheses `PairConst`
(`prop:intpairing` (i)) and `PairHodge` (`lem:Hodge`):

* `energyPairingOfConstHodge`: the `EnergyPairing` of `ω`;
* `bjAppSeq_of_constHodge`: `thm:BJappseq` from `thm:pshdetbydiv`, `PairConst`, `PairHodge` and the
  charging of divisorial points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJEnergy SGPT.NAPotential.BJ.NativePicard

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable [CompactSpace X] [X.IsSeparated]

omit [IsIntegral X] [X.IsSeparated] in
/-- A line bundle whose numerical class is nef is nef on every closed integral curve. -/
theorem isNefOn_univ_of_mem_nefCone (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h : SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass p L hL ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.nefCone p) : IsNefOn p L Set.univ := by
  intro C _
  have := (SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass_mem_nefCone_iff p L hL).mp h C
  exact_mod_cast this

omit [IsIntegral X] [X.IsSeparated] in
/-- **A rational class with ample numerical class is a nonnegative multiple of a nef line
bundle**, hence lies in `relNefCone p univ`. -/
theorem omega_mem_relNefCone (ω : RationalPicardSpace X)
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p) :
    ω ∈ relNefCone p Set.univ := by
  obtain ⟨L, hL, m, hm, rfl, hnum⟩ := picQ_atlas_presentation (p := p) ω
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hclass : SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass p L hL ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p := by
    have h2 := (SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p).smul_mem hmR hω
    rw [hnum, ← Rat.cast_smul_eq_qsmul ℝ, smul_smul] at h2
    have h3 : (m : ℝ) * (((1 / (m : ℚ)) : ℚ) : ℝ) = 1 := by
      push_cast
      field_simp
    rwa [h3, one_smul] at h2
  have hnef := isNefOn_univ_of_mem_nefCone L hL
    (SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone_le_nefCone p hclass)
  exact Submodule.smul_mem _ (⟨1 / (m : ℚ), by positivity⟩ : {r : ℚ // 0 ≤ r})
    (picQ_mem_relNefCone p ⟨L, hL⟩ hnef)

/-- **The energy pairing of an ample rational class** ([BJ22, §3.2]) for `dim X = n ≥ 1`, from the
two remaining axioms `PairConst` and `PairHodge`; `(ω^n) > 0` and `PairTriv` are proved. -/
def energyPairingOfConstHodge (n : ℕ) (hX : topologicalKrullDim X ≤ n)
    (hXn : topologicalKrullDim X = n) (hn : 0 < n) (ω : RationalPicardSpace X)
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p)
    (hconst : PairConst p n hX ω) (hhodge : PairHodge p n hX ω) :
    EnergyPairing (BerkovichPoint p) n :=
  energyPairingOfAxioms n hX ω (omega_mem_relNefCone ω hω) (volQ_pos n hX hXn ω hω) hconst
    (pairTriv n hX ω hXn hn) hhodge

/-- **`thm:BJappseq` from `PairConst`, `PairHodge` and the charging of divisorial points**, for `X`
of dimension `n ≥ 1`: everything else about the energy pairing (well-definedness,
multilinearity, `prop:intpairing` (iii), `equ:mixedMA0`, `lem:enmono`, `(ω^n) > 0`, the `ω`-psh
functions and the Fubini–Study functions among them) is proved. -/
theorem bjAppSeq_of_constHodge
    (hcomp : SGPT.NAPotential.ThinApprox.BJ.AppSeq.DivisorialComparison p) (n : ℕ)
    (hX : topologicalKrullDim X ≤ n) (hXn : topologicalKrullDim X = n) (hn : 0 < n)
    (hE : ∀ (ω : RationalPicardSpace X)
      (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈
        SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p),
        ∃ (hconst : PairConst p n hX ω) (hhodge : PairHodge p n hX ω),
          ∀ v ∈ divisorialSet p,
            (energyPairingOfConstHodge n hX hXn hn ω hω hconst hhodge).IsCharged v) :
    SGPT.NAPotential.ThinApprox.BJ.AppSeq.BJAppSeqStatement.{u} p := by
  refine bjAppSeq_of_flagFS_pairings p hcomp fun ω hω => ?_
  obtain ⟨hconst, hhodge, hcharged⟩ := hE ω hω
  exact ⟨n, energyPairingOfConstHodge n hX hXn hn ω hω hconst hhodge, rfl,
    energyPairingOfAxioms_flagFS n hX (omega_mem_relNefCone ω hω) (volQ_pos n hX hXn ω hω)
      hconst (pairTriv n hX ω hXn hn) hhodge, hcharged⟩

end SGPT.NAPotential.ThinApprox.BJ
