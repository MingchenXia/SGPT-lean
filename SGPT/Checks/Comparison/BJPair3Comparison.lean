import SGPT.Checks.Comparison.BJPair3DivOriginalDivisorialComparison
import SGPT.Checks.Comparison.BJPair2HodgePair

/-!
# `thm:pshdetbydiv` in SGPT.Checks.Comparison, and `thm:BJappseq` from the charging of divisorial points


Source: [BJ22] (`references/bj22-trivval`), Theorem 4.22 (`thm:pshdetbydiv`) and Corollary 12.18
(`thm:BJappseq` of `chapter_NApotential.tex`). Blueprint: `claude-bj-pair.tex`.

The comparison theorem `thm:pshdetbydiv` was proved in the library `SGPT.Checks.Literature`
(`SGPT.NAPotential.BJ.Divisorial.original_le_of_sourceDivisorial_le`, from SGPT.Foundations.Envelope's
`IsPSH.le_of_forall_isDivisorial_le` on a native projective model and the identification of its
divisorial points with the source's `sourceDivisorialSet`). That library pins another revision of
SGPT.Foundations.Envelope and cannot be imported here, so its proof chain is ported verbatim as the files
`BJPair3Div*` (namespace `SGPT.NAPotential.BJ.Pair3Div`; only the imports and the namespace of the
de Jong alterations library differ).

* `divisorialComparison`: `AppSeq.DivisorialComparison p` holds;
* `bjAppSeq_of_charging`: `thm:BJappseq` for `X` of dimension `n ≥ 1` follows from the charging of
  the divisorial points by the energy pairings of ample classes (step R8) alone.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJEnergy

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **`thm:pshdetbydiv`** ([BJ22, Theorem 4.22]): a psh metric lies below an upper semicontinuous
function as soon as it does on the divisorial set and at `v_triv`. -/
theorem divisorialComparison : AppSeq.DivisorialComparison p :=
  fun _ _ _ hφ hψ hle => Pair3Div.original_le_of_sourceDivisorial_le p hφ hψ hle

include p in
omit [IsIntegral X] in
/-- `X` is quasi-compact, being proper over a point. -/
theorem compactSpace_of_projective : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace p

include p in
omit [IsIntegral X] in
/-- `X` is separated, being projective over a point. -/
theorem isSeparated_of_projective : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from p]; infer_instance⟩

/-- **`thm:BJappseq` from the charging of divisorial points** ([BJ22, Corollary 12.18]) for an
integral projective `X` of dimension `n ≥ 1` (`X` is then quasi-compact and separated:
`compactSpace_of_projective`, `isSeparated_of_projective`): the comparison theorem
(`divisorialComparison`) and the energy pairings of ample classes with all their axioms
(`energyPairingOfAmple`) are proved; the only hypothesis is step R8, that every divisorial point is
charged by these pairings. -/
theorem bjAppSeq_of_charging (n : ℕ) (hXn : topologicalKrullDim X = n) (hn : 0 < n)
    (hE : ∀ (ω : NativePicard.RationalPicardSpace X)
      (hω : NativePicard.numericalClass p ω ∈
        SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p),
        ∀ v ∈ divisorialSet p,
          (haveI := compactSpace_of_projective p; haveI := isSeparated_of_projective p
            energyPairingOfAmple n hXn.le hXn hn ω hω).IsCharged v) :
    AppSeq.BJAppSeqStatement.{u} p :=
  haveI := compactSpace_of_projective p
  haveI := isSeparated_of_projective p
  bjAppSeq_of_charged (divisorialComparison p) n hXn.le hXn hn hE

end SGPT.NAPotential.BJ
