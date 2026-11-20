import SGPT.Checks.Comparison.BJWholePointwiseMax
import SGPT.Checks.Comparison.BJRelAmpleAppSeq
import SGPT.Checks.Comparison.BJAsmPLTest
import SGPT.Checks.Comparison.BJAsmUnique
import SGPT.Checks.Comparison.BJExistNet
import SGPT.Checks.Comparison.PhiPshMain
import SGPT.Checks.Comparison.DimZeroPhiPsh
import SGPT.Checks.Comparison.DimZeroComparison
import SGPT.Checks.Comparison.DimZeroDXZ
import SGPT.NAPotential.DimZeroPsiPhi
import SGPT.NAPotential.DimZeroAnalytification
import SGPT.NAPotential.TowerAlgReflect
import SGPT.NAPotential.TowerAlgRealize
import SGPT.NAPotential.AlgPrimesHypersurface
import SGPT.NAPotential.AlgPrimes2Divisor
import SGPT.NAPotential.AlgPrimes3GraphMap
import SGPT.NAPotential.AlgPrimes3Algebra
import SGPT.Checks.Comparison.RIsoBRepresentative
import SGPT.Checks.Comparison.GfImLimit
import SGPT.Checks.Comparison.DXZSurjLimit
import SGPT.NAPotential.RIsoBTraceRepresentative
import SGPT.NAPotential.RIsoBRepresentativeOps

/-!
# SGPT.Checks.Comparison

Downstream library of the SGPT book formalization for the environments of `chapter_NApotential`
that rest on the Boucksom–Jonsson theory of psh metrics on Berkovich analytifications
(`subsec:BJ_recap`, `subsec:analytic_alg`, `subsec:NA_comparison`).

That theory is formalized in `SGPT.Foundations.Envelope` (`SGPT.Foundations.Envelope.Source.PSH` and the
comparison theorem behind it). `SGPT.Foundations.Envelope` depends on `the book formalization`, so SGPT cannot
import it; this library imports both and bridges SGPT's Berkovich points to SGPT.Foundations.Envelope's
analytification points. Declarations live in the namespace `SGPT.NAPotential.BJ`; the ledger entries
they prove carry `"library": "SGPT.Checks.Comparison"` in `../the book formalization/coverage.json` and are
kernel-checked by `audit/Coverage.lean`.
-/
