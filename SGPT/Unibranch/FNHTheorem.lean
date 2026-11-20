import SGPT.Unibranch.FNHRunge
import SGPT.Unibranch.FNASuspension
import SGPT.Unibranch.FNATheorem

/-!
# `[FN80]` Theorem 5.3.1 and `thm:FN` from the local parametrization theorem

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Theorem 5.3.1 (`[FN80]`); SGPT `thm:FN` (`appendix_unibranch.tex`).

The only remaining input is the local parametrization theorem for pure-dimensional analytic sets
(`FNL.LocalCoveringCharts`, lane FNL: near each point a pure-dimensional analytic set is, after a
linear change of coordinates, a finite branched covering of a polydisc). From it:

* `localFNExtensionPure_of_charts : FNL.LocalCoveringCharts → FNA.LocalFNExtensionPure`: the
  local `[FN80, Thm. 5.3.1]` for pure-dimensional `X`. Proof: global equations near `a`
  (`FNA.exists_equations_half`), the Runge half `FNH.hartogsRunge_of_charts` on a smaller
  polydisc, and the Siu/Hartogs half `FNS.exists_ambient_psh_of_hartogsRunge`.
* `localFNExtension_of_charts : FNL.LocalCoveringCharts → FNA.LocalFNExtension` (lane FNA's
  suspension `FNA.localFNExtension_of_pure` removes pure dimensionality).
* `fornaessNarasimhan_of_charts`: `thm:FN` on every complex space (`FNA.fornaessNarasimhan`).
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch.FNR SGPT.Unibranch.FNL

variable {n : ℕ}

/-- Pure dimensionality passes to open pieces. -/
theorem isPureDim_inter_open {X O : Set (ComplexModel n)} (hO : IsOpen O) {d : ℕ}
    (h : AnalyticDimensionBasics.IsPureDim (n := n) (M := ComplexModel n) X d) :
    AnalyticDimensionBasics.IsPureDim (n := n) (M := ComplexModel n) (X ∩ O) d := by
  intro y j hy
  have hyO : y ∈ O := hy.2.1.2
  refine h y j (RegularPointDimension.regularAtDim_of_inter_eq hO hyO ?_ hy)
  rw [inter_assoc, inter_self]

/-- **`[FN80]` Theorem 5.3.1, local form, for pure-dimensional `X`**, from the local
parametrization theorem. -/
theorem localFNExtensionPure_of_charts (hC : FNL.LocalCoveringCharts) :
    FNA.LocalFNExtensionPure := by
  intro n X a r d φ hr hXΔ hloc hpure haX hWP
  obtain ⟨V, hV, hCV, m, h, hh, hmemX⟩ := FNA.exists_equations_half hr hloc
  have hr' := FNA.half_radii_pos hr
  set r' : Fin n → ℝ := fun i => r i / 2 with hr'def
  set O : Set (ComplexModel n) := FNA.polydisc a r' with hOdef
  have hO : IsOpen O := FNA.isOpen_polydisc _ _
  have hOV : O ⊆ V := (FNA.polydisc_subset_closedPolydisc a _).trans hCV
  have haO : a ∈ O := FNA.center_mem_polydisc a hr'
  have hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0 := fun z hz => hmemX z (hOV hz)
  have hX'Δ : X ∩ O ⊆ pdisc a r' := inter_subset_right
  have hX'eq : HasLocalEquationsOn (X ∩ O) (pdisc a r') := by
    intro z hz
    refine ⟨O, hO, hz, m, h, fun l => (hh l).mono hOV, fun y hy => ?_⟩
    rw [← hXO y hy]
    exact ⟨fun hy' => hy'.1, fun hy' => ⟨hy', hy⟩⟩
  have hpure' : AnalyticDimensionBasics.IsPureDim (n := n) (M := ComplexModel n)
      ((X ∩ O) ∩ pdisc a r') d :=
    isPureDim_inter_open (isOpen_pdisc a r') (isPureDim_inter_open hO hpure)
  have hcharts : ∀ z ∈ X ∩ O, HasCoveringChartAt (X ∩ O) z univ := fun z hz =>
    hC n d (X ∩ O) (pdisc a r') z (isOpen_pdisc a r') hz hz.2 hX'eq hpure' univ isOpen_univ
      (mem_univ z)
  have hR : FNS.HartogsRunge (X ∩ O) φ :=
    hartogsRunge_of_charts hX'Δ hX'eq hcharts (hWP.mono inter_subset_left)
  exact FNS.exists_ambient_psh_of_hartogsRunge hO (fun l => (hh l).mono hOV) hXO hWP hR ⟨haX, haO⟩

/-- **`[FN80]` Theorem 5.3.1, local form** (every closed analytic subset of a polydisc), from the
local parametrization theorem. -/
theorem localFNExtension_of_charts (hC : FNL.LocalCoveringCharts) : FNA.LocalFNExtension :=
  FNA.localFNExtension_of_pure (localFNExtensionPure_of_charts hC)

open SourceReducedComplexSpace in
/-- **Source `thm:FN` (Fornæss–Narasimhan)** on every complex space, from the local
parametrization theorem `FNL.LocalCoveringCharts`: for `φ : X → [-∞, ∞)` not identically `-∞` on
any irreducible component of `X`, `φ` is plurisubharmonic iff it is upper semicontinuous and its
pull-back by every holomorphic disc `f : Δ → X` with `f^*φ ≢ -∞` is subharmonic. -/
theorem fornaessNarasimhan_of_charts (hC : FNL.LocalCoveringCharts)
    {X : SourceReducedComplexSpace} {φ : X.obj.left → EReal} (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) :
    X.IsPSH φ ↔
      (UpperSemicontinuous φ ∧
        ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
          SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :=
  FNA.fornaessNarasimhan (localFNExtension_of_charts hC) hne_top hcomp

end SGPT.Unibranch.FNH
