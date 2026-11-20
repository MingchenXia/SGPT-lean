import SGPT.Unibranch.FNHProduct
import SGPT.Unibranch.FNSLocal

/-!
# The Hartogs domain `{φ(z) + log |w| < 0}` is Runge in `X × ℂ`

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Theorem 5.3.1, first half of the proof (`[FN80]`), used for SGPT `thm:FN`
(2) ⇒ (1) (`appendix_unibranch.tex`).

`[FN80]`: for `φ ∈ WP(X)` put `ψ(z, w) = φ(z) + log |w|` on `X × ℂ`; then `ψ ∈ WP(X × ℂ)` and
`Ω = {ψ < 0}` is Runge in `X × ℂ`: otherwise there is a compact `K ⊆ Ω` with `K̂ ⊄ Ω`, which
contradicts Lemma 5.2 after localization by Rossi's local maximum principle at a point of `K̂`
where `X × ℂ` is a branched covering. Here:

* `isWeaklyPSHOn_hartogsFun`: `ψ = φ ∘ zpart + log |w| ∈ WP(X × ℂ)` (`log |w|` is FNS's
  `monoLog (X₀) 1`);
* `hartogsFun_lt_zero_iff`: `x ∈ Ω_φ` (the real form `hartogsDomain`) iff `ψ(x) < 0`;
* `polyHull_subset_zpart_preimage`: for `X` closed analytic in a polydisc, hulls of compact
  subsets of `X × ℂ` stay in `X × ℂ` (`FNR.polyHull_subset_of_localEquations_polydisc`);
* `hartogsRunge_of_charts`: **`FNS.HartogsRunge X φ`** for `X` closed analytic in a polydisc
  with a branched-covering chart (`FNL.HasCoveringChartAt`) at each of its points (this holds
  for pure-dimensional `X` by the local parametrization theorem `FNL.LocalCoveringCharts`);
  the charts of `X × ℂ` are the products `FNH.hasCoveringChartAt_zpart_preimage`, and the
  Runge step is `FNH.polyHull_subset_sublevel_of_charts`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron
open SGPT.Unibranch.FNR SGPT.Unibranch.FNL
open SGPT.Unibranch.FNS (zpart mkPt zpart_apply mkPt_zero mkPt_succ zpart_mkPt mkPt_zpart
  continuous_zpart differentiable_zpart hartogsDomain HartogsRunge)

variable {n : ℕ}

/-! ### EReal arithmetic -/

theorem EReal.exists_real_of_add_lt_zero {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : a + b < 0) : ∃ c : ℝ, a < c ∧ b < ((-c : ℝ) : EReal) := by
  induction a using EReal.rec with
  | top => exact absurd rfl ha
  | bot =>
    induction b using EReal.rec with
    | top => exact absurd rfl hb
    | bot => exact ⟨0, EReal.bot_lt_coe 0, EReal.bot_lt_coe _⟩
    | coe y => exact ⟨-y - 1, EReal.bot_lt_coe _, by rw [EReal.coe_lt_coe_iff]; linarith⟩
  | coe x =>
    induction b using EReal.rec with
    | top => exact absurd rfl hb
    | bot => exact ⟨x + 1, by rw [EReal.coe_lt_coe_iff]; linarith, EReal.bot_lt_coe _⟩
    | coe y =>
      have hxy : x + y < 0 := by
        rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff] at h
        exact h
      exact ⟨(x - y) / 2, by rw [EReal.coe_lt_coe_iff]; linarith,
        by rw [EReal.coe_lt_coe_iff]; linarith⟩

/-! ### The function `ψ(z, w) = φ(z) + log |w|` -/

/-- `log |w|` on `ℂ^{n+1}` (`w` the coordinate `0`), as the `monoLog (X₀) 1`. -/
def logW (x : ComplexModel (n + 1)) : EReal :=
  FNS.monoLog (MvPolynomial.X 0) 1 x

theorem logW_lt_iff (x : ComplexModel (n + 1)) (t : ℝ) : logW x < t ↔ ‖x 0‖ < Real.exp t := by
  rw [logW, FNS.monoLog_lt_iff _ one_ne_zero]
  simp [polyEval]

theorem logW_ne_top (x : ComplexModel (n + 1)) : logW x ≠ ⊤ := by
  refine ne_top_of_lt ((logW_lt_iff x ‖x 0‖).mpr ?_)
  linarith [Real.add_one_le_exp ‖x 0‖]

theorem plurisubharmonicOn_logW : PlurisubharmonicOn (logW (n := n)) univ :=
  (FNS.discPshOn_monoLog (MvPolynomial.X 0) one_ne_zero univ).plurisubharmonicOn isOpen_univ

/-- `ψ(z, w) = φ(z) + log |w|` (`[FN80]` §5.3). -/
def hartogsFun (φ : ComplexModel n → EReal) (x : ComplexModel (n + 1)) : EReal :=
  φ (zpart x) + logW x

/-- `ψ ∈ WP(X × ℂ)`. -/
theorem isWeaklyPSHOn_hartogsFun {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) : IsWeaklyPSHOn (zpart ⁻¹' X) (hartogsFun φ) :=
  (isWeaklyPSHOn_comp_clm hφ FNS.zpartCLM fun _ hy => hy).add
    (IsWeaklyPSHOn.of_plurisubharmonicOn plurisubharmonicOn_logW (subset_univ _))

/-- `Ω_φ = {ψ < 0}` over `X`. -/
theorem hartogsFun_lt_zero_iff {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    {x : ComplexModel (n + 1)} (hx : zpart x ∈ X) (hφ : φ (zpart x) ≠ ⊤) :
    hartogsFun φ x < 0 ↔ x ∈ hartogsDomain X φ := by
  constructor
  · intro h
    obtain ⟨c, h1, h2⟩ := EReal.exists_real_of_add_lt_zero hφ (logW_ne_top x) h
    exact ⟨hx, c, h1, (logW_lt_iff x (-c)).mp h2⟩
  · rintro ⟨-, c, h1, h2⟩
    have h3 : logW x < ((-c : ℝ) : EReal) := (logW_lt_iff x (-c)).mpr h2
    calc hartogsFun φ x < (c : EReal) + ((-c : ℝ) : EReal) := EReal.add_lt_add h1 h3
      _ = 0 := by rw [← EReal.coe_add]; simp

/-! ### Hulls stay in `X × ℂ` -/

theorem hasLocalEquationsOn_zpart_preimage {X Ω : Set (ComplexModel n)}
    (h : HasLocalEquationsOn X Ω) : HasLocalEquationsOn (zpart ⁻¹' X) (zpart ⁻¹' Ω) := by
  intro x hx
  obtain ⟨W, hW, hxW, M, g, hg, hiff⟩ := h (zpart x) hx
  exact ⟨zpart ⁻¹' W, hW.preimage continuous_zpart, hxW, M, fun i y => g i (zpart y),
    fun i => (hg i).comp differentiable_zpart.differentiableOn fun _ hy => hy,
    fun y hy => hiff (zpart y) hy⟩

/-- For `X` closed analytic in a polydisc `Δ(a, r)`, the polynomial hull of a compact subset of
`X × ℂ` lies in `X × ℂ` (`[FN80]`: "`K̂` = hull in `S_j × ℂ`"). -/
theorem polyHull_subset_zpart_preimage {X : Set (ComplexModel n)} {a : ComplexModel n}
    {r : Fin n → ℝ} (hXΔ : X ⊆ pdisc a r) (hXeq : HasLocalEquationsOn X (pdisc a r))
    {K : Set (ComplexModel (n + 1))} (hK : IsCompact K) (hKX : K ⊆ zpart ⁻¹' X) :
    polyHull K ⊆ zpart ⁻¹' X := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  set R : ℝ := C + 1 with hRdef
  have hloc : HasLocalEquationsOn (zpart ⁻¹' X)
      (pdisc (mkPt a 0) (Fin.cons R r : Fin (n + 1) → ℝ)) := by
    rw [pdisc_cons, mkPt_zero, zpart_mkPt]
    exact (hasLocalEquationsOn_zpart_preimage hXeq).mono fun x hx => hx.2
  refine (polyHull_subset_of_localEquations_polydisc hloc hK hKX ?_).trans inter_subset_left
  intro x hx i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [mkPt_zero, sub_zero, Fin.cons_zero]
    linarith [norm_apply_le x 0, hC x hx]
  · simpa using hXΔ (hKX hx) j

/-! ### The Runge property -/

/-- **`[FN80]` Theorem 5.3.1, first half.** Let `X` be closed analytic in a polydisc `Δ(a, r)`
with a branched-covering chart at each of its points (e.g. `X` pure-dimensional, by the local
parametrization theorem), and let `φ ∈ WP(X)`. Then the Hartogs domain
`Ω_φ = {(z, w) : z ∈ X, φ(z) + log |w| < 0}` is Runge in `X × ℂ`: the polynomial hull of every
compact `K ⊆ Ω_φ` meets `X × ℂ` only in `Ω_φ`. -/
theorem hartogsRunge_of_charts {X : Set (ComplexModel n)} {a : ComplexModel n} {r : Fin n → ℝ}
    {φ : ComplexModel n → EReal} (hXΔ : X ⊆ pdisc a r) (hXeq : HasLocalEquationsOn X (pdisc a r))
    (hchart : ∀ z ∈ X, HasCoveringChartAt X z univ) (hφ : IsWeaklyPSHOn X φ) :
    HartogsRunge X φ := by
  intro K hK hKΩ x ⟨hxK, hxX⟩
  have hKX : K ⊆ zpart ⁻¹' X := fun y hy => (hKΩ hy).1
  have hHY := polyHull_subset_zpart_preimage hXΔ hXeq hK hKX
  have hcharts : ∀ p ∈ zpart ⁻¹' X, HasCoveringChartAt (zpart ⁻¹' X) p univ :=
    fun p hp => hasCoveringChartAt_zpart_preimage (hchart _ hp)
  have hψK : ∀ y ∈ K, hartogsFun φ y < 0 := by
    intro y hy
    have hyX : zpart y ∈ X := hKX hy
    exact (hartogsFun_lt_zero_iff hyX (hφ.ne_top _ hyX)).mpr (hKΩ hy)
  have hx := polyHull_subset_sublevel_of_charts hcharts (isWeaklyPSHOn_hartogsFun hφ) hK hHY
    hψK hxK
  exact (hartogsFun_lt_zero_iff hxX (hφ.ne_top _ hxX)).mp hx

end SGPT.Unibranch.FNH
