import SGPT.Toric.Toric5IOrder
import SGPT.PSH.SourcePIComparison
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.NonPluripolarPoleCoalescing

/-!
# `𝓘`-goodness of toric potentials

Source `chapter_Igood.tex`, `ex:toricIgood`: on a smooth projective toric variety, every
`φ ∈ PSH_tor(X, θ)` (`θ` invariant under `T_c`) is `𝓘`-good, i.e. `P_θ[φ] = P_θ[φ]_𝓘` in a
background where `φ` has positive mass (`def:Igoodpot`).

The source proof combines `lma:Igoodinsenspert`, `thm:charIgoodasclosure`, `thm:DXmain1` and
`thm:Yao`.  Here the asymptotic Riemann--Roch formula `thm:DXmain1` is not used.  For
`θ = c_1(O(D), h)` with a `T_c`-invariant metric (`BigToricMetric`), we show directly
`P_θ[φ] = P_θ[φ]_𝓘`:

* `ψ = P_θ[φ]_𝓘` is `T_c`-invariant: the compact torus acts by biholomorphisms preserving `θ`
  and `φ`, the `𝓘`-order is invariant under these biholomorphisms (in vertex charts they are
  linear, and local weighted integrability is a biholomorphic invariant), so `ψ ∘ t` is again a
  competitor for `P_θ[φ]_𝓘` (`BigToricMetric.sourceIEnvelope_invariant`);
* `ψ ∼_𝓘 φ` (`prop:PandPI`), so by `cor:PequivtorD` ((2) ⇒ (3), proved from Yao's theorem in
  `Toric5IOrder`) `Δ(θ, ψ) ⊆ Δ(θ, φ)`, hence `P_θ[ψ] ≤ P_θ[φ]` (`prop:GPenvelopebig`) and
  `ψ ≤ P_θ[ψ] ≤ P_θ[φ]`; the other inequality `P_θ[φ] ≤ P_θ[φ]_𝓘` is `prop:PandPI`.

`𝓘`-goodness then follows in the background `θ + ω` (`BigToricMetric.addGuillemin`), in which
every toric `θ`-psh function has positive mass.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal Pointwise

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### The torus action on chart functions and on the `𝓘`-order -/

/-- In a vertex chart, the pullback by `t ∈ T(ℂ)` is the composition with the linear action. -/
theorem chartFunction_comp_action (u : PolytopeToricVariety γ hs → EReal)
    (v : latticePolytopeVertices γ) (t : Fin n → ℂˣ) (z : ComplexModel n) :
    chartFunction (fun p => u (polytopeToricAction γ hs t p)) (polytopeToricVertexChart γ hs v) z =
      chartFunction u (polytopeToricVertexChart γ hs v)
        (originalPolytopeNativeModelActionLinear γ hs v t z) := by
  change u (originalPolytopeNativeAction γ t ((originalPolytopeNativeModelChart γ hs v).symm z)) =
    u ((originalPolytopeNativeModelChart γ hs v).symm
      (originalPolytopeNativeModelActionLinear γ hs v t z))
  have hsrc : originalPolytopeNativeAction γ t ((originalPolytopeNativeModelChart γ hs v).symm z) ∈
      (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    apply (originalPolytopeNativeAction_mem_chart_source_iff γ hs v t _).mpr
    rw [← originalPolytopeNativeModelChart_source]
    exact vertexChart_symm_mem_source v z
  rw [← originalPolytopeNativeModelChart_action_symm γ hs v t z,
    (originalPolytopeNativeModelChart γ hs v).left_inv hsrc]

/-- Every chart of `X` is a vertex chart. -/
theorem exists_eq_vertexChart (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    ∃ v, e = polytopeToricVertexChart γ hs v :=
  originalPolytopeNativeComplexChart_exhaustive γ hs e

/-- The `𝓘`-order is invariant under the torus action. -/
theorem sourceIOrder_comp_action {u w : PolytopeToricVariety γ hs → EReal}
    (hI : sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs)) u w) (t : Fin n → ℂˣ)
    (hu' : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH
      (fun p => u (polytopeToricAction γ hs t p)))
    (hw' : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH
      (fun p => w (polytopeToricAction γ hs t p))) :
    sourceIOrder (ofFixedModel n (PolytopeToricVariety γ hs))
      (fun p => u (polytopeToricAction γ hs t p)) (fun p => w (polytopeToricAction γ hs t p)) := by
  refine ⟨hu', hw', fun c hc i => ?_⟩
  obtain ⟨v, rfl⟩ := exists_eq_vertexChart i
  have hinc := hI.2.2 c hc (polytopeToricVertexChart γ hs v)
  set L := originalPolytopeNativeModelActionLinear γ hs v t
  set L' := originalPolytopeNativeModelActionLinear γ hs v t⁻¹
  have hLL' : ∀ z, L (L' z) = z := fun z => by
    rw [modelActionLinear_mul, mul_inv_cancel, modelActionLinear_one]
  have hL'L : ∀ z, L' (L z) = z := fun z => by
    rw [modelActionLinear_mul, inv_mul_cancel, modelActionLinear_one]
  have huq := IsQPSH.chartFunction hI.1 (polytopeToricVertexChart γ hs v)
  have hwq' := IsQPSH.chartFunction hw' (polytopeToricVertexChart γ hs v)
  rw [vertexChart_val, vertexChart_target] at huq hwq'
  intro (z : ComplexModel n) _ (f : ComplexModel n → ℂ) hf hintB
  refine (Pending.QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp ?_
  have hint := (Pending.QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mpr hintB
  change MultiplierIntegrableAt
    (chartFunction (fun p => u (polytopeToricAction γ hs t p)) (polytopeToricVertexChart γ hs v))
    c f z volume at hint
  change MultiplierIntegrableAt
    (chartFunction (fun p => w (polytopeToricAction γ hs t p)) (polytopeToricVertexChart γ hs v))
    c f z volume
  -- to the chart function of `u` at `L z`
  have h1 : MultiplierIntegrableAt (chartFunction u (polytopeToricVertexChart γ hs v)) c
      (fun y => f (L' y)) (L z) volume := by
    refine Pending.ChartWeightedL2.multiplierIntegrableAt_comp (τ := L') (σ := L)
      (ψ := chartFunction (fun p => u (polytopeToricAction γ hs t p))
        (polytopeToricVertexChart γ hs v))
      isOpen_univ isOpen_univ L'.differentiable.differentiableOn
      (L.restrictScalars ℝ).contDiff.contDiffOn (mapsTo_univ _ _) (mapsTo_univ _ _)
      (fun y _ => hLL' y) (fun y _ => hL'L y) (fun y _ => ?_) huq.upperSemicontinuousOn
      hc.ne' (mem_univ _) ?_
    · rw [chartFunction_comp_action, hLL']
    · rwa [hL'L]
  have hfa : AnalyticAt ℂ (fun y => f (L' y)) (L z) := by
    apply AnalyticAt.comp (g := f) (f := L') _ (L'.analyticAt (L z))
    rw [hL'L]; exact hf
  have hLz : L z ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [vertexChart_target]; exact mem_univ _
  have h2B := hinc (L z) hLz _ hfa
    ((Pending.QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mp h1)
  have h2 : MultiplierIntegrableAt (chartFunction w (polytopeToricVertexChart γ hs v)) c
      (fun y => f (L' y)) (L z) volume :=
    (Pending.QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr h2B
  -- back to the chart function of `w ∘ t` at `z`
  have h3 : MultiplierIntegrableAt
      (chartFunction (fun p => w (polytopeToricAction γ hs t p)) (polytopeToricVertexChart γ hs v))
      c (fun y => f (L' (L y))) z volume := by
    refine Pending.ChartWeightedL2.multiplierIntegrableAt_comp (τ := L) (σ := L')
      isOpen_univ isOpen_univ L.differentiable.differentiableOn
      (L'.restrictScalars ℝ).contDiff.contDiffOn (mapsTo_univ _ _) (mapsTo_univ _ _)
      (fun y _ => hL'L y) (fun y _ => hLL' y) (fun y _ => ?_) hwq'.upperSemicontinuousOn
      hc.ne' (mem_univ _) h2
    rw [chartFunction_comp_action]
  simpa only [hL'L] using h3

/-! ### `T_c`-invariance of the `𝓘`-envelope -/

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- Source proof of `ex:toricIgood`: for `φ ∈ PSH_tor(X, θ)` the `𝓘`-envelope `P_θ[φ]_𝓘` is
`T_c`-invariant. -/
theorem sourceIEnvelope_invariant {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    PolytopeToricInvariant γ hs (sourceIEnvelope h.atlasForm u) := by
  set ψ := sourceIEnvelope h.atlasForm u
  have hψ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm ψ :=
    isThetaPSH_sourceIEnvelope hu.1
  have huψ := sourceIEquivalent_iEnvelope hu.1
  have hkey : ∀ t : Fin n → ℂˣ, IsCompactTorusElement t →
      (fun p => ψ (polytopeToricAction γ hs t p)) ≤ ψ := by
    intro t ht
    have hψt := h.isThetaPSH_comp_action hψ ht
    have hut : (fun p => u (polytopeToricAction γ hs t p)) = u := funext fun p => hu.2 t ht p
    have hut' := h.isThetaPSH_comp_action hu.1 ht
    apply le_sourceIEnvelope hψt (fun p => sourceIEnvelope_le_zero _ _ _)
    have h1 := sourceIOrder_comp_action huψ.2 t ⟨_, hψt⟩ ⟨_, hut'⟩
    have h2 := sourceIOrder_comp_action huψ.1 t ⟨_, hut'⟩ ⟨_, hψt⟩
    rw [hut] at h1 h2
    exact ⟨h1, h2⟩
  intro t ht p
  apply le_antisymm (hkey t ht p)
  have := hkey t⁻¹ (isCompactTorusElement_inv ht) (polytopeToricAction γ hs t p)
  simp only at this
  rw [← polytopeToricAction_mul, inv_mul_cancel, polytopeToricAction_one] at this
  exact this

/-- Source `ex:toricIgood` (main step): for `θ = c_1(O(D), h)` and `φ ∈ PSH_tor(X, θ)`,
`P_θ[φ] = P_θ[φ]_𝓘`. -/
theorem sourceSingularityEnvelope_eq_sourceIEnvelope {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) :
    sourceSingularityEnvelope h.atlasForm u = sourceIEnvelope h.atlasForm u := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  set ψ := sourceIEnvelope h.atlasForm u
  have hψ : ψ ∈ h.PSHTor := ⟨isThetaPSH_sourceIEnvelope hu.1, h.sourceIEnvelope_invariant hu⟩
  apply le_antisymm (sourcePEnvelope_le_IEnvelope hu.1)
  have hIψ := (sourceIEquivalent_iEnvelope hu.1).2
  have hsub := h.newtonBody_subset_of_sourceIOrder hψ hu hIψ
  have hPP := (h.sourceSingularityEnvelope_le_iff hP hψ hu).mpr hsub
  calc ψ ≤ sourceSingularityEnvelope h.atlasForm ψ :=
        le_sourceSingularityEnvelope hψ.1 (sourceIEnvelope_le_zero _ _) (singularityLE_refl ψ)
    _ ≤ sourceSingularityEnvelope h.atlasForm u := hPP

/-- Every toric `θ`-psh function has positive mass in the background `θ + ω`. -/
theorem MA_addGuillemin_pos {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    0 < h.addGuillemin.MA (h.mem_PSHTor_addGuillemin hu) univ := by
  have hun : IsThetaPshPotential h.form.val u :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
  change Pending.DiagonalMass.HasPositivePotentialMass
    (h.form + (polytopeToricKahlerBackground γ hs).form) u _
  simpa only [one_smul] using
    Pending.SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
      (polytopeToricKahlerBackground γ hs) hun zero_lt_one

/-- Source `ex:toricIgood`, for `θ = c_1(O(D), h)` with `h` a `T_c`-invariant metric on the line
bundle of any torus-invariant divisor `D`: every `φ ∈ PSH_tor(X, θ)` is `𝓘`-good, witnessed by
the `T_c`-invariant background `θ + ω` in which `φ` has positive mass. -/
theorem sourceIGood_of_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    sourceIGood (n := n) u :=
  ⟨h.addGuillemin.atlasForm, (h.mem_PSHTor_addGuillemin hu).1,
    h.MA_addGuillemin_pos hu,
    h.addGuillemin.sourceSingularityEnvelope_eq_sourceIEnvelope (h.mem_PSHTor_addGuillemin hu)⟩

end BigToricMetric

/-- Source `ex:toricIgood` in the ample setting: every `φ ∈ PSH_tor(X, ω)` is `𝓘`-good, and
`P_ω[φ] = P_ω[φ]_𝓘`. -/
theorem polytopeToric_sourceIGood {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    sourceIGood (n := n) u ∧
      sourceSingularityEnvelope (polytopeToricOmega γ hs) u =
        sourceIEnvelope (polytopeToricOmega γ hs) u :=
  ⟨(guilleminBigToricMetric γ hs).sourceIGood_of_mem hu,
    (guilleminBigToricMetric γ hs).sourceSingularityEnvelope_eq_sourceIEnvelope hu⟩

/-! ### Arbitrary backgrounds -/

variable (γ hs) in
/-- The metrics `h_P^{⊗(k+1)}` on `O((k+1) D_P)`, with curvature `(k+1) ω`. -/
def iterGuillemin : ℕ → Σ D : ToricDivisor γ hs, BigToricMetric D
  | 0 => ⟨polytopeToricAmpleDivisor γ hs, guilleminBigToricMetric γ hs⟩
  | k + 1 => ⟨(iterGuillemin k).1 + polytopeToricAmpleDivisor γ hs, (iterGuillemin k).2.addGuillemin⟩

theorem iterGuillemin_form (k : ℕ) :
    (iterGuillemin γ hs k).2.form = ((k : ℝ) + 1) • polytopeToricKahlerForm γ hs := by
  induction k with
  | zero =>
    change polytopeToricKahlerForm γ hs = _
    rw [Nat.cast_zero, zero_add, one_smul]
  | succ k ih =>
    change (iterGuillemin γ hs k).2.form + polytopeToricKahlerForm γ hs = _
    rw [ih]
    push_cast
    simp only [add_smul, one_smul]

/-- Source `ex:toricIgood`: on the smooth projective toric manifold `X`, every `T_c`-invariant
`θ`-psh function, for any smooth closed real `(1,1)`-form `θ`, is `𝓘`-good.  (`φ` is
`(k+1)ω`-psh for `k` large by Kähler domination, `(k+1)ω = c_1(O((k+1)D_P), h_P^{k+1})`, and
`BigToricMetric.sourceIGood_of_mem` applies; the invariance of `θ` assumed in the source is not
needed.) -/
theorem sourceIGood_of_isThetaPSH_of_invariant
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (PolytopeToricVariety γ hs))}
    {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH θ u)
    (hinv : PolytopeToricInvariant γ hs u) : sourceIGood (n := n) u := by
  set ωK := polytopeToricKahlerBackground γ hs
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  obtain ⟨A, -, hsemi⟩ :=
    Pending.KahlerDomination.exists_pos_isSemipositive_add_smul ωK (-(atlasClosedFormToNative θ))
  have h1 := Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive hn hsemi
  rw [add_neg_cancel_left] at h1
  obtain ⟨k, hk⟩ := exists_nat_ge A
  have h2 := Pending.NonPluripolarPoleCoalescing.isThetaPshPotential_smul_kahler_mono ωK
    (show A ≤ (k : ℝ) + 1 by linarith) h1
  set g := (iterGuillemin γ hs k).2
  have hmem : u ∈ g.PSHTor := by
    refine ⟨(isThetaPSH_iff_nativeThetaPotential g.atlasForm u).mpr ?_, hinv⟩
    change IsThetaPshPotential g.form.val u
    rw [iterGuillemin_form]
    exact h2
  exact g.sourceIGood_of_mem hmem

end SGPT.Toric
