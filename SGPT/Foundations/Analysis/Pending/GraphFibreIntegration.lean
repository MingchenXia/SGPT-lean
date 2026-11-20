import SGPT.Foundations.Analysis.Pending.DiagonalFibreIntegration

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Fibre integration of the current of integration over a graph

Source: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`) and Boucksom, proof of
Theorem 4.8 (`bou02-volume:4.8`), in the GRAPH form of the TN.4 plan (§1 F6 "(P) GRAPH ROUTE",
the proof of Boucksom's mass estimate): Boucksom's Lemma 4.10 is run on `X_k × X` with the graph
`Γ_k` of the modification `μ_k : X_k → X` in place of the diagonal of `X_k × X_k`.

Let `f : V → X` be a holomorphic map between complex manifolds of the same dimension `n = q + 1`, and
`[Γ_f] = (id, f)_*[V]` the current of integration over its graph (TN23's `graphCurrent`, the statement under discussion;
stated here on the push-forward term itself, so that this module does not wait for it).

* `fibrePushforward_graphCurrent`: `p₁_*([Γ_f] ∧ p₂^*β) = [V] ∧ f^*β` — the analogue of
  `DiagonalFibreIntegration.fibrePushforward_diagonalCurrent` (`f = id`).
* `isPositive_fibrePushforward_sub_graph`: if `Θ − δ [Γ_f]` is positive and `β` semipositive, then
  `p₁_*(Θ ∧ p₂^*β) − δ [V] ∧ f^*β` is positive — with `β = ω` this is `R ≥ δ μ^*ω`, the lower bound that
  descends exactly along a blowup sequence.
* `mass_graphCurrent`: for the product Kähler form `p₁^*w + p₂^*ω`, the mass of `[Γ_f]` is
  `∫_V (w + f^*ω)ⁿ`.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.GraphFibreIntegration

open FirstPass FirstPass.HolomorphicMaps FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent SmoothCurrentTraceMeasure
  ProductComplexManifold DiagonalFibreIntegration
open scoped ProductComplexManifold

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (q + 1)) X] [IsComplexManifold (q + 1) X] {f : V → X}
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-- The graph map `v ↦ (v, f v)` is holomorphic. -/
theorem contMDiff_graph (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f) :
    ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel ((q + 1) + (q + 1))) ∞
      (fun v : V => (v, f v)) :=
  contMDiff_prodMk contMDiff_id hf

/-- `(id, f)^*(p₁^*φ ∧ p₂^*β) = φ ∧ f^*β` geometrically. -/
theorem pullback_graph_fibreTest_geometricallyEq
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (β : SmoothRealForm (q + 1) X 2) (φ : testSpace (q + 1) V q) :
    (SmoothRealForm.pullback (contMDiff_graph hf)
        (wedgeTwo (SmoothRealForm.pullback contMDiff_fst (φ : SmoothRealForm (q + 1) V (2 * q)))
          (SmoothRealForm.pullback contMDiff_snd β))).GeometricallyEq
      (wedgeTwo (φ : SmoothRealForm (q + 1) V (2 * q)) (SmoothRealForm.pullback hf β)) := by
  rw [pullback_wedgeTwo (contMDiff_graph hf)]
  refine wedgeTwo_geometricallyEq ?_ ?_
  · refine ((pullback_comp_geometricallyEq contMDiff_fst (contMDiff_graph hf) _).symm).trans ?_
    exact pullback_id_geometricallyEq _
  · exact (pullback_comp_geometricallyEq contMDiff_snd (contMDiff_graph hf) _).symm

/-- **Fibre integration of the graph**: `p₁_*([Γ_f] ∧ p₂^*β) = [V] ∧ f^*β`
(`dp04-kahler-cone:2.12`, `bou02-volume:4.8`, graph form). -/
theorem fibrePushforward_graphCurrent
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (w : KahlerBackground (q + 1) V) {β : SmoothRealForm (q + 1) X 2} (hβ : β.IsTypeOneOne) :
    fibrePushforward hβ (pushforward (contMDiff_graph hf) (integrationCurrent w)) =
      wedge (isTypeOneOne_pullback hf hβ) (integrationCurrent w) := by
  ext φ
  rw [fibrePushforward_apply, pushforward_apply, wedge_apply]
  exact IsPositive.apply_eq_of_geometricallyEq (isPositive_integrationCurrent w)
    (pullback_graph_fibreTest_geometricallyEq hf β φ)

/-- For a closed `(1,1)`-form `β` on `X`, the fibre integral of the graph is the smooth current of
`f^*β` on `V`. -/
theorem fibrePushforward_graphCurrent_eq_smoothCurrent
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (w : KahlerBackground (q + 1) V) (β : ClosedRealOneOneForm (q + 1) X) :
    fibrePushforward β.2.2 (pushforward (contMDiff_graph hf) (integrationCurrent w)) =
      smoothCurrent (q := q) (p := 1) w ![ClosedRealOneOneForm.pullback hf β] :=
  fibrePushforward_graphCurrent hf w β.2.2

/-- **The lower bound passes to the fibre integral** (graph form): if `Θ − δ [Γ_f]` is positive and
`β` is semipositive, then `p₁_*(Θ ∧ p₂^*β) − δ [V] ∧ f^*β` is positive.  With `β = ω` and `f = μ` a
modification this is `R ≥ δ μ^*ω`. -/
theorem isPositive_fibrePushforward_sub_graph
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (w : KahlerBackground (q + 1) V) {β : SmoothRealForm (q + 1) X 2} (hβ : β.IsTypeOneOne)
    (hβp : ∀ (e : ComplexChart (q + 1) X) z, z ∈ e.val.target →
      IsSemipositiveOneOne (β.coeff e z))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (V × X) (q + 1)} {δ : ℝ}
    (hΘ : IsPositive (Θ - δ • pushforward (contMDiff_graph hf) (integrationCurrent w))) :
    IsPositive (fibrePushforward hβ Θ -
      δ • wedge (isTypeOneOne_pullback hf hβ) (integrationCurrent w)) := by
  have h := IsPositive.fibrePushforward hβ hβp hΘ
  rwa [fibrePushforward_sub, fibrePushforward_smul, fibrePushforward_graphCurrent] at h

/-- A Kähler form plus a semipositive closed form is Kähler. -/
theorem isKahler_add_of_isSemipositive {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (w : KahlerBackground n M)
    {s : ClosedRealOneOneForm n M} (hs : s.val.IsSemipositive) : (w.form + s).val.IsKahler := by
  refine ⟨fun e z hz => ⟨fun a b => (w.form + s).property.2 e z hz a b, fun v hv => ?_⟩,
    (w.form + s).property.1⟩
  have h1 := hs e z hz v
  have h2 := (w.isKahler.1 e z hz).2 v hv
  simp only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] at h1 ⊢
  linarith

/-- The Kähler form `w + f^*ω` on `V` (the restriction of `p₁^*w + p₂^*ω` to the graph). -/
def graphKahler (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (w : KahlerBackground (q + 1) V) (om : KahlerBackground (q + 1) X) : KahlerBackground (q + 1) V :=
  ⟨w.form + ClosedRealOneOneForm.pullback hf om.form,
    isKahler_add_of_isSemipositive w (ClosedRealOneOneForm.pullback_isSemipositive hf om.isSemipositive)⟩

/-- `(id, f)^*(p₁^*w + p₂^*ω) = w + f^*ω` geometrically. -/
theorem pullback_graph_prodForm_geometricallyEq
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (a : ClosedRealOneOneForm (q + 1) V) (b : ClosedRealOneOneForm (q + 1) X) :
    (SmoothRealForm.pullback (contMDiff_graph hf) (prodForm a b).val).GeometricallyEq
      (a + ClosedRealOneOneForm.pullback hf b).val := by
  have hval : (prodForm a b).val = SmoothRealForm.pullback contMDiff_fst a.val +
      SmoothRealForm.pullback contMDiff_snd b.val := smoothRealForm_ext fun _ _ => rfl
  rw [hval, pullback_add (contMDiff_graph hf)]
  intro e z hz
  have e1 : (SmoothRealForm.pullback (contMDiff_graph hf)
      (SmoothRealForm.pullback contMDiff_fst a.val)).coeff e z = a.val.coeff e z := by
    rw [← (pullback_comp_geometricallyEq contMDiff_fst (contMDiff_graph hf) a.val) e hz]
    exact pullback_id_geometricallyEq a.val e hz
  have e2 : (SmoothRealForm.pullback (contMDiff_graph hf)
      (SmoothRealForm.pullback contMDiff_snd b.val)).coeff e z =
        (SmoothRealForm.pullback hf b.val).coeff e z := by
    rw [← (pullback_comp_geometricallyEq contMDiff_snd (contMDiff_graph hf) b.val) e hz]
  rw [coeff_add, e1, e2, ClosedRealOneOneForm.coeff_add]
  rfl

/-- **The mass of the graph current**: for the product Kähler form `p₁^*w + p₂^*ω`, the mass of
`[Γ_f]` is `∫_V (w + f^*ω)ⁿ`, the integral current of `V` evaluated on the `n`-th power of the Kähler
form `w + f^*ω`. -/
theorem mass_graphCurrent
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (w : KahlerBackground (q + 1) V) (om : KahlerBackground (q + 1) X) :
    mass (prodKahlerBackground w om) (pushforward (contMDiff_graph hf) (integrationCurrent w)) =
      integrationCurrent w (kahlerTest (graphKahler hf w om) (q + 1)) := by
  have hgeom : ((pullbackTestLM (contMDiff_graph hf) (q + 1)
      (kahlerTest (prodKahlerBackground w om) (q + 1)) : testSpace (q + 1) V (q + 1)) :
        SmoothRealForm (q + 1) V (2 * (q + 1))).GeometricallyEq
        ((kahlerTest (graphKahler hf w om) (q + 1) : testSpace (q + 1) V (q + 1)) :
          SmoothRealForm (q + 1) V (2 * (q + 1))) := by
    intro e z hz
    change (SmoothRealForm.pullback (contMDiff_graph hf)
        (formPow (prodForm w.form om.form).val (q + 1))).coeff e z =
      (formPow (w.form + ClosedRealOneOneForm.pullback hf om.form).val (q + 1)).coeff e z
    rw [pullback_formPow, formPow_coeff, (pullback_graph_prodForm_geometricallyEq hf w.form om.form) e hz,
      formPow_coeff]
  rw [mass, pushforward_apply]
  exact IsPositive.apply_eq_of_geometricallyEq (isPositive_integrationCurrent w) hgeom

end SGPT.Foundations.Analysis.Pending.GraphFibreIntegration
