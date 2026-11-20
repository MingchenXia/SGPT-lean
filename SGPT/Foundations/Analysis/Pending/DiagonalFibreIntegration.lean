import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.SmoothCurrentTraceMeasure
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Fibre integration along the second factor and the diagonal current

Sources: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`), and Boucksom, the last
paragraph of the proof of Theorem 4.8 (`bou02-volume:4.8`); blueprint
`bou:pushforward-lower-bound`.  On `X × X` a closed positive `(n,n)`-current `Θ` with
`Θ ≥ δ [Δ]` is turned into a `(1,1)`-current on `X` by
`R = p₁_*(Θ ∧ p₂^*ω)`, and the inequality passes to `R ≥ δ ω`, because
`p₁_*([Δ] ∧ p₂^*ω) = ω`.  This module proves that identity in the product-test-form framework
of `Pending.PositiveProductCurrents` (TN.4 plan, step B6).

* `fibrePushforward hβ Θ = p₁_*(Θ ∧ p₂^*β)` for a current `Θ` on `X × Y` and a real
  `(1,1)`-form `β` on `Y` (`pushforward` of `wedge`); linear, positive for semipositive `β`
  (`IsPositive.fibrePushforward`), weakly continuous.
* `diagonalCurrent w = diag_*[X]`, the current of integration over the diagonal
  `Δ = diag(X)` (`demailly-cadg:III.2.14` for a smooth connected component), positive.
* `fibrePushforward_diagonalCurrent`: **`p₁_*([Δ] ∧ p₂^*β) = [X] ∧ β`**, an equality of
  currents on `X`; for a closed `β` the right side is the smooth current
  `SmoothCurrentTraceMeasure.smoothCurrent w ![β]` (`fibrePushforward_diagonalCurrent_eq_smoothCurrent`).
* `isPositive_fibrePushforward_sub`: if `Θ - δ [Δ]` is positive, so is
  `p₁_*(Θ ∧ p₂^*β) - δ [X] ∧ β` (semipositive `β`): with `β = ω` this is `R ≥ δ ω`.
* `mass_diagonalCurrent`: for `ω̃ = p₁^*ω + p₂^*ω`, the mass of `[Δ]` is `2ⁿ ∫_X ωⁿ`
  (`diag^*ω̃ = 2ω`, `pullback_diag_prodForm_geometricallyEq`), the normalisation in the last
  paragraph of `bou:uniform-diagonal-domination`.

The proof is functoriality: `p₁ ∘ diag = p₂ ∘ diag = id`, so
`diag^*(p₁^*φ ∧ p₂^*β) = φ ∧ β` geometrically (`pullback_comp_geometricallyEq`, the
mixed-dimension form of `FirstPass.SmoothRealForm.pullback_comp_geometricallyEq`), and positive
currents only see coefficients on chart targets.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.DiagonalFibreIntegration

open FirstPass FirstPass.HolomorphicMaps FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent SmoothCurrentTraceMeasure
  ProductComplexManifold
open scoped ProductComplexManifold

noncomputable section

/-! ### Functoriality of the pullback between manifolds of different dimensions -/

section Functorial

variable {p k l n : ℕ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel l) Z] [IsComplexManifold l Z]

/-- **`(f ∘ g)^* a = g^* (f^* a)`** geometrically, for holomorphic maps `g : Z → Y`, `f : Y → X`
between manifolds of arbitrary dimensions. -/
theorem pullback_comp_geometricallyEq {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel k) ∞ g)
    (a : SmoothRealForm n X p) :
    (SmoothRealForm.pullback (hf.comp hg) a).GeometricallyEq
      (SmoothRealForm.pullback hg (SmoothRealForm.pullback hf a)) := by
  intro e z hz
  set x : Z := e.val.symm z with hx
  set d₂ := complexChartAt (n := k) (g x) with hd₂
  set d₁ := complexChartAt (n := n) (f (g x)) with hd₁
  have hgx : g x ∈ d₂.val.source := mem_complexChartAt_source _
  have hfgx : f (g x) ∈ d₁.val.source := mem_complexChartAt_source _
  set w : ComplexModel k := coordinateMap g e d₂ z with hw
  have hwx : d₂.val.symm w = g x := by
    rw [hw]
    exact d₂.val.left_inv hgx
  have hzdom : z ∈ coordinateDomain g e d₂ := ⟨hz, by
    simpa only [mem_preimage, ← hx] using hgx⟩
  have hwdom : w ∈ coordinateDomain f d₂ d₁ :=
    ⟨d₂.val.map_source hgx, by simpa only [mem_preimage, hwx] using hfgx⟩
  have hzdom₁ : z ∈ coordinateDomain (f ∘ g) e d₁ := ⟨hz, by
    simpa only [mem_preimage, ← hx, Function.comp_apply] using hfgx⟩
  have heq : coordinateMap (f ∘ g) e d₁ =ᶠ[𝓝 z]
      (coordinateMap f d₂ d₁) ∘ (coordinateMap g e d₂) := by
    filter_upwards [(coordinateDomain_isOpen hg e d₂).mem_nhds hzdom] with y hy
    show d₁.val (f (g (e.val.symm y))) =
      d₁.val (f (d₂.val.symm (d₂.val (g (e.val.symm y)))))
    rw [d₂.val.left_inv hy.2]
  have hchain : fderiv ℝ (coordinateMap (f ∘ g) e d₁) z =
      (fderiv ℝ (coordinateMap f d₂ d₁) w).comp
        (fderiv ℝ (coordinateMap g e d₂) z) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp z
      ((coordinateMap_contDiffAt_real hf d₂ d₁ hwdom).differentiableAt (by simp))
      ((coordinateMap_contDiffAt_real hg e d₂ hzdom).differentiableAt (by simp))
  have hpoint : coordinateMap f d₂ d₁ w = coordinateMap (f ∘ g) e d₁ z := by
    show d₁.val (f (d₂.val.symm w)) = d₁.val (f (g (e.val.symm z)))
    rw [hwx]
  rw [SmoothRealForm.pullback_coeff (hf.comp hg) a e d₁ hzdom₁,
    SmoothRealForm.pullback_coeff hg (SmoothRealForm.pullback hf a) e d₂ hzdom,
    SmoothRealForm.pullback_coeff hf a d₂ d₁ hwdom, hchain, hpoint]
  ext v
  rfl

/-- `id^* a = a` geometrically (any dimension). -/
theorem pullback_id_geometricallyEq (a : SmoothRealForm n X p) :
    (SmoothRealForm.pullback (f := (id : X → X))
      (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) a).GeometricallyEq a :=
  SmoothRealForm.pullback_id_geometricallyEq a

end Functorial

/-! ### Geometric equality and the wedge -/

section Wedge

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The wedge with a two-form respects geometric equality in both factors. -/
theorem wedgeTwo_geometricallyEq {k : ℕ} {P P' : SmoothRealForm n M k}
    {β β' : SmoothRealForm n M 2} (hP : P.GeometricallyEq P') (hβ : β.GeometricallyEq β') :
    (wedgeTwo P β).GeometricallyEq (wedgeTwo P' β') := by
  intro e z hz
  rw [wedgeTwo_coeff, wedgeTwo_coeff, hP e hz, hβ e hz]

/-- A positive current takes the same value on geometrically equal test forms. -/
theorem IsPositive.apply_eq_of_geometricallyEq {q : ℕ} {T : ProductCurrent n M q}
    (hT : IsPositive T) {φ ψ : testSpace n M q}
    (h : (φ : SmoothRealForm n M (2 * q)).GeometricallyEq (ψ : SmoothRealForm n M (2 * q))) :
    T φ = T ψ :=
  hT.apply_eq_of_coeff_eqOn fun e _ hz => h e hz

end Wedge

/-! ### Fibre integration along the second factor -/

section Fibre

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

/-- **Fibre integration along the second factor**: `p₁_*(Θ ∧ p₂^*β)` for a current `Θ` of
bidimension `(q+1,q+1)` on `X × Y` and a real `(1,1)`-form `β` on `Y`; a current of
bidimension `(q,q)` on `X` (`dp04-kahler-cone:2.12`, `bou02-volume:4.8`). -/
def fibrePushforward {β : SmoothRealForm m Y 2} (hβ : β.IsTypeOneOne) {q : ℕ}
    (Θ : ProductCurrent (n + m) (X × Y) (q + 1)) : ProductCurrent n X q :=
  pushforward contMDiff_fst (wedge (isTypeOneOne_pullback contMDiff_snd hβ) Θ)

variable {β : SmoothRealForm m Y 2} (hβ : β.IsTypeOneOne) {q : ℕ}

theorem fibrePushforward_apply (Θ : ProductCurrent (n + m) (X × Y) (q + 1))
    (φ : testSpace n X q) :
    fibrePushforward hβ Θ φ =
      Θ (wedgeTestLM (isTypeOneOne_pullback contMDiff_snd hβ) q
        (pullbackTestLM contMDiff_fst q φ)) := rfl

/-- The test form `p₁^*φ ∧ p₂^*β` against which `Θ` is evaluated. -/
theorem coe_fibreTest (φ : testSpace n X q) :
    ((wedgeTestLM (isTypeOneOne_pullback contMDiff_snd hβ) q
        (pullbackTestLM contMDiff_fst q φ) : testSpace (n + m) (X × Y) (q + 1)) :
          SmoothRealForm (n + m) (X × Y) (2 * (q + 1))) =
      wedgeTwo (SmoothRealForm.pullback contMDiff_fst (φ : SmoothRealForm n X (2 * q)))
        (SmoothRealForm.pullback contMDiff_snd β) := rfl

theorem fibrePushforward_add (S T : ProductCurrent (n + m) (X × Y) (q + 1)) :
    fibrePushforward hβ (S + T) = fibrePushforward hβ S + fibrePushforward hβ T := rfl

theorem fibrePushforward_smul (c : ℝ) (T : ProductCurrent (n + m) (X × Y) (q + 1)) :
    fibrePushforward hβ (c • T) = c • fibrePushforward hβ T := rfl

theorem fibrePushforward_sub (S T : ProductCurrent (n + m) (X × Y) (q + 1)) :
    fibrePushforward hβ (S - T) = fibrePushforward hβ S - fibrePushforward hβ T := rfl

/-- **Positivity**: for a semipositive `β`, `p₁_*(Θ ∧ p₂^*β)` is positive when `Θ` is. -/
theorem IsPositive.fibrePushforward
    (hβp : ∀ (e : ComplexChart m Y) z, z ∈ e.val.target → IsSemipositiveOneOne (β.coeff e z))
    {Θ : ProductCurrent (n + m) (X × Y) (q + 1)} (hΘ : IsPositive Θ) :
    IsPositive (DiagonalFibreIntegration.fibrePushforward hβ Θ) := by
  have hpb : ∀ (e : ComplexChart (n + m) (X × Y)) z, z ∈ e.val.target →
      IsSemipositiveOneOne ((SmoothRealForm.pullback contMDiff_snd β).coeff e z) := by
    intro e z hz
    set d := complexChartAt (n := m) (Prod.snd (e.val.symm z))
    have hzd : z ∈ coordinateDomain Prod.snd e d := ⟨hz, mem_complexChartAt_source _⟩
    rw [SmoothRealForm.pullback_coeff contMDiff_snd β e d hzd]
    exact (hβp d _ (coordinateMap_mem_target hzd)).comp _
      (fun v => coordinateMap_fderiv_map_smul_complex contMDiff_snd e d hzd Complex.I v)
  exact (hΘ.wedge (isTypeOneOne_pullback contMDiff_snd hβ) hpb).pushforward contMDiff_fst

/-- Fibre integration is weakly continuous. -/
theorem tendsto_fibrePushforward_apply {ι : Type*} {l : Filter ι}
    {T : ι → ProductCurrent (n + m) (X × Y) (q + 1)} {S : ProductCurrent (n + m) (X × Y) (q + 1)}
    (h : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ))) (φ : testSpace n X q) :
    Tendsto (fun i => fibrePushforward hβ (T i) φ) l (𝓝 (fibrePushforward hβ S φ)) :=
  h _

end Fibre

/-! ### The diagonal current and its fibre integral -/

section Diagonal

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **The current of integration over the diagonal**, `[Δ] = diag_*[X]`, a current of
bidimension `(n,n)` on `X × X` (`demailly-cadg:III.2.14`). -/
def diagonalCurrent (w : KahlerBackground n X) : ProductCurrent (n + n) (X × X) n :=
  pushforward contMDiff_diag (integrationCurrent w)

theorem diagonalCurrent_apply (w : KahlerBackground n X) (φ : testSpace (n + n) (X × X) n) :
    diagonalCurrent w φ = integrationCurrent w (pullbackTestLM contMDiff_diag n φ) := rfl

/-- The diagonal current is positive. -/
theorem isPositive_diagonalCurrent (w : KahlerBackground n X) :
    IsPositive (diagonalCurrent w) :=
  (isPositive_integrationCurrent w).pushforward contMDiff_diag

end Diagonal

section DiagonalFibre

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- `diag^*(p₁^*φ ∧ p₂^*β) = φ ∧ β` geometrically. -/
theorem pullback_diag_fibreTest_geometricallyEq (β : SmoothRealForm (q + 1) X 2)
    (φ : testSpace (q + 1) X q) :
    (SmoothRealForm.pullback contMDiff_diag
        (wedgeTwo (SmoothRealForm.pullback contMDiff_fst (φ : SmoothRealForm (q + 1) X (2 * q)))
          (SmoothRealForm.pullback contMDiff_snd β))).GeometricallyEq
      (wedgeTwo (φ : SmoothRealForm (q + 1) X (2 * q)) β) := by
  rw [pullback_wedgeTwo contMDiff_diag]
  refine wedgeTwo_geometricallyEq ?_ ?_
  · refine ((pullback_comp_geometricallyEq contMDiff_fst contMDiff_diag _).symm).trans ?_
    exact pullback_id_geometricallyEq _
  · refine ((pullback_comp_geometricallyEq contMDiff_snd contMDiff_diag _).symm).trans ?_
    exact pullback_id_geometricallyEq _

/-- **Fibre integration of the diagonal**: `p₁_*([Δ] ∧ p₂^*β) = [X] ∧ β`
(`dp04-kahler-cone:2.12`, `bou02-volume:4.8`). -/
theorem fibrePushforward_diagonalCurrent (w : KahlerBackground (q + 1) X)
    {β : SmoothRealForm (q + 1) X 2} (hβ : β.IsTypeOneOne) :
    fibrePushforward hβ (diagonalCurrent w) = wedge hβ (integrationCurrent w) := by
  ext φ
  rw [fibrePushforward_apply, diagonalCurrent_apply, wedge_apply]
  exact IsPositive.apply_eq_of_geometricallyEq (isPositive_integrationCurrent w)
    (pullback_diag_fibreTest_geometricallyEq β φ)

/-- For a closed `(1,1)`-form `β` the fibre integral of the diagonal is the smooth current of
`β`: `p₁_*([Δ] ∧ p₂^*β) = [X] ∧ β`. -/
theorem fibrePushforward_diagonalCurrent_eq_smoothCurrent (w : KahlerBackground (q + 1) X)
    (β : ClosedRealOneOneForm (q + 1) X) :
    fibrePushforward β.2.2 (diagonalCurrent w) = smoothCurrent (q := q) (p := 1) w ![β] :=
  fibrePushforward_diagonalCurrent w β.2.2

/-- **The lower bound passes to the fibre integral**: if `Θ - δ [Δ]` is positive and `β` is
semipositive, then `p₁_*(Θ ∧ p₂^*β) - δ [X] ∧ β` is positive.  With `β = ω` this is
`R ≥ δ ω` in the proof of `bou:pushforward-lower-bound`. -/
theorem isPositive_fibrePushforward_sub (w : KahlerBackground (q + 1) X)
    {β : SmoothRealForm (q + 1) X 2} (hβ : β.IsTypeOneOne)
    (hβp : ∀ (e : ComplexChart (q + 1) X) z, z ∈ e.val.target →
      IsSemipositiveOneOne (β.coeff e z))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)} {δ : ℝ}
    (hΘ : IsPositive (Θ - δ • diagonalCurrent w)) :
    IsPositive (fibrePushforward hβ Θ - δ • wedge hβ (integrationCurrent w)) := by
  have h := IsPositive.fibrePushforward hβ hβp hΘ
  rwa [fibrePushforward_sub, fibrePushforward_smul, fibrePushforward_diagonalCurrent] at h

end DiagonalFibre

/-! ### The mass of the diagonal current -/

section DiagonalMass

theorem formPower_smul {n : ℕ} (c : ℝ) (A : RealForm n 2) :
    ∀ q, formPower (c • A) q = c ^ q • formPower A q
  | 0 => by simp
  | q + 1 => by
    rw [formPower_succ, formPower_succ, formPower_smul c A q, coordinateWedge_smul_left,
      coordinateWedge_smul_right, smul_smul, pow_succ]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem formPow_geometricallyEq {w w' : SmoothRealForm n M 2} (h : w.GeometricallyEq w')
    (q : ℕ) : (formPow w q).GeometricallyEq (formPow w' q) := by
  intro e z hz
  rw [formPow_coeff, formPow_coeff, h e hz]

theorem pullback_formPow {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (w : SmoothRealForm n M 2) :
    ∀ q, SmoothRealForm.pullback hf (formPow w q) = formPow (SmoothRealForm.pullback hf w) q
  | 0 => pullback_unitForm hf
  | q + 1 => by
    rw [formPow, pullback_wedgeTwo hf, pullback_formPow hf w q]
    rfl

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `diag^*(p₁^*a + p₂^*b) = a + b` geometrically. -/
theorem pullback_diag_prodForm_geometricallyEq (a b : ClosedRealOneOneForm n X) :
    (SmoothRealForm.pullback (contMDiff_diag (X := X)) (prodForm a b).val).GeometricallyEq
      (a + b).val := by
  have hval : (prodForm a b).val = SmoothRealForm.pullback contMDiff_fst a.val +
      SmoothRealForm.pullback contMDiff_snd b.val := smoothRealForm_ext fun _ _ => rfl
  rw [hval, pullback_add contMDiff_diag]
  intro e z hz
  have e1 : (SmoothRealForm.pullback contMDiff_diag
      (SmoothRealForm.pullback contMDiff_fst a.val)).coeff e z = a.val.coeff e z := by
    rw [← (pullback_comp_geometricallyEq contMDiff_fst contMDiff_diag a.val) e hz]
    exact pullback_id_geometricallyEq a.val e hz
  have e2 : (SmoothRealForm.pullback contMDiff_diag
      (SmoothRealForm.pullback contMDiff_snd b.val)).coeff e z = b.val.coeff e z := by
    rw [← (pullback_comp_geometricallyEq contMDiff_snd contMDiff_diag b.val) e hz]
    exact pullback_id_geometricallyEq b.val e hz
  rw [coeff_add, e1, e2, ClosedRealOneOneForm.coeff_add]

/-- **The mass of the diagonal current**: for the product Kähler form `ω̃ = p₁^*ω + p₂^*ω`,
`∫_Δ ω̃ⁿ = 2ⁿ ∫_X ωⁿ` (`diag^*ω̃ = 2ω`; used in `bou:uniform-diagonal-domination`). -/
theorem mass_diagonalCurrent [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (w : KahlerBackground n X) :
    mass (prodKahlerBackground w w) (diagonalCurrent w) = 2 ^ n * (kahlerVolume w).real univ := by
  have hgeom : ((pullbackTestLM contMDiff_diag n (kahlerTest (prodKahlerBackground w w) n) :
      testSpace n X n) : SmoothRealForm n X (2 * n)).GeometricallyEq
        (((2 : ℝ) ^ n • kahlerTest w n : testSpace n X n) : SmoothRealForm n X (2 * n)) := by
    intro e z hz
    change (SmoothRealForm.pullback contMDiff_diag
        (formPow (prodForm w.form w.form).val n)).coeff e z =
      ((2 : ℝ) ^ n • formPow w.form.val n).coeff e z
    rw [pullback_formPow, formPow_coeff, (pullback_diag_prodForm_geometricallyEq w.form w.form) e hz,
      ClosedRealOneOneForm.coeff_add, ← two_smul ℝ (w.form.val.coeff e z), formPower_smul,
      coeff_smul, formPow_coeff]
  rw [mass, diagonalCurrent_apply,
    IsPositive.apply_eq_of_geometricallyEq (isPositive_integrationCurrent w) hgeom, map_smul,
    smul_eq_mul, ← mass_integrationCurrent w]
  rfl

end DiagonalMass

end

end SGPT.Foundations.Analysis.Pending.DiagonalFibreIntegration
