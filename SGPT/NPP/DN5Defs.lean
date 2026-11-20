import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.NPP.DN3RadialWeight
import SGPT.NPP.DN2SmoothingInterface

/-!
# The global fibre map `F` and the joint smoothing `Ψ` (definitions)

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 1, lines 156–214).  This file contains
**definitions only**; their properties are proved in `SGPT.NPP.DN5*`.

## The fibre map (FPT Step 1, last part, with flat chart maps)

FPT glues the jet maps `F_ν(x, ζ) = κ_ν⁻¹(J^ν(Dκ_ν(x) ζ))` of a finite atlas by an inductive
convex combination.  Following lane DN3 (`DN3/notes.md`, §2) we glue the *flat* chart maps
`F_ν(x, ζ) = κ_ν⁻¹(κ_ν(x) + Dκ_ν(x) ζ)`: the only properties used later are that `F` is smooth,
holomorphic in `ζ`, `F(x, 0) = x` and `D_ζ F(x, 0) = id`, and convex combinations (with weights
depending on `x` only) of fibrewise holomorphic maps with the same `1`-jet along the zero section
again have these properties.

A tangent vector is represented by its coordinates in a chart: `fibreMap A e z ξ` is the point
`F(x, ζ)` for the base point `x = e⁻¹ z` and the tangent vector `ζ` with `e`-coordinates `ξ`.  The
construction is made simultaneously for all charts `e` of the atlas, by the same formula, so the
compatibility `fibreMap A e z ξ = fibreMap A e' (τ z) (Dτ(z) ξ)` (`τ` the coordinate change) is a
theorem rather than a choice.  The gluing data (`FibreAtlas`) are a finite family of atlas charts
`κ_i` with chart-smooth cutoffs `ϑ_i ∈ [0, 1]`, `tsupport ϑ_i ⊆ source κ_i`, such that the
interiors of the sets `{ϑ_i = 1}` cover `Y`; one gluing step (`fibreStep`) is FPT's formula
`F̂_k = κ_k⁻¹((1 - ϑ_k) κ_k ∘ F̂_{k-1} + ϑ_k κ_k ∘ F_k)` on `tsupport ϑ_k` and `F̂_k = F̂_{k-1}`
elsewhere.

## The smoothing

`Ψ_g(x, t) = ∫ g(F(x, t ζ)) χ(|ζ|²_ω) dζ / ∫ χ(|ζ|²_ω) dζ` (FPT's definition, with the
Lebesgue measure of the coordinates of `T_x Y` in a chart; dividing by the mass of the kernel makes
the quotient independent of the chart, see `SGPT.NPP.DN5Smoothing`).  Here `χ` is the radial weight
`SGPT.NPP.DN3.chi` of FPT (normalized by `∫ χ(|ζ|²) dζ = 1` on `ℂⁿ`) and
`|ζ|²_ω = π ω(ζ, Jζ)` (`fibreNormSq`): in a frame `L` with `ω(L·, L·) = flatForm`
(`SGPT.Analysis.KahlerNormal.exists_normalizing_linear`) this is the Euclidean `‖·‖²`, so that
`Ψ_g(x, t) = ∫ g(F(x, t L s)) χ(‖s‖²) ds` (FPT's unitary coordinates of `T_x Y`).
`smoothing` reads `Ψ` in the preferred chart `complexChartAt x`; `chartSmoothing` reads it in an
arbitrary chart.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **Gluing data for the fibre map** (FPT Step 1: the finite atlas `κ_ν` and the cutoffs
`ϑ_ν`).  The interiors of `{ϑ_i = 1}` cover `Y`. -/
structure FibreAtlas (N : ℕ) (Y : Type*) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] where
  /-- Number of charts. -/
  card : ℕ
  /-- The charts `κ_i`. -/
  chart : Fin card → ComplexChart N Y
  /-- The cutoffs `ϑ_i`. -/
  cutoff : Fin card → Y → ℝ
  cutoff_smooth : ∀ i, ChartSmooth (n := N) (cutoff i)
  cutoff_nonneg : ∀ i y, 0 ≤ cutoff i y
  cutoff_le_one : ∀ i y, cutoff i y ≤ 1
  tsupport_subset : ∀ i, tsupport (cutoff i) ⊆ (chart i).val.source
  isCompact_tsupport : ∀ i, IsCompact (tsupport (cutoff i))
  cover : ∀ y, ∃ i, ∀ᶠ y' in 𝓝 y, cutoff i y' = 1

/-- A family of fibre maps, one coordinate expression per chart: `G e z ξ` is the image of the
tangent vector with `e`-coordinates `ξ` at the point `e⁻¹ z`. -/
abbrev FibreFamily (N : ℕ) (Y : Type*) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y] :=
  ComplexChart N Y → ComplexModel N → ComplexModel N → Y

open scoped Classical in
/-- **One gluing step** (FPT Step 1): in the chart `κ`, with the cutoff `ϑ`,
`κ(F̂(x, ζ)) = κ(x) + ζ^κ + (1 - ϑ(x)) (κ(G(x, ζ)) - κ(x) - ζ^κ)` on `tsupport ϑ` (where
`ζ^κ = D(κ ∘ e⁻¹)(z) ξ` are the `κ`-coordinates of `ζ`), i.e. the convex combination
`(1 - ϑ) κ ∘ G + ϑ κ ∘ F_κ` with the flat map `F_κ(x, ζ) = κ⁻¹(κ(x) + ζ^κ)`; `F̂ = G` off
`tsupport ϑ`. -/
def fibreStep (κ : ComplexChart N Y) (ϑ : Y → ℝ) (G : FibreFamily N Y) : FibreFamily N Y :=
  fun e z ξ =>
    if e.val.symm z ∈ tsupport ϑ then
      κ.val.symm (κ.val (e.val.symm z) + chartTransitionDerivative e κ z ξ +
        (1 - ϑ (e.val.symm z)) •
          (κ.val (G e z ξ) - κ.val (e.val.symm z) - chartTransitionDerivative e κ z ξ))
    else G e z ξ

/-- The fibre map after the first `k` gluing steps (`F̂_k`); `F̂_0(x, ζ) = x`. -/
def fibreFamilyUpTo (A : FibreAtlas N Y) : ℕ → FibreFamily N Y
  | 0 => fun e z _ => e.val.symm z
  | k + 1 =>
    if h : k < A.card then fibreStep (A.chart ⟨k, h⟩) (A.cutoff ⟨k, h⟩) (fibreFamilyUpTo A k)
    else fibreFamilyUpTo A k

/-- **The glued fibre map `F`** of FPT Step 1 (flat version, lane DN3 §2): `fibreMap A e z ξ` is
`F(e⁻¹ z, ζ)` for the tangent vector `ζ` with `e`-coordinates `ξ`. -/
def fibreMap (A : FibreAtlas N Y) : FibreFamily N Y :=
  fibreFamilyUpTo A A.card

/-- The squared Kähler length `|ξ|²_ω = π ω(ξ, Jξ)` of a tangent vector in the chart `e` at `z`
(`π` times `SGPT.NPP.DN2.chartNormSq`; it is `‖s‖²` in a frame normalizing `ω` to `flatForm`). -/
def fibreNormSq (wY : KahlerBackground N Y) (e : ComplexChart N Y) (z ξ : ComplexModel N) : ℝ :=
  Real.pi * DN2.chartNormSq wY e z ξ

/-- The radial weight of the kernel, `χ(|ξ|²_ω)`. -/
def fibreWeight (wY : KahlerBackground N Y) (e : ComplexChart N Y) (z ξ : ComplexModel N) : ℝ :=
  DN3.chi N (fibreNormSq wY e z ξ)

/-- **The smoothing read in the chart `e`**:
`Ψ^e_g(z, t) = ∫ g(F(e⁻¹ z, t ξ)) χ(|ξ|²_ω) dξ / ∫ χ(|ξ|²_ω) dξ`. -/
def chartSmoothing (wY : KahlerBackground N Y) (A : FibreAtlas N Y) (g : Y → ℝ)
    (e : ComplexChart N Y) (z : ComplexModel N) (t : ℝ) : ℝ :=
  (∫ ξ, g (fibreMap A e z (t • ξ)) * fibreWeight wY e z ξ) / ∫ ξ, fibreWeight wY e z ξ

/-- **The joint smoothing `Ψ_g(x, t)`** of FPT `lem:chern-joint-smoothing` (with the glued flat
fibre map), read in the preferred chart at `x`. -/
def smoothing (wY : KahlerBackground N Y) (A : FibreAtlas N Y) : (Y → ℝ) → Y → ℝ → ℝ :=
  fun g x t => chartSmoothing wY A g (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x) t

/-! ### Chart-level objects (for the local estimates of lanes DN4 and DN6) -/

/-- The chart-level radial mean with a general fibre map `Φ` (values in the chart) and metric
coefficient `α`: `(∫ f(Φ(z, t ξ)) χ(π α_z(ξ, iξ)) dξ) / ∫ χ(π α_z(ξ, iξ)) dξ`.  In the chart `e`,
`chartSmoothing` is `localSmoothing` with `Φ(z, ξ) = e(F(e⁻¹ z, ξ))`, `α = ω` and `f = g ∘ e⁻¹`
(`SGPT.NPP.DN5Smoothing.chartSmoothing_eq_localSmoothing`). -/
def localSmoothing (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (f : ComplexModel N → ℝ)
    (z : ComplexModel N) (t : ℝ) : ℝ :=
  (∫ ξ, f (Φ z (t • ξ)) * DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ])) /
    ∫ ξ, DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ])

/-- **A local fibre map** on an open set `O` of `ℂⁿ × ℂⁿ` (pairs `(z, ξ)` of a base point and a
tangent vector): smooth, holomorphic in `ξ`, `Φ(z, 0) = z`, `D_ξ Φ(z, 0) = id` (the properties of
`F` that FPT Steps 2–7 use, lane DN3 §2). -/
structure IsLocalFibreMap (Φ : ComplexModel N → ComplexModel N → ComplexModel N)
    (O : Set (ComplexModel N × ComplexModel N)) : Prop where
  isOpen : IsOpen O
  contDiffOn : ContDiffOn ℝ ∞ (fun q : ComplexModel N × ComplexModel N => Φ q.1 q.2) O
  holo : ∀ q ∈ O, DifferentiableAt ℂ (Φ q.1) q.2
  map_zero : ∀ z, (z, (0 : ComplexModel N)) ∈ O → Φ z 0 = z
  fderiv_zero : ∀ z, (z, (0 : ComplexModel N)) ∈ O →
    fderiv ℝ (Φ z) 0 = ContinuousLinearMap.id ℝ (ComplexModel N)

end SGPT.NPP.DN5
