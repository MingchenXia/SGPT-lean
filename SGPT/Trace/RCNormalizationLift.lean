import SGPT.Trace.TYRescomm
import SGPT.Trace.TYCorPSH
import SGPT.Unibranch.ComplexSpaceUnibranchFibers
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
import Mathlib.Topology.Separation.Connected

/-!
# The induced map of normalizations `Π̃ : W̃ → Ỹ` of `lma:rescommpullback`

Source: `chapter_trace.tex`, `lma:rescommpullback`: let `π : Z → X` be a proper bimeromorphic
morphism, `Z` a connected Kähler manifold, `W ⊆ Z`, `Y ⊆ X` irreducible analytic subsets such that
the restriction `Π : W → Y` of `π` is defined and bimeromorphic, "so that we have the following
commutative diagram" with `Π̃ : W̃ → Ỹ` the induced map of the normalizations. Then
`Π̃^* Tr_Y(φ) ∼_P Tr_W(π^*φ)` for `φ ∈ QPSH(X)` with `ν(φ, Y) = 0`.

Lane TY proved the lemma (`SGPT.Trace.TY.rescommpullback`) for any continuous `Π̃` over `π`
(`Ỹ → X` composed with `Π̃` equal to `π` composed with `W̃ → Z`), taking `Π̃` as an input. This
file proves that for the normalizations themselves (`normalizationTildeY`) such a `Π̃` exists and
is unique, and states the lemma for it.

* `exists_continuous_descent`: topological descent. If `q : A → B` is a continuous surjection from
  a compact space onto a Hausdorff space with (pre)connected fibres and `g : A → E` is continuous
  with `t ∘ g = f ∘ q` for a map `t : E → X` with finite fibres (`E` T1), then `g = h ∘ q` with
  `h` continuous: `g` maps each connected fibre of `q` into a finite fibre of `t`, hence to a
  point, and `q` is a quotient map (a closed map).
* `exists_lift_of_finite_fibres`, `exists_lift_of_finite_fibres'`: for a `TildeY` whose point map
  `Ỹ → X` has finite fibres, EVERY resolution `ι : V → X` of `Y` lifts continuously to `Ỹ`: `V` and
  the given resolution of `Ỹ` are dominated by a common resolution `V₃` (TN goal P5,
  `P5Wire.exists_common_resolutionTarget`), the lift on `V₃` descends along the modification
  `V₃ → V`, whose fibres are connected (Zariski's main theorem for a smooth target,
  `AnalyticModificationConnectedFibres.isConnected_fibre`).
* `Normalization.toX_finite`: the normalization map `Ỹ → Y` has finite fibres.
* `Normalization.exists_resolution_isPreconnected_fibre`: `W̃` has a resolution `ν : V → W̃` with
  connected fibres (the canonical resolution is a proper bimeromorphic morphism of complex spaces
  onto the normal, hence unibranch, space `W̃`; Zariski's main theorem,
  `IsProperBimeromorphic.isConnected_fiber_of_isUnibranch`).
* `exists_unique_normalizationLift`: **existence and uniqueness of `Π̃`**: there is exactly one
  continuous `Π̃ : W̃ → Ỹ` with `(Ỹ → X) ∘ Π̃ = π ∘ (W̃ → Z)`. Existence: `π ∘ ι_W` is a resolution
  of `Y` (`isResolutionOf_comp`), it lifts to `Ỹ`, and the lift descends along `ν : V → W̃`
  (connected fibres) because `Ỹ → X` has finite fibres. Uniqueness: two such maps agree after
  composing with `ν` (they lift the resolution `π ∘ ι_W` of `Y` and agree over the dense preimage
  of `Y_reg`, where `Ỹ → X` is injective), and `ν` is surjective.
* `normalizationLift`: the induced map `Π̃` (`continuous_normalizationLift`,
  `toX_normalizationLift`, `eq_normalizationLift`).
* `rescommpullback'`: **`lma:rescommpullback` with `Π̃` the induced map of normalizations**:
  there is a unique continuous `Π̃` over `π`, and for it `ν(π^*φ, W) = 0`, the readings of
  `Π̃^* Tr_Y(φ)` on the resolutions of `W̃` are trace operators of `π^*φ`, and
  `Π̃^* Tr_Y(φ) ∼_P Tr_W(π^*φ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Trace.RC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Trace.TY

/-! ### Topological descent along maps with connected fibres -/

/-- **Descent along a map with connected fibres into a space with finite fibres.** Let
`q : A → B` be a continuous surjection from a compact space onto a Hausdorff space whose fibres
are preconnected, `t : E → X` a map with finite fibres from a T1 space, and `g : A → E` a
continuous map with `t ∘ g = f ∘ q`. Then `g` factors as `h ∘ q` with `h : B → E` continuous. -/
theorem exists_continuous_descent {A B E X : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace E] [CompactSpace A] [T2Space B] [T1Space E]
    {q : A → B} (hq : Continuous q) (hqs : Function.Surjective q)
    (hfib : ∀ b, IsPreconnected (q ⁻¹' {b})) {t : E → X} (ht : ∀ x, (t ⁻¹' {x}).Finite)
    {g : A → E} (hg : Continuous g) {f : B → X} (hgf : ∀ a, t (g a) = f (q a)) :
    ∃ h : B → E, Continuous h ∧ ∀ a, h (q a) = g a := by
  have hconst : ∀ a₁ a₂, q a₁ = q a₂ → g a₁ = g a₂ := by
    intro a₁ a₂ h12
    by_contra hne
    have hpre : IsPreconnected (g '' (q ⁻¹' {q a₁})) := (hfib (q a₁)).image g hg.continuousOn
    have hnt : (g '' (q ⁻¹' {q a₁})).Nontrivial :=
      ⟨g a₁, ⟨a₁, rfl, rfl⟩, g a₂, ⟨a₂, h12.symm, rfl⟩, hne⟩
    have hsub : g '' (q ⁻¹' {q a₁}) ⊆ t ⁻¹' {f (q a₁)} := by
      rintro _ ⟨a, ha, rfl⟩
      change t (g a) = f (q a₁)
      rw [hgf a]
      exact congrArg f ha
    exact hpre.infinite_of_nontrivial hnt ((ht _).subset hsub)
  have hcomp : ∀ a, g (Function.surjInv hqs (q a)) = g a :=
    fun a => hconst _ _ (Function.surjInv_eq hqs (q a))
  refine ⟨fun b => g (Function.surjInv hqs b), ?_, hcomp⟩
  have hQ : IsQuotientMap q := hq.isClosedMap.isQuotientMap hq hqs
  rw [hQ.continuous_iff]
  have heq : (fun b => g (Function.surjInv hqs b)) ∘ q = g := funext hcomp
  rw [heq]
  exact hg

/-! ### Lifting resolutions of `Y` to `Ỹ` -/

section Lift

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- **Every resolution target of `Y` lifts to `Ỹ`** when the point map `Ỹ → X` has finite
fibres: the given resolution of `Ỹ` and `V` are dominated by a common resolution `V₃` (TN goal
P5), and the lift on `V₃` descends along the modification `V₃ → V`, whose fibres are connected. -/
theorem exists_lift_of_finite_fibres (T : TildeY Y) (hfin : ∀ x, (T.toX ⁻¹' {x}).Finite)
    (R : ResolutionTarget Y) :
    ∃ ν : R.V → T.space.obj.left, Continuous ν ∧ ∀ v, T.toX (ν v) = R.ι v := by
  obtain ⟨N₀⟩ := T.nonempty_resolution
  obtain ⟨R₃, p, p₀, hp, hp₀, hc, hc₀⟩ := P5Wire.exists_common_resolutionTarget R N₀.R
  have hfib := fun b => AnalyticModificationConnectedFibres.isConnected_fibre hp b
  have hsurj : Function.Surjective p := fun b => (hfib b).1.nonempty
  obtain ⟨h, hh, hhq⟩ := exists_continuous_descent hp.1.continuous hsurj
    (fun b => (hfib b).1.isPreconnected) hfin (N₀.continuous.comp hp₀.1.continuous) (f := R.ι)
    (fun a => by
      rw [Function.comp_apply, N₀.toX_comp, ← hc₀, hc])
  refine ⟨h, hh, fun v => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj v
  rw [hhq, Function.comp_apply, N₀.toX_comp, ← hc₀, hc]

/-- `exists_lift_of_finite_fibres` for a resolution `ι : V → X` of `Y` by a compact connected
Kähler manifold `V` of dimension `d = dim Y`. -/
theorem exists_lift_of_finite_fibres' (T : TildeY Y) (hfin : ∀ x, (T.toX ⁻¹' {x}).Finite)
    {d : ℕ} (hd : d = Y.dim) (V : Type u) [TopologicalSpace V] [ChartedSpace (ComplexModel d) V]
    [IsComplexManifold d V] [CompactSpace V] [ConnectedSpace V] (ι : V → X)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ ι) (hres : IsResolutionOf Y ι)
    (κ : KahlerBackground d V) :
    ∃ ν : V → T.space.obj.left, Continuous ν ∧ ∀ v, T.toX (ν v) = ι v := by
  subst hd
  exact exists_lift_of_finite_fibres T hfin
    { V := V
      ι := ι
      contMDiff := hι
      isResolutionOf := hres
      kahler := κ }

end Lift

/-! ### The normalization: finite fibres, connected fibres of a resolution -/

namespace Normalization

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- The point map `Ỹ → X` of the normalization has finite fibres (the normalization map is
finite). -/
theorem toX_finite (omega : KahlerBackground n X) (Y : ClosedIrreducibleAnalyticSubvariety n X)
    (x : X) : ((normalizationTildeY omega Y).toX ⁻¹' {x}).Finite := by
  by_cases hx : x ∈ Y.carrier
  · refine (KSNormalizedSubvariety.normalizationMap_finite_fibres Y.carrier Y.analytic
      ⟨x, hx⟩).subset ?_
    intro y hy
    exact Subtype.ext hy
  · convert Set.finite_empty
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro hy
    exact hx (hy ▸ (normalizationTildeY omega Y).toX_mem y)

/-- **`Ỹ` has a resolution `ν : V → Ỹ` with connected fibres** (Zariski's main theorem: the
canonical resolution is a proper bimeromorphic morphism of complex spaces onto the normal, hence
unibranch, space `Ỹ`). -/
theorem exists_resolution_isPreconnected_fibre (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ N : (normalizationTildeY omega Y).Resolution, ∀ y, IsPreconnected (N.ν ⁻¹' {y}) := by
  obtain ⟨N, F, hF, hFN⟩ := Normalization.exists_resolution_morphism omega Y
  refine ⟨N, fun y => ?_⟩
  have hc := SourceReducedComplexSpace.IsProperBimeromorphic.isConnected_fiber_of_isUnibranch hF
    (KSNormalizedSubvariety.normalization_isUnibranch Y.carrier Y.analytic) y
  have hval : Continuous
      (fun x : (OriginalNativeModification.wholeModel (n := Y.dim) N.R.V).obj.left =>
        (x : (univ : Set N.R.V)).val) := continuous_subtype_val
  have himg := hc.isPreconnected.image _ hval.continuousOn
  convert himg using 1
  ext v
  constructor
  · intro hv
    refine ⟨⟨v, mem_univ v⟩, ?_, rfl⟩
    change F.hom.left.base ⟨v, mem_univ v⟩ = y
    rw [hFN v]
    exact hv
  · rintro ⟨⟨v', hv'u⟩, hv', rfl⟩
    change N.ν v' = y
    rw [← hFN v']
    exact hv'

end Normalization

/-! ### The induced map of normalizations `Π̃ : W̃ → Ỹ` -/

section InducedMap

variable {n : ℕ} {X Z : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]

/-- **The induced map of normalizations exists and is unique** (`lma:rescommpullback`, the
diagram): for a holomorphic `π : Z → X` and irreducible analytic `W ⊆ Z`, `Y ⊆ X` such that
`Π = π|_W : W → Y` is bimeromorphic, there is exactly one continuous `Π̃ : W̃ → Ỹ` with
`(Ỹ → X) ∘ Π̃ = π ∘ (W̃ → Z)`. -/
theorem exists_unique_normalizationLift {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
    (hPi : IsBimeromorphicRestriction π W Y) (omegaX : KahlerBackground n X)
    (omegaZ : KahlerBackground n Z) :
    ∃! Pi' : (normalizationTildeY omegaZ W).space.obj.left →
        (normalizationTildeY omegaX Y).space.obj.left,
      Continuous Pi' ∧ ∀ w, (normalizationTildeY omegaX Y).toX (Pi' w) =
        π ((normalizationTildeY omegaZ W).toX w) := by
  obtain ⟨NW, hNW⟩ := Normalization.exists_resolution_isPreconnected_fibre omegaZ W
  have hres : IsResolutionOf Y (π ∘ NW.R.ι) :=
    isResolutionOf_comp hπ hPi NW.R.contMDiff NW.R.isResolutionOf
  obtain ⟨ν', hν', hν'X⟩ := exists_lift_of_finite_fibres' (normalizationTildeY omegaX Y)
    (Normalization.toX_finite omegaX Y) hPi.dim_eq NW.R.V (π ∘ NW.R.ι)
    (hπ.comp NW.R.contMDiff) hres NW.R.kahler
  obtain ⟨Pi', hPic, hPiq⟩ := exists_continuous_descent NW.continuous NW.surjective hNW
    (Normalization.toX_finite omegaX Y) hν'
    (f := fun w => π ((normalizationTildeY omegaZ W).toX w))
    (fun v => by rw [hν'X, Function.comp_apply, NW.toX_comp])
  refine ⟨Pi', ⟨hPic, fun w => ?_⟩, ?_⟩
  · obtain ⟨v, rfl⟩ := NW.surjective w
    rw [hPiq, hν'X, Function.comp_apply, NW.toX_comp]
  · rintro Pi'' ⟨hc'', h''⟩
    apply NW.surjective.injective_comp_right
    obtain ⟨B, -, hsing, -, hdense⟩ := hres.exists_isoLocus
    refine Continuous.ext_on hdense (hc''.comp NW.continuous) (hPic.comp NW.continuous) ?_
    intro v hv
    have hreg : (π ∘ NW.R.ι) v ∉ singularLocus Y := fun hs => hv (hsing hs)
    have e1 : (normalizationTildeY omegaX Y).toX (Pi'' (NW.ν v)) = (π ∘ NW.R.ι) v := by
      rw [h'', NW.toX_comp, Function.comp_apply]
    have e2 : (normalizationTildeY omegaX Y).toX (Pi' (NW.ν v)) = (π ∘ NW.R.ι) v := by
      rw [hPiq, hν'X]
    refine (normalizationTildeY omegaX Y).injOn_regular ?_ ?_ (e1.trans e2.symm)
    · change (normalizationTildeY omegaX Y).toX (Pi'' (NW.ν v)) ∉ singularLocus Y
      rw [e1]
      exact hreg
    · change (normalizationTildeY omegaX Y).toX (Pi' (NW.ν v)) ∉ singularLocus Y
      rw [e2]
      exact hreg

/-- **The induced map of normalizations `Π̃ : W̃ → Ỹ`** (`lma:rescommpullback`): the unique
continuous map with `(Ỹ → X) ∘ Π̃ = π ∘ (W̃ → Z)`. -/
def normalizationLift {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
    (hPi : IsBimeromorphicRestriction π W Y) (omegaX : KahlerBackground n X)
    (omegaZ : KahlerBackground n Z) :
    (normalizationTildeY omegaZ W).space.obj.left → (normalizationTildeY omegaX Y).space.obj.left :=
  Classical.choose (exists_unique_normalizationLift hπ hPi omegaX omegaZ).exists

variable {π : Z → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
  {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
  (hPi : IsBimeromorphicRestriction π W Y) (omegaX : KahlerBackground n X)
  (omegaZ : KahlerBackground n Z)

theorem continuous_normalizationLift : Continuous (normalizationLift hπ hPi omegaX omegaZ) :=
  (Classical.choose_spec (exists_unique_normalizationLift hπ hPi omegaX omegaZ).exists).1

/-- The square of `lma:rescommpullback` commutes: `(Ỹ → X) ∘ Π̃ = π ∘ (W̃ → Z)`. -/
theorem toX_normalizationLift (w : (normalizationTildeY omegaZ W).space.obj.left) :
    (normalizationTildeY omegaX Y).toX (normalizationLift hπ hPi omegaX omegaZ w) =
      π ((normalizationTildeY omegaZ W).toX w) :=
  (Classical.choose_spec (exists_unique_normalizationLift hπ hPi omegaX omegaZ).exists).2 w

/-- `Π̃` is the only continuous map `W̃ → Ỹ` over `π`. -/
theorem eq_normalizationLift
    {Pi' : (normalizationTildeY omegaZ W).space.obj.left →
      (normalizationTildeY omegaX Y).space.obj.left} (hPic : Continuous Pi')
    (hPi' : ∀ w, (normalizationTildeY omegaX Y).toX (Pi' w) =
      π ((normalizationTildeY omegaZ W).toX w)) :
    Pi' = normalizationLift hπ hPi omegaX omegaZ :=
  (exists_unique_normalizationLift hπ hPi omegaX omegaZ).unique ⟨hPic, hPi'⟩
    ⟨continuous_normalizationLift hπ hPi omegaX omegaZ,
      toX_normalizationLift hπ hPi omegaX omegaZ⟩

end InducedMap

/-! ### `lma:rescommpullback` for the induced map of normalizations -/

section Rescomm

variable {n : ℕ} {X Z : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z]

/-- **Source `lma:rescommpullback` for the induced map `Π̃` of normalizations.** Let
`π : Z → X` be a proper bimeromorphic morphism of compact Kähler manifolds, `W ⊆ Z`, `Y ⊆ X`
irreducible analytic subsets such that `Π = π|_W : W → Y` is bimeromorphic, and `Π̃ : W̃ → Ỹ` the
induced map of the normalizations `normalizationTildeY` (`normalizationLift`, the unique
continuous map over `π`). Let `ψ = Tr_Y(φ)` be a trace operator of `φ` along `Y` (so
`ν(φ, Y) = 0`). Then `ν(π^*φ, W) = 0`, the readings of `Π̃^*ψ` on the resolutions of `W̃` are
trace operators of `π^*φ`, and `Π̃^* Tr_Y(φ) ∼_P Tr_W(π^*φ)` for every trace operator
`Tr_W(π^*φ)` of `π^*φ` along `W`. -/
theorem rescommpullback_normalizationLift {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
    (hPi : IsBimeromorphicRestriction π W Y) (omegaX : KahlerBackground n X)
    (omegaZ : KahlerBackground n Z) {φ : X → EReal}
    {ψ : (normalizationTildeY omegaX Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omegaX Y).IsTrace φ ψ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel n Z).sourceGenericLelong (φ ∘ π) W.carrier = 0 ∧
      (∀ NW : (normalizationTildeY omegaZ W).Resolution,
        TildeY.IsTraceOn NW (φ ∘ π) ((ψ ∘ normalizationLift hπ.1 hPi omegaX omegaZ) ∘ NW.ν)) ∧
      ∀ ρ : (normalizationTildeY omegaZ W).space.obj.left → EReal,
        (normalizationTildeY omegaZ W).IsTrace (φ ∘ π) ρ →
          (normalizationTildeY omegaZ W).PEquivalent
            (ψ ∘ normalizationLift hπ.1 hPi omegaX omegaZ) ρ :=
  rescommpullback hπ hPi (normalizationTildeY omegaZ W) (normalizationTildeY omegaX Y)
    (normalizationLift hπ.1 hPi omegaX omegaZ) (continuous_normalizationLift hπ.1 hPi omegaX omegaZ)
    (toX_normalizationLift hπ.1 hPi omegaX omegaZ) omegaZ hψ

/-- **Source `lma:rescommpullback`, with the diagram**: under the hypotheses of the lemma there
is a unique continuous `Π̃ : W̃ → Ỹ` making the square `W̃ → Z`, `Ỹ → X` commute, and for it
`ν(π^*φ, W) = 0` and `Π̃^* Tr_Y(φ) ∼_P Tr_W(π^*φ)` (with the readings of `Π̃^* Tr_Y(φ)` on the
resolutions of `W̃` trace operators of `π^*φ`). -/
theorem rescommpullback' {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
    (hPi : IsBimeromorphicRestriction π W Y) (omegaX : KahlerBackground n X)
    (omegaZ : KahlerBackground n Z) {φ : X → EReal}
    {ψ : (normalizationTildeY omegaX Y).space.obj.left → EReal}
    (hψ : (normalizationTildeY omegaX Y).IsTrace φ ψ) :
    ∃ Pi' : (normalizationTildeY omegaZ W).space.obj.left →
        (normalizationTildeY omegaX Y).space.obj.left,
      Continuous Pi' ∧
      (∀ w, (normalizationTildeY omegaX Y).toX (Pi' w) = π ((normalizationTildeY omegaZ W).toX w)) ∧
      (∀ Pi'' : (normalizationTildeY omegaZ W).space.obj.left →
          (normalizationTildeY omegaX Y).space.obj.left, Continuous Pi'' →
        (∀ w, (normalizationTildeY omegaX Y).toX (Pi'' w) =
          π ((normalizationTildeY omegaZ W).toX w)) → Pi'' = Pi') ∧
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel n Z).sourceGenericLelong (φ ∘ π) W.carrier = 0 ∧
      (∀ NW : (normalizationTildeY omegaZ W).Resolution,
        TildeY.IsTraceOn NW (φ ∘ π) ((ψ ∘ Pi') ∘ NW.ν)) ∧
      ∀ ρ : (normalizationTildeY omegaZ W).space.obj.left → EReal,
        (normalizationTildeY omegaZ W).IsTrace (φ ∘ π) ρ →
          (normalizationTildeY omegaZ W).PEquivalent (ψ ∘ Pi') ρ :=
  ⟨normalizationLift hπ.1 hPi omegaX omegaZ, continuous_normalizationLift hπ.1 hPi omegaX omegaZ,
    toX_normalizationLift hπ.1 hPi omegaX omegaZ,
    fun _ hc h => eq_normalizationLift hπ.1 hPi omegaX omegaZ hc h,
    rescommpullback_normalizationLift hπ hPi omegaX omegaZ hψ⟩

end Rescomm

end SGPT.Trace.RC
