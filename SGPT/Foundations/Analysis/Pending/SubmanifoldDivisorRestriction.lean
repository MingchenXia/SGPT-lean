import SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The identity principle on a connected complex manifold, and divisors restricted to a
submanifold

Source: Copy-4, `sec:fixed-data`; the classical content is the identity theorem (Griffiths--Harris
Chapter 0 §1).  `Pending.RiemannExtension` has it for a preconnected open subset of a complex
normed space; this file lifts it to a connected complex manifold in the only form the
modification side needs, and uses it to turn an ambient effective divisor into a divisor on a
closed connected submanifold.

## The two steps

* `eq_univ_of_isLocallyZeroSet_of_interior_nonempty`: if `Z ⊆ M` is, near every point, the zero
  set of one holomorphic function, and `Z` has nonempty interior, then `Z = M`.  Proof: `interior
  Z` is open, and it is closed because in a chart ball around a point of its closure the local
  equation vanishes near an interior point, hence on the whole ball
  (`RiemannExtension.eventually_eq_zero_of_eventually_eq_zero`).  Connectedness finishes.

* `isInvertibleAlong_of_isInvertible`: an invertible ideal whose zero locus does not contain the
  closed connected submanifold `W` is invertible **along** `W`.  This is the gap between the
  ambient `IsInvertible` (whose generator may vanish identically on `W`) and the
  `IsInvertibleAlong` of `Pending.RestrictedIdealQuotient`; bridging it is exactly an identity
  principle *on `W`*, which is why `W` had to be made a manifold first.

Combining with `Pending.SubmanifoldIdealRestriction`, an effective divisor `D` on `X` with
`¬ W ⊆ Supp D` restricts to an effective divisor on `↥W`.  In Copy-4 this is how `G_m` and `G_M`
arise: `FactorizationData` (`Pending.RelativePrincipalization`:167-179) hands out exactly an `H` (:173) with
`¬ strictTransform f W ⊆ H.support` (:176).
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.SubmanifoldDivisorRestriction

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.RestrictedIdealQuotient
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction

noncomputable section

/-! ### The identity principle on a connected complex manifold -/

section Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
  [IsComplexManifold m M]

variable (m) in
/-- `Z` is, near every point, cut out by a single holomorphic equation. -/
def IsLocallyZeroSet (Z : Set M) : Prop :=
  ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ h : M → ℂ,
    MDifferentiableOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) h U ∧ ∀ y ∈ U, (y ∈ Z ↔ h y = 0)

/-- A map holomorphic on an open set of `M` is complex differentiable in the preferred chart. -/
theorem differentiableOn_comp_chartSymm {U : Set M} (hU : IsOpen U)
    {h : M → ℂ} (hhol : MDifferentiableOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) h U) (p : M)
    {B : Set (ComplexModel m)}
    (hB : B ⊆ (chartAt (ComplexModel m) p).target ∩
      (chartAt (ComplexModel m) p).symm ⁻¹' U) :
    DifferentiableOn ℂ (fun z => h ((chartAt (ComplexModel m) p).symm z)) B := by
  intro z hz
  set e := chartAt (ComplexModel m) p with he
  have hze : z ∈ e.target := (hB hz).1
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) e.symm z :=
    ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
      (e.open_target.mem_nhds hze)).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) h (e.symm z) :=
    (hhol _ (hB hz).2).mdifferentiableAt (hU.mem_nhds (hB hz).2)
  exact (mdifferentiableAt_iff_differentiableAt.mp (h2.comp z h1)).differentiableWithinAt

/-- **Identity principle on a connected complex manifold.**  A set which is locally the zero set
of a single holomorphic equation and has nonempty interior is everything. -/
theorem eq_univ_of_isLocallyZeroSet_of_interior_nonempty [ConnectedSpace M] {Z : Set M}
    (hZ : IsLocallyZeroSet m Z) (hne : (interior Z).Nonempty) : Z = univ := by
  have hclosed : IsClosed (interior Z) := by
    rw [← closure_subset_iff_isClosed]
    intro p hp
    obtain ⟨U, hU, hpU, h, hhol, hiff⟩ := hZ p
    set e := chartAt (ComplexModel m) p with he
    have hpe : p ∈ e.source := mem_chart_source _ p
    set V : Set (ComplexModel m) := e.target ∩ e.symm ⁻¹' (U ∩ e.source) with hV
    have hVopen : IsOpen V := e.isOpen_inter_preimage_symm (hU.inter e.open_source)
    have hpV : e p ∈ V := by
      refine ⟨e.map_source hpe, ?_⟩
      rw [mem_preimage, e.left_inv hpe]
      exact ⟨hpU, hpe⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVopen (e p) hpV
    have hballsub : ball (e p) ε ⊆ e.target ∩ e.symm ⁻¹' U := fun z hz =>
      ⟨(hball hz).1, (hball hz).2.1⟩
    have hdiff : DifferentiableOn ℂ (fun z => h (e.symm z)) (ball (e p) ε) :=
      differentiableOn_comp_chartSymm hU hhol p hballsub
    -- a point of `interior Z` inside the chart ball
    set N : Set M := e.source ∩ e ⁻¹' ball (e p) ε with hN
    have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
    have hpN : p ∈ N := ⟨hpe, by rw [mem_preimage]; exact mem_ball_self hε⟩
    obtain ⟨q, hqN, hqZ⟩ := mem_closure_iff.1 hp N hNopen hpN
    have hqU : q ∈ U := by
      have := (hball hqN.2).2.1
      rwa [e.left_inv hqN.1] at this
    -- `h` vanishes near `q`
    have hq0 : ∀ᶠ y in 𝓝 q, h y = 0 := by
      filter_upwards [mem_interior_iff_mem_nhds.1 hqZ, hU.mem_nhds hqU] with y hyZ hyU
      exact (hiff y hyU).1 hyZ
    have hq0' : ∀ᶠ z in 𝓝 (e q), h (e.symm z) = 0 := by
      have hcont : ContinuousAt e.symm (e q) :=
        (e.continuousOn_symm).continuousAt (e.open_target.mem_nhds (e.map_source hqN.1))
      have : e.symm (e q) = q := e.left_inv hqN.1
      exact hcont.eventually (this ▸ hq0)
    -- the identity theorem on the ball
    have hall := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero isOpen_ball
      (convex_ball (e p) ε).isPreconnected hdiff hqN.2 hq0'
    have hp0 : ∀ᶠ z in 𝓝 (e p), h (e.symm z) = 0 := hall _ (mem_ball_self hε)
    have hp0' : ∀ᶠ y in 𝓝 p, h y = 0 := by
      have hcont : ContinuousAt (e : M → ComplexModel m) p :=
        e.continuousOn.continuousAt (e.open_source.mem_nhds hpe)
      filter_upwards [hcont.eventually hp0, e.open_source.mem_nhds hpe] with y hy hysrc
      rwa [e.left_inv hysrc] at hy
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [hp0', hU.mem_nhds hpU] with y hy hyU
    exact (hiff y hyU).2 hy
  have hclopen : IsClopen (interior Z) := ⟨hclosed, isOpen_interior⟩
  have := hclopen.eq_univ hne
  exact eq_univ_of_univ_subset (this ▸ interior_subset)

/-! ### The zero locus of an invertible ideal -/

/-- Inside a set where `𝔞` is generated by the single function `h`, the zero locus of `𝔞` is
`{h = 0}`. -/
theorem mem_zeroLocus_iff_of_generator {𝔞 : GermIdeal m M} {U : Set M} (hU : IsOpen U)
    {h : M → ℂ} (hhol : MDifferentiableOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) h U)
    (hgen : ∀ y ∈ U, ∀ g, 𝔞.mem y g ↔ IsInSpanAt (n := m) (· = h) y g)
    {y : M} (hy : y ∈ U) : y ∈ 𝔞.zeroLocus ↔ h y = 0 := by
  constructor
  · intro hyZ
    refine hyZ h ((hgen y hy h).mpr ?_)
    exact isInSpanAt_of_eq_mul rfl
      (SubmanifoldIdealRestriction.holomorphicAt_of_mdifferentiableOn hU hhol hy)
      (holomorphicAt_const 1) (by simp)
  · intro hh g hg
    obtain ⟨-, c, -, hceq⟩ := isInSpanAt_eq_iff.mp ((hgen y hy g).mp hg)
    rw [hceq.self_of_nhds]
    simp [hh]

end Manifold

/-! ### From ambient invertibility to invertibility along the submanifold -/

section Submanifold

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]
  (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))

include hval in
/-- The part of `W` lying over the zero locus of an invertible ideal is, near every point of
`↥W`, cut out by one holomorphic equation on `↥W` — the restricted local generator. -/
theorem isLocallyZeroSet_val_preimage_zeroLocus {𝔩 : GermIdeal n X} (h𝔩 : 𝔩.IsInvertible) :
    IsLocallyZeroSet k (Subtype.val ⁻¹' 𝔩.zeroLocus : Set W) := by
  intro p
  obtain ⟨U, hU, hpU, h, hhol, -, hgen⟩ := h𝔩 p.1
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hpU,
    fun q : W => h q.1, ?_, ?_⟩
  · intro q hq
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n)
        (Subtype.val : W → X) q := (hval q).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h q.1 :=
      (hhol q.1 hq).mdifferentiableAt (hU.mem_nhds hq)
    exact (h2.comp q h1).mdifferentiableWithinAt
  · intro q hq
    exact mem_zeroLocus_iff_of_generator hU hhol hgen hq

include hval in
/-- **The bridge.**  An invertible ideal whose zero locus does not contain the connected
submanifold `W` is invertible **along** `W`: if the local generator vanished on a nonempty
relatively open piece of `W`, the identity principle on the connected manifold `↥W` would force
`W ⊆ zeroLocus 𝔩`.  This is the step that needs `↥W` to be a manifold, and it is what supplies
`Pending.RestrictedIdealQuotient`'s `IsInvertibleAlong`, which had no producer before. -/
theorem isInvertibleAlong_of_isInvertible [ConnectedSpace W] {𝔩 : GermIdeal n X}
    (h𝔩 : 𝔩.IsInvertible) (hWZ : ¬ W ⊆ 𝔩.zeroLocus) : IsInvertibleAlong n W 𝔩 := by
  intro x _
  obtain ⟨U, hU, hxU, h, hhol, hnv, hgen⟩ := h𝔩 x
  refine ⟨U, hU, hxU, h, hhol, ?_, hgen⟩
  intro V hV hVU hVW
  by_contra hcon
  push Not at hcon
  have hsub : (Subtype.val ⁻¹' V : Set W) ⊆ Subtype.val ⁻¹' 𝔩.zeroLocus := fun q hq =>
    (mem_zeroLocus_iff_of_generator hU hhol hgen (hVU hq)).mpr (hcon q.1 ⟨hq, q.2⟩)
  have hne : (interior (Subtype.val ⁻¹' 𝔩.zeroLocus : Set W)).Nonempty := by
    obtain ⟨y, hyV, hyW⟩ := hVW
    exact ⟨⟨y, hyW⟩, mem_interior.mpr ⟨Subtype.val ⁻¹' V, hsub,
      hV.preimage continuous_subtype_val, hyV⟩⟩
  have huniv := eq_univ_of_isLocallyZeroSet_of_interior_nonempty
    (isLocallyZeroSet_val_preimage_zeroLocus hval h𝔩) hne
  refine hWZ fun y hy => ?_
  have hmem : (⟨y, hy⟩ : W) ∈ (Subtype.val ⁻¹' 𝔩.zeroLocus : Set W) := huniv ▸ mem_univ _
  exact hmem

end Submanifold

/-! ### The divisor on the submanifold -/

section Divisor

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **An effective divisor whose support does not contain a closed connected submanifold `W`
restricts to an effective divisor on `W`.**  `hk : k ≤ n` is not a hypothesis: it is carried by
`RegularAtDim` at any point of the (nonempty, because connected) `W`.

This is the shape in which Copy-4's Step 1 needs the statement: `FactorizationData`
(`Pending.RelativePrincipalization`:167-179) hands out exactly an `IsClosedConnectedSubmanifold n
(strictTransform n f W) k`, an `H : EffectiveDivisor n Y'` and `¬ strictTransform n f W ⊆
H.support`. -/
theorem exists_chartedSpace_restrictDivisor {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) (D : EffectiveDivisor n X)
    (hWD : ¬ W ⊆ D.support) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs ∧ InclusionHolomorphicFor n k W cs ∧
        SubmanifoldIdealRestriction.RestrictIsInvertibleFor n k W cs D.ideal := by
  obtain ⟨y, hy⟩ := hW.2.1.nonempty
  have hk : k ≤ n := (hW.2.2 y hy).1
  refine ⟨chartedSpace hk hW.2.2, isComplexManifold_chartedSpace hk hW.2.2,
    contMDiff_val hk hW.2.2, ?_⟩
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  exact SubmanifoldIdealRestriction.isInvertible_restrictIdeal (contMDiff_val hk hW.2.2)
    (isInvertibleAlong_of_isInvertible (contMDiff_val hk hW.2.2) D.isInvertible hWD)

/-- `IsInvertibleAlong` for a closed connected submanifold, stated without the subtype: the
producer `Pending.RestrictedIdealQuotient` was missing. -/
theorem isInvertibleAlong_of_isClosedConnectedSubmanifold {W : Set X} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) {𝔩 : GermIdeal n X} (h𝔩 : 𝔩.IsInvertible)
    (hWZ : ¬ W ⊆ 𝔩.zeroLocus) : IsInvertibleAlong n W 𝔩 := by
  obtain ⟨y, hy⟩ := hW.2.1.nonempty
  have hk : k ≤ n := (hW.2.2 y hy).1
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  exact isInvertibleAlong_of_isInvertible (contMDiff_val hk hW.2.2) h𝔩 hWZ

end Divisor

end

end SGPT.Foundations.Analysis.Pending.SubmanifoldDivisorRestriction
