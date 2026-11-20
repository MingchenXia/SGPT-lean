import SGPT.Hodge.ConePositive
import SGPT.BDivisor.VolumeBDivisor
import SGPT.BDivisor.BlowupModelVolume
import SGPT.BDivisor.BlowupModelModifiedNef
import SGPT.BDivisor.Modification3MnLevelNef
import SGPT.BDivisor.Modification3AugmentedNef
import SGPT.BDivisor.BlowupModel2Linear

/-!
# The Euclidean topology of `H^{1,1}` in the theory of b-divisors

Blueprint `claude-hodge-top`; source Xia, *Singularities in global
pluripotential theory*, `chap:bdiv`.  With the finite dimensionality of `H^{1,1}`
(`SGPT.Hodge.finiteDimensional_realBottChern`) and the cone topology of `SGPT.Hodge.ConePositive`
the Hodge-theoretic clauses of the following environments become unconditional:

* `def:nefb` (and the remark after it): on every model carrying a Kähler form — in particular on
  every blow-up model — the project's intrinsic Euclidean topology of `H^{1,1}(Y, ℝ)` is the
  Euclidean topology (every Hausdorff vector space topology coincides with it) and is TN's
  quotient `C⁰` topology (`Modification.euclideanTopology_eq_classC0Topology`,
  `Modification.eq_euclideanTopology_of_kahler`, `ModelSystem.eq_euclideanTopology_blowup`).
* `def:augmented_nefb`: the convergence of `∑_E c_E {E}` in `H^{1,1}(X, ℝ)` is convergence for
  the Euclidean = quotient `C⁰` topology (`hasDivisorClassSum_iff_classC0`).
* `cor:mn_level_nefb`, (1) ⇒ (2), and the closedness of the modified nef cone (remark after
  `def:mnclass`), without the hypothesis `[FiniteDimensional ℝ H^{1,1}]`
  (`Siu.classModifiedNef_of_tendsto_of_connected`, `Siu.isClosed_setOf_classModifiedNef`,
  `WeilBDivisor.IsNef.classModifiedNef_of_kahler`,
  `WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup`).
* **`lma:volbdivnet`** over the book's models: for a net `(𝔻_i)` of pseudo-effective
  b-divisors converging to `𝔻`, `𝔻` is pseudo-effective, `limsup vol 𝔻_i ≤ vol 𝔻`, and
  `vol 𝔻_i → vol 𝔻` if the net is decreasing (`WeilBDivisorOn.isPseudoeffective_of_converges_blowup`,
  `WeilBDivisorOn.limsup_vol_le_blowup`, `WeilBDivisorOn.tendsto_vol_of_antitone_blowup`).
  The book's proof: `vol 𝔻_Y = lim vol 𝔻_{i,Y} ≥ limsup vol 𝔻_i` on every model (continuity of
  the volume on `H^{1,1}(Y, ℝ)`, `SGPT.Hodge.continuous_sourceClassVolume`); in the decreasing
  case `𝔻 ≤ 𝔻_i` (closedness of the pseudo-effective cone) and the volume is monotone.
* `thm:DT`, Step 1, the b-divisor half of the volume reduction:
  `vol 𝔻(T + ε_kθ) → vol 𝔻(T)` for `ε_k = 1/(k+1) ↓ 0` and a smooth semipositive `θ`
  (`currentBDivisorOn_tendsto_vol_add_blowup`, by `lma:volbdivnet` for the decreasing net
  `𝔻(T) + ε_k 𝔻(θ)`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ENNReal

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent

/-! ### `def:nefb`: the Euclidean topology on the models -/

section Topology

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- On a model carrying a Kähler form, the intrinsic Euclidean topology of `H^{1,1}(Y, ℝ)` is
TN's quotient `C⁰` topology. -/
theorem Modification.euclideanTopology_eq_classC0Topology (π : Modification n X)
    (ωY : KahlerBackground n π.carrier) :
    euclideanTopology (RealBottChern n π.carrier) = classC0Topology ωY :=
  (SGPT.Hodge.classC0Topology_eq_euclideanTopology ωY).symm

/-- **`def:nefb`, the Euclidean topology**: on a model carrying a Kähler form, every Hausdorff
vector space topology of `H^{1,1}(Y, ℝ)` is the intrinsic Euclidean topology. -/
theorem Modification.eq_euclideanTopology_of_kahler (π : Modification n X)
    (hK : Nonempty (KahlerBackground n π.carrier)) [τ : TopologicalSpace (RealBottChern n π.carrier)]
    [IsTopologicalAddGroup (RealBottChern n π.carrier)]
    [ContinuousSMul ℝ (RealBottChern n π.carrier)] [T2Space (RealBottChern n π.carrier)] :
    τ = euclideanTopology (RealBottChern n π.carrier) := by
  have := SGPT.Hodge.finiteDimensional_realBottChern hK.some
  exact eq_euclideanTopology

/-- **`def:nefb` over the book's models**: for `X` compact connected Kähler and a blow-up model
`Y`, the intrinsic Euclidean topology of `H^{1,1}(Y, ℝ)` is the quotient `C⁰` topology of every
Kähler form of `Y` and every Hausdorff vector space topology of `H^{1,1}(Y, ℝ)`. -/
theorem ModelSystem.eq_euclideanTopology_blowup (hK : Nonempty (KahlerBackground n X))
    (π : (ModelSystem.blowup n X).Model) :
    (∀ ωY : KahlerBackground n π.1.carrier,
      euclideanTopology (RealBottChern n π.1.carrier) = classC0Topology ωY) ∧
    ∀ [τ : TopologicalSpace (RealBottChern n π.1.carrier)]
      [IsTopologicalAddGroup (RealBottChern n π.1.carrier)]
      [ContinuousSMul ℝ (RealBottChern n π.1.carrier)] [T2Space (RealBottChern n π.1.carrier)],
      τ = euclideanTopology (RealBottChern n π.1.carrier) :=
  ⟨fun ωY => π.1.euclideanTopology_eq_classC0Topology ωY,
    π.1.eq_euclideanTopology_of_kahler (ModelSystem.blowup_nonempty_kahlerBackground hK π)⟩

end Topology

/-! ### `def:augmented_nefb`: convergence of divisor class series -/

section Augmented

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **`def:augmented_nefb`**: `∑_E c_E {E} = α` in the intrinsic Euclidean topology of
`H^{1,1}(X, ℝ)` is the same as in TN's quotient `C⁰` topology. -/
theorem hasDivisorClassSum_iff_classC0 (w : KahlerBackground (m + 1) X)
    (c : SGPT.PSH.GeometricPrimeCarrier (m + 1) X → ℝ) (α : RealBottChern (m + 1) X) :
    HasDivisorClassSum c α ↔
      (letI := classC0Topology w; HasSum (fun E => c E • primeDivisorClass E) α) := by
  unfold HasDivisorClassSum
  rw [SGPT.Hodge.classC0Topology_eq_euclideanTopology w]

end Augmented

/-! ### `cor:mn_level_nefb` without the finite-dimensionality hypothesis -/

section ModifiedNef

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] {hn : 0 < m + 1}

omit [ConnectedSpace X] in
/-- **The modified nef cone is closed** (remark after `def:mnclass`), unconditionally on a compact
connected Kähler manifold: limits (along any nontrivial filter, in the Euclidean topology) of
modified nef classes are modified nef. -/
theorem _root_.SGPT.Siu.classModifiedNef_of_tendsto_of_connected [ConnectedSpace X]
    (ωX : KahlerBackground (m + 1) X) {ι : Type*} {l : Filter ι} [l.NeBot]
    {α : ι → RealBottChern (m + 1) X} {β : RealBottChern (m + 1) X}
    (hα : ∀ i, Siu.ClassModifiedNefWithRespectTo ωX (α i))
    (hlim : Tendsto α l (@nhds _ (euclideanTopology (RealBottChern (m + 1) X)) β)) :
    Siu.ClassModifiedNefWithRespectTo ωX β := by
  have := SGPT.Hodge.finiteDimensional_realBottChern ωX
  exact Siu.classModifiedNef_of_tendsto ωX hα hlim

/-- **The modified nef cone is a closed set** of `H^{1,1}(X, ℝ)` (Euclidean topology). -/
theorem _root_.SGPT.Siu.isClosed_setOf_classModifiedNef (ωX : KahlerBackground (m + 1) X) :
    IsClosed[euclideanTopology (RealBottChern (m + 1) X)]
      {α : RealBottChern (m + 1) X | Siu.ClassModifiedNefWithRespectTo ωX α} := by
  let : TopologicalSpace (RealBottChern (m + 1) X) := euclideanTopology _
  rw [← closure_subset_iff_isClosed]
  intro β hβ
  set s := {α : RealBottChern (m + 1) X | Siu.ClassModifiedNefWithRespectTo ωX α}
  have hne : (comap ((↑) : s → RealBottChern (m + 1) X) (𝓝 β)).NeBot :=
    mem_closure_iff_comap_neBot.mp hβ
  exact Siu.classModifiedNef_of_tendsto_of_connected ωX (l := comap ((↑) : s → _) (𝓝 β))
    (fun i => i.2) tendsto_comap

/-- **`cor:mn_level_nefb`, (1) ⇒ (2)**, unconditionally: for a nef b-divisor `𝔻` over the compact
connected manifold `X` (`def:nefb`, all modifications), the class `𝔻_Y` on every model `Y`
carrying a Kähler form `ω_Y` is modified nef with respect to `ω_Y`. -/
theorem WeilBDivisor.IsNef.classModifiedNef_of_kahler {𝔻 : WeilBDivisor (m + 1) X hn}
    (h𝔻 : 𝔻.IsNef) (π : Modification (m + 1) X) (ωY : KahlerBackground (m + 1) π.carrier) :
    Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) := by
  have := SGPT.Hodge.finiteDimensional_realBottChern ωY
  exact h𝔻.classModifiedNef π ωY

/-- **`cor:mn_level_nefb`, (1) ⇒ (2), over the book's models**, unconditionally: for `X` compact
connected Kähler and a nef b-divisor `𝔻` over the blow-up models, every blow-up model `Y` carries
a Kähler form and `𝔻_Y` is modified nef with respect to every Kähler form of `Y`. -/
theorem WeilBDivisorOn.IsNef.forall_classModifiedNef_blowup
    (hK : Nonempty (KahlerBackground (m + 1) X)) {𝔻 : BlowupWeilBDivisor (m + 1) X hn}
    (h𝔻 : 𝔻.IsNef) (π : (ModelSystem.blowup (m + 1) X).Model) :
    Nonempty (KahlerBackground (m + 1) π.1.carrier) ∧
      ∀ ωY : KahlerBackground (m + 1) π.1.carrier,
        Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) := by
  have := SGPT.Hodge.finiteDimensional_realBottChern_blowupModel hK π
  exact h𝔻.classModifiedNef_blowup hK π

end ModifiedNef

/-! ### `lma:volbdivnet` over the book's models -/

namespace WeilBDivisorOn

section Volume

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] {hn : 0 < m + 1}

/-- **`lma:volbdivnet`, first observation**: a limit (along any nontrivial filter) of
pseudo-effective b-divisors over the book's models is pseudo-effective (the pseudo-effective cone
of every blow-up model is closed). -/
theorem isPseudoeffective_of_converges_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {ι : Type*} {l : Filter ι} [l.NeBot] {D : ι → BlowupWeilBDivisor (m + 1) X hn}
    {𝔻 : BlowupWeilBDivisor (m + 1) X hn} (hD : ∀ i, (D i).IsPseudoeffective)
    (h : Converges l D 𝔻) : 𝔻.IsPseudoeffective := by
  rw [isPseudoeffective_iff]
  intro π
  obtain ⟨ωY⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
  let : TopologicalSpace (RealBottChern (m + 1) π.1.carrier) := euclideanTopology _
  exact (SGPT.Hodge.isClosed_setOf_classPseudoeffective ωY).mem_of_tendsto (h π)
    (Eventually.of_forall fun i => (isPseudoeffective_iff (D i)).mp (hD i) π)

/-- The class volume on a blow-up model is continuous for the Euclidean topology. -/
theorem tendsto_classVolume_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    (π : (ModelSystem.blowup (m + 1) X).Model) {ι : Type*} {l : Filter ι}
    {α : ι → RealBottChern (m + 1) π.1.carrier} {β : RealBottChern (m + 1) π.1.carrier}
    (h : Tendsto α l (@nhds _ (euclideanTopology (RealBottChern (m + 1) π.1.carrier)) β)) :
    Tendsto (fun i => Modification.classVolume π.1 (α i)) l
      (𝓝 (Modification.classVolume π.1 β)) := by
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  have : BorelSpace π.1.carrier := ⟨rfl⟩
  obtain ⟨ωY⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
  exact SGPT.Hodge.tendsto_sourceClassVolume ωY h

/-- **`lma:volbdivnet`, `eq:vollimsup`**: for a net (any nontrivial filter) of pseudo-effective
b-divisors `𝔻_i` over the book's models converging to `𝔻`, `limsup vol 𝔻_i ≤ vol 𝔻`. -/
theorem limsup_vol_le_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {ι : Type*} {l : Filter ι} [l.NeBot] {D : ι → BlowupWeilBDivisor (m + 1) X hn}
    {𝔻 : BlowupWeilBDivisor (m + 1) X hn} (hD : ∀ i, (D i).IsPseudoeffective)
    (h : Converges l D 𝔻) : limsup (fun i => (D i).vol) l ≤ 𝔻.vol := by
  rw [vol_of_isPseudoeffective (isPseudoeffective_of_converges_blowup hK hD h)]
  refine le_iInf fun π => ?_
  calc limsup (fun i => (D i).vol) l
      ≤ limsup (fun i => Modification.classVolume π.1 ((D i).onModel π)) l :=
        limsup_le_limsup (Eventually.of_forall fun i => vol_le_classVolume (D i) π)
    _ = Modification.classVolume π.1 (𝔻.onModel π) :=
        (tendsto_classVolume_blowup hK π (h π)).limsup_eq

/-- On a blow-up model, `D_i - 𝔻` is pseudo-effective when `𝔻` is the limit of a decreasing net
`D_j ≤ D_i` (`i ≤ j`). -/
theorem classPseudoeffective_sub_of_antitone_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {D : ι → BlowupWeilBDivisor (m + 1) X hn} {𝔻 : BlowupWeilBDivisor (m + 1) X hn}
    (hanti : ∀ i j, i ≤ j → (D j).LE (D i)) (h : Converges atTop D 𝔻) (i : ι)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    ClassPseudoeffectiveViaPotentials ((D i).onModel π - 𝔻.onModel π) := by
  obtain ⟨ωY⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
  let : TopologicalSpace (RealBottChern (m + 1) π.1.carrier) := euclideanTopology _
  have hsub : Tendsto (fun j => (D i).onModel π - (D j).onModel π) atTop
      (𝓝 ((D i).onModel π - 𝔻.onModel π)) := by
    rw [tendsto_euclideanTopology_iff]
    intro f
    simp only [map_sub]
    exact tendsto_const_nhds.sub ((tendsto_euclideanTopology_iff.mp (h π)) f)
  exact (SGPT.Hodge.isClosed_setOf_classPseudoeffective ωY).mem_of_tendsto hsub
    ((eventually_ge_atTop i).mono fun j hj => hanti i j hj π)

/-- **`lma:volbdivnet`, decreasing nets**: for a decreasing net (`𝔻_j ≤ 𝔻_i` for `i ≤ j`) of
pseudo-effective b-divisors over the book's models converging to `𝔻`, `vol 𝔻_i → vol 𝔻`. -/
theorem tendsto_vol_of_antitone_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {D : ι → BlowupWeilBDivisor (m + 1) X hn} {𝔻 : BlowupWeilBDivisor (m + 1) X hn}
    (hD : ∀ i, (D i).IsPseudoeffective) (hanti : ∀ i j, i ≤ j → (D j).LE (D i))
    (h : Converges atTop D 𝔻) :
    Tendsto (fun i => (D i).vol) atTop (𝓝 𝔻.vol) := by
  have h𝔻 := isPseudoeffective_of_converges_blowup hK hD h
  have hle : ∀ i, 𝔻.vol ≤ (D i).vol := by
    intro i
    rw [vol_of_isPseudoeffective h𝔻, vol_of_isPseudoeffective (hD i)]
    refine iInf_mono fun π => ?_
    let : MeasurableSpace π.1.carrier := borel π.1.carrier
    have : BorelSpace π.1.carrier := ⟨rfl⟩
    obtain ⟨ωY⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
    have hx := (isPseudoeffective_iff 𝔻).mp h𝔻 π
    have hy := classPseudoeffective_sub_of_antitone_blowup hK hanti h i π
    have hmono := SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_le_add_of_pseudoeffective
      ωY hx hy
    rw [add_sub_cancel] at hmono
    exact hmono
  exact tendsto_of_le_liminf_of_limsup_le (le_liminf_of_le (h := Eventually.of_forall hle))
    (limsup_vol_le_blowup hK hD h)

end Volume

end WeilBDivisorOn

/-! ### `thm:DT`, Step 1: the volume of `𝔻(T + εθ)` -/

section DT

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

local notation "CurX" => GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))

/-- **`thm:DT`, Step 1, the b-divisor half of the volume reduction**: for a closed positive
current `T` and a closed semipositive smooth form `θ` (e.g. a Kähler form `ω`), the volumes of the
b-divisors `𝔻(T + ε_k θ)`, `ε_k = 1/(k+1)`, converge to `vol 𝔻(T)`: the b-divisors
`𝔻(T) + ε_k 𝔻(θ)` decrease to `𝔻(T)`, and `lma:volbdivnet` applies. -/
theorem currentBDivisorOn_tendsto_vol_add_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {T : CurX} (hT : SGPT.Siu.IsClosedPositiveCurrent T) (θ : ClosedRealOneOneForm (m + 1) X)
    (hθ : IsThetaPshPotential θ.val (fun _ => (0 : EReal)))
    (hk : ∀ k : ℕ, SGPT.Siu.IsClosedPositiveCurrent
      (T + (1 / ((k : ℝ) + 1)) • thetaPotentialCurrent θ.val (fun _ => 0) hθ)) :
    Tendsto (fun k : ℕ =>
        (currentBDivisorOn (ModelSystem.blowup (m + 1) X) _ (hk k)).vol) atTop
      (𝓝 (currentBDivisorOn (ModelSystem.blowup (m + 1) X) T hT).vol) := by
  set S := ModelSystem.blowup (m + 1) X
  have hω := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hθ
  have hc : ∀ k : ℕ, (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := fun k => by positivity
  have heq : ∀ (k : ℕ) (π : S.Model), (currentBDivisorOn S _ (hk k)).onModel π =
      (currentBDivisorOn S T hT).onModel π +
        (1 / ((k : ℝ) + 1)) • (currentBDivisorOn S _ hω).onModel π := by
    intro k π
    rw [currentBDivisorOn_add S hT (hω.smul (hc k)) (hk k), WeilBDivisorOn.add_onModel,
      currentBDivisorOn_smul S hω (hc k), WeilBDivisorOn.smul_onModel]
  have hDθ := (WeilBDivisorOn.isPseudoeffective_iff _).mp
    (currentBDivisorOn_isPseudoeffective S _ hω)
  apply WeilBDivisorOn.tendsto_vol_of_antitone_blowup hK
    (fun k => currentBDivisorOn_isPseudoeffective S _ (hk k))
  · intro i j hij π
    rw [heq i π, heq j π]
    have hij' : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    have he : (currentBDivisorOn S T hT).onModel π +
        (1 / ((i : ℝ) + 1)) • (currentBDivisorOn S _ hω).onModel π -
        ((currentBDivisorOn S T hT).onModel π +
          (1 / ((j : ℝ) + 1)) • (currentBDivisorOn S _ hω).onModel π) =
        (1 / ((i : ℝ) + 1) - 1 / ((j : ℝ) + 1)) • (currentBDivisorOn S _ hω).onModel π := by
      rw [sub_smul]
      abel
    rw [he]
    exact SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul (hDθ π)
      (sub_nonneg.mpr hij')
  · rw [WeilBDivisorOn.converges_iff_forall_dual]
    intro π f
    simp_rw [heq, map_add, map_smul, smul_eq_mul]
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add (h0.mul_const (f ((currentBDivisorOn S _ hω).onModel π)))

end DT

end SGPT.BDivisor
