import SGPT.Unibranch.FNAInterface
import SGPT.Unibranch.ComplexSpaceFornaessNarasimhan
import SGPT.Unibranch.NativeNov16LocalAmbientPSHPullback

/-!
# From complex spaces to embedded analytic sets and back

Source `thm:FN` (`appendix_unibranch.tex`), implication (2) ⇒ (1), following
[FN80, Theorem 5.3.1] ("the theorem is local, so that we may suppose that `X` is a closed complex
subvariety of `Δⁿ`"). This file contains the two translations between the complex space `X`
(`SGPT.Unibranch.SourceReducedComplexSpace`) and the embedded analytic sets of [FN80] §5.

**Hypothesis (2) of `thm:FN` gives `WP` on every local embedding.** For a local embedding
`e : V ≅ (Ω, C) ↪ Ω ⊆ ℂ^N` of `X` (`LocalEmbedding`), `carrierSet e = C ⊆ ℂ^N` and
`carrierFunction e φ` is `φ` read on `C` (extended by `-∞` off `C`). A holomorphic map
`f : Δ → ℂ^N` of the unit disc with values in `C` is a morphism of complex spaces `Δ → X`
(`carrierDisc`: the reduced structure of `C` lets `f` factor through the model `(Ω, C)`), whose
pull-back of `φ` is `carrierFunction e φ ∘ f` on `Δ` (`discPullback_carrierDisc`). Hence
(`isWeaklyPSHOn_carrierFunction`) if `φ` is upper semicontinuous, `< +∞`, and `f^*φ` is
subharmonic for every disc `f : Δ → X` with `f^*φ ≢ -∞`, then `carrierFunction e φ ∈ WP(C)`
in the sense of [FN80] (`FNL.IsWeaklyPSHOn`).

*Reconciliation of the two notions of subharmonicity.* [FN80] count `≡ -∞` as subharmonic,
the book (`def:subhar1`, `SGPT.PSH.SubharmonicOn`) does not and only tests discs with
`f^*φ ≢ -∞`. On the (connected) unit disc a pull-back is either `≢ -∞`, and then subharmonic by
hypothesis, or `≡ -∞`, and then it trivially satisfies the disc criterion
`SGPT.Foundations.Analysis.DiscPshOn` used by `FNL.IsWeaklyPSHOn`. So the two hypotheses agree.

**A local ambient extension gives condition 2 of `def:unibranch:L105`.** If near a point of the
carrier `φ` is the restriction of an ambient function `u` satisfying the disc criterion
(possibly `≡ -∞`), then `φ` satisfies `IsLocallyAmbientPSHAt` there
(`isLocallyAmbientPSHAt_of_extension`): restrict `e` to a ball, stabilize the embedding by one
coordinate (`NativeNov16LocalAmbientPSHPullback.stabilizedEmbedding`,
`C ↪ Ω × ℂ, c ↦ (c, 0)`) and use `max(u(z), log |w|²)`, which is in `PSH(Ω × ℂ)` (it is
`≢ -∞`), connected ambient, and equal to `u` on `C × {0}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps

namespace SGPT.Unibranch.FNA

noncomputable section

open SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace}

/-! ### The carrier of a local embedding as a subset of `ℂ^N` -/

/-- The carrier `C ⊆ Ω ⊆ ℂ^N` of a local embedding, as a subset of `ℂ^N`. -/
def carrierSet (e : LocalEmbedding X) : Set (ComplexModel e.dim) :=
  Subtype.val '' (e.carrier : Set e.ambient)

theorem val_mem_carrierSet (e : LocalEmbedding X) (c : e.carrier) : c.val.val ∈ carrierSet e :=
  ⟨c.val, c.property, rfl⟩

theorem exists_of_mem_carrierSet {e : LocalEmbedding X} {z : ComplexModel e.dim}
    (hz : z ∈ carrierSet e) : ∃ c : e.carrier, c.val.val = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨⟨y, hy⟩, rfl⟩

theorem mem_ambient_of_mem_carrierSet {e : LocalEmbedding X} {z : ComplexModel e.dim}
    (hz : z ∈ carrierSet e) : z ∈ e.ambient := by
  obtain ⟨y, -, rfl⟩ := hz
  exact y.property

/-- The carrier is cut out locally by holomorphic equations in the ambient open set. -/
theorem hasLocalEquationsOn_carrierSet (e : LocalEmbedding X) :
    FNR.HasLocalEquationsOn (carrierSet e) (e.ambient : Set (ComplexModel e.dim)) :=
  FNR.hasLocalEquationsOn_of_isComplexAnalyticSubset e.analytic

open Classical in
/-- A function on `X`, read on the carrier `C ⊆ ℂ^N` of a local embedding `e` (and `-∞` off
`C`). -/
def carrierFunction (e : LocalEmbedding X) (φ : X.obj.left → EReal) :
    ComplexModel e.dim → EReal := fun z =>
  if h : ∃ c : e.carrier, c.val.val = z then φ (e.toPoint h.choose) else ⊥

theorem carrierFunction_apply (e : LocalEmbedding X) (φ : X.obj.left → EReal) (c : e.carrier) :
    carrierFunction e φ c.val.val = φ (e.toPoint c) := by
  have h : ∃ c' : e.carrier, c'.val.val = c.val.val := ⟨c, rfl⟩
  rw [carrierFunction, dif_pos h]
  have hc : h.choose = c := Subtype.ext (Subtype.ext h.choose_spec)
  rw [hc]

/-- Upper semicontinuity passes from `X` to the carrier of a local embedding. -/
theorem upperSemicontinuousOn_carrierFunction (e : LocalEmbedding X) {φ : X.obj.left → EReal}
    (husc : UpperSemicontinuous φ) :
    UpperSemicontinuousOn (carrierFunction e φ) (carrierSet e) := by
  intro z hz y hy
  obtain ⟨c, rfl⟩ := exists_of_mem_carrierSet hz
  let ι : e.carrier → ComplexModel e.dim := fun c => c.val.val
  have hι : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange : range ι = carrierSet e := by
    ext w
    constructor
    · rintro ⟨c', rfl⟩
      exact val_mem_carrierSet e c'
    · intro hw
      obtain ⟨c', rfl⟩ := exists_of_mem_carrierSet hw
      exact ⟨c', rfl⟩
  rw [carrierFunction_apply] at hy
  have h1 : ∀ᶠ c' in 𝓝 c, φ (e.toPoint c') < y :=
    (e.isOpenEmbedding_toPoint.continuous.tendsto c).eventually (husc _ y hy)
  have hmap := hι.map_nhds_eq c
  rw [hrange] at hmap
  change ∀ᶠ w in 𝓝[carrierSet e] (ι c), carrierFunction e φ w < y
  rw [← hmap]
  exact eventually_map.mpr (h1.mono fun c' hc' => by
    change carrierFunction e φ c'.val.val < y
    rw [carrierFunction_apply]
    exact hc')

/-! ### Holomorphic discs in the carrier are holomorphic discs in `X` -/

theorem coord_mem_ball_of_mem_unitDiscOpens {z : ComplexModel 1} (hz : z ∈ unitDiscOpens) :
    z 0 ∈ ball (0 : ℂ) 1 :=
  mem_ball_zero_iff.mpr (norm_le_of_mem_unitDiscOpens hz)

/-- The map `Δ → Ω` underlying a holomorphic disc in the carrier. -/
def discMap (e : LocalEmbedding X) (f : ℂ → ComplexModel e.dim)
    (hfC : MapsTo f (ball (0 : ℂ) 1) (carrierSet e)) : unitDiscOpens → e.ambient :=
  fun z => ⟨f (z.val 0),
    mem_ambient_of_mem_carrierSet (hfC (coord_mem_ball_of_mem_unitDiscOpens z.property))⟩

theorem discMap_mem_carrier (e : LocalEmbedding X) (f : ℂ → ComplexModel e.dim)
    (hfC : MapsTo f (ball (0 : ℂ) 1) (carrierSet e)) (z : unitDiscOpens) :
    discMap e f hfC z ∈ e.carrier := by
  obtain ⟨y, hy, hyz⟩ := hfC (coord_mem_ball_of_mem_unitDiscOpens z.property)
  have : discMap e f hfC z = y := Subtype.ext hyz.symm
  rw [this]
  exact hy

theorem contMDiff_discMap (e : LocalEmbedding X) (f : ℂ → ComplexModel e.dim)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hfC : MapsTo f (ball (0 : ℂ) 1) (carrierSet e)) :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel e.dim) ∞ (discMap e f hfC) := by
  apply (ContMDiff.subtypeVal_comp_iff e.ambient _).mp
  have h0 : ContDiffOn ℂ ∞ (fun z : ComplexModel 1 => f (z 0))
      (unitDiscOpens : Set (ComplexModel 1)) :=
    (hf.contDiffOn isOpen_ball).comp
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff.contDiffOn
      (fun z hz => coord_mem_ball_of_mem_unitDiscOpens hz)
  have h1 : ContMDiffOn 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel e.dim) ∞
      (fun z : ComplexModel 1 => f (z 0)) (unitDiscOpens : Set (ComplexModel 1)) :=
    contMDiffOn_iff_contDiffOn.mpr h0
  exact h1.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

/-- A holomorphic map `f` of the unit disc into the carrier of a local embedding `e`, as a
morphism of complex spaces `Δ → X`. -/
def carrierDisc (e : LocalEmbedding X) (f : ℂ → ComplexModel e.dim)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hfC : MapsTo f (ball (0 : ℂ) 1) (carrierSet e)) : unitDisc ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (contMDiff_discMap e f hf hfC) (C := (univ : Set unitDiscOpens))
      (D := e.carrier) (fun z _ => discMap_mem_carrier e f hfC z) ≫ e.map)
    (by
      rw [Category.assoc, e.overPoint]
      exact actualSubspaceMap_point _ _))

/-- The pull-back of `φ` by the disc `carrierDisc e f` is `carrierFunction e φ ∘ f` on `Δ`. -/
theorem discPullback_carrierDisc (e : LocalEmbedding X) (f : ℂ → ComplexModel e.dim)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hfC : MapsTo f (ball (0 : ℂ) 1) (carrierSet e)) (φ : X.obj.left → EReal) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) 1) :
    discPullback (carrierDisc e f hf hfC) φ t = carrierFunction e φ (f t) := by
  have h := discCoordinate_mem_unitDiscOpens ht
  obtain ⟨c, hc⟩ := exists_of_mem_carrierSet (hfC ht)
  have hq : (actualSubspaceMap (contMDiff_discMap e f hf hfC) (C := (univ : Set unitDiscOpens))
      (D := e.carrier) (fun z _ => discMap_mem_carrier e f hfC z)).base
        (⟨⟨discCoordinate t, h⟩, trivial⟩ : (univ : Set unitDiscOpens)) = c := by
    apply Subtype.ext
    apply Subtype.ext
    change f (discCoordinate t 0) = c.val.val
    rw [discCoordinate_apply_zero, hc]
  unfold discPullback modelPullback
  rw [dif_pos h, ← hc, carrierFunction_apply, ← hq]
  rfl

/-- **Hypothesis (2) of `thm:FN` gives `WP` of [FN80] on every local embedding.** If `φ` is
upper semicontinuous with values in `[-∞, ∞)` and `f^*φ` is subharmonic for every holomorphic
disc `f : Δ → X` with `f^*φ ≢ -∞`, then on the carrier `C ⊆ ℂ^N` of every local embedding the
function `φ` is weakly plurisubharmonic: `φ ∘ f` satisfies the disc criterion (subharmonic or
`≡ -∞`) for every holomorphic `f : Δ → C`. -/
theorem isWeaklyPSHOn_carrierFunction (e : LocalEmbedding X) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤) (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :
    FNL.IsWeaklyPSHOn (carrierSet e) (carrierFunction e φ) := by
  refine ⟨?_, upperSemicontinuousOn_carrierFunction e husc, ?_⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := exists_of_mem_carrierSet hz
    rw [carrierFunction_apply]
    exact hne_top _
  · intro f hf hfC
    have heq : EqOn (discPullback (carrierDisc e f hf hfC) φ)
        (fun t => carrierFunction e φ (f t)) (ball (0 : ℂ) 1) :=
      fun t ht => discPullback_carrierDisc e f hf hfC φ ht
    by_cases hne : ∃ t ∈ ball (0 : ℂ) 1, discPullback (carrierDisc e f hf hfC) φ t ≠ ⊥
    · exact (hdisc _ hne).discPshOn.congr heq
    · simp only [not_exists, not_and, not_not] at hne
      refine (SGPT.Foundations.Analysis.discPshOn_const (⊥ : EReal) bot_ne_top
        (ball (0 : ℂ) 1)).congr ?_
      intro t ht
      change (⊥ : EReal) = carrierFunction e φ (f t)
      rw [← hne t ht]
      exact heq ht

/-! ### Local ambient extensions give condition 2 of `def:unibranch:L105` -/

/-- **A local ambient extension satisfying the disc criterion gives condition 2 of
`def:unibranch:L105`.** If near the point `c` of the carrier of a local embedding `e` the
function `φ` is the restriction of an ambient function `u` satisfying the disc criterion on an
open set `W` (plurisubharmonic or `≡ -∞`), then `φ` is locally the restriction of an element of
`PSH(Ω')` for a closed immersion of a neighbourhood of `e(c)` into a domain `Ω'`. -/
theorem isLocallyAmbientPSHAt_of_extension {φ : X.obj.left → EReal} (e : LocalEmbedding X)
    (c : e.carrier) {W : Set (ComplexModel e.dim)} (hW : IsOpen W) (hcW : c.val.val ∈ W)
    {u : ComplexModel e.dim → EReal} (hu : SGPT.Foundations.Analysis.DiscPshOn u W)
    (hrep : ∀ z : e.carrier, z.val.val ∈ W → φ (e.toPoint z) = u z.val.val) :
    X.IsLocallyAmbientPSHAt φ (e.toPoint c) := by
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (hW.inter e.ambient.isOpen) c.val.val ⟨hcW, c.val.property⟩
  let T : Opens (ComplexModel e.dim) := ⟨ball c.val.val r, isOpen_ball⟩
  have hT : T ≤ e.ambient := fun z hz => (hball hz).2
  let b := e.restrict T hT
  have huT : SGPT.Foundations.Analysis.DiscPshOn u T := hu.mono fun z hz => (hball hz).1
  have hconn : IsConnected (T : Set (ComplexModel e.dim)) :=
    (convex_ball _ _).isConnected ⟨c.val.val, mem_ball_self hr⟩
  let F : ComplexModel (e.dim + 1) → EReal := fun z =>
    NativeNov16AmbientPSHStabilization.potential u (PrimeNov16StabilizedAnalyticModel.split e.dim z)
  have hF : SGPT.PSH.PSHOn F (PrimeNov16StabilizedAnalyticModel.domain T) := by
    rw [PrimeNov16StabilizedAnalyticModel.domain_eq_split_preimage]
    exact NativeNov16AmbientPSHStabilization.psh_comp_equiv
      (NativeNov16AmbientPSHStabilization.psh_univ huT hconn.nonempty)
      (PrimeNov16StabilizedAnalyticModel.split e.dim)
  let cT : b.carrier := ⟨⟨c.val.val, mem_ball_self hr⟩, c.property⟩
  have hbc : b.toPoint cT = e.toPoint c := by
    rw [LocalEmbedding.restrict_toPoint]
    rfl
  refine ⟨NativeNov16LocalAmbientPSHPullback.stabilizedEmbedding b, ?_,
    PrimeNov16StabilizedAnalyticModel.domain_connected T hconn, F, hF, ?_⟩
  · refine ⟨(PrimeNov16StabilizedAnalyticModel.inclusion b.ambient b.carrier
      b.analytic).hom.left.base cT, ?_⟩
    rw [NativeNov16LocalAmbientPSHPullback.stabilized_toPoint,
      NativeNov16LocalAmbientPSHPullback.projection_inclusion_point]
    exact hbc
  · intro z
    let q : b.carrier :=
      (PrimeNov16StabilizedAnalyticModel.projection b.ambient b.carrier b.analytic).hom.left.base z
    have hz : PrimeNov16StabilizedAnalyticModel.split e.dim z.val.val = (q.val.val, 0) :=
      PrimeNov16StabilizedAnalyticModel.split_carrier_coordinates b.ambient b.carrier b.analytic z
    rw [NativeNov16LocalAmbientPSHPullback.stabilized_toPoint]
    change φ (b.toPoint q) =
      NativeNov16AmbientPSHStabilization.potential u
        (PrimeNov16StabilizedAnalyticModel.split e.dim z.val.val)
    rw [hz, NativeNov16AmbientPSHStabilization.zero, LocalEmbedding.restrict_toPoint]
    exact hrep _ (hball q.val.property).1

end

end SGPT.Unibranch.FNA
