import SGPT.GAGA.SerreM5Main
import SGPT.GAGA.H0SConeGraph
import SGPT.Foundations.Analysis.Pending.CartanCoherenceInterface
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology

/-!
# Chow's theorem: closed analytic subsets of `ℙᴺ` are algebraic


Let `S ⊆ ℙᴺ` be a closed complex analytic subset (`IsComplexAnalyticSubset` in the affine charts
of `ℙᴺ`, e.g. a closed complex submanifold).  Its affine cone `Ŝ ⊆ ℂ^{N+1}` is, off the vertex,
an analytic subset of the complex manifold `ℂ^{N+1} ∖ 0` (`isComplexAnalyticSubset_coneTrace`):
in the chart `{Z_i ≠ 0}` it is cut out by the equations of `S` composed with the affine ratios.
By Cartan's coherence theorem (`SGPT.Foundations.Analysis`'s `cartanCoherence`), the ideal sheaf
`coneIdeal S` of germs vanishing on `Ŝ` is coherent on `ℂ^{N+1} ∖ 0`
(`isCoherentOn_coneIdeal`); it is invariant under `ℂ^*` (`isConeInvariant_coneIdeal`).
Serre's GAGA for ideal sheaves of `𝒪_{ℙᴺ}` (the `SGPT.GAGA.PN.gaga_ideal`, part of
the verified `lma:GAGA`) then gives:

**Chow's theorem** (`chow`).  For every large `m` there are finitely many homogeneous
polynomials `P_k` of degree `m` which generate the ideal sheaf of `Ŝ` at every point of
`ℂ^{N+1} ∖ 0` (so `S` is the analytification of the reduced closed subscheme `V(P)` of `ℙᴺ`),
and `S = {x ∈ ℙᴺ : P_k(x) = 0 for all k}`.

`chow_of_isClosedSubmanifold` is the case of closed complex submanifolds.
-/

set_option autoImplicit false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core SGPT.GAGA.PN SGPT.GAGA.H0S
open SGPT.Foundations.Analysis.Pending.CoherentIdealColon
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.ChowBl

variable {N : ℕ}

/-! ### Holomorphy on the model space -/

/-- On the model space, `SGPT.Foundations.Analysis`'s holomorphy at a point is `HolAt`. -/
theorem holomorphicAt_model_iff {m : ℕ} {g : ComplexModel m → ℂ} {y : ComplexModel m} :
    HolomorphicAt m g y ↔ HolAt g y := by
  simp only [HolomorphicAt, HolAt, mdifferentiableAt_iff_differentiableAt]

/-! ### The affine cone over an analytic subset is analytic off the vertex -/

/-- The cone is cut out, in the chart `{Z_i ≠ 0}`, by the equations of `S` composed with the
affine ratios. -/
def conePresentation {S : Set (ComplexProjectiveSpace N)} {z : ComplexModel (N + 1)}
    (hz : WithLp.ofLp z ≠ 0)
    (P : ComplexAnalyticPresentationAt (n := N) S (mk (WithLp.ofLp z) hz)) :
    ComplexAnalyticPresentationAt (n := N + 1) (affineCone S) z where
  generatorCount := P.generatorCount
  generator l w := P.generator l (affineRatio (chartIndex (mk (WithLp.ofLp z) hz)) (WithLp.ofLp w))
  coordinateNeighborhood := {w | w (chartIndex (mk (WithLp.ofLp z) hz)) ≠ 0} ∩
    (fun w : ComplexModel (N + 1) =>
      affineRatio (chartIndex (mk (WithLp.ofLp z) hz)) (WithLp.ofLp w)) ⁻¹'
        P.coordinateNeighborhood
  isOpen_coordinateNeighborhood := by
    set i := chartIndex (mk (WithLp.ofLp z) hz)
    have ho : IsOpen {w : ComplexModel (N + 1) | w i ≠ 0} :=
      isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) i).continuous continuous_const
    refine ContinuousOn.isOpen_inter_preimage ?_ ho P.isOpen_coordinateNeighborhood
    intro w hw
    exact ((differentiableAt_affineRatio i (v := WithLp.ofLp w) hw).comp w
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (N + 1) => ℂ)).differentiableAt
      ).continuousAt.continuousWithinAt
  center_mem_coordinateNeighborhood := by
    set i := chartIndex (mk (WithLp.ofLp z) hz)
    have hsrc := mem_affineChart_chartIndex (mk (WithLp.ofLp z) hz)
    have hzi : (WithLp.ofLp z) i ≠ 0 := (mk_mem_affineChart_source_iff i hz).mp hsrc
    have hc := P.center_mem_coordinateNeighborhood
    change affineChart i (mk (WithLp.ofLp z) hz) ∈ P.coordinateNeighborhood at hc
    rw [affineChart_mk i hz hzi] at hc
    exact ⟨hzi, hc⟩
  coordinateNeighborhood_subset_target := by
    intro w _
    exact (show w ∈ (OpenPartialHomeomorph.refl (ComplexModel (N + 1))).target from trivial)
  generator_holomorphic l := by
    set i := chartIndex (mk (WithLp.ofLp z) hz)
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ComplexModel (N + 1) => affineRatio i (WithLp.ofLp w)) w :=
      (differentiableAt_affineRatio i (v := WithLp.ofLp w) hw.1).comp w
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (N + 1) => ℂ)).differentiableAt
    have h2 := (P.generator_holomorphic l).differentiableAt
      (P.isOpen_coordinateNeighborhood.mem_nhds hw.2)
    exact (h2.comp w h1).differentiableWithinAt
  zeroLocus := by
    intro y _ hyN
    set i := chartIndex (mk (WithLp.ofLp z) hz) with hi
    have e : (complexChartAt (n := N + 1) z).val y = y := rfl
    rw [e] at hyN ⊢
    obtain ⟨hyi, hyP⟩ := hyN
    rw [mem_affineCone_iff hyi]
    have hsrc : affinePoint i (affineRatio i (WithLp.ofLp y)) ∈
        (complexChartAt (n := N) (mk (WithLp.ofLp z) hz)).val.source :=
      affinePoint_mem_source i _
    have hch : (complexChartAt (n := N) (mk (WithLp.ofLp z) hz)).val
        (affinePoint i (affineRatio i (WithLp.ofLp y))) = affineRatio i (WithLp.ofLp y) :=
      affineChart_affinePoint i _
    have key := P.zeroLocus hsrc (by rw [hch]; exact hyP)
    rw [hch] at key
    exact key

/-- **The affine cone over an analytic subset of `ℙᴺ` is analytic off the vertex**: a local
presentation at every nonzero point. -/
theorem nonempty_conePresentation {S : Set (ComplexProjectiveSpace N)}
    (hS : IsComplexAnalyticSubset (n := N) S) {z : ComplexModel (N + 1)} (hz : z ≠ 0) :
    Nonempty (ComplexAnalyticPresentationAt (n := N + 1) (affineCone S) z) := by
  have hz' : WithLp.ofLp z ≠ 0 := fun h => hz (by simpa using congrArg (WithLp.toLp 2) h)
  exact ⟨conePresentation hz' (hS _).some⟩

variable (N) in
/-- `ℂ^{N+1} ∖ 0`, as an open subset (a complex manifold). -/
def punctured : TopologicalSpace.Opens (ComplexModel (N + 1)) :=
  ⟨{z | z ≠ 0}, isOpen_ne⟩

/-- The trace of the cone on `ℂ^{N+1} ∖ 0` is an analytic subset of that manifold. -/
theorem isComplexAnalyticSubset_coneTrace {S : Set (ComplexProjectiveSpace N)}
    (hS : IsComplexAnalyticSubset (n := N) S) :
    IsComplexAnalyticSubset (n := N + 1) ((↑) ⁻¹' affineCone S : Set (punctured N)) :=
  fun x => ⟨AnalyticSubsetOpens.presentationPreimageVal x
    (nonempty_conePresentation hS (show (x : ComplexModel (N + 1)) ≠ 0 from x.2)).some⟩

/-- **Cartan**: the ideal of the cone is coherent on `ℂ^{N+1} ∖ 0`. -/
theorem isCoherent_coneTrace {S : Set (ComplexProjectiveSpace N)}
    (hS : IsComplexAnalyticSubset (n := N) S) :
    (vanishingIdeal (n := N + 1) ((↑) ⁻¹' affineCone S : Set (punctured N))).IsCoherent :=
  CartanCoherenceInterface.cartanCoherence _ (isComplexAnalyticSubset_coneTrace hS)

/-! ### The ideal sheaf of the cone in the germ-module model of lane SERRE-CORE -/

/-- The ideal sheaf of germs on `ℂ^{N+1}` vanishing on the affine cone over `S`: the germ of
`a` at `y` lies in it iff `a` is holomorphic near `y` and vanishes on the cone near `y`.  On
`ℂ^{N+1} ∖ 0` this is the pull-back to the cone of the ideal sheaf `𝓘_S ⊆ 𝒪_{ℙᴺ}`. -/
def coneIdeal (S : Set (ComplexProjectiveSpace N)) : GermModule (ConeSpace N) Unit where
  mem y a := HolAt (a ()) y ∧ ∀ᶠ z in 𝓝 y, z ∈ affineCone S → a () z = 0

theorem mem_coneIdeal {S : Set (ComplexProjectiveSpace N)} {y : ConeSpace N}
    {a : Unit → ConeSpace N → ℂ} :
    (coneIdeal S).mem y a ↔ HolAt (a ()) y ∧ ∀ᶠ z in 𝓝 y, z ∈ affineCone S → a () z = 0 :=
  Iff.rfl

/-- Functions on `ℂ^{N+1} ∖ 0`, holomorphic in the sense of `SGPT.Foundations.Analysis`, extend
to functions holomorphic at the same point. -/
theorem holAt_extendOpens {g : punctured N → ℂ} {x : punctured N}
    (hg : HolomorphicAt (N + 1) g x) : HolAt (extendOpens (punctured N) g) (x : ComplexModel (N + 1)) :=
  holomorphicAt_model_iff.mp ((holomorphicAt_iff_extendOpens (punctured N)).mp hg)

theorem holomorphicAt_comp_val {f : ComplexModel (N + 1) → ℂ} {x : punctured N}
    (hf : HolAt f (x : ComplexModel (N + 1))) :
    HolomorphicAt (N + 1) (f ∘ Subtype.val : punctured N → ℂ) x :=
  (holomorphicAt_comp_val_iff (punctured N)).mpr (holomorphicAt_model_iff.mpr hf)

/-- **The ideal sheaf of the cone is coherent** on `ℂ^{N+1} ∖ 0` (Cartan's theorem). -/
theorem isCoherentOn_coneIdeal {S : Set (ComplexProjectiveSpace N)}
    (hS : IsComplexAnalyticSubset (n := N) S) :
    (coneIdeal S).IsCoherentOn (puncture (ConeSpace N)) := by
  intro y hy
  set A : Set (punctured N) := (↑) ⁻¹' affineCone S with hA
  obtain ⟨U, hU, hxU, K, s, hsd, hsI⟩ := isCoherent_coneTrace hS ⟨y, hy⟩
  have hsmem : ∀ x' ∈ U, ∀ k, (vanishingIdeal (n := N + 1) A).mem x' (s k) := by
    intro x' hx' k
    refine (hsI x' hx' (s k)).mpr (isInSpanAt_range_iff.mpr ⟨holomorphicAt_of_mdifferentiableOn
      hU (hsd k) hx', fun l p => if l = k then 1 else 0, fun l => ?_, ?_⟩)
    · exact holomorphicAt_comp_val (f := fun _ => (if l = k then 1 else 0 : ℂ))
        (Eventually.of_forall fun _ => differentiableAt_const _)
    · exact Eventually.of_forall fun p => by simp
  refine ⟨Subtype.val '' U, (punctured N).isOpen.isOpenMap_subtype_val U hU, ⟨_, hxU, rfl⟩,
    Fin K, inferInstance, fun k _ => extendOpens (punctured N) (s k), ?_, ?_⟩
  · rintro k - _ ⟨x', hx', rfl⟩
    exact (holAt_extendOpens (holomorphicAt_of_mdifferentiableOn hU (hsd k) hx')).self_of_nhds
      |>.differentiableWithinAt
  · rintro _ ⟨x', hx', rfl⟩ a
    constructor
    · rintro ⟨ha, hvan⟩
      have hmem : (vanishingIdeal (n := N + 1) A).mem x' (a () ∘ Subtype.val) := by
        refine ⟨holomorphicAt_comp_val ha, ?_⟩
        exact (eventually_nhds_val_iff (punctured N)).mp hvan
      obtain ⟨-, c, hc, hca⟩ := isInSpanAt_range_iff.mp ((hsI x' hx' _).mp hmem)
      refine ⟨fun k => extendOpens (punctured N) (c k), fun k => holAt_extendOpens (hc k),
        fun j => ?_⟩
      have h1 := (eventually_nhds_val_iff (punctured N) (x := x')
        (P := fun z => ∀ hz : z ∈ punctured N, a () z =
          ∑ k, c k ⟨z, hz⟩ * s k ⟨z, hz⟩)).mpr (hca.mono fun p hp _ => hp)
      filter_upwards [h1, eventually_mem_opens (punctured N) x'] with z hz hzO
      cases j
      simp only [extendOpens, dif_pos hzO]
      exact hz hzO
    · rintro ⟨c, hc, hca⟩
      have hg : ∀ k, HolAt (extendOpens (punctured N) (s k)) (x' : ComplexModel (N + 1)) :=
        fun k => holAt_extendOpens (holomorphicAt_of_mdifferentiableOn hU (hsd k) hx')
      have hsum := hca ()
      refine ⟨?_, ?_⟩
      · have : HolAt (fun z => ∑ k, c k z * extendOpens (punctured N) (s k) z)
            (x' : ComplexModel (N + 1)) :=
          HolAt.fintype_sum fun k => (hc k).mul (hg k)
        exact this.congr hsum.symm
      · have hv : ∀ k, ∀ᶠ z in 𝓝 (x' : ComplexModel (N + 1)), ∀ hz : z ∈ punctured N,
            (⟨z, hz⟩ : punctured N) ∈ A → s k ⟨z, hz⟩ = 0 := fun k =>
          (eventually_nhds_val_iff (punctured N) (x := x')
            (P := fun z => ∀ hz : z ∈ punctured N, (⟨z, hz⟩ : punctured N) ∈ A →
              s k ⟨z, hz⟩ = 0)).mpr ((hsmem x' hx' k).2.mono fun p hp _ => hp)
        filter_upwards [hsum, eventually_all.2 hv, eventually_mem_opens (punctured N) x']
          with z hz hzv hzO hzS
        rw [hz]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp only [extendOpens, dif_pos hzO]
        rw [hzv k hzO hzS, mul_zero]

/-- The ideal sheaf of the cone is invariant under `ℂ^*`. -/
theorem isConeInvariant_coneIdeal (S : Set (ComplexProjectiveSpace N)) :
    IsConeInvariant (coneIdeal S) := by
  refine isConeInvariant_of_imp fun w _ c hc f hf => ?_
  obtain ⟨hhol, hvan⟩ := hf
  refine ⟨?_, ?_⟩
  · have h1 : HolAt (f ()) (c⁻¹ • (c • w)) := by rw [inv_smul_smul₀ hc]; exact hhol
    exact h1.comp (continuous_const_smul c⁻¹) fun _ => differentiableAt_id.const_smul c⁻¹
  · have hcont : Tendsto (fun z : ConeSpace N => c⁻¹ • z) (𝓝 (c • w)) (𝓝 w) := by
      have := ((continuous_const_smul c⁻¹).tendsto (c • w))
      rwa [inv_smul_smul₀ hc] at this
    filter_upwards [hcont.eventually hvan] with z hz hzS
    exact hz (smul_mem_affineCone c⁻¹ hzS)

/-! ### Chow's theorem -/

/-- The homogeneous lift of a point of `ℙᴺ`, as a vector of the cone. -/
def coneRep (x : ComplexProjectiveSpace N) : ConeSpace N := WithLp.toLp 2 x.rep

theorem coneRep_ne_zero (x : ComplexProjectiveSpace N) : coneRep x ≠ 0 := by
  intro h
  exact x.rep_ne_zero (by simpa [coneRep] using congrArg WithLp.ofLp h)

theorem mem_affineCone_coneRep_iff {S : Set (ComplexProjectiveSpace N)}
    (x : ComplexProjectiveSpace N) : coneRep x ∈ affineCone S ↔ x ∈ S := by
  constructor
  · intro h
    have := h x.rep_ne_zero
    change mk x.rep _ ∈ S at this
    rwa [mk_rep] at this
  · intro hx h
    change mk x.rep h ∈ S
    rwa [mk_rep]

theorem polyTuple_coneRep (P : MvPolynomial (Fin (N + 1)) ℂ) (x : ComplexProjectiveSpace N) :
    polyTuple P () (coneRep x) = MvPolynomial.eval x.rep P := rfl

/-- **Chow's theorem** (closed analytic subsets of `ℙᴺ` are algebraic).  Let `S ⊆ ℙᴺ` be a
closed complex analytic subset.  For every large `m` there are finitely many homogeneous
polynomials `P_k` of degree `m` such that

* the `P_k` generate the ideal sheaf of the affine cone over `S` at every point of
  `ℂ^{N+1} ∖ 0`: `S` is the analytification of the (reduced) closed subscheme of `ℙᴺ` defined by
  the `P_k`;
* `S` is the common zero locus of the `P_k`. -/
theorem chow {S : Set (ComplexProjectiveSpace N)} (hS : IsComplexAnalyticSubset (n := N) S) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ (μ : Type) (_ : Fintype μ) (P : μ → MvPolynomial (Fin (N + 1)) ℂ),
      (∀ k, (P k).IsHomogeneous m) ∧
      (coneIdeal S).GeneratedOn (puncture (ConeSpace N)) (fun k => polyTuple (P k)) ∧
      S = {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0} := by
  obtain ⟨m₀, hm⟩ := gaga_ideal (isCoherentOn_coneIdeal hS) (isConeInvariant_coneIdeal S)
  refine ⟨m₀, fun m hm' => ?_⟩
  obtain ⟨μ, hμ, P, hP, hgen⟩ := hm m hm'
  refine ⟨μ, hμ, P, hP, hgen, ?_⟩
  ext x
  have hZ : coneRep x ∈ puncture (ConeSpace N) := coneRep_ne_zero x
  constructor
  · intro hx k
    have hk := (hgen.gen_mem hZ k).2.self_of_nhds ((mem_affineCone_coneRep_iff x).mpr hx)
    rwa [polyTuple_coneRep] at hk
  · intro h0
    have h0' : ∀ k, MvPolynomial.eval x.rep (P k) = 0 := h0
    by_contra hx
    have hcl : IsClosed (affineCone S) := isClosed_affineCone hS.isClosed
    have hnot : coneRep x ∉ affineCone S := fun h => hx ((mem_affineCone_coneRep_iff x).mp h)
    have hone : (coneIdeal S).mem (coneRep x) (fun _ _ => 1) := by
      refine ⟨Eventually.of_forall fun _ => differentiableAt_const _, ?_⟩
      filter_upwards [hcl.isOpen_compl.mem_nhds hnot] with z hz hzS
      exact absurd hzS hz
    obtain ⟨c, -, hc⟩ := (hgen.2 _ hZ _).mp hone
    have h1 := (hc ()).self_of_nhds
    simp only [polyTuple_coneRep, h0', mul_zero, Finset.sum_const_zero] at h1
    exact one_ne_zero h1

/-- **Chow's theorem for closed complex submanifolds of `ℙᴺ`.** -/
theorem chow_of_isClosedSubmanifold {S : Set (ComplexProjectiveSpace N)}
    (hS : BlowupSequences.IsClosedSubmanifold N S) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ (μ : Type) (_ : Fintype μ) (P : μ → MvPolynomial (Fin (N + 1)) ℂ),
      (∀ k, (P k).IsHomogeneous m) ∧
      (coneIdeal S).GeneratedOn (puncture (ConeSpace N)) (fun k => polyTuple (P k)) ∧
      S = {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0} :=
  chow (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hS)

end SGPT.GAGA.ChowBl
