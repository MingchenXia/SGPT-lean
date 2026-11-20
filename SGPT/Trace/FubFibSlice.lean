import SGPT.Trace.CohFubiniCoords
import SGPT.Foundations.Analysis.Pending.HiepSliceGeometry
import SGPT.Foundations.Analysis.Pending.ChartWeightedL2Transfer
import SGPT.Okounkov.TranscendentalVolIdPointDegree

/-!
# Slice charts of the fibres of a submersion onto `Δ*`, and Fubini

Infrastructure of lane FUBINI-FIB for `lma:fibIeq` (`chapter_trace.tex` lines 1166--1193;
blueprint `claude-fubini-fib.tex`, node `claude-fubini-fib:ae-reverse`).

Let `f : X → Δ*` be holomorphic on a complex manifold of dimension `b + 1`, `x ∈ X` a point where
`df` is onto, `e` the preferred chart at `x` and `Θ` coordinates adapted to `f` at `e(x)`
(`SGPT.Trace.CohFib.exists_fibre_theta`: `Θ(e x) = 0` and the last coordinate of `Θ ∘ e` is
`t - t(x)`, `t` the coordinate of `f`). For an open `P ⊆ Θ(target)` and `z ∈ Δ*`, put
`u = t(z) - t(x)` (`height`).

* `sliceFlatData`: the flattening datum of the fibre `X_z` given by the ambient chart `e` and the
  biholomorphism `w ↦ Θ(w) - u e_b` on `Θ⁻¹(P)`. Its chart belongs to the atlas of the complex
  manifold `X_z` (`SubmanifoldChartedSpace.chartedSpace`), and in it the fibre is parametrised by
  the slice `ζ ↦ e⁻¹ Θ⁻¹(ζ, u)` (`sliceFlatData_ofCoord`, `sliceFlatData_coordTarget`).
* `ae_slice_finite`: **Fubini on a polydisc** — a finite weighted integral over a polydisc of
  `ℂ^{b+1}` has finite (and a.e.-measurable) slice integrals over almost every slice
  `ℂ^b × {u}`.
* `volume_preimage_coord_sub_null`: a Lebesgue-null set of heights pulls back to a null set of
  `ℂ¹`.
* `restStalk_le_comap_of_generators`: the reverse inclusion `Rest_W 𝓘(cφ) ⊆ 𝓘(cφ|_W)` at a point
  of a closed submanifold `W` holds as soon as it holds for local generators of `𝓘(cφ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Trace.FubFib

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace SGPT.Foundations.Analysis.Pending.RankDegeneracy
  SGPT.GAGA.Coherent SGPT.Trace.DirectImg

/-! ### Slices of `ℂ^{b+1}` -/

/-- `(ζ, 0) + u e_b = (ζ, u)`. -/
theorem coordinateInclusion_add_single {b : ℕ} (ζ : ComplexModel b) (u : ℂ) :
    coordinateInclusion (b + 1) b ζ + EuclideanSpace.single (Fin.last b) u = sliceMap b u ζ := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [coordinateInclusion_apply, sliceMap]
  · simp [coordinateInclusion_apply, sliceMap, Fin.castSucc_ne_last]

/-- The standard hyperplane `ℂ^b × 0` of `ℂ^{b+1}` is `{v_b = 0}`. -/
theorem mem_complexCoordinatePlane_succ_iff {b : ℕ} (v : ComplexModel (b + 1)) :
    v ∈ complexCoordinatePlane (b + 1) b ↔ v (Fin.last b) = 0 := by
  constructor
  · intro h
    exact h _ (by simp)
  · intro h i hi
    have hi' : i = Fin.last b := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    rw [hi']
    exact h

/-- An open set contains a polydisc around each of its points. -/
theorem exists_polydiscN_subset {m : ℕ} {O : Set (ComplexModel m)} (hO : IsOpen O)
    {p : ComplexModel m} (hp : p ∈ O) : ∃ r > 0, polydiscN p r ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO p hp
  have hs : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  refine ⟨ε / (Real.sqrt m + 1), by positivity, (polydiscN_subset_ball p (by positivity) ?_).trans
    hball⟩
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith

/-! ### Fubini on a polydisc -/

/-- **Fubini on a polydisc.** If `G ≥ 0` has finite integral over the polydisc `P(p, r)` of
`ℂ^{b+1}`, then for almost every height `u` in the last disc, the slice `ζ ↦ G(ζ, u)` is
a.e.-measurable with finite integral over the polydisc `P(p', r)` of `ℂ^b`. -/
theorem ae_slice_finite {b : ℕ} (p : ComplexModel (b + 1)) (r : ℝ)
    {G : ComplexModel (b + 1) → ℝ≥0∞} (hG : AEMeasurable G (volume.restrict (polydiscN p r)))
    (hfin : ∫⁻ w in polydiscN p r, G w ≠ ⊤) :
    ∀ᵐ u ∂(volume.restrict (ball (p (Fin.last b)) r)),
      AEMeasurable (fun ζ => G (sliceMap b u ζ)) (volume.restrict (polydiscN (initCoords p) r)) ∧
        ∫⁻ ζ in polydiscN (initCoords p) r, G (sliceMap b u ζ) < ⊤ := by
  obtain ⟨hm, hint⟩ := aemeasurable_lintegral_sliceMap_prod p r hG hfin
  have h1 := hm.aestronglyMeasurable.prodMk_right
  have h2 := lintegral_prod_symm _ hm
  rw [h2] at hint
  have h3 := ae_lt_top' hm.lintegral_prod_left' hint
  filter_upwards [h1, h3] with u hu1 hu3
  exact ⟨hu1.aemeasurable, hu3⟩

/-- A Lebesgue-null set of heights `u = w₀ - a` pulls back to a null subset of `ℂ¹`. -/
theorem volume_preimage_coord_sub_null {N : Set ℂ} (hN : volume N = 0) (a : ℂ) :
    volume {w : ComplexModel 1 | w 0 - a ∈ N} = 0 := by
  have hmp : MeasurePreserving (fun w : ComplexModel 1 =>
      SGPT.Okounkov.TranscendentalVolId.complexCoordinate w - a) volume volume :=
    (measurePreserving_sub_right volume a).comp
      SGPT.Okounkov.TranscendentalVolId.measurePreserving_complexCoordinate
  exact hmp.quasiMeasurePreserving.preimage_null hN

/-! ### Points of `Δ*` -/

/-- Points of `Δ*` are determined by their coordinate. -/
theorem puncturedDisc_eq_iff {a a' : puncturedDisc} :
    a = a' ↔ (a : ComplexModel 1) 0 = (a' : ComplexModel 1) 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    ext i
    fin_cases i
    exact h

/-! ### The slice chart of a fibre -/

variable {b : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (b + 1)) X]
  [IsComplexManifold (b + 1) X] {f : X → puncturedDisc}

variable (f) in
/-- The height `u = t(z) - t(x)` of the fibre `X_z` in coordinates adapted at `x`. -/
def height (x : X) (z : puncturedDisc) : ℂ := (z : ComplexModel 1) 0 - coord f x

/-- The flattening biholomorphism `w ↦ Θ(w) - u e_b` on `Θ⁻¹(P)`. -/
def sliceFlat {p : ComplexModel (b + 1)} (Θ : LocalHolomorphicEquivAt (n := b + 1) p)
    {P : Set (ComplexModel (b + 1))} (hP : IsOpen P) (hPt : P ⊆ Θ.target) (u : ℂ) :
    OpenPartialHomeomorph (ComplexModel (b + 1)) (ComplexModel (b + 1)) where
  toFun w := Θ.toFun w - EuclideanSpace.single (Fin.last b) u
  invFun v := Θ.invFun (v + EuclideanSpace.single (Fin.last b) u)
  source := Θ.source ∩ Θ.toFun ⁻¹' P
  target := (· + EuclideanSpace.single (Fin.last b) u) ⁻¹' P
  map_source' w hw := by
    show Θ.toFun w - _ + _ ∈ P
    rw [sub_add_cancel]
    exact hw.2
  map_target' v hv := ⟨Θ.mapsTo_invFun (hPt hv), by
    show Θ.toFun (Θ.invFun _) ∈ P
    rw [Θ.right_inv _ (hPt hv)]
    exact hv⟩
  left_inv' w hw := by
    show Θ.invFun (Θ.toFun w - _ + _) = w
    rw [sub_add_cancel, Θ.left_inv w hw.1]
  right_inv' v hv := by
    show Θ.toFun (Θ.invFun _) - _ = v
    rw [Θ.right_inv _ (hPt hv), add_sub_cancel_right]
  open_source := Θ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Θ.isOpen_source hP
  open_target := hP.preimage (continuous_add_const _)
  continuousOn_toFun :=
    (Θ.toFun_holomorphic.continuousOn.mono inter_subset_left).sub continuousOn_const
  continuousOn_invFun := Θ.invFun_holomorphic.continuousOn.comp
    (continuous_add_const _).continuousOn fun _ hv => hPt hv

/-- **The slice chart of the fibre `X_z`**, as a flattening datum: the ambient chart is the
preferred chart `e` at `x` and the flattening is `w ↦ Θ(w) - u e_b` on `Θ⁻¹(P)`, `u = t(z) - t(x)`.
Its chart belongs to the atlas of the complex manifold `X_z`. -/
def sliceFlatData {x : X}
    (Θ : LocalHolomorphicEquivAt (n := b + 1) ((complexChartAt (n := b + 1) x).val x))
    (hΘt : Θ.source ⊆ (complexChartAt (n := b + 1) x).val.target)
    (hΘ : ∀ {y : X}, y ∈ (complexChartAt (n := b + 1) x).val.source →
      (complexChartAt (n := b + 1) x).val y ∈ Θ.source →
        Θ.toFun ((complexChartAt (n := b + 1) x).val y) (Fin.last b) = coord f y - coord f x)
    {P : Set (ComplexModel (b + 1))} (hP : IsOpen P) (hPt : P ⊆ Θ.target)
    {z : puncturedDisc} (q₀ : X) (hq₀ : q₀ ∈ fibre f z) : FlatData (b + 1) b X (fibre f z) where
  amb := complexChartAt (n := b + 1) x
  flat := sliceFlat Θ hP hPt (height f x z)
  differentiableOn_flat := (Θ.toFun_holomorphic.mono inter_subset_left).sub_const _
  differentiableOn_flat_symm := Θ.invFun_holomorphic.comp
    (differentiable_id.add_const _).differentiableOn fun _ hv => hPt hv
  flat_source_subset := fun _ hw => hΘt hw.1
  mem_iff := fun y hy hyΘ => by
    rw [mem_complexCoordinatePlane_succ_iff, mem_fibre]
    show f y = z ↔ (Θ.toFun _ - EuclideanSpace.single (Fin.last b) (height f x z)) (Fin.last b) = 0
    rw [PiLp.sub_apply, hΘ hy hyΘ.1, PiLp.single_apply, if_pos rfl, height,
      puncturedDisc_eq_iff]
    simp only [coord]
    constructor
    · intro h
      rw [h]
      ring
    · intro h
      linear_combination h
  base := q₀
  base_mem := hq₀

section SliceFlatData

variable {x : X} {Θ : LocalHolomorphicEquivAt (n := b + 1) ((complexChartAt (n := b + 1) x).val x)}
  {hΘt : Θ.source ⊆ (complexChartAt (n := b + 1) x).val.target}
  {hΘ : ∀ {y : X}, y ∈ (complexChartAt (n := b + 1) x).val.source →
      (complexChartAt (n := b + 1) x).val y ∈ Θ.source →
        Θ.toFun ((complexChartAt (n := b + 1) x).val y) (Fin.last b) = coord f y - coord f x}
  {P : Set (ComplexModel (b + 1))} {hP : IsOpen P} {hPt : P ⊆ Θ.target}
  {z : puncturedDisc} {q₀ : X} {hq₀ : q₀ ∈ fibre f z}

/-- In the slice chart, the fibre is parametrised by `ζ ↦ e⁻¹ Θ⁻¹(ζ, u)`. -/
theorem sliceFlatData_ofCoord (ζ : ComplexModel b) :
    (sliceFlatData Θ hΘt hΘ hP hPt q₀ hq₀).ofCoord ζ =
      (complexChartAt (n := b + 1) x).val.symm (Θ.invFun (sliceMap b (height f x z) ζ)) := by
  show (complexChartAt (n := b + 1) x).val.symm
    (Θ.invFun (coordinateInclusion (b + 1) b ζ + EuclideanSpace.single (Fin.last b) _)) = _
  rw [coordinateInclusion_add_single]

/-- The target of the slice chart is the slice of `P` at height `u`. -/
theorem sliceFlatData_coordTarget :
    (sliceFlatData Θ hΘt hΘ hP hPt q₀ hq₀).coordTarget = sliceMap b (height f x z) ⁻¹' P := by
  ext ζ
  show coordinateInclusion (b + 1) b ζ + EuclideanSpace.single (Fin.last b) _ ∈ P ↔ _
  rw [coordinateInclusion_add_single]
  rfl

/-- The domain of the slice chart, in `X`. -/
theorem sliceFlatData_ambSource :
    (sliceFlatData Θ hΘt hΘ hP hPt q₀ hq₀).ambSource =
      (complexChartAt (n := b + 1) x).val.source ∩
        (complexChartAt (n := b + 1) x).val ⁻¹' (Θ.source ∩ Θ.toFun ⁻¹' P) :=
  rfl

end SliceFlatData

/-! ### Reduction to local generators -/

section Generators

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi in
/-- **Reduction to generators.** Let `W` be a closed submanifold of dimension `k`, `q ∈ W`, and
let `s₁, …, s_N` generate `𝓘(cφ)` at `q`. If every restriction `sᵢ|_W` lies in `𝓘(cφ|_W)` at `q`,
then `(Rest_W 𝓘(cφ))_q ⊆ 𝓘(cφ|_W)_q` (transported to `𝒪_{X,q}/𝓘_{W,q}` by
`structureStalkEquiv`). -/
theorem restStalk_le_comap_of_generators {W : Set M} (hk : k ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (hW : BlowupSequences.IsClosedSubmanifold n W) {φ : M → EReal} {c : ℝ} (q : W) {N : ℕ}
    (s : Fin N → M → ℂ) (hs : ∀ i, HolomorphicAt n (s i) q.1)
    (hI : ∀ g, (multiplierIdeal (n := n) c φ).mem q.1 g ↔
      IsInSpanAt (n := n) (· ∈ range s) q.1 g)
    (hJ : letI := chartedSpace hk hreg
      ∀ i, (multiplierIdeal (n := k) c (fun p : W => φ p.1)).mem q (s i ∘ Subtype.val)) :
    letI := chartedSpace hk hreg
    restStalk (multiplierIdeal (n := n) c φ) (submanifoldSubspace hW) q.1 ≤
      Ideal.comap (structureStalkEquiv hk hreg hW q)
        (stalkIdeal (multiplierIdeal (n := k) c (fun p : W => φ p.1)) q) := by
  let := chartedSpace hk hreg
  have := isComplexManifold_chartedSpace hk hreg
  rw [restStalk, Ideal.map_le_iff_le_comap, stalkIdeal_eq_span _ s hs hI, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_comap, structureStalkEquiv_mk, restrictGerm_mk]
  exact SGPT.NAPotential.GAGAMult.mk_mem_stalkIdeal _ (hJ i)

end Generators

/-! ### The local almost-everywhere reverse inclusion -/

open SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi SGPT.Trace.CohFib
  SGPT.Foundations.Analysis.Pending.ChartWeightedL2 in
/-- **The reverse inclusion along almost every fibre, near a point.** Let `f : X → Δ*` be
holomorphic with surjective differential at `x`, `φ` quasi-psh and `c > 0`. There are an open
`V ∋ x` and a Lebesgue-null set `N ⊆ ℂ` of heights such that for every `z ∈ Δ*` with
`t(z) - t(x) ∉ N`, for every structure of complex manifold of dimension `b` on `X_z` given by
`RegularAtDim` and every `q ∈ X_z ∩ V`, `(Rest_{X_z} 𝓘(cφ))_q ⊆ 𝓘(cφ|_{X_z})_q`.

Proof: generators `sᵢ` of `𝓘(cφ)` near `x` (Nadel); in adapted coordinates `Θ` the weighted
integrals of the `sᵢ` are finite on a polydisc `P` (change of variables); by Fubini almost every
slice integral is finite; the slice at height `u = t(z) - t(x)` is the slice chart of `X_z`
(`sliceFlatData`), so `sᵢ|_{X_z} ∈ 𝓘(cφ|_{X_z})` at the points of `X_z ∩ V` (chart
independence), and the reverse inclusion follows from the generators. -/
theorem exists_local_reverse
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel 1) ∞ f)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := b + 1) φ) {c : ℝ} (hc : 0 < c)
    {x : X} (hD : Function.Surjective (chartDeriv (complexChartAt (n := b + 1) x)
      (complexChartAt (n := 1) (f x)) f x)) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ N : Set ℂ, volume N = 0 ∧
      ∀ z : puncturedDisc, height f x z ∉ N →
        ∀ (hreg : ∀ y ∈ fibre f z, RegularAtDim (n := b + 1) (fibre f z) y b) (hk : b ≤ b + 1)
          (hW : BlowupSequences.IsClosedSubmanifold (b + 1) (fibre f z)) (q : fibre f z),
          q.1 ∈ V →
            letI := chartedSpace hk hreg
            restStalk (multiplierIdeal (n := b + 1) c φ) (submanifoldSubspace hW) q.1 ≤
              Ideal.comap (structureStalkEquiv hk hreg hW q)
                (stalkIdeal (multiplierIdeal (n := b) c (fun p : fibre f z => φ p.1)) q) := by
  classical
  set e := complexChartAt (n := b + 1) x with he
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := exists_fibre_theta hf hD
  obtain ⟨U, hU, hxU, N, s, hs, hspan⟩ :=
    GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      (Nat.succ_pos b) hφ hc x
  -- the generators lie in `𝓘(cφ)` at `x`
  have hsx : ∀ i, (multiplierIdeal (n := b + 1) c φ).mem x (s i) := fun i =>
    (hspan x hxU (s i)).2 ⟨holomorphicAt_of_mdifferentiableOn hU (hs i) hxU, 1, fun _ => s i,
      fun _ _ => 1, fun _ => ⟨i, rfl⟩, fun _ => holomorphicAt_const 1,
      Eventually.of_forall fun y => by simp⟩
  -- transfer to the adapted coordinates `Θ`
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have h0t : (0 : ComplexModel (b + 1)) ∈ Θ.target := by
    rw [← hΘ0]
    exact Θ.mapsTo_toFun Θ.center_mem_source
  have hinv0 : Θ.invFun 0 = e.val x := by
    rw [← hΘ0]
    exact Θ.left_inv _ Θ.center_mem_source
  have husc : UpperSemicontinuous φ := hφ.upperSemicontinuous
  have hcontT : ContinuousOn (fun w => e.val.symm (Θ.invFun w)) Θ.target :=
    e.val.continuousOn_symm.comp Θ.invFun_holomorphic.continuousOn fun w hw =>
      hΘt (Θ.mapsTo_invFun hw)
  set φΘ : ComplexModel (b + 1) → EReal := fun w => chartFunction φ e (Θ.invFun w) with hφΘ
  set F : Fin N → ComplexModel (b + 1) → ℂ := fun i w => s i (e.val.symm (Θ.invFun w)) with hF
  have hφΘusc : UpperSemicontinuousOn φΘ Θ.target :=
    (husc.upperSemicontinuousOn univ).comp hcontT (mapsTo_univ _ _)
  have hσ : ContDiffOn ℝ 1 Θ.toFun Θ.source :=
    ((contDiffOn_of_differentiableOn_complex Θ.toFun_holomorphic
      Θ.isOpen_source).restrict_scalars ℝ).of_le (by simp)
  have hMI : ∀ i, MultiplierIntegrableAt φΘ c (F i) 0 volume := by
    intro i
    have h := (hsx i).2
    rw [← hinv0] at h
    exact multiplierIntegrableAt_comp Θ.isOpen_target Θ.isOpen_source Θ.invFun_holomorphic hσ
      Θ.mapsTo_invFun Θ.mapsTo_toFun Θ.right_inv Θ.left_inv (fun _ _ => rfl) hφΘusc hc.ne' h0t h
  choose W hWo hW0 hWd hWL using fun i => (hMI i).2
  -- a polydisc `P` on which all weighted integrals are finite
  set O : Set (ComplexModel (b + 1)) :=
    (Θ.target ∩ (fun w => e.val.symm (Θ.invFun w)) ⁻¹' U) ∩ ⋂ i, W i with hOdef
  have hO : IsOpen O :=
    (hcontT.isOpen_inter_preimage Θ.isOpen_target hU).inter (isOpen_iInter_of_finite hWo)
  have h0O : (0 : ComplexModel (b + 1)) ∈ O := by
    refine ⟨⟨h0t, ?_⟩, mem_iInter.2 hW0⟩
    show e.val.symm (Θ.invFun 0) ∈ U
    rw [hinv0, e.val.left_inv hxe]
    exact hxU
  obtain ⟨r, hr, hPO⟩ := exists_polydiscN_subset hO h0O
  set P := polydiscN (0 : ComplexModel (b + 1)) r with hPdef
  have hPopen : IsOpen P := isOpen_polydiscN _ _
  have hPt : P ⊆ Θ.target := fun w hw => (hPO hw).1.1
  have hPU : ∀ w ∈ P, e.val.symm (Θ.invFun w) ∈ U := fun w hw => (hPO hw).1.2
  have hPW : ∀ i, P ⊆ W i := fun i w hw => mem_iInter.1 (hPO hw).2 i
  -- Fubini
  set G : Fin N → ComplexModel (b + 1) → ℝ≥0∞ := fun i => multiplierDensity φΘ c (F i) with hG
  have hae : ∀ i, ∀ᵐ u ∂(volume.restrict (ball ((0 : ComplexModel (b + 1)) (Fin.last b)) r)),
      AEMeasurable (fun ζ => G i (sliceMap b u ζ))
          (volume.restrict (polydiscN (initCoords (0 : ComplexModel (b + 1))) r)) ∧
        ∫⁻ ζ in polydiscN (initCoords (0 : ComplexModel (b + 1))) r, G i (sliceMap b u ζ) < ⊤ :=
    fun i => ae_slice_finite 0 r ((hWL i).1.mono_measure (Measure.restrict_mono (hPW i) le_rfl))
      ((lintegral_mono_set (hPW i)).trans_lt (hWL i).2).ne
  have hall := ae_all_iff.2 hae
  rw [ae_restrict_iff' measurableSet_ball] at hall
  refine ⟨e.val.source ∩ e.val ⁻¹' (Θ.source ∩ Θ.toFun ⁻¹' P),
    e.val.isOpen_inter_preimage
      (Θ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Θ.isOpen_source hPopen),
    ⟨hxe, Θ.center_mem_source, ?_⟩, _, ae_iff.1 hall, ?_⟩
  · show Θ.toFun (e.val x) ∈ P
    rw [hΘ0]
    intro i
    simpa using hr
  intro z hz hreg hk hW q hqV
  let := chartedSpace hk hreg
  have := isComplexManifold_chartedSpace hk hreg
  have hqe : q.1 ∈ e.val.source := hqV.1
  have hqΘ : e.val q.1 ∈ Θ.source := hqV.2.1
  have hqP : Θ.toFun (e.val q.1) ∈ P := hqV.2.2
  have hqU : q.1 ∈ U := by
    have h := hPU _ hqP
    rwa [Θ.left_inv _ hqΘ, e.val.left_inv hqe] at h
  have hlast : Θ.toFun (e.val q.1) (Fin.last b) = height f x z := by
    rw [hΘ hqe hqΘ, height]
    simp only [coord]
    rw [show f q.1 = z from q.2]
  have hu : height f x z ∈ ball ((0 : ComplexModel (b + 1)) (Fin.last b)) r := by
    rw [← hlast, mem_ball, dist_eq_norm]
    exact hqP (Fin.last b)
  have hgood : ∀ i, AEMeasurable (fun ζ => G i (sliceMap b (height f x z) ζ))
        (volume.restrict (polydiscN (initCoords (0 : ComplexModel (b + 1))) r)) ∧
      ∫⁻ ζ in polydiscN (initCoords (0 : ComplexModel (b + 1))) r,
        G i (sliceMap b (height f x z) ζ) < ⊤ := by
    by_contra hcon
    exact hz fun h => hcon (h hu)
  have hslice : sliceMap b (height f x z) ⁻¹' P =
      polydiscN (initCoords (0 : ComplexModel (b + 1))) r := by
    rw [mem_ball, dist_eq_norm] at hu
    exact sliceMap_preimage_polydiscN 0 hu
  set Q := polydiscN (initCoords (0 : ComplexModel (b + 1))) r with hQdef
  have hQopen : IsOpen Q := isOpen_polydiscN _ _
  have hmaps : ∀ ζ ∈ Q, sliceMap b (height f x z) ζ ∈ P := fun ζ hζ => by
    rw [← hslice] at hζ
    exact hζ
  -- the slice chart of `X_z`
  set Fd := sliceFlatData (f := f) Θ hΘt hΘ hPopen hPt q.1 q.2 with hFd
  set Fch : ComplexChart b (fibre f z) := ⟨Fd.chart hk, chart_mem_atlas hk hreg Fd⟩ with hFch
  have hqF : q ∈ Fch.val.source := show q.1 ∈ Fd.ambSource from ⟨hqe, hqΘ, hqP⟩
  have htarget : Fch.val.target = Q := by
    show Fd.coordTarget = _
    rw [sliceFlatData_coordTarget, hslice]
  have hsymm : ∀ ζ ∈ Q, ((Fch.val.symm ζ : fibre f z) : X) =
      e.val.symm (Θ.invFun (sliceMap b (height f x z) ζ)) := by
    intro ζ hζ
    rw [← htarget] at hζ
    show (Fd.invPoint ζ : X) = _
    rw [Fd.invPoint_val hζ, sliceFlatData_ofCoord]
  have hsq : ∀ i, HolomorphicAt (b + 1) (s i) q.1 := fun i =>
    holomorphicAt_of_mdifferentiableOn hU (hs i) hqU
  refine restStalk_le_comap_of_generators hk hreg hW q s hsq (hspan q.1 hqU) fun i => ?_
  refine ⟨holomorphicAt_comp_val hk hreg (hsq i), ?_⟩
  refine multiplierIntegrableAt_chart (complexChartAt (n := b) q) Fch
    (mem_complexChartAt_source q) hqF ?_ hc.ne' ?_
  · have hcont : ContinuousOn (fun ζ => ((complexChartAt (n := b) q).val.symm ζ : X))
        (complexChartAt (n := b) q).val.target :=
      continuous_subtype_val.comp_continuousOn (complexChartAt (n := b) q).val.continuousOn_symm
    exact ((husc.upperSemicontinuousOn univ).comp hcont (mapsTo_univ _ _)).mono fun ζ hζ => hζ.1
  refine ⟨hc, Q, hQopen, ?_, ?_, ?_⟩
  · rw [← htarget]
    exact Fch.val.map_source hqF
  · have hd : DifferentiableOn ℂ (fun ζ => F i (sliceMap b (height f x z) ζ)) Q :=
      (hWd i).comp (differentiable_sliceMap _).differentiableOn fun ζ hζ => hPW i (hmaps ζ hζ)
    refine hd.congr fun ζ hζ => ?_
    show s i ((Fch.val.symm ζ : fibre f z) : X) = s i (e.val.symm (Θ.invFun _))
    rw [hsymm ζ hζ]
  · obtain ⟨hgm, hgi⟩ := hgood i
    have heq : EqOn (multiplierDensity (chartFunction (fun p : fibre f z => φ p.1) Fch) c
        (fun ζ => (s i ∘ Subtype.val) (Fch.val.symm ζ)))
        (fun ζ => G i (sliceMap b (height f x z) ζ)) Q := by
      intro ζ hζ
      show ENNReal.ofReal (‖s i ((Fch.val.symm ζ : fibre f z) : X)‖ ^ 2) *
          multiplierWeight c (φ ((Fch.val.symm ζ : fibre f z) : X)) = _
      rw [hsymm ζ hζ]
      rfl
    refine ⟨hgm.congr ((ae_restrict_mem hQopen.measurableSet).mono fun ζ hζ => (heq hζ).symm), ?_⟩
    rw [setLIntegral_congr_fun hQopen.measurableSet heq]
    exact hgi

end SGPT.Trace.FubFib
