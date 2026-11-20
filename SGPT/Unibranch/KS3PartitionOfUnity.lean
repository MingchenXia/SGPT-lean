import SGPT.Unibranch.ComplexSpaceThetaPSH

/-!
# Smooth partitions of unity on compact complex spaces

Lane KS3 (towards Kähler preservation under blowups, `def:unibranch:L212`).  A function on a
complex space `X` is *smooth* if near every point of every local embedding it is the restriction
of a smooth function of the ambient domain (`IsAmbientSmooth`).  For a compact `X` and a choice,
at every point `x`, of a local embedding `E x` and of an ambient open set `U x` around a carrier
point over `x`, this file constructs a finite smooth partition of unity `χ` such that each `χ x`
vanishes off a closed set lying in the image of `U x` (`exists_partitionOfUnity`).

The bump functions are `ContDiffBump`s of the ambient domains, transported to `X` through the
local embeddings and extended by zero; sums and quotients are smooth because transition maps
between local embeddings are holomorphic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.KS3PartitionOfUnity

variable {X : SourceReducedComplexSpace}

/-- Smooth functions on a complex space: near every point of every local embedding, restrictions
of smooth functions of the ambient domain. -/
def IsAmbientSmooth (f : X.obj.left → ℝ) : Prop :=
  ∀ (e : LocalEmbedding X) (c : e.carrier), ∃ O : Set (ComplexModel e.dim), IsOpen O ∧
    c.val.val ∈ O ∧ ∃ F : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ F O ∧
      ∀ c' : e.carrier, c'.val.val ∈ O → f (e.toPoint c') = F c'.val.val

theorem isAmbientSmooth_const (a : ℝ) : IsAmbientSmooth (fun _ : X.obj.left => a) := by
  intro e c
  exact ⟨univ, isOpen_univ, trivial, fun _ => a, contDiffOn_const, fun _ _ => rfl⟩

theorem IsAmbientSmooth.add {f g : X.obj.left → ℝ} (hf : IsAmbientSmooth f)
    (hg : IsAmbientSmooth g) : IsAmbientSmooth (fun p => f p + g p) := by
  intro e c
  obtain ⟨O, hO, hcO, F, hF, hfF⟩ := hf e c
  obtain ⟨O', hO', hcO', F', hF', hgF'⟩ := hg e c
  refine ⟨O ∩ O', hO.inter hO', ⟨hcO, hcO'⟩, fun u => F u + F' u,
    (hF.mono inter_subset_left).add (hF'.mono inter_subset_right), fun c' hc' => ?_⟩
  change f (e.toPoint c') + g (e.toPoint c') = F c'.val.val + F' c'.val.val
  rw [hfF c' hc'.1, hgF' c' hc'.2]

theorem isAmbientSmooth_sum {ι : Type} (s : Finset ι) {f : ι → X.obj.left → ℝ}
    (hf : ∀ i, IsAmbientSmooth (f i)) : IsAmbientSmooth (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isAmbientSmooth_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

theorem IsAmbientSmooth.div {f g : X.obj.left → ℝ} (hf : IsAmbientSmooth f)
    (hg : IsAmbientSmooth g) (hpos : ∀ p, 0 < g p) : IsAmbientSmooth (fun p => f p / g p) := by
  intro e c
  obtain ⟨O, hO, hcO, F, hF, hfF⟩ := hf e c
  obtain ⟨O', hO', hcO', F', hF', hgF'⟩ := hg e c
  have hpos' : 0 < F' c.val.val := by rw [← hgF' c hcO']; exact hpos _
  let O'' := O ∩ (O' ∩ F' ⁻¹' {0}ᶜ)
  have hO'' : IsOpen O'' :=
    hO.inter (hF'.continuousOn.isOpen_inter_preimage hO' isClosed_singleton.isOpen_compl)
  refine ⟨O'', hO'', ⟨hcO, hcO', hpos'.ne'⟩, fun u => F u / F' u, ?_, fun c' hc' => ?_⟩
  · exact (hF.mono fun u hu => hu.1).div (hF'.mono fun u hu => hu.2.1) fun u hu => hu.2.2
  · change f (e.toPoint c') / g (e.toPoint c') = F c'.val.val / F' c'.val.val
    rw [hfF c' hc'.1, hgF' c' hc'.2.1]

/-- Input of the partition of unity: at every point a local embedding, a carrier point over it
and an ambient open set around this carrier point. -/
structure Cover (X : SourceReducedComplexSpace) where
  E : X.obj.left → LocalEmbedding X
  w : ∀ x, (E x).carrier
  hw : ∀ x, (E x).toPoint (w x) = x
  U : ∀ x, Set (ComplexModel (E x).dim)
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, (w x).val.val ∈ U x
  U_sub : ∀ x, U x ⊆ (E x).ambient

namespace Cover

variable (K : Cover X)

/-- A radius with the closed ball of twice the radius inside `U x`. -/
theorem exists_radius (x : X.obj.left) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall (K.w x).val.val (2 * ρ) ⊆ K.U x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (K.isOpen_U x) _ (K.mem_U x)
  refine ⟨ε / 3, by positivity, fun u hu => hball ?_⟩
  rw [mem_closedBall] at hu
  rw [mem_ball]
  linarith

/-- The chosen radius. -/
def ρ (x : X.obj.left) : ℝ := Classical.choose (K.exists_radius x)

theorem ρ_pos (x : X.obj.left) : 0 < K.ρ x := (Classical.choose_spec (K.exists_radius x)).1

theorem closedBall_sub (x : X.obj.left) :
    closedBall (K.w x).val.val (2 * K.ρ x) ⊆ K.U x :=
  (Classical.choose_spec (K.exists_radius x)).2

/-- The bump function at `x`, in the ambient coordinates of `E x`. -/
def bump (x : X.obj.left) : ContDiffBump (K.w x).val.val :=
  ⟨K.ρ x, 2 * K.ρ x, K.ρ_pos x, by linarith [K.ρ_pos x]⟩

/-- The carrier points of `E x` in the closed ball of radius `2ρ`. -/
def ballCarrier (x : X.obj.left) : Set (K.E x).carrier :=
  {c | c.val.val ∈ closedBall (K.w x).val.val (2 * K.ρ x)}

theorem isCompact_ballCarrier (x : X.obj.left) : IsCompact (K.ballCarrier x) := by
  let ι : (K.E x).carrier → ComplexModel (K.E x).dim := fun c => c.val.val
  have hemb : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff]
  -- the carrier is closed in the ambient domain
  obtain ⟨Z, hZ, hZeq⟩ : ∃ Z : Set (ComplexModel (K.E x).dim), IsClosed Z ∧
      (Subtype.val : (K.E x).ambient → ComplexModel (K.E x).dim) ⁻¹' Z = (K.E x).carrier :=
    isClosed_induced_iff.mp (K.E x).analytic.isClosed
  have himage : ι '' K.ballCarrier x = closedBall (K.w x).val.val (2 * K.ρ x) ∩ Z := by
    ext u
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hc, ?_⟩
      have : c.val ∈ (Subtype.val : (K.E x).ambient → ComplexModel (K.E x).dim) ⁻¹' Z := by
        rw [hZeq]; exact c.property
      exact this
    · rintro ⟨hu, huZ⟩
      have huA : u ∈ (K.E x).ambient := K.U_sub x (K.closedBall_sub x hu)
      have huC : (⟨u, huA⟩ : (K.E x).ambient) ∈ (K.E x).carrier := by
        rw [← hZeq]; exact huZ
      exact ⟨⟨⟨u, huA⟩, huC⟩, hu, rfl⟩
  rw [himage]
  exact (isCompact_closedBall _ _).inter_right hZ

/-- The closed set of `X` carrying the bump at `x`. -/
def supportSet (x : X.obj.left) : Set X.obj.left := (K.E x).toPoint '' K.ballCarrier x

theorem isClosed_supportSet (x : X.obj.left) : IsClosed (K.supportSet x) := by
  have : T2Space X.obj.left := X.property.1
  exact ((K.isCompact_ballCarrier x).image (K.E x).isOpenEmbedding_toPoint.continuous).isClosed

open Classical in
/-- The bump function at `x`, transported to `X` and extended by zero. -/
def bumpX (x : X.obj.left) (p : X.obj.left) : ℝ :=
  if h : ∃ c : (K.E x).carrier, (K.E x).toPoint c = p then K.bump x (Classical.choose h).val.val
  else 0

theorem bumpX_apply (x : X.obj.left) (c : (K.E x).carrier) :
    K.bumpX x ((K.E x).toPoint c) = K.bump x c.val.val := by
  have h : ∃ c' : (K.E x).carrier, (K.E x).toPoint c' = (K.E x).toPoint c := ⟨c, rfl⟩
  rw [bumpX, dif_pos h]
  have := (K.E x).isOpenEmbedding_toPoint.injective (Classical.choose_spec h)
  rw [this]

theorem bumpX_nonneg (x p : X.obj.left) : 0 ≤ K.bumpX x p := by
  unfold bumpX
  split
  · exact (K.bump x).nonneg
  · exact le_rfl

theorem bumpX_eq_zero_of_notMem (x p : X.obj.left) (hp : p ∉ K.supportSet x) :
    K.bumpX x p = 0 := by
  unfold bumpX
  split
  · rename_i h
    by_contra hne
    apply hp
    refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
    have hmem : (Classical.choose h).val.val ∈ Function.support (K.bump x : _ → ℝ) := hne
    rw [(K.bump x).support_eq] at hmem
    exact ball_subset_closedBall hmem
  · rfl

theorem bumpX_eq_one (x : X.obj.left) (c : (K.E x).carrier)
    (hc : c.val.val ∈ ball (K.w x).val.val (K.ρ x)) : K.bumpX x ((K.E x).toPoint c) = 1 := by
  rw [bumpX_apply]
  exact (K.bump x).one_of_mem_closedBall (ball_subset_closedBall hc)

theorem isAmbientSmooth_bumpX (x : X.obj.left) : IsAmbientSmooth (K.bumpX x) := by
  intro e c
  by_cases hp : e.toPoint c ∈ range (K.E x).toPoint
  · obtain ⟨W, H, hcW, hW, -, hH, -, hfac⟩ := e.exists_isTransition (K.E x) c hp
    refine ⟨W, hW, hcW, fun u => K.bump x (H u), ?_, fun c' hc' => ?_⟩
    · exact (K.bump x).contDiff.comp_contDiffOn
        (contDiffOn_of_differentiableOn_complex hH hW |>.restrict_scalars ℝ)
    · obtain ⟨z, hz, hzpt⟩ := hfac c' hc'
      rw [← hzpt, bumpX_apply, hz]
  · have hK : e.toPoint c ∉ K.supportSet x := fun h => hp (image_subset_range _ _ h)
    have hopen : IsOpen (e.toPoint ⁻¹' (K.supportSet x)ᶜ) :=
      (K.isClosed_supportSet x).isOpen_compl.preimage e.isOpenEmbedding_toPoint.continuous
    obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp hopen
    obtain ⟨t', ht', ht'eq⟩ := isOpen_induced_iff.mp ht
    refine ⟨t', ht', ?_, fun _ => 0, contDiffOn_const, fun c' hc' => ?_⟩
    · have : c ∈ e.toPoint ⁻¹' (K.supportSet x)ᶜ := hK
      rw [← hteq] at this
      change c.val ∈ t at this
      rw [← ht'eq] at this
      exact this
    · have h1 : c'.val ∈ t := by rw [← ht'eq]; exact hc'
      have h2 : c' ∈ e.toPoint ⁻¹' (K.supportSet x)ᶜ := by rw [← hteq]; exact h1
      exact K.bumpX_eq_zero_of_notMem x _ h2

end Cover

/-- **Smooth partitions of unity on a compact complex space**, subordinate to a given choice of
local embeddings and ambient open sets. -/
theorem exists_partitionOfUnity [CompactSpace X.obj.left] (K : Cover X) :
    ∃ (F : Finset X.obj.left) (χ : X.obj.left → X.obj.left → ℝ),
      (∀ x p, 0 ≤ χ x p) ∧ (∀ p, ∑ x ∈ F, χ x p = 1) ∧ (∀ x, IsAmbientSmooth (χ x)) ∧
      ∀ x, ∃ Kx : Set X.obj.left, IsClosed Kx ∧ (∀ p ∉ Kx, χ x p = 0) ∧
        ∀ p ∈ Kx, ∃ c : (K.E x).carrier, c.val.val ∈ K.U x ∧ (K.E x).toPoint c = p := by
  classical
  -- the inner open sets
  let I : X.obj.left → Set X.obj.left := fun x =>
    (K.E x).toPoint '' {c | c.val.val ∈ ball (K.w x).val.val (K.ρ x)}
  have hIo : ∀ x, IsOpen (I x) := by
    intro x
    apply (K.E x).isOpenEmbedding_toPoint.isOpenMap
    exact isOpen_ball.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hIx : ∀ x, x ∈ I x := fun x =>
    ⟨K.w x, mem_ball_self (K.ρ_pos x), K.hw x⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover I hIo
    (fun x _ => mem_iUnion.mpr ⟨x, hIx x⟩)
  let S : X.obj.left → ℝ := fun p => ∑ y ∈ F, K.bumpX y p
  have hSpos : ∀ p, 0 < S p := by
    intro p
    obtain ⟨y, hyF, hpy⟩ := mem_iUnion₂.mp (hF (mem_univ p))
    obtain ⟨c, hc, rfl⟩ := hpy
    have h1 : K.bumpX y ((K.E y).toPoint c) = 1 := K.bumpX_eq_one y c hc
    calc (0 : ℝ) < K.bumpX y ((K.E y).toPoint c) := by rw [h1]; exact one_pos
      _ ≤ S ((K.E y).toPoint c) :=
        Finset.single_le_sum (fun z _ => K.bumpX_nonneg z _) hyF
  have hSsmooth : IsAmbientSmooth S := isAmbientSmooth_sum F K.isAmbientSmooth_bumpX
  refine ⟨F, fun x p => K.bumpX x p / S p, fun x p => div_nonneg (K.bumpX_nonneg x p)
    (hSpos p).le, fun p => ?_, fun x => (K.isAmbientSmooth_bumpX x).div hSsmooth hSpos,
    fun x => ⟨K.supportSet x, K.isClosed_supportSet x, fun p hp => ?_, ?_⟩⟩
  · rw [← Finset.sum_div]
    exact div_self (hSpos p).ne'
  · show K.bumpX x p / S p = 0
    rw [K.bumpX_eq_zero_of_notMem x p hp, zero_div]
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, K.closedBall_sub x hc, rfl⟩

end SGPT.Unibranch.KS3PartitionOfUnity
