import SGPT.Convex.Semicontinuity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Order.DenselyOrdered

/-!
# The source convex closure operation

Real-height regularization is constructed intrinsically from the topological
closure of the actual epigraph. Its universal property identifies it as the
greatest lower semicontinuous minorant. The SGPT closure additionally collapses
to the bottom constant when the original function takes a bottom value.
-/

namespace SGPT.Convex

open Set Filter Topology

section IntrinsicSeparation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Separation in the actual affine span, followed by an actual continuous
Hahn--Banach extension to the ambient space. -/
theorem exists_functional_of_mem_intrinsicInterior {C : Set X} (hC : Convex ℝ C)
    {p q : X} (hp : p ∈ intrinsicInterior ℝ C)
    (hq : q ∈ affineSpan ℝ C) (hqnot : q ∉ C) :
    ∃ L : X →L[ℝ] ℝ, L q < L p ∧ ∀ z ∈ C, L q ≤ L z := by
  rcases mem_intrinsicInterior.mp hp with ⟨pA, hpA, rfl⟩
  let A := affineSpan ℝ C
  let : Nonempty A := ⟨pA⟩
  let e := AffineIsometryEquiv.vaddConst ℝ pA
  let F := A.subtype.comp e.toAffineEquiv.toAffineMap
  let C' : Set A.direction := F ⁻¹' C
  let qA : A := ⟨q, hq⟩
  let qD : A.direction := e.symm qA
  have hC' : Convex ℝ C' := hC.affine_preimage F
  have hzero : (0 : A.direction) ∈ interior C' := by
    change (0 : A.direction) ∈ interior (e.toHomeomorph ⁻¹' ((↑) ⁻¹' C : Set A))
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior ((↑) ⁻¹' C : Set A)
    simpa [e] using hpA
  have hqDnot : qD ∉ C' := by
    intro h
    apply hqnot
    simpa [C', F, qD] using h
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hC'.interior isOpen_interior
    (fun h ↦ hqDnot (interior_subset h))
  have hbound : C' ⊆ {v | l qD ≤ l v} := by
    intro v hv
    have hs : IsClosed {v | l qD ≤ l v} := isClosed_le continuous_const l.continuous
    have hi : interior C' ⊆ {v | l qD ≤ l v} := fun v hv ↦ (hl v hv).le
    have hm : v ∈ _root_.closure (interior C') := by
      rw [hC'.closure_interior_eq_closure_of_nonempty_interior ⟨0, hzero⟩]
      exact subset_closure hv
    exact closure_minimal hi hs hm
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq A.direction l
  have hvalue (v : A.direction) : L (F v) = L pA + l v := by
    have hv : (F v : X) = (v : X) + (pA : X) := by
      simp [F, e, AffineSubspace.coe_vadd, vadd_eq_add]
    rw [hv, map_add, hL]
    ring
  have hqvalue : L q = L pA + l qD := by
    have hF : F qD = q := by simp [F, qD, qA]
    rw [← hF]
    exact hvalue qD
  refine ⟨L, ?_, ?_⟩
  · have hs := hl 0 hzero
    rw [map_zero] at hs
    rw [hqvalue]
    linarith
  · intro z hz
    let zA : A := ⟨z, subset_affineSpan ℝ C hz⟩
    let zD : A.direction := e.symm zA
    have hF : F zD = z := by simp [F, zD, zA]
    have hzD : zD ∈ C' := by change F zD ∈ C; rw [hF]; exact hz
    have hs := hbound hzD
    change l qD ≤ l zD at hs
    rw [← hF, hvalue, hqvalue]
    linarith

end IntrinsicSeparation

section Regularization

variable {V : Type*} [TopologicalSpace V]

omit [TopologicalSpace V] in
/-- Pointwise order is the reverse of real-height epigraph inclusion. -/
theorem le_iff_epigraph_subset {f g : V → EReal} :
    f ≤ g ↔ epigraph g ⊆ epigraph f := by
  constructor
  · intro h p hp
    exact (h p.1).trans hp
  · intro h x
    by_contra hfg
    obtain ⟨r, hgr, hrf⟩ := EReal.exists_between_coe_real (lt_of_not_ge hfg)
    have hfr : f x ≤ (r : EReal) := h (show (x, r) ∈ epigraph g from hgr.le)
    exact not_le_of_gt hrf hfr

/-- Upward closure in the real height coordinate survives topological closure. -/
theorem mem_closure_epigraph_of_le {f : V → EReal} {x : V} {r s : ℝ}
    (h : (x, r) ∈ _root_.closure (epigraph f)) (hrs : r ≤ s) :
    (x, s) ∈ _root_.closure (epigraph f) := by
  let T : V × ℝ → V × ℝ := fun p ↦ (p.1, p.2 + (s - r))
  have hc : Continuous T := continuous_fst.prodMk (continuous_snd.add continuous_const)
  have hm : Set.MapsTo T (epigraph f) (epigraph f) := by
    intro p hp
    exact hp.trans (EReal.coe_le_coe_iff.mpr (by dsimp [T]; linarith))
  have ht := map_mem_closure hc h hm
  simpa [T] using ht

/-- The actual lower semicontinuity regularization, defined by closed epigraph heights. -/
noncomputable def regularization (f : V → EReal) (x : V) : EReal :=
  ⨅ (r : ℝ) (_ : (x, r) ∈ _root_.closure (epigraph f)), (r : EReal)

/-- The real-height epigraph of the regularization is precisely the closed epigraph. -/
theorem epigraph_regularization (f : V → EReal) :
    epigraph (regularization f) = _root_.closure (epigraph f) := by
  ext p
  constructor
  · intro hp
    have hs : IsClosed {r : ℝ | (p.1, r) ∈ _root_.closure (epigraph f)} :=
      isClosed_closure.preimage (continuous_const.prodMk continuous_id)
    have hsub : Set.Ioi p.2 ⊆ {r : ℝ | (p.1, r) ∈ _root_.closure (epigraph f)} := by
      intro s hps
      have hlt : regularization f p.1 < (s : EReal) :=
        hp.trans_lt (EReal.coe_lt_coe_iff.mpr hps)
      obtain ⟨r, hr⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hm, hrs⟩ := iInf_lt_iff.mp hr
      exact mem_closure_epigraph_of_le hm (EReal.coe_lt_coe_iff.mp hrs).le
    have hmem : p.2 ∈ _root_.closure (Set.Ioi p.2) := by simp [closure_Ioi]
    have h := _root_.closure_mono hsub hmem
    simpa only [hs.closure_eq, Set.mem_ofPred_eq, Prod.eta] using h
  · intro hp
    change regularization f p.1 ≤ (p.2 : EReal)
    unfold regularization
    exact iInf_le_of_le p.2 (iInf_le_of_le hp le_rfl)

/-- The regularization is lower semicontinuous by its actual closed epigraph. -/
theorem lowerSemicontinuous_regularization (f : V → EReal) :
    LowerSemicontinuous (regularization f) := by
  apply isClosed_epigraph_iff_lowerSemicontinuous.mp
  rw [epigraph_regularization]
  exact isClosed_closure

/-- Regularization lies below the original obstacle. -/
theorem regularization_le (f : V → EReal) : regularization f ≤ f := by
  apply le_iff_epigraph_subset.mpr
  rw [epigraph_regularization]
  exact subset_closure

/-- Every lower semicontinuous minorant lies below the regularization. -/
theorem le_regularization_of_lowerSemicontinuous_le {f g : V → EReal}
    (hg : LowerSemicontinuous g) (hgf : g ≤ f) : g ≤ regularization f := by
  apply le_iff_epigraph_subset.mpr
  rw [epigraph_regularization]
  exact closure_minimal (le_iff_epigraph_subset.mp hgf)
    (isClosed_epigraph_iff_lowerSemicontinuous.mpr hg)

/-- Lower semicontinuous functions are fixed by regularization. -/
theorem regularization_eq_self {f : V → EReal} (hf : LowerSemicontinuous f) :
    regularization f = f :=
  le_antisymm (regularization_le f) (le_regularization_of_lowerSemicontinuous_le hf le_rfl)

/-- Regularization is monotone in the obstacle. -/
theorem regularization_mono {f g : V → EReal} (hfg : f ≤ g) :
    regularization f ≤ regularization g :=
  le_regularization_of_lowerSemicontinuous_le (lowerSemicontinuous_regularization f)
    ((regularization_le f).trans hfg)

/-- Regularization is idempotent on every extended-real function. -/
theorem regularization_idempotent (f : V → EReal) :
    regularization (regularization f) = regularization f :=
  regularization_eq_self (lowerSemicontinuous_regularization f)

/-- An actual continuous real-valued minorant remains below the regularization. -/
theorem le_regularization_of_continuous_le {f : V → EReal} (g : V → ℝ)
    (hg : Continuous g) (hgf : (fun x ↦ (g x : EReal)) ≤ f) :
    (fun x ↦ (g x : EReal)) ≤ regularization f :=
  le_regularization_of_lowerSemicontinuous_le
    (continuous_coe_real_ereal.comp hg).lowerSemicontinuous hgf

/-- The finite lower bounds of a continuous real minorant exclude bottom values. -/
theorem regularization_ne_bot_of_continuous_minorant {f : V → EReal} (g : V → ℝ)
    (hg : Continuous g) (hgf : (fun x ↦ (g x : EReal)) ≤ f) :
    ∀ x, regularization f x ≠ ⊥ := by
  intro x
  exact ne_of_gt ((EReal.bot_lt_coe (g x)).trans_le
    (le_regularization_of_continuous_le g hg hgf x))

/-- SGPT's convex closure: any negative-infinite value collapses the result to
the bottom constant; otherwise use actual lower semicontinuity regularization. -/
noncomputable def convexClosure (f : V → EReal) : V → EReal := by
  classical
  exact if ∃ x, f x = ⊥ then fun _ ↦ ⊥ else regularization f

/-- The negative-infinite branch is the whole bottom constant, as in the source. -/
theorem convexClosure_of_exists_bot {f : V → EReal} (hf : ∃ x, f x = ⊥) :
    convexClosure f = (fun _ ↦ ⊥) := by
  classical
  exact if_pos hf

/-- With no negative-infinite values, source closure is precisely regularization. -/
theorem convexClosure_of_forall_ne_bot {f : V → EReal} (hf : ∀ x, f x ≠ ⊥) :
    convexClosure f = regularization f := by
  classical
  exact if_neg (by simpa only [not_exists] using hf)

/-- Source closure lies below its obstacle in both exceptional branches. -/
theorem convexClosure_le (f : V → EReal) : convexClosure f ≤ f := by
  classical
  by_cases h : ∃ x, f x = ⊥
  · rw [convexClosure_of_exists_bot h]
    exact fun _ ↦ bot_le
  · rw [convexClosure_of_forall_ne_bot (by simpa only [not_exists] using h)]
    exact regularization_le f

/-- Source closure is lower semicontinuous, including its bottom branch. -/
theorem lowerSemicontinuous_convexClosure (f : V → EReal) :
    LowerSemicontinuous (convexClosure f) := by
  classical
  by_cases h : ∃ x, f x = ⊥
  · rw [convexClosure_of_exists_bot h]
    exact lowerSemicontinuous_const
  · rw [convexClosure_of_forall_ne_bot (by simpa only [not_exists] using h)]
    exact lowerSemicontinuous_regularization f

/-- Source closure is monotone, even when the larger obstacle takes `-∞`. -/
theorem convexClosure_mono {f g : V → EReal} (hfg : f ≤ g) :
    convexClosure f ≤ convexClosure g := by
  classical
  by_cases h : ∃ x, f x = ⊥
  · rw [convexClosure_of_exists_bot h]
    exact fun _ ↦ bot_le
  · have hf : ∀ x, f x ≠ ⊥ := by simpa only [not_exists] using h
    have hg : ∀ x, g x ≠ ⊥ := by
      intro x hx
      apply hf x
      exact le_bot_iff.mp (by simpa only [hx] using hfg x)
    rw [convexClosure_of_forall_ne_bot hf, convexClosure_of_forall_ne_bot hg]
    exact regularization_mono hfg

/-- An actual continuous real minorant makes source closure idempotent.
Existence of the minorant is not assumed for arbitrary proper convex functions. -/
theorem convexClosure_idempotent_of_continuous_minorant {f : V → EReal} (g : V → ℝ)
    (hg : Continuous g) (hgf : (fun x ↦ (g x : EReal)) ≤ f) :
    convexClosure (convexClosure f) = convexClosure f := by
  have hf : ∀ x, f x ≠ ⊥ := fun x ↦ ne_of_gt ((EReal.bot_lt_coe (g x)).trans_le (hgf x))
  rw [convexClosure_of_forall_ne_bot hf,
    convexClosure_of_forall_ne_bot (regularization_ne_bot_of_continuous_minorant g hg hgf)]
  exact regularization_idempotent f

end Regularization

section ClosedFixedPoints

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The source's two infinite constants and proper lower semicontinuous functions
are fixed by the actual convex closure operation. -/
theorem convexClosure_eq_self_of_isClosedConvex {f : V → EReal} (hf : IsClosedConvex f) :
    convexClosure f = f := by
  classical
  rcases hf with h | h | h
  · rw [h]
    exact convexClosure_of_exists_bot ⟨0, rfl⟩
  · rw [h, convexClosure_of_forall_ne_bot (by simp)]
    exact regularization_eq_self lowerSemicontinuous_const
  · rw [convexClosure_of_forall_ne_bot h.1.2.2]
    exact regularization_eq_self h.2

/-- For convex functions, the source's closed-convex classification is exactly
the fixed-point condition for its closure operation. -/
theorem convexClosure_eq_self_iff_isClosedConvex {f : V → EReal} (hf : IsConvex f) :
    convexClosure f = f ↔ IsClosedConvex f := by
  classical
  constructor
  · intro heq
    by_cases hb : ∃ x, f x = ⊥
    · exact Or.inl (heq.symm.trans (convexClosure_of_exists_bot hb))
    have hnb : ∀ x, f x ≠ ⊥ := by simpa only [not_exists] using hb
    by_cases ht : f = (fun _ ↦ ⊤)
    · exact Or.inr (Or.inl ht)
    refine Or.inr (Or.inr ⟨⟨hf, ?_, hnb⟩, ?_⟩)
    · have hex : ∃ x, f x ≠ ⊤ := by
        by_contra hn
        apply ht
        funext x
        by_contra hx
        exact hn ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hex
      exact ⟨x, lt_top_iff_ne_top.mpr hx⟩
    · rw [← heq]
      exact lowerSemicontinuous_convexClosure f
  · exact convexClosure_eq_self_of_isClosedConvex

/-- Every source-closed convex minorant lies below the actual closure. -/
theorem le_convexClosure_of_isClosedConvex_le {f g : V → EReal}
    (hg : IsClosedConvex g) (hgf : g ≤ f) : g ≤ convexClosure f := by
  rw [← convexClosure_eq_self_of_isClosedConvex hg]
  exact convexClosure_mono hgf

end ClosedFixedPoints

section Convexity

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- Topological epigraph closure preserves convexity. -/
theorem isConvex_regularization {f : V → EReal} (hf : IsConvex f) :
    IsConvex (regularization f) := by
  unfold IsConvex
  rw [epigraph_regularization]
  exact hf.closure

/-- The source closure operation preserves convexity in both branches. -/
theorem isConvex_convexClosure {f : V → EReal} (hf : IsConvex f) :
    IsConvex (convexClosure f) := by
  classical
  by_cases h : ∃ x, f x = ⊥
  · rw [convexClosure_of_exists_bot h]
    exact isConvex_bot
  · rw [convexClosure_of_forall_ne_bot (by simpa only [not_exists] using h)]
    exact isConvex_regularization hf

/-- Properness of regularization is produced from a proper obstacle and an actual
continuous real minorant; the effective-domain witness comes from the obstacle. -/
theorem isProper_regularization_of_continuous_minorant {f : V → EReal}
    (hf : IsProper f) (g : V → ℝ) (hg : Continuous g)
    (hgf : (fun x ↦ (g x : EReal)) ≤ f) : IsProper (regularization f) := by
  refine ⟨isConvex_regularization hf.1, ?_,
    regularization_ne_bot_of_continuous_minorant g hg hgf⟩
  obtain ⟨x, hx⟩ := hf.2.1
  exact ⟨x, (regularization_le f x).trans_lt hx⟩

/-- With an actual continuous real minorant, source closure of a proper convex
function is proper. This is a consumer of the affine-minorant producer. -/
theorem isProper_convexClosure_of_continuous_minorant {f : V → EReal}
    (hf : IsProper f) (g : V → ℝ) (hg : Continuous g)
    (hgf : (fun x ↦ (g x : EReal)) ≤ f) : IsProper (convexClosure f) := by
  rw [convexClosure_of_forall_ne_bot hf.2.2]
  exact isProper_regularization_of_continuous_minorant hf g hg hgf

/-- The proper lower-semicontinuous branch of the source classification follows
from an actual minorant, not from an assumed closure certificate. -/
theorem isClosedConvex_convexClosure_of_continuous_minorant {f : V → EReal}
    (hf : IsProper f) (g : V → ℝ) (hg : Continuous g)
    (hgf : (fun x ↦ (g x : EReal)) ≤ f) : IsClosedConvex (convexClosure f) :=
  Or.inr (Or.inr ⟨isProper_convexClosure_of_continuous_minorant hf g hg hgf,
    lowerSemicontinuous_convexClosure f⟩)

end Convexity

end SGPT.Convex
