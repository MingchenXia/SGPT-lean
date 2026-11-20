import SGPT.Checks.Comparison.BJCycleStalk
import SGPT.Checks.Comparison.ThinApprox.BJCharge4Positivity

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# The multiplicity bound along a prime filtration

Towards the cycle lower bound `CycleLowerBound` of `bjAppSeq_of_cycleLowerBound` (book
`thm:BJappseq`, [BJ22, Cor. 12.18]). Blueprint: `claude-bj-cycle.tex`.

Let `D` be projective over `ℂ` of dimension `≤ n`, `z` a maximal point of `D` (no proper
generization) and `V = closure {z}` with its reduced structure. For invertible sheaves `N₁, …, N_n`
nef on `D`,

  `ℓ(𝒪_{D,z}) · (N₁|_V ⋯ N_n|_V)_V ≤ (N₁ ⋯ N_n · 𝒪_D)_D`

(`mixedEulerDifference_ge_length_mul`): along a prime filtration of `𝒪_D` (SGPT.Foundations.Envelope) the
successive quotients are push-forwards `ι_* T` of invertible sheaves on point closures
`closure {η}`; those with `η = z` contribute `(N|_V)^n` each and have stalk length `≤ 1` at
`z` (`stalkLength_pushforward_le_one`), the others contribute `≥ 0` (nef positivity) and have
stalk length `0` at `z` (`z ∉ closure {η}` by maximality). Additivity of stalk lengths and of
intersection numbers gives the bound. `interFormQ_ge_length_mul` is the version for `ℚ`-classes
nef on `D` (expansion over the nef cone), and `interFormQ_nonneg_of_mem_relNefCone` is nef
positivity for `ℚ`-classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules

universe u

namespace SGPT.NAPotential.ThinApprox.BJCycle
open SGPT.NAPotential.BJCycle

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
open SGPT.NAPotential.BJIntersect SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJProj

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Nef positivity for `ℚ`-classes -/

section nef

variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
  (p : X ⟶ Spec (.of k)) [IsProjective p]

omit [X.IsSeparated] [IsProjective p] in
/-- The nef cone of `X` is spanned by the classes of nef invertible sheaves. -/
theorem relNefCone_univ_le_hull :
    relNefCone p Set.univ ≤ PointedCone.hull ℚ (Set.range fun N :
      {N : {N : X.Modules // IsInvertible N} // IsNefOn p N.1 Set.univ} => picQ N.1) :=
  Submodule.span_mono fun _ ⟨N, hN, hθ⟩ => ⟨⟨N, hN⟩, hθ.symm⟩

/-- **Nef positivity for `ℚ`-classes**: on a projective scheme of dimension `≤ d`, the
intersection numbers of `ℚ`-classes nef on `X` against a coherent sheaf are nonnegative. -/
theorem interFormQ_nonneg_of_mem_relNefCone (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : Multiset (PicQ X))
    (hs : ∀ θ ∈ s, θ ∈ relNefCone p Set.univ) : 0 ≤ interFormQ p d hdim F s := by
  have h := MultisetForm.nonneg_of_mem_hull (interFormQ p d hdim F)
    (fun N : {N : {N : X.Modules // IsInvertible N} // IsNefOn p N.1 Set.univ} => picQ N.1) s 0
    (fun θ hθ => relNefCone_univ_le_hull p (hs θ hθ)) (fun l hl => ?_)
  · simpa using h
  · rw [zero_add]
    by_cases hd : l.length = d
    · have h1 := interFormQ_picQ p d hdim F (l.map Subtype.val) (by simpa using hd)
      rw [List.map_map] at h1
      change 0 ≤ interFormQ p d hdim F (((l.map ((fun N => picQ N) ∘ Subtype.val)) : List _) :
        Multiset _)
      rw [h1]
      have h2 := mixedEulerDifference_nef_nonneg d p hdim (l.map Subtype.val) (by simpa using hd)
        (fun N hN => by
          obtain ⟨M, -, rfl⟩ := List.mem_map.mp hN
          exact M.2.mem_nefCone M.1.2) F
      exact_mod_cast h2
    · rw [interFormQ_hasDegree p d hdim F _ (by simpa using hd)]

end nef

/-! ### The multiplicity bound -/

section core

variable {D : Scheme.{0}} [CompactSpace D] [D.IsSeparated] (p : D ⟶ Spec (.of ℂ))
  [IsProjective p]

omit [CompactSpace D] [D.IsSeparated] in
/-- The closure of a point of a scheme of dimension `≤ n` has dimension `≤ n`. -/
theorem topologicalKrullDim_pointClosure_le_of_le {n : ℕ} (hdim : topologicalKrullDim D ≤ n)
    (z : D) : topologicalKrullDim (pointClosure z) ≤ n :=
  (pointClosureι z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim

private theorem isFiniteType_of_isInvertible' {Y : Scheme.{0}} {T : Y.Modules}
    (hT : IsInvertible T) : T.IsFiniteType :=
  let : T.IsFinitePresentation := hT.isFinitePresentation
  SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Y.ringCatSheaf) T

/-- The bound along a prime filtration. -/
private theorem filtration_bound (n : ℕ) (hdim : topologicalKrullDim D ≤ n) (z : D)
    (hmax : ∀ y : D, y ⤳ z → y = z) (ns : List {N : D.Modules // IsInvertible N})
    (hlen : ns.length = n) (hnef : ∀ N ∈ ns, IsNefOn p N.1 Set.univ)
    {r : ℕ} {G : D.Modules} (hfil : ActualCoherentPrimeFiltration r G) :
    ∃ k : ℕ, stalkLength G z ≤ k ∧
      (k : ℤ) * mixedEulerDifference (pointClosureι z ≫ p)
          (ns.map fun N => (Scheme.Modules.pullback (pointClosureι z)).obj N.1)
          (unitObj (pointClosure z)) ≤
        mixedEulerDifference p (ns.map Subtype.val) G := by
  have hls : ∀ L ∈ ns.map Subtype.val, IsInvertible L := by
    intro L hL
    obtain ⟨N, -, rfl⟩ := List.mem_map.mp hL
    exact N.2
  induction hfil with
  | zero M hM =>
    refine ⟨0, by rw [stalkLength_eq_zero_of_isZero M hM z]; exact zero_le, ?_⟩
    rw [mixedEulerDifference_eq_zero_of_isZero p _ hls M hM]
    norm_num
  | iso e _ ih =>
    obtain ⟨k, hk, hk'⟩ := ih
    exact ⟨k, (stalkLength_of_iso e z).symm.trans_le hk,
      hk'.trans_eq (mixedEulerDifference_eq_of_iso p _ e)⟩
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    obtain ⟨k, hk, hk'⟩ := ih
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    have hlenS := stalkLength_shortExact S hS z
    have hadd := mixedEulerDifference_add p _ hls S hS
    let : T.IsQuasicoherent := hT.isQuasicoherent
    let : T.IsFiniteType := isFiniteType_of_isInvertible' hT
    by_cases heta : eta = z
    · subst heta
      refine ⟨k + 1, ?_, ?_⟩
      · rw [hlenS, stalkLength_of_iso e]
        have h1 := stalkLength_pushforward_le_one (pointClosureι eta) T hT
        have hg : pointClosureι eta (genericPoint (pointClosure eta)) = eta := by
          rw [← (SGPT.Foundations.Envelope.SchemePointClosureIntegral.isGenericPoint_pointClosureLift
            eta).eq (genericPoint_spec (pointClosure eta))]
          rfl
        rw [stalkLength_congr _ hg] at h1
        push_cast
        exact add_le_add hk h1
      · have h3 : mixedEulerDifference p (ns.map Subtype.val) S.X₃ =
            mixedEulerDifference (pointClosureι eta ≫ p)
              (ns.map fun N => (Scheme.Modules.pullback (pointClosureι eta)).obj N.1)
              (unitObj (pointClosure eta)) := by
          rw [mixedEulerDifference_eq_of_iso p _ e,
            mixedEulerDifference_pushforward p (pointClosureι eta) _ hls T, List.map_map]
          refine mixedEulerDifference_eq_unit_of_dimension_le (pointClosureι eta ≫ p) n
            (topologicalKrullDim_pointClosure_le_of_le hdim eta) _ (by simpa using hlen) ?_ T hT
          intro L hL
          obtain ⟨N, -, rfl⟩ := List.mem_map.mp hL
          exact N.2.pullback _
        rw [hadd, h3]
        push_cast
        linarith
    · have hz : z ∉ Set.range (pointClosureι eta) := by
        rw [range_pointClosureι]
        intro hz
        exact heta (hmax eta (specializes_iff_mem_closure.mpr hz))
      refine ⟨k, ?_, ?_⟩
      · rw [hlenS, stalkLength_of_iso e,
          stalkLength_pushforward_eq_zero (pointClosureι eta)
            (by rw [range_pointClosureι]; exact isClosed_closure) T z hz, add_zero]
        exact hk
      · have h3 : 0 ≤ mixedEulerDifference p (ns.map Subtype.val) S.X₃ :=
          mixedEulerDifference_nef_nonneg n p hdim ns hlen
            (fun N hN => (hnef N hN).mem_nefCone N.2) S.X₃
        rw [hadd]
        linarith

/-- **The multiplicity bound**: on a projective `D` of dimension `≤ n`, for a maximal point `z`
of `D` (no proper generization), its reduced closure `V`, invertible sheaves `N₁, …, N_n` nef on
`D` and `m ≤ ℓ(𝒪_{D,z})`: `m · (N₁|_V ⋯ N_n|_V)_V ≤ (N₁ ⋯ N_n · 𝒪_D)_D`. -/
theorem mixedEulerDifference_ge_length_mul (n : ℕ) (hdim : topologicalKrullDim D ≤ n) (z : D)
    (hmax : ∀ y : D, y ⤳ z → y = z) (ns : List {N : D.Modules // IsInvertible N})
    (hlen : ns.length = n) (hnef : ∀ N ∈ ns, IsNefOn p N.1 Set.univ) (m : ℕ)
    (hm : (m : ℕ∞) ≤ stalkLength (unitObj D) z) :
    (m : ℤ) * mixedEulerDifference (pointClosureι z ≫ p)
        (ns.map fun N => (Scheme.Modules.pullback (pointClosureι z)).obj N.1)
        (unitObj (pointClosure z)) ≤
      mixedEulerDifference p (ns.map Subtype.val) (unitObj D) := by
  let : (unitObj D).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D).IsFiniteType := isFiniteType_of_isInvertible' isInvertible_unit
  obtain ⟨r, hfil⟩ := exists_finite_coherent_primeFiltration p (unitObj D)
  obtain ⟨k, hk, hk'⟩ := filtration_bound p n hdim z hmax ns hlen hnef hfil
  have hmk : (m : ℤ) ≤ k := by exact_mod_cast (hm.trans hk : (m : ℕ∞) ≤ k)
  have hc : 0 ≤ mixedEulerDifference (pointClosureι z ≫ p)
      (ns.map fun N => (Scheme.Modules.pullback (pointClosureι z)).obj N.1)
      (unitObj (pointClosure z)) := by
    let : (unitObj (pointClosure z)).IsQuasicoherent := isInvertible_unit.isQuasicoherent
    let : (unitObj (pointClosure z)).IsFiniteType :=
      isFiniteType_of_isInvertible' isInvertible_unit
    have h := mixedEulerDifference_nef_nonneg n (pointClosureι z ≫ p)
      (topologicalKrullDim_pointClosure_le_of_le hdim z)
      (ns.map fun N => ⟨(Scheme.Modules.pullback (pointClosureι z)).obj N.1, N.2.pullback _⟩)
      (by simpa using hlen)
      (fun N' hN' => by
        obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hN'
        exact (((hnef N hN).pullback (pointClosureι z)).mono fun _ _ => trivial).mem_nefCone _)
      (unitObj (pointClosure z))
    rwa [List.map_map] at h
  exact (mul_le_mul_of_nonneg_right hmk hc).trans hk'

/-- **The multiplicity bound for `ℚ`-classes**: with the hypotheses of
`mixedEulerDifference_ge_length_mul`, for `n` classes `θ₁, …, θ_n ∈ Pic(D)_ℚ` nef on `D`:
`m · (θ₁|_V ⋯ θ_n|_V)_V ≤ (θ₁ ⋯ θ_n)_D`. -/
theorem interFormQ_ge_length_mul (n : ℕ) (hdim : topologicalKrullDim D ≤ n) (z : D)
    (hmax : ∀ y : D, y ⤳ z → y = z) (m : ℕ) (hm : (m : ℕ∞) ≤ stalkLength (unitObj D) z)
    (s : Multiset (PicQ D)) (hs : ∀ θ ∈ s, θ ∈ relNefCone p Set.univ)
    (hcard : Multiset.card s = n) :
    (m : ℚ) * interFormQ (pointClosureι z ≫ p) n (topologicalKrullDim_pointClosure_le_of_le hdim z)
        (unitObj (pointClosure z)) (s.map (picPullbackQ (pointClosureι z))) ≤
      interFormQ p n hdim (unitObj D) s := by
  let : (unitObj D).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D).IsFiniteType := isFiniteType_of_isInvertible' isInvertible_unit
  let : (unitObj (pointClosure z)).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj (pointClosure z)).IsFiniteType := isFiniteType_of_isInvertible' isInvertible_unit
  set Φ := interFormQ p n hdim (unitObj D) with hΦ
  set Ψ := (interFormQ (pointClosureι z ≫ p) n (topologicalKrullDim_pointClosure_le_of_le hdim z)
    (unitObj (pointClosure z))).comp (picPullbackQ (pointClosureι z)) with hΨ
  let Δ : MultisetForm ℚ (PicQ D) :=
    { toFun := fun t => Φ t - (m : ℚ) * Ψ t
      map_add' := fun x y t => by rw [Φ.map_add', Ψ.map_add']; ring
      map_smul' := fun c x t => by rw [Φ.map_smul', Ψ.map_smul']; ring }
  have h := MultisetForm.nonneg_of_mem_hull Δ
    (fun N : {N : {N : D.Modules // IsInvertible N} // IsNefOn p N.1 Set.univ} => picQ N.1) s 0
    (fun θ hθ => relNefCone_univ_le_hull p (hs θ hθ)) (fun l hl => ?_)
  · rw [zero_add] at h
    change 0 ≤ Φ s - (m : ℚ) * Ψ s at h
    change (m : ℚ) * Ψ s ≤ Φ s
    linarith
  · rw [zero_add]
    change 0 ≤ Φ _ - (m : ℚ) * Ψ _
    have hl' : (l.map fun N => N.1).length = n := by simpa [hcard] using hl
    have h1 := interFormQ_picQ p n hdim (unitObj D) (l.map fun N => N.1) hl'
    let L' : List {N : (pointClosure z).Modules // IsInvertible N} :=
      (l.map fun N => N.1).map fun N =>
        ⟨(Scheme.Modules.pullback (pointClosureι z)).obj N.1, N.2.pullback _⟩
    have h2 := interFormQ_picQ (pointClosureι z ≫ p) n
      (topologicalKrullDim_pointClosure_le_of_le hdim z) (unitObj (pointClosure z)) L'
      (by simpa [L'] using hl')
    have hΦl : Φ ((l.map fun N => picQ N.1 : List (PicQ D)) : Multiset (PicQ D)) =
        mixedEulerDifference p ((l.map fun N => N.1).map Subtype.val) (unitObj D) := by
      rw [← h1, List.map_map]
      rfl
    have e1 : L'.map Subtype.val =
        (l.map fun N => N.1).map fun N => (Scheme.Modules.pullback (pointClosureι z)).obj N.1 := by
      simp only [L', List.map_map]
      rfl
    have e2 : ((L'.map picQ : List (PicQ (pointClosure z))) : Multiset (PicQ (pointClosure z))) =
        ((l.map fun N => picQ N.1 : List (PicQ D)) : Multiset (PicQ D)).map
          (picPullbackQ (pointClosureι z)) := by
      simp only [L', Multiset.map_coe, List.map_map]
      congr 1
      refine List.map_congr_left fun N _ => ?_
      exact (picPullbackQ_picQ _ _).symm
    have hΨl : Ψ ((l.map fun N => picQ N.1 : List (PicQ D)) : Multiset (PicQ D)) =
        mixedEulerDifference (pointClosureι z ≫ p)
          ((l.map fun N => N.1).map fun N => (Scheme.Modules.pullback (pointClosureι z)).obj N.1)
          (unitObj (pointClosure z)) := by
      rw [← e1, ← h2, e2]
      rfl
    rw [hΦl, hΨl]
    have key := mixedEulerDifference_ge_length_mul p n hdim z hmax (l.map fun N => N.1) hl'
      (fun N hN => by
        obtain ⟨M, -, rfl⟩ := List.mem_map.mp hN
        exact M.2) m hm
    have key' : ((m : ℤ) : ℚ) * ((mixedEulerDifference (pointClosureι z ≫ p)
        ((l.map fun N => N.1).map fun N => (Scheme.Modules.pullback (pointClosureι z)).obj N.1)
        (unitObj (pointClosure z)) : ℤ) : ℚ) ≤
        ((mixedEulerDifference p ((l.map fun N => N.1).map Subtype.val) (unitObj D) : ℤ) : ℚ) := by
      exact_mod_cast key
    push_cast at key'
    linarith

end core

end SGPT.NAPotential.ThinApprox.BJCycle
