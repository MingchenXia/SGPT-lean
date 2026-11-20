import SGPT.Toric.BigToricCorrespondence
import SGPT.Toric.PolytopeToricOperations

/-!
# Rooftops, regularized suprema and decreasing limits in a big toric class

Source `chapter_toric_big.tex`:

* `prop:toricrooftopbig`: for `φ, ψ ∈ PSH_tor(X, θ)` with `φ ∧ ψ ≢ -∞`, the rooftop is
  toric, `F_{φ∧ψ} = F_φ ∧ F_ψ` and `G_{φ∧ψ} = G_φ ∨ G_ψ`;
* `prop:toricseqbig`: for a non-empty family uniformly bounded above, the regularized
  supremum is toric with `F = ⋁ F_{φ_i}` and `G = cl ⋀ G_{φ_i}` (`G = ⋀ G_{φ_i}` for finite
  families, where the regularized supremum is the maximum); for a decreasing net with
  `inf φ_i ≢ -∞`, the infimum is toric with `F = inf F_{φ_i}` and `G = ⋁ G_{φ_i}`.

`θ = c_1(O(D), h)` for an arbitrary torus-invariant divisor `D` and `T_c`-invariant metric
`h`; `P_D` is assumed nonempty where Legendre duality is used (it is `n`-dimensional for a
big `D`, and it is nonempty as soon as `PSH_tor(X, θ) ≠ ∅`, see
`nonempty_toricDivisorPolytope_of_mem`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- A convex function `> -∞` which is bounded by `C + F_θ` is in the real growth class. -/
theorem realGrowth_of_le_potential {H : EuclideanSpace ℝ (Fin n) → EReal} (hH : IsConvex H)
    (hbot : ∀ x, H x ≠ ⊥) (C : ℝ)
    (hle : ∀ x, H x ≤ ((C + h.potential x : ℝ) : EReal)) :
    (fun x => (H x).toReal) ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) ∧
      H = fun x => ((H x).toReal : EReal) := by
  have htop : ∀ x, H x ≠ ⊤ := fun x => ne_of_lt ((hle x).trans_lt (EReal.coe_lt_top _))
  have hreal : H = fun x => ((H x).toReal : EReal) :=
    funext fun x => (EReal.coe_toReal (htop x) (hbot x)).symm
  have hconv : ConvexOn ℝ univ (fun x => (H x).toReal) := by
    apply isConvex_coe_iff.mp
    rw [← hreal]
    exact hH
  refine ⟨⟨hconv, ?_⟩, hreal⟩
  apply h.singularityLE_support_of_le_potential hconv C
  intro x
  have h1 := hle x
  rw [hreal] at h1
  exact EReal.coe_le_coe_iff.mp h1

/-- A convex function `> -∞` below a toric profile is in the real growth class. -/
theorem realGrowth_of_le_profile {H : EuclideanSpace ℝ (Fin n) → EReal} (hH : IsConvex H)
    (hbot : ∀ x, H x ≠ ⊥) {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hle : H ≤ h.profile u) :
    (fun x => (H x).toReal) ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) ∧
      H = fun x => ((H x).toReal : EReal) := by
  obtain ⟨C, hC⟩ := h.exists_upper_bound hu.1
  exact h.realGrowth_of_le_potential hH hbot C
    (fun x => (hle x).trans (h.profile_le_of_le hC x))

/-! ### Rooftops (source `prop:toricrooftopbig`) -/

/-- The rooftop of two `T_c`-invariant functions is `T_c`-invariant. -/
theorem invariant_thetaRooftop {u v : PolytopeToricVariety γ hs → EReal}
    (hiu : PolytopeToricInvariant γ hs u) (hiv : PolytopeToricInvariant γ hs v) :
    PolytopeToricInvariant γ hs (thetaRooftop h.atlasForm u v) := by
  have hle (a : Fin n → ℂˣ) (ha : IsCompactTorusElement a) (p : PolytopeToricVariety γ hs) :
      thetaRooftop h.atlasForm u v (polytopeToricAction γ hs a p) ≤
        thetaRooftop h.atlasForm u v p := by
    change (⨆ f : {f : PolytopeToricVariety γ hs → EReal //
        (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm f ∧
          f ≤ u ∧ f ≤ v}, f.val (polytopeToricAction γ hs a p)) ≤ _
    apply iSup_le
    intro f
    exact le_thetaRooftop (h.isThetaPSH_comp_action f.property.1 ha)
      (fun q => (f.property.2.1 (polytopeToricAction γ hs a q)).trans_eq (hiu a ha q))
      (fun q => (f.property.2.2 (polytopeToricAction γ hs a q)).trans_eq (hiv a ha q)) p
  intro a ha p
  apply le_antisymm (hle a ha p)
  have h' := hle a⁻¹ (isCompactTorusElement_inv ha) (polytopeToricAction γ hs a p)
  rwa [← polytopeToricAction_mul, inv_mul_cancel, polytopeToricAction_one] at h'

/-- Source `prop:toricrooftopbig`: under `φ ∧ ψ ≢ -∞`, the rooftop is a toric potential. -/
theorem mem_PSHTor_thetaRooftop {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (hne : thetaRooftop h.atlasForm u v ≠ ⊥) :
    thetaRooftop h.atlasForm u v ∈ h.PSHTor := by
  refine ⟨?_, h.invariant_thetaRooftop hu.2 hv.2⟩
  rcases isThetaPSHOrBot_thetaRooftop (Or.inl hu.1) (Or.inl hv.1) with h' | h'
  · exact h'
  · exact False.elim (hne h')

/-- Source `prop:toricrooftopbig`: `F_{φ∧ψ} = F_φ ∧ F_ψ`. -/
theorem profile_thetaRooftop (hP : (toricDivisorPolytope D).Nonempty)
    {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (hne : thetaRooftop h.atlasForm u v ≠ ⊥) :
    h.profile (thetaRooftop h.atlasForm u v) =
      convexInf (fun b : Bool => if b then h.profile v else h.profile u) := by
  let R := thetaRooftop h.atlasForm u v
  let f := fun b : Bool => if b then h.profile v else h.profile u
  let H := convexInf f
  have hR : R ∈ h.PSHTor := h.mem_PSHTor_thetaRooftop hu hv hne
  have hRF := h.profile_mem_growthClass hP hR
  have hRu : h.profile R ≤ h.profile u := (h.le_iff hR hu).mp (thetaRooftop_le_left _ u v)
  have hRv : h.profile R ≤ h.profile v := (h.le_iff hR hv).mp (thetaRooftop_le_right _ u v)
  have hRH : h.profile R ≤ H := by
    apply le_convexInf hRF.1.1
    intro b
    cases b
    · exact hRu
    · exact hRv
  have hHu : H ≤ h.profile u := convexInf_le f false
  have hHv : H ≤ h.profile v := convexInf_le f true
  have hbot : ∀ x, H x ≠ ⊥ := fun x =>
    ne_of_gt ((bot_lt_iff_ne_bot.mpr (hRF.1.2.2 x)).trans_le (hRH x))
  obtain ⟨hgrowth, hreal⟩ := h.realGrowth_of_le_profile (isConvex_convexInf f) hbot hu hHu
  let w := h.extension (fun x => (H x).toReal) hgrowth
  have hw := h.extension_mem _ hgrowth
  have hwF : h.profile w = H := (h.profile_extension _ hgrowth).trans hreal.symm
  have hwu : w ≤ u := (h.le_iff hw hu).mpr (by rw [hwF]; exact hHu)
  have hwv : w ≤ v := (h.le_iff hw hv).mpr (by rw [hwF]; exact hHv)
  have hwR : w ≤ R := le_thetaRooftop hw.1 hwu hwv
  have hHR := (h.le_iff hw hR).mp hwR
  rw [hwF] at hHR
  exact le_antisymm hRH hHR

/-- Source `prop:toricrooftopbig`: `G_{φ∧ψ} = G_φ ∨ G_ψ`. -/
theorem legendre_thetaRooftop (hP : (toricDivisorPolytope D).Nonempty)
    {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (hne : thetaRooftop h.atlasForm u v ≠ ⊥) :
    h.legendre (thetaRooftop h.atlasForm u v) =
      fun m => max (h.legendre u m) (h.legendre v m) := by
  unfold legendre
  rw [h.profile_thetaRooftop hP hu hv hne, conjugate_convexInf]
  funext m
  simp [convexSup, iSup_bool_eq, sup_comm]

/-! ### Regularized suprema (source `prop:toricseqbig`, first part) -/

/-- Torus values of a toric potential through its profile. -/
theorem embedding_add {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (a : Fin n → ℂˣ) :
    u (polytopeToricEmbedding γ hs a) + (h.potential (unitTorusLog a) : EReal) =
      h.profile u (unitTorusLog a) := by
  rw [profile, hu.2.embedding_eq γ hs a]

/-- The pointwise supremum `⋁ F_{φ_i}` of the profiles of a family. -/
def supProfile {I : Type*} (u : I → PolytopeToricVariety γ hs → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨆ i, h.profile (u i) x

theorem supProfile_realGrowth (hP : (toricDivisorPolytope D).Nonempty) {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    (fun x => (h.supProfile u x).toReal) ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) ∧
      h.supProfile u = fun x => ((h.supProfile u x).toReal : EReal) := by
  let i₀ := Classical.arbitrary I
  have hconv : IsConvex (h.supProfile u) :=
    isConvex_iSup fun i => (h.profile_mem_growthClass hP (hu i)).1.1
  have hbot : ∀ x, h.supProfile u x ≠ ⊥ := fun x =>
    ne_of_gt ((bot_lt_iff_ne_bot.mpr
      ((h.profile_mem_growthClass hP (hu i₀)).1.2.2 x)).trans_le
        (le_iSup (fun i => h.profile (u i) x) i₀))
  have hle : ∀ x, h.supProfile u x ≤ ((C + h.potential x : ℝ) : EReal) := fun x =>
    iSup_le fun i => h.profile_le_of_le (hC i) x
  exact h.realGrowth_of_le_potential hconv hbot C hle

/-- On the torus, the pointwise supremum is `Trop^*(⋁ F_{φ_i} - F_θ)`. -/
theorem iSup_embedding (hP : (toricDivisorPolytope D).Nonempty) {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) (a : Fin n → ℂˣ) :
    (⨆ i, u i (polytopeToricEmbedding γ hs a)) =
      (((h.supProfile u (unitTorusLog a)).toReal -
        h.potential (unitTorusLog a) : ℝ) : EReal) := by
  apply EReal.eq_coe_sub_of_add_coe_eq
  rw [← SGPT.Foundations.Analysis.FirstPass.iSup_add_coe,
    iSup_congr fun i => h.embedding_add (hu i) a]
  exact congrFun (h.supProfile_realGrowth hP hu hC).2 (unitTorusLog a)

/-- The regularized supremum of a uniformly bounded family of toric potentials is the
extension of the supremum of the profiles. -/
theorem uscSup_eq_extension (hP : (toricDivisorPolytope D).Nonempty) {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    uscSup u = h.extension (fun x => (h.supProfile u x).toReal)
      (h.supProfile_realGrowth hP hu hC).1 := by
  obtain ⟨hgrowth, hreal⟩ := h.supProfile_realGrowth hP hu hC
  have hw := h.extension_mem _ hgrowth
  have hwF : h.profile (h.extension _ hgrowth) = h.supProfile u :=
    (h.profile_extension _ hgrowth).trans hreal.symm
  have hU : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm (uscSup u) :=
    isThetaPSH_uscSup_of_majorant (fun i => (hu i).1) upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top C) (fun i p => hC i p)
  apply le_antisymm
  · apply uscRegularization_le hw.1.upperSemicontinuous
    intro p
    apply iSup_le
    intro i
    have hle : h.profile (u i) ≤ h.profile (h.extension _ hgrowth) := by
      rw [hwF]
      exact fun x => le_iSup (fun j => h.profile (u j) x) i
    exact (h.le_iff (hu i) hw).mpr hle p
  · intro p
    have h' := h.le_add_of_le_off hw.1 hU 0 ?_ p
    · simpa only [EReal.coe_zero, add_zero] using h'
    intro q hq
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs q).mp hq
    rw [EReal.coe_zero, add_zero,
      (h.extension_spec _ hgrowth).2 (polytopeToricEmbedding_mem_compl γ hs a),
      offPotential_embedding, ← h.iSup_embedding hP hu hC a]
    exact le_uscRegularization (fun x => ⨆ i, u i x) (polytopeToricEmbedding γ hs a)

/-- Source `prop:toricseqbig`: the regularized supremum of a non-empty uniformly bounded
above family in `PSH_tor(X, θ)` is in `PSH_tor(X, θ)`. -/
theorem mem_PSHTor_uscSup (hP : (toricDivisorPolytope D).Nonempty) {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) : uscSup u ∈ h.PSHTor := by
  rw [h.uscSup_eq_extension hP hu hC]
  exact h.extension_mem _ _

/-- Source `prop:toricseqbig`: `F_{usc sup φ_i} = ⋁ F_{φ_i}`. -/
theorem profile_uscSup (hP : (toricDivisorPolytope D).Nonempty) {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    h.profile (uscSup u) = convexSup (fun i => h.profile (u i)) := by
  rw [h.uscSup_eq_extension hP hu hC, h.profile_extension]
  exact (h.supProfile_realGrowth hP hu hC).2.symm

/-- Source `prop:toricseqbig`: `G_{usc sup φ_i} = cl ⋀ G_{φ_i}`. -/
theorem legendre_uscSup (hP : (toricDivisorPolytope D).Nonempty) {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    h.legendre (uscSup u) = convexClosure (convexInf (fun i => h.legendre (u i))) := by
  unfold legendre
  rw [h.profile_uscSup hP hu hC]
  have h' := conjugate_convexSup_convexClosure (innerₗ (EuclideanSpace ℝ (Fin n)))
    (f := fun i => h.profile (u i))
    (fun i => (h.profile_mem_growthClass hP (hu i)).1.1)
  have hcl : (fun i => convexClosure (h.profile (u i))) = fun i => h.profile (u i) :=
    funext fun i => convexClosure_eq_self_of_isClosedConvex (h.isClosedConvex_profile hP (hu i))
  rw [hcl] at h'
  exact h'

/-- For a finite family the regularized supremum is the pointwise maximum. -/
theorem uscSup_eq_iSup_of_finite {I : Type*} [Finite I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor) :
    uscSup u = fun p => ⨆ i, u i p := by
  funext p
  exact uscSup_eq_iSup_finite isOpen_univ
    (fun i => (hu i).1.upperSemicontinuous.upperSemicontinuousOn univ) (mem_univ p)

/-- Source `prop:toricseqbig`, finite families: `G_{max φ_i} = ⋀ G_{φ_i}`. -/
theorem legendre_iSup_of_fintype (hP : (toricDivisorPolytope D).Nonempty)
    {I : Type*} [Fintype I] [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor) :
    (fun p => ⨆ i, u i p) ∈ h.PSHTor ∧
      h.legendre (fun p => ⨆ i, u i p) = convexInf (fun i => h.legendre (u i)) := by
  have hbound : ∀ i, ∃ C : ℝ, ∀ p, u i p ≤ (C : EReal) := fun i => h.exists_upper_bound (hu i).1
  choose c hc using hbound
  let C : ℝ := Finset.univ.sup' Finset.univ_nonempty c
  have hC : ∀ i p, u i p ≤ (C : EReal) := fun i p =>
    (hc i p).trans (EReal.coe_le_coe_iff.mpr (Finset.le_sup' c (Finset.mem_univ i)))
  have heq := h.uscSup_eq_iSup_of_finite hu
  refine ⟨by rw [← heq]; exact h.mem_PSHTor_uscSup hP hu hC, ?_⟩
  rw [← heq]
  unfold legendre
  rw [h.profile_uscSup hP hu hC]
  apply conjugate_convexSup_eq_convexInf_of_isContPerfPair_of_closure_eq
  · exact fun i => (h.profile_mem_growthClass hP (hu i)).1
  · intro i j
    rw [effectiveDomain_eq_univ_of_mem_growthClass _ (isCompact_toricDivisorPolytope D) hP
        (h.profile_mem_growthClass hP (hu i)),
      effectiveDomain_eq_univ_of_mem_growthClass _ (isCompact_toricDivisorPolytope D) hP
        (h.profile_mem_growthClass hP (hu j))]

/-! ### Decreasing nets (source `prop:toricseqbig`, second part) -/

/-- Source `prop:toricseqbig`: the limit of a decreasing net in `PSH_tor(X, θ)` with
`inf φ_i ≢ -∞` is in `PSH_tor(X, θ)`. -/
theorem mem_PSHTor_iInf {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ h.PSHTor)
    (hanti : ∀ p, Antitone (fun i => u i p)) (hne : (fun p => ⨅ i, u i p) ≠ ⊥) :
    (fun p => ⨅ i, u i p) ∈ h.PSHTor := by
  refine ⟨?_, fun a ha p => iInf_congr fun i => (hu i).2 a ha p⟩
  have hn : ∀ i, IsThetaPshPotential h.form.val (u i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm (u i)).mp (hu i).1
  obtain ⟨p, hp⟩ : ∃ p, (⨅ i, u i p) ≠ ⊥ := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hne (funext hc)
  let i₀ := Classical.arbitrary I
  have htop : (⨅ i, u i p) ≠ ⊤ :=
    ne_of_lt ((iInf_le (fun i => u i p) i₀).trans_lt (lt_top_iff_ne_top.mpr ((hu i₀).1.1 p)))
  have ha : ∀ i, (((⨅ i, u i p).toReal : ℝ) : EReal) ≤ ⨆ x, u i x := by
    intro i
    rw [EReal.coe_toReal htop hp]
    exact (iInf_le (fun i => u i p) i).trans (le_iSup (fun x => u i x) p)
  have hlim := (isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound hn hanti _ ha).1
  exact (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mpr hlim

/-- Source `prop:toricseqbig`: `F_{inf φ_i} = inf F_{φ_i}`. -/
theorem profile_iInf {I : Type*} (u : I → PolytopeToricVariety γ hs → EReal) :
    h.profile (fun p => ⨅ i, u i p) = fun x => ⨅ i, h.profile (u i) x := by
  funext x
  exact (Pending.ThetaPshDecreasingLimit.iInf_add_coe _ _).symm

/-- Source `prop:toricseqbig`: `G_{inf φ_i} = ⋁ G_{φ_i}`. -/
theorem legendre_iInf {I : Type*} (u : I → PolytopeToricVariety γ hs → EReal) :
    h.legendre (fun p => ⨅ i, u i p) = convexSup (fun i => h.legendre (u i)) := by
  unfold legendre
  rw [profile_iInf]
  exact conjugate_iInf _ _

end BigToricMetric

end SGPT.Toric
