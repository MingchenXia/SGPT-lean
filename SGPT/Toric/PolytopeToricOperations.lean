import SGPT.Toric.PolytopeToricCorrespondence
import SGPT.PSH.ThetaRooftop
import SGPT.PSH.ThetaDecreasingNets
import SGPT.Convex.FamilyOperations
import SGPT.Convex.CommonDomainFamily

/-!
# Rooftops, regularized suprema and decreasing limits of toric potentials

Source `chapter_toric_ample.tex`:

* `prop:toricrooftop`: for `φ, ψ ∈ PSH_tor(X, ω)` with `φ ∧ ψ ≢ -∞`, the rooftop
  `φ ∧ ψ` is toric, `F_{φ∧ψ} = F_φ ∧ F_ψ` and `G_{φ∧ψ} = G_φ ∨ G_ψ`;
* `prop:toricseq`: for a non-empty uniformly bounded above family, the regularized
  supremum is toric with `F = ⋁ F_{φ_i}` and `G = cl ⋀ G_{φ_i}` (and `G = ⋀ G_{φ_i}`
  for finite families, where the regularized supremum is the maximum); for a
  decreasing net with `inf φ_i ≢ -∞`, the infimum is toric with `F = inf F_{φ_i}` and
  `G = ⋁ G_{φ_i}`.

Here `X = PolytopeToricVariety γ hs` for an arbitrary Delzant lattice polytope.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-- The toric manifold is connected: it is the closure of the connected torus. -/
instance : ConnectedSpace (PolytopeToricVariety γ hs) := by
  let w := polytopeToricBaseVertex γ
  let c := originalPolytopeNativeModelChart γ hs w
  have heq : (polytopeToricBoundary γ hs)ᶜ = c.symm '' complexTorus n := by
    ext p
    constructor
    · intro hp
      obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
      have hs' : polytopeToricEmbedding γ hs a ∈ c.source := by
        change polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs w).source
        rw [originalPolytopeNativeModelChart_source]
        exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs w a
      refine ⟨c (polytopeToricEmbedding γ hs a), ?_, c.left_inv hs'⟩
      apply (polytopeToricVertexChart_symm_mem_compl_iff γ hs w _).mp
      change c.symm (c (polytopeToricEmbedding γ hs a)) ∈ _
      rw [c.left_inv hs']
      exact polytopeToricEmbedding_mem_compl γ hs a
    · rintro ⟨z, hz, rfl⟩
      exact (polytopeToricVertexChart_symm_mem_compl_iff γ hs w z).mpr hz
  have hT : IsConnected (polytopeToricBoundary γ hs)ᶜ := by
    rw [heq]
    apply (isConnected_complexTorus n).image
    apply c.continuousOn_symm.mono
    intro z _
    change z ∈ (originalPolytopeNativeModelChart γ hs w).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hd : closure (polytopeToricBoundary γ hs)ᶜ = univ :=
    (dense_originalPolytopeNativeTorus γ).closure_eq
  apply connectedSpace_iff_univ.mpr
  rw [← hd]
  exact hT.closure

/-- The zero function is a toric potential (`ω` is Kähler). -/
theorem zero_mem_polytopeToricPSH : (fun _ => (0 : EReal)) ∈ PolytopeToricPSH γ hs := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  apply (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) _).mpr
  exact (Pending.LocalPotentials.isThetaPshPotential_zero_iff
    (polytopeToricKahlerBackground γ hs).form).mpr
      (polytopeToricKahlerBackground γ hs).isSemipositive

/-- An upper bound `u ≤ C` gives `F_u ≤ C + F_0`. -/
theorem polytopeToricProfile_le_of_le {u : PolytopeToricVariety γ hs → EReal} {C : ℝ}
    (hC : ∀ p, u p ≤ (C : EReal)) (x : EuclideanSpace ℝ (Fin n)) :
    polytopeToricProfile γ hs u x ≤ ((C + polytopeToricReference γ hs x : ℝ) : EReal) := by
  rw [polytopeToricProfile, EReal.coe_add]
  exact add_le_add (hC _) le_rfl

/-- A convex function `> -∞` which is bounded by `C + F_0` is in the real growth class. -/
theorem realGrowth_of_le_reference {H : EuclideanSpace ℝ (Fin n) → EReal} (hH : IsConvex H)
    (hbot : ∀ x, H x ≠ ⊥) (C : ℝ)
    (hle : ∀ x, H x ≤ ((C + polytopeToricReference γ hs x : ℝ) : EReal)) :
    (fun x => (H x).toReal) ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) ∧
      H = fun x => ((H x).toReal : EReal) := by
  have htop : ∀ x, H x ≠ ⊤ := fun x => ne_of_lt ((hle x).trans_lt (EReal.coe_lt_top _))
  have hreal : H = fun x => ((H x).toReal : EReal) :=
    funext fun x => (EReal.coe_toReal (htop x) (hbot x)).symm
  obtain ⟨h1, _⟩ := (SGPT.PSH.singularityEquiv_iff _ _).mp
    (polytopeToricReference_singularityEquiv_support γ hs)
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h1
  refine ⟨⟨?_, ?_⟩, hreal⟩
  · apply isConvex_coe_iff.mp
    rw [← hreal]
    exact hH
  · rw [← hreal]
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C + D, fun x => ?_⟩
    calc H x ≤ ((C + polytopeToricReference γ hs x : ℝ) : EReal) := hle x
      _ = (C : EReal) + (polytopeToricReference γ hs x : EReal) := EReal.coe_add _ _
      _ ≤ (C : EReal) + (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip
            (polytopeToricMomentPolytope γ) x + (D : EReal)) := add_le_add le_rfl (hD x)
      _ = _ := by rw [add_comm (C : EReal), add_assoc, ← EReal.coe_add, add_comm D C]

/-- A convex function `> -∞` below a toric profile is in the real growth class. -/
theorem realGrowth_of_le_profile {H : EuclideanSpace ℝ (Fin n) → EReal} (hH : IsConvex H)
    (hbot : ∀ x, H x ≠ ⊥) {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hle : H ≤ polytopeToricProfile γ hs u) :
    (fun x => (H x).toReal) ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) ∧
      H = fun x => ((H x).toReal : EReal) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_polytopeToricPSH γ hs hu.1
  exact realGrowth_of_le_reference γ hs hH hbot C
    (fun x => (hle x).trans (polytopeToricProfile_le_of_le γ hs hC x))

/-! ### Rooftops (source `prop:toricrooftop`) -/

/-- The rooftop of two `T_c`-invariant functions is `T_c`-invariant. -/
theorem polytopeToricInvariant_thetaRooftop {u v : PolytopeToricVariety γ hs → EReal}
    (hiu : PolytopeToricInvariant γ hs u) (hiv : PolytopeToricInvariant γ hs v) :
    PolytopeToricInvariant γ hs (thetaRooftop (polytopeToricOmega γ hs) u v) := by
  have hle (a : Fin n → ℂˣ) (ha : IsCompactTorusElement a) (p : PolytopeToricVariety γ hs) :
      thetaRooftop (polytopeToricOmega γ hs) u v (polytopeToricAction γ hs a p) ≤
        thetaRooftop (polytopeToricOmega γ hs) u v p := by
    change (⨆ f : {f : PolytopeToricVariety γ hs → EReal //
        (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) f ∧
          f ≤ u ∧ f ≤ v}, f.val (polytopeToricAction γ hs a p)) ≤ _
    apply iSup_le
    intro f
    exact le_thetaRooftop (isThetaPSH_comp_polytopeToricAction γ hs f.property.1 ha)
      (fun q => (f.property.2.1 (polytopeToricAction γ hs a q)).trans_eq (hiu a ha q))
      (fun q => (f.property.2.2 (polytopeToricAction γ hs a q)).trans_eq (hiv a ha q)) p
  intro a ha p
  apply le_antisymm (hle a ha p)
  have h := hle a⁻¹ (isCompactTorusElement_inv ha) (polytopeToricAction γ hs a p)
  rwa [← polytopeToricAction_mul, inv_mul_cancel, polytopeToricAction_one] at h

/-- Source `prop:toricrooftop`: under `φ ∧ ψ ≢ -∞`, the rooftop is a toric potential. -/
theorem mem_polytopeToricPSH_thetaRooftop {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs)
    (hne : thetaRooftop (polytopeToricOmega γ hs) u v ≠ ⊥) :
    thetaRooftop (polytopeToricOmega γ hs) u v ∈ PolytopeToricPSH γ hs := by
  refine ⟨?_, polytopeToricInvariant_thetaRooftop γ hs hu.2 hv.2⟩
  rcases isThetaPSHOrBot_thetaRooftop (Or.inl hu.1) (Or.inl hv.1) with h | h
  · exact h
  · exact False.elim (hne h)

/-- Source `prop:toricrooftop`: `F_{φ∧ψ} = F_φ ∧ F_ψ`. -/
theorem polytopeToricProfile_thetaRooftop {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs)
    (hne : thetaRooftop (polytopeToricOmega γ hs) u v ≠ ⊥) :
    polytopeToricProfile γ hs (thetaRooftop (polytopeToricOmega γ hs) u v) =
      convexInf (fun b : Bool => if b then polytopeToricProfile γ hs v
        else polytopeToricProfile γ hs u) := by
  let R := thetaRooftop (polytopeToricOmega γ hs) u v
  let f := fun b : Bool => if b then polytopeToricProfile γ hs v else polytopeToricProfile γ hs u
  let H := convexInf f
  have hR : R ∈ PolytopeToricPSH γ hs := mem_polytopeToricPSH_thetaRooftop γ hs hu hv hne
  have hRF := polytopeToricProfile_mem_growthClass γ hs hR
  have hRu : polytopeToricProfile γ hs R ≤ polytopeToricProfile γ hs u :=
    (polytopeToricPSH_le_iff γ hs hR hu).mp (thetaRooftop_le_left _ u v)
  have hRv : polytopeToricProfile γ hs R ≤ polytopeToricProfile γ hs v :=
    (polytopeToricPSH_le_iff γ hs hR hv).mp (thetaRooftop_le_right _ u v)
  have hRH : polytopeToricProfile γ hs R ≤ H := by
    apply le_convexInf hRF.1.1
    intro b
    cases b
    · exact hRu
    · exact hRv
  have hHu : H ≤ polytopeToricProfile γ hs u := convexInf_le f false
  have hHv : H ≤ polytopeToricProfile γ hs v := convexInf_le f true
  have hbot : ∀ x, H x ≠ ⊥ := fun x =>
    ne_of_gt ((bot_lt_iff_ne_bot.mpr (hRF.1.2.2 x)).trans_le (hRH x))
  obtain ⟨hgrowth, hreal⟩ := realGrowth_of_le_profile γ hs (isConvex_convexInf f) hbot hu hHu
  let w := polytopeToricExtension γ hs (fun x => (H x).toReal) hgrowth
  have hw := polytopeToricExtension_mem γ hs _ hgrowth
  have hwF : polytopeToricProfile γ hs w = H :=
    (polytopeToricProfile_extension γ hs _ hgrowth).trans hreal.symm
  have hwu : w ≤ u := (polytopeToricPSH_le_iff γ hs hw hu).mpr (by rw [hwF]; exact hHu)
  have hwv : w ≤ v := (polytopeToricPSH_le_iff γ hs hw hv).mpr (by rw [hwF]; exact hHv)
  have hwR : w ≤ R := le_thetaRooftop hw.1 hwu hwv
  have hHR := (polytopeToricPSH_le_iff γ hs hw hR).mp hwR
  rw [hwF] at hHR
  exact le_antisymm hRH hHR

/-- Source `prop:toricrooftop`: `G_{φ∧ψ} = G_φ ∨ G_ψ`. -/
theorem polytopeToricLegendre_thetaRooftop {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (hv : v ∈ PolytopeToricPSH γ hs)
    (hne : thetaRooftop (polytopeToricOmega γ hs) u v ≠ ⊥) :
    polytopeToricLegendre γ hs (thetaRooftop (polytopeToricOmega γ hs) u v) =
      fun m => max (polytopeToricLegendre γ hs u m) (polytopeToricLegendre γ hs v m) := by
  unfold polytopeToricLegendre
  rw [polytopeToricProfile_thetaRooftop γ hs hu hv hne, conjugate_convexInf]
  funext m
  simp [convexSup, iSup_bool_eq, sup_comm]

/-! ### Regularized suprema (source `prop:toricseq`, first part) -/

/-- Torus values of a toric potential through its profile. -/
theorem polytopeToricPSH_embedding_add {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (a : Fin n → ℂˣ) :
    u (polytopeToricEmbedding γ hs a) + (polytopeToricReference γ hs (unitTorusLog a) : EReal) =
      polytopeToricProfile γ hs u (unitTorusLog a) := by
  rw [polytopeToricProfile, hu.2.embedding_eq γ hs a]

/-- The pointwise supremum `⋁ F_{φ_i}` of the profiles of a family. -/
def polytopeToricSupProfile {I : Type*} (u : I → PolytopeToricVariety γ hs → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨆ i, polytopeToricProfile γ hs (u i) x

theorem polytopeToricSupProfile_realGrowth {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    (fun x => (polytopeToricSupProfile γ hs u x).toReal) ∈
        RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) ∧
      polytopeToricSupProfile γ hs u =
        fun x => ((polytopeToricSupProfile γ hs u x).toReal : EReal) := by
  let i₀ := Classical.arbitrary I
  have hconv : IsConvex (polytopeToricSupProfile γ hs u) :=
    isConvex_iSup fun i => (polytopeToricProfile_mem_growthClass γ hs (hu i)).1.1
  have hbot : ∀ x, polytopeToricSupProfile γ hs u x ≠ ⊥ := fun x =>
    ne_of_gt ((bot_lt_iff_ne_bot.mpr
      ((polytopeToricProfile_mem_growthClass γ hs (hu i₀)).1.2.2 x)).trans_le
        (le_iSup (fun i => polytopeToricProfile γ hs (u i) x) i₀))
  have hle : ∀ x, polytopeToricSupProfile γ hs u x ≤
      ((C + polytopeToricReference γ hs x : ℝ) : EReal) := fun x =>
    iSup_le fun i => polytopeToricProfile_le_of_le γ hs (hC i) x
  exact realGrowth_of_le_reference γ hs hconv hbot C hle

/-- On the torus, the pointwise supremum is `Trop^*(⋁ F_{φ_i} - F_0)`. -/
theorem polytopeToric_iSup_embedding {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) (a : Fin n → ℂˣ) :
    (⨆ i, u i (polytopeToricEmbedding γ hs a)) =
      (((polytopeToricSupProfile γ hs u (unitTorusLog a)).toReal -
        polytopeToricReference γ hs (unitTorusLog a) : ℝ) : EReal) := by
  apply EReal.eq_coe_sub_of_add_coe_eq
  rw [← SGPT.Foundations.Analysis.FirstPass.iSup_add_coe,
    iSup_congr fun i => polytopeToricPSH_embedding_add γ hs (hu i) a]
  exact congrFun (polytopeToricSupProfile_realGrowth γ hs hu hC).2 (unitTorusLog a)

/-- The regularized supremum of a uniformly bounded family of toric potentials is the
extension of the supremum of the profiles. -/
theorem polytopeToric_uscSup_eq_extension {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    uscSup u = polytopeToricExtension γ hs (fun x => (polytopeToricSupProfile γ hs u x).toReal)
      (polytopeToricSupProfile_realGrowth γ hs hu hC).1 := by
  obtain ⟨hgrowth, hreal⟩ := polytopeToricSupProfile_realGrowth γ hs hu hC
  have hw := polytopeToricExtension_mem γ hs _ hgrowth
  have hwF : polytopeToricProfile γ hs (polytopeToricExtension γ hs _ hgrowth) =
      polytopeToricSupProfile γ hs u :=
    (polytopeToricProfile_extension γ hs _ hgrowth).trans hreal.symm
  have hU : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs)
      (uscSup u) :=
    isThetaPSH_uscSup_of_majorant (fun i => (hu i).1) upperSemicontinuous_const
      (fun _ => EReal.coe_ne_top C) (fun i p => hC i p)
  apply le_antisymm
  · apply uscRegularization_le hw.1.upperSemicontinuous
    intro p
    apply iSup_le
    intro i
    have hle : polytopeToricProfile γ hs (u i) ≤
        polytopeToricProfile γ hs (polytopeToricExtension γ hs _ hgrowth) := by
      rw [hwF]
      exact fun x => le_iSup (fun j => polytopeToricProfile γ hs (u j) x) i
    exact (polytopeToricPSH_le_iff γ hs (hu i) hw).mpr hle p
  · intro p
    have h := polytopeToricPSH_le_add_of_le_off γ hs hw.1 hU 0 ?_ p
    · simpa only [EReal.coe_zero, add_zero] using h
    intro q hq
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs q).mp hq
    rw [EReal.coe_zero, add_zero,
      (polytopeToricExtension_spec γ hs _ hgrowth).2 (polytopeToricEmbedding_mem_compl γ hs a),
      polytopeToricOffPotential_embedding, ← polytopeToric_iSup_embedding γ hs hu hC a]
    exact le_uscRegularization (fun x => ⨆ i, u i x) (polytopeToricEmbedding γ hs a)

/-- Source `prop:toricseq`: the regularized supremum of a non-empty uniformly bounded
above family in `PSH_tor(X, ω)` is in `PSH_tor(X, ω)`. -/
theorem mem_polytopeToricPSH_uscSup {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) : uscSup u ∈ PolytopeToricPSH γ hs := by
  rw [polytopeToric_uscSup_eq_extension γ hs hu hC]
  exact polytopeToricExtension_mem γ hs _ _

/-- Source `prop:toricseq`: `F_{usc sup φ_i} = ⋁ F_{φ_i}`. -/
theorem polytopeToricProfile_uscSup {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    polytopeToricProfile γ hs (uscSup u) =
      convexSup (fun i => polytopeToricProfile γ hs (u i)) := by
  rw [polytopeToric_uscSup_eq_extension γ hs hu hC, polytopeToricProfile_extension]
  exact (polytopeToricSupProfile_realGrowth γ hs hu hC).2.symm

/-- Source `prop:toricseq`: `G_{usc sup φ_i} = cl ⋀ G_{φ_i}`. -/
theorem polytopeToricLegendre_uscSup {I : Type*} [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    {C : ℝ} (hC : ∀ i p, u i p ≤ (C : EReal)) :
    polytopeToricLegendre γ hs (uscSup u) =
      convexClosure (convexInf (fun i => polytopeToricLegendre γ hs (u i))) := by
  unfold polytopeToricLegendre
  rw [polytopeToricProfile_uscSup γ hs hu hC]
  have h := conjugate_convexSup_convexClosure (innerₗ (EuclideanSpace ℝ (Fin n)))
    (f := fun i => polytopeToricProfile γ hs (u i))
    (fun i => (polytopeToricProfile_mem_growthClass γ hs (hu i)).1.1)
  have hcl : (fun i => convexClosure (polytopeToricProfile γ hs (u i))) =
      fun i => polytopeToricProfile γ hs (u i) :=
    funext fun i => convexClosure_eq_self_of_isClosedConvex
      (isClosedConvex_polytopeToricProfile γ hs (hu i))
  rw [hcl] at h
  exact h

/-- For a finite family the regularized supremum is the pointwise maximum. -/
theorem polytopeToric_uscSup_eq_iSup_of_finite {I : Type*} [Finite I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs) :
    uscSup u = fun p => ⨆ i, u i p := by
  funext p
  exact uscSup_eq_iSup_finite isOpen_univ
    (fun i => (hu i).1.upperSemicontinuous.upperSemicontinuousOn univ) (mem_univ p)

/-- Source `prop:toricseq`, finite families: `G_{max φ_i} = ⋀ G_{φ_i}`. -/
theorem polytopeToricLegendre_iSup_of_fintype {I : Type*} [Fintype I] [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs) :
    (fun p => ⨆ i, u i p) ∈ PolytopeToricPSH γ hs ∧
      polytopeToricLegendre γ hs (fun p => ⨆ i, u i p) =
        convexInf (fun i => polytopeToricLegendre γ hs (u i)) := by
  have hbound : ∀ i, ∃ C : ℝ, ∀ p, u i p ≤ (C : EReal) :=
    fun i => exists_upper_bound_polytopeToricPSH γ hs (hu i).1
  choose c hc using hbound
  let C : ℝ := Finset.univ.sup' Finset.univ_nonempty c
  have hC : ∀ i p, u i p ≤ (C : EReal) := fun i p =>
    (hc i p).trans (EReal.coe_le_coe_iff.mpr (Finset.le_sup' c (Finset.mem_univ i)))
  have heq := polytopeToric_uscSup_eq_iSup_of_finite γ hs hu
  refine ⟨by rw [← heq]; exact mem_polytopeToricPSH_uscSup γ hs hu hC, ?_⟩
  rw [← heq]
  unfold polytopeToricLegendre
  rw [polytopeToricProfile_uscSup γ hs hu hC]
  apply conjugate_convexSup_eq_convexInf_of_isContPerfPair_of_closure_eq
  · exact fun i => (polytopeToricProfile_mem_growthClass γ hs (hu i)).1
  · intro i j
    rw [effectiveDomain_eq_univ_of_mem_growthClass _ (isCompact_polytopeToricMomentPolytope γ)
        (nonempty_polytopeToricMomentPolytope γ) (polytopeToricProfile_mem_growthClass γ hs (hu i)),
      effectiveDomain_eq_univ_of_mem_growthClass _ (isCompact_polytopeToricMomentPolytope γ)
        (nonempty_polytopeToricMomentPolytope γ) (polytopeToricProfile_mem_growthClass γ hs (hu j))]

/-! ### Decreasing nets (source `prop:toricseq`, second part) -/

/-- Source `prop:toricseq`: the limit of a decreasing net in `PSH_tor(X, ω)` with
`inf φ_i ≢ -∞` is in `PSH_tor(X, ω)`. -/
theorem mem_polytopeToricPSH_iInf {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → PolytopeToricVariety γ hs → EReal} (hu : ∀ i, u i ∈ PolytopeToricPSH γ hs)
    (hanti : ∀ p, Antitone (fun i => u i p)) (hne : (fun p => ⨅ i, u i p) ≠ ⊥) :
    (fun p => ⨅ i, u i p) ∈ PolytopeToricPSH γ hs := by
  refine ⟨?_, fun a ha p => iInf_congr fun i => (hu i).2 a ha p⟩
  have hn : ∀ i, IsThetaPshPotential (polytopeToricKahlerForm γ hs).val (u i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) (u i)).mp (hu i).1
  obtain ⟨p, hp⟩ : ∃ p, (⨅ i, u i p) ≠ ⊥ := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (funext h)
  let i₀ := Classical.arbitrary I
  have htop : (⨅ i, u i p) ≠ ⊤ :=
    ne_of_lt ((iInf_le (fun i => u i p) i₀).trans_lt (lt_top_iff_ne_top.mpr ((hu i₀).1.1 p)))
  have ha : ∀ i, (((⨅ i, u i p).toReal : ℝ) : EReal) ≤ ⨆ x, u i x := by
    intro i
    rw [EReal.coe_toReal htop hp]
    exact (iInf_le (fun i => u i p) i).trans (le_iSup (fun x => u i x) p)
  have hlim := (isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound hn hanti _ ha).1
  exact (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) _).mpr hlim

/-- Source `prop:toricseq`: `F_{inf φ_i} = inf F_{φ_i}`. -/
theorem polytopeToricProfile_iInf {I : Type*} (u : I → PolytopeToricVariety γ hs → EReal) :
    polytopeToricProfile γ hs (fun p => ⨅ i, u i p) =
      fun x => ⨅ i, polytopeToricProfile γ hs (u i) x := by
  funext x
  exact (Pending.ThetaPshDecreasingLimit.iInf_add_coe _ _).symm

/-- Source `prop:toricseq`: `G_{inf φ_i} = ⋁ G_{φ_i}`. -/
theorem polytopeToricLegendre_iInf {I : Type*} (u : I → PolytopeToricVariety γ hs → EReal) :
    polytopeToricLegendre γ hs (fun p => ⨅ i, u i p) =
      convexSup (fun i => polytopeToricLegendre γ hs (u i)) := by
  unfold polytopeToricLegendre
  rw [polytopeToricProfile_iInf]
  exact conjugate_iInf _ _

end SGPT.Toric
