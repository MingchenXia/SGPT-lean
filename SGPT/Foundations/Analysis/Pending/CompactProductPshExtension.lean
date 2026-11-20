import SGPT.Foundations.Analysis.Pending.ProductPshAssembly
import SGPT.Foundations.Analysis.Pending.CurveCollarPsh
import SGPT.Foundations.Analysis.Pending.ThetaPshCollarGluing
import SGPT.Foundations.Analysis.FirstPass.QuasiPshSingularities

set_option autoImplicit false

/-! # Actual compact-curve collar extension retaining singular reference poles -/

open Set
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactProductPshExtension

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses FirstPass.AnalyticGluingData
  ProductComplexManifold CurveCollarBackground

noncomputable section

/-- Natural joint subgeodesic data and a true compact curve collar produce the
actual global PSH extension and a zero-background core. No gluing, background
positivity, reference singularity or target core identity is assumed. -/
theorem exists_compact_product_psh_extension {n : ℕ} {M T : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
    [CompactSpace T]
    (θ : ClosedRealOneOneForm n M) (ωT : KahlerBackground 1 T)
    {φ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {U : ℝ → M → EReal} (hU : IsSubgeodesicInterior θ.val U)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      φ x + ((-C : ℝ) : EReal) ≤ U t x ∧ U t x ≤ φ x + (C : EReal))
    {K V1 V2 V3 : Set T} (hK : IsCompact K)
    (hV1 : IsOpen V1) (hV2 : IsOpen V2) (hV3 : IsOpen V3)
    (hKV1 : K ⊆ V1) (hcl1 : closure V1 ⊆ V2) (hcl2 : closure V2 ⊆ V3)
    {τ : T → ℂ}
    (hτ : ∀ b : ComplexChart 1 T, DifferentiableOn ℂ (τ ∘ b.val.symm)
      (b.val.target ∩ b.val.symm ⁻¹' V3))
    (htime : ∀ y ∈ V3, (τ y).re ∈ Ioo (0 : ℝ) 1) :
    ∃ (κ : ClosedRealOneOneForm 1 T) (W : M × T → EReal) (N : Set T),
      κ.val.IsSemipositive ∧
      IsThetaPshPotential (prodForm θ κ).val (fun p : M × T => φ p.1) ∧
      IsThetaPshPotential (prodForm θ κ).val W ∧
      SameSingularityTypeOn W (fun p : M × T => φ p.1) univ ∧
      IsOpen N ∧ K ⊆ N ∧ N ⊆ V3 ∧
      (∀ (e : ComplexChart 1 T) z, z ∈ e.val.target → e.val.symm z ∈ N →
        κ.val.coeff e z = 0) ∧
      (∀ x y, y ∈ N → W (x, y) = U (τ y).re x) ∧
      ∀ p : M × T, φ p.1 + ((-C - 1 : ℝ) : EReal) ≤ W p ∧
        W p ≤ φ p.1 + (C : EReal) := by
  classical
  let D : ℝ := 2 * C + 2
  have hD : 0 ≤ D := by dsimp [D]; linarith
  obtain ⟨ρin, ρout, hin, hout, B, -, -, -, hinN, -, -, houtup,
    houtN, houtoff, hκ, -, hq⟩ :=
    CurveCollarPsh.exists_curveCollarPsh ωT hK hV1 hV2 hKV1 hcl1 D hD
  let κ := curveCollarBackground ωT D B ρin hin
  let q : T → EReal := fun y => ((D * ρout y : ℝ) : EReal)
  let f : M × T → EReal := fun p => U (τ p.2).re p.1 + q p.2
  let g : M × T → EReal := fun p => φ p.1 + ((-C - 1 : ℝ) : EReal)
  let Ω : Set (M × T) := univ ×ˢ V3
  let Ω' : Set (M × T) := univ ×ˢ V2
  let W := gluedMax Ω f g
  have hreference := ProductPshAssembly.isThetaPshPotential_product_reference θ κ hφ hκ
  have hg : IsThetaPshPotential (prodForm θ κ).val g := hreference.add_const (-C - 1)
  have hf : ThetaPlurisubharmonicOn (prodForm θ κ).val f Ω :=
    ProductPshAssembly.thetaPlurisubharmonicOn_product_subgeodesic_add_vertical
      θ κ hU hq.1 hV3 hτ htime
  have hclosure : closure Ω' ⊆ Ω := by
    rw [closure_prod_eq]
    intro p hp
    exact ⟨mem_univ _, hcl2 hp.2⟩
  have hcollar : ∀ p ∈ Ω \ Ω', f p ≤ g p := by
    intro p hp
    have houtp : ρout p.2 = -1 := houtoff _ (fun hy => hp.2 ⟨mem_univ _, hy⟩)
    change U (τ p.2).re p.1 + ((D * ρout p.2 : ℝ) : EReal) ≤
      φ p.1 + ((-C - 1 : ℝ) : EReal)
    rw [houtp, mul_neg_one]
    calc
      U (τ p.2).re p.1 + ((-D : ℝ) : EReal) ≤
          (φ p.1 + (C : EReal)) + ((-D : ℝ) : EReal) :=
        add_le_add (hbound _ (htime p.2 hp.1.2) p.1).2 le_rfl
      _ = φ p.1 + ((C + -D : ℝ) : EReal) := by rw [EReal.coe_add, add_assoc]
      _ ≤ φ p.1 + ((-C - 1 : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by dsimp [D]; linarith))
  have hW : IsThetaPshPotential (prodForm θ κ).val W :=
    QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax
      (isOpen_univ.prod hV3) hclosure hcollar hf hg
  have hgup (p : M × T) : g p ≤ φ p.1 + (C : EReal) :=
    add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
  have hWbounds (p : M × T) : g p ≤ W p ∧ W p ≤ φ p.1 + (C : EReal) := by
    by_cases hp : p ∈ Ω
    · change g p ≤ gluedMax Ω f g p ∧ gluedMax Ω f g p ≤ _
      rw [gluedMax_eq_max hp]
      refine ⟨le_max_right _ _, max_le ?_ (hgup p)⟩
      have hqup : q p.2 ≤ 0 := by
        change ((D * ρout p.2 : ℝ) : EReal) ≤ 0
        exact_mod_cast mul_nonpos_of_nonneg_of_nonpos hD (houtup p.2)
      calc
        f p ≤ U (τ p.2).re p.1 + 0 := add_le_add le_rfl hqup
        _ = U (τ p.2).re p.1 := add_zero _
        _ ≤ φ p.1 + (C : EReal) := (hbound _ (htime p.2 hp.2) p.1).2
    · have heq : W p = g p := by simp only [W, gluedMax, hp, ↓reduceIte]
      exact ⟨le_of_eq heq.symm, heq.le.trans (hgup p)⟩
  have hsame : SameSingularityTypeOn W (fun p : M × T => φ p.1) univ := by
    refine ⟨⟨C, fun p _ => (hWbounds p).2⟩, ⟨C + 1, fun p _ => ?_⟩⟩
    calc
      φ p.1 = g p + ((C + 1 : ℝ) : EReal) := by
        change φ p.1 = (φ p.1 + ((-C - 1 : ℝ) : EReal)) + ((C + 1 : ℝ) : EReal)
        rw [add_assoc, ← EReal.coe_add]
        have heq : -C - 1 + (C + 1) = 0 := by ring
        rw [heq]
        simp
      _ ≤ W p + ((C + 1 : ℝ) : EReal) := add_le_add (hWbounds p).1 le_rfl
  obtain ⟨Nin, hNin, hKNin, hinzero⟩ := hinN
  obtain ⟨Nout, -, hcl1Nout, houtzero⟩ := houtN
  let N := Nin ∩ V1
  have hNV3 : N ⊆ V3 := fun y hy => hcl2 (subset_closure (hcl1 (subset_closure hy.2)))
  refine ⟨κ, W, N, hκ, hreference, hW, hsame, hNin.inter hV1,
    fun y hy => ⟨hKNin hy, hKV1 hy⟩, hNV3, ?_, ?_, hWbounds⟩
  · intro e z _ hzN
    change (curveCollarBackground ωT D B ρin hin).val.coeff e z = 0
    rw [curveCollarBackground_coeff, hinzero _ hzN.1]
    simp
  · intro x y hy
    have hyV3 := hNV3 hy
    change gluedMax Ω f g (x, y) = U (τ y).re x
    have hpΩ : (x, y) ∈ Ω := ⟨mem_univ _, hyV3⟩
    rw [gluedMax_eq_max hpΩ]
    have hqy : q y = 0 := by
      change ((D * ρout y : ℝ) : EReal) = 0
      rw [houtzero _ (hcl1Nout (subset_closure hy.2))]
      simp
    have hfy : f (x, y) = U (τ y).re x := by dsimp [f]; rw [hqy, add_zero]
    rw [hfy]
    apply max_eq_left
    calc
      g (x, y) ≤ φ x + ((-C : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
      _ ≤ U (τ y).re x := (hbound _ (htime y hyV3) x).1

end

end SGPT.Foundations.Analysis.Pending.CompactProductPshExtension
