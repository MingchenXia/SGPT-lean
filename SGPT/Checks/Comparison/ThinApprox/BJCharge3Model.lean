import SGPT.Checks.Comparison.ThinApprox.BJCharge3Ord

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
# Rees points on every dominating model (lane BJ-CHARGE, R8(c) with the `ordPoint`)

Source: [BJ22] (`references/bj22-trivval`), Lemma `lem:tcdiv` and §2.2; [BHJ17, Theorem 4.6].
Towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-charge3.tex`.

the `exists_reesComponent` proves [BJ22, `lem:tcdiv`] on the normalized blow-up of
`t^N 𝔞` for the flag ideal `𝔞 = valFlag v N` of valuation ideals. The charging of divisorial
points needs the same statement on every model dominating that one (the pairing is computed on
common models), in the language of lane BJ-PAIR:

* `exists_gaussGerms_model`: the germs `pr₁^*(α) t^j` at the centre of the normalized Gauss point
  on an arbitrary model `(𝔠, c₀)`;
* `exists_reesPoint_of_lift`, `exists_reesPoint_of_model`: on every model on which `(t^N 𝔞) · 𝒪`
  is invertible and for every normalized lift of the Gauss point, `σ(v)` is
  `β · ordPoint c` for a codimension-one DVR point `c` of the central fibre, and
  `ord_c((t^b 𝔟) · 𝒪) = β⁻¹ (b - φ_𝔟(v))` for every flag ideal `𝔟` with weight bound `b`;
* `exists_reesPoint_of_divisorial`: the same for every divisorial point `v = s · ord_F`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BerkovichPoint
open SGPT.NAPotential.BJCharge SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel FlagIdealBound
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open scoped Polynomial

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- `exists_gaussGerms` on an arbitrary normalized model `(𝔠, c₀)`: the germs `pr₁^*(α) t^j` at
the centre of the normalized Gauss point, their images in `ℂ(X)(t)`, the values of pulled-back
ideals, and membership in `(t^N 𝔞) · 𝒪`. -/
theorem exists_gaussGerms_model (v : BerkovichPoint p)
    (𝔠 : FlagIdeal X) (c₀ : ℤ) (𝔞 : FlagIdeal X) (N : ℕ)
    (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔠 c₀)
    (hgν : letI := residueComplexAlgebra p v.support
      g ≫ normModelν p 𝔠 c₀ = gaussModelMap (K := X.residueField v.support) p
        (X.fromSpecResidueField v.support) (fromSpecResidueField_structure v) 𝔠 c₀)
    (hg : letI := residueComplexAlgebra p v.support
      g ≫ normModelStructure p 𝔠 c₀ =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X])))) :
    letI := residueComplexAlgebra p v.support
    (∀ J : (productLine p).IdealSheafData,
      (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v)).idealVal
        (J.comap (normModelπ p 𝔠 c₀)) = (gaussPoint v).idealVal J) ∧
    normModelπ p 𝔠 c₀ (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg
      (berkovichGaussExtension v)).center ∈ ((centralIdeal p).support : Set (productLine p)) ∧
    ∃ H : X.presheaf.stalk v.center → ℕ → (normModel p 𝔠 c₀).presheaf.stalk
        (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v)).center,
      (∀ α j, (fieldEmb g).hom ((specializationMap (fieldBerkovichPoint (normModelStructure p 𝔠 c₀)
        g hg (berkovichGaussExtension v)).support_specializes_center).hom (H α j)) =
          polyEmb (Polynomial.C ((specializationMap v.support_specializes_center).hom α)) *
            polyEmb Polynomial.X ^ j) ∧
      (∀ α j, α ∈ stalkIdeal (𝔞.ideal ((N : ℤ) - (j : ℕ))) v.center →
        H α j ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀))
          (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg
            (berkovichGaussExtension v)).center) := by
  let := residueComplexAlgebra p v.support
  let ι := X.fromSpecResidueField v.support
  have hι := fromSpecResidueField_structure v
  have h_gπ : g ≫ normModelπ p 𝔠 c₀ = gaussMap (K := X.residueField v.support) p ι hι := by
    rw [normModelπ, ← Category.assoc, hgν, gaussModelMap_π]
  let W := berkovichGaussExtension v
  let w := fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg W
  have hππ : normModelπ p 𝔠 c₀ ≫ productStructure p = normModelStructure p 𝔠 c₀ := rfl
  -- centres
  have hx₀ : (gaussPoint v).center = normModelπ p 𝔠 c₀ w.center := by
    have h := center_fieldBerkovichPoint_comp g hg (normModelπ p 𝔠 c₀) hππ W
    rw [fieldBerkovichPoint_congr h_gπ _ (gaussMap_structure (K := X.residueField v.support) p ι
      hι)] at h
    exact h
  set x₀ := normModelπ p 𝔠 c₀ w.center
  have e₁ : productFst p x₀ = v.center := by
    have h := center_fieldBerkovichPoint_comp (gaussMap (K := X.residueField v.support) p ι hι)
      (gaussMap_structure (K := X.residueField v.support) p ι hι) (productFst p) rfl W
    rw [fieldBerkovichPoint_congr (gaussMap_fst (K := X.residueField v.support) p ι hι) _
      (gaussBaseMap_structure (K := X.residueField v.support) p ι hι)] at h
    rw [← hx₀]
    refine h.symm.trans ?_
    refine center_fieldBerkovichPoint_fromSpecResidueField v
      (CommRingCat.ofHom (algebraMap (X.residueField v.support)
        (FractionRing (X.residueField v.support)[X]))) W _ (fun a => ?_)
    change gaussExtension v.val (algebraMap (X.residueField v.support)
      (FractionRing (X.residueField v.support)[X]) a) = v.val a
    rw [IsScalarTower.algebraMap_apply (X.residueField v.support) (X.residueField v.support)[X]
      (FractionRing (X.residueField v.support)[X]), Polynomial.algebraMap_apply]
    exact gaussExtension_C v.val a
  have e₂ : productSnd p x₀ = lineChart ℂ chartZero := by
    have h := center_fieldBerkovichPoint_comp (gaussMap (K := X.residueField v.support) p ι hι)
      (gaussMap_structure (K := X.residueField v.support) p ι hι) (productSnd p)
      (productSnd_structure p) W
    rw [fieldBerkovichPoint_congr (gaussMap_snd (K := X.residueField v.support) p ι hι) _
      (gaussLineMap_structure _)] at h
    rw [← hx₀]
    refine h.symm.trans ?_
    exact (((lineGaussPoint v.val).isCenter_iff_eq_center _).mp
      (lineGaussPoint_isCenter v.val)).symm
  obtain ⟨sₜ, hsₜI, hsₜ⟩ := exists_mem_stalkIdeal_zeroIdeal_stalkMap
  have hs := w.support_specializes_center
  let A : X.presheaf.stalk v.center → (productLine p).presheaf.stalk x₀ := fun α =>
    ((productFst p).stalkMap x₀).hom
      ((X.presheaf.stalkSpecializes (Inseparable.of_eq e₁).specializes).hom α)
  let B : (productLine p).presheaf.stalk x₀ :=
    ((productSnd p).stalkMap x₀).hom (((projectiveSpace ℂ 1).presheaf.stalkSpecializes
      (Inseparable.of_eq e₂).specializes).hom sₜ)
  let H : X.presheaf.stalk v.center → ℕ → (normModel p 𝔠 c₀).presheaf.stalk w.center :=
    fun α j => ((normModelπ p 𝔠 c₀).stalkMap w.center).hom (A α * B ^ j)
  have himgA : ∀ α, (fieldEmb (g ≫ normModelπ p 𝔠 c₀)).hom
      ((specializationMap (hs.map (normModelπ p 𝔠 c₀).continuous)).hom (A α)) =
        polyEmb (Polynomial.C ((specializationMap v.support_specializes_center).hom α)) := by
    intro α
    refine (fieldEmb_specializationMap_stalkMap (g ≫ normModelπ p 𝔠 c₀) (productFst p)
      (hs.map (normModelπ p 𝔠 c₀).continuous) (Inseparable.of_eq e₁).specializes α).trans ?_
    refine (fieldEmb_specializationMap_of_eq _ (CommRingCat.ofHom (algebraMap
      (X.residueField v.support) (FractionRing (X.residueField v.support)[X]))) ?_ _
      v.support_specializes_center α).trans ?_
    · rw [h_gπ, gaussMap_fst]
      rfl
    · change algebraMap (X.residueField v.support)
        (FractionRing (X.residueField v.support)[X]) _ = _
      rw [IsScalarTower.algebraMap_apply (X.residueField v.support) (X.residueField v.support)[X]
        (FractionRing (X.residueField v.support)[X]), Polynomial.algebraMap_apply]
      rfl
  have himgB : (fieldEmb (g ≫ normModelπ p 𝔠 c₀)).hom
      ((specializationMap (hs.map (normModelπ p 𝔠 c₀).continuous)).hom B) =
        polyEmb Polynomial.X := by
    refine (fieldEmb_specializationMap_stalkMap (g ≫ normModelπ p 𝔠 c₀) (productSnd p)
      (hs.map (normModelπ p 𝔠 c₀).continuous) (Inseparable.of_eq e₂).specializes sₜ).trans ?_
    exact fieldEmb_specializationMap_chartGerm _ (by rw [h_gπ, gaussMap_snd]; rfl) _ hsₜ
  refine ⟨?_, ?_, H, ?_, ?_⟩
  · intro J
    refine (idealVal_comap_fieldBerkovichPoint (normModelπ p 𝔠 c₀) hππ g hg W _).trans ?_
    rw [fieldBerkovichPoint_congr h_gπ _ (gaussMap_structure (K := X.residueField v.support) p ι
      hι)]
    rfl
  · rw [support_centralIdeal]
    refine ⟨closedPoint ℂ, ?_⟩
    rw [e₂]
    rfl
  · intro α j
    refine (fieldEmb_comp_specializationMap g (normModelπ p 𝔠 c₀) hs (A α * B ^ j)).symm.trans ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (himgA α) (congrArg (· ^ j) himgB)
  · intro α j hα
    rw [stalkIdeal_comap]
    apply Ideal.mem_map_of_mem
    apply stalkIdeal_mono (le_flagSheaf p 𝔞 N j)
    rw [stalkIdeal_mul, stalkIdeal_pow]
    refine Ideal.mul_mem_mul ?_ (Ideal.pow_mem_pow ?_ j)
    · rw [stalkIdeal_comap]
      exact Ideal.mem_map_of_mem _ (stalkSpecializes_mem_stalkIdeal e₁ _ hα)
    · change B ∈ stalkIdeal ((zeroIdeal ℂ).comap (productSnd p)) x₀
      rw [stalkIdeal_comap]
      exact Ideal.mem_map_of_mem _ (stalkSpecializes_mem_stalkIdeal e₂ _ hsₜI)


/-- **Rees points for every normalized Gauss lift** (step R8(c), [BJ22, `lem:tcdiv`], with lane
BJ-PAIR's `ordPoint`): let `v` be a valuation of `ℂ(X)` with `m` ratios `a_i / b_i`
(`dim X ≤ m + 1`) of germs at its centre, of equal integral values `μ_i`, residually independent for
`v`, and a germ `f` of positive integral value `l`; let `N = l + Σ μ_i`. Let `(𝔠, c₀)` be a model on
which `(t^N valFlag v N) · 𝒪` is invertible and `g : Spec ℂ(X)(t) ⟶ 𝒳̃` a lift of the Gauss point
to its normalization hitting the generic point. Then `σ(v)` (the point of `g`) is centred at a point
`c` of codimension one of the central fibre with a DVR as local ring, `σ(v) = β · ord_c`
(`rescalePoint (ordPoint _ c) β`), and `ord_c((t^b 𝔟) · 𝒪) = β⁻¹ (b - φ_𝔟(v))` for all flag ideals
`𝔟` with weight bound `b`. -/
theorem exists_reesPoint_of_lift (v : BerkovichPoint p)
    {m : ℕ} (hdimX : topologicalKrullDim X ≤ (m + 1 : ℕ))
    (a b : Fin m → X.presheaf.stalk v.center) (μ : Fin m → ℕ)
    (f : X.presheaf.stalk v.center) (l : ℕ)
    (hab : ∀ i, v.centerVal (a i) = ((μ i : ℝ) : WithTop ℝ) ∧
      v.centerVal (b i) = ((μ i : ℝ) : WithTop ℝ))
    (hl : 0 < l) (hf : v.centerVal f = ((l : ℝ) : WithTop ℝ))
    (hind : letI := residueComplexAlgebra p v.support
      ResiduallyIndependent v.val (fun i =>
        (specializationMap v.support_specializes_center).hom (a i) /
          (specializationMap v.support_specializes_center).hom (b i)))
    (𝔠 : FlagIdeal X) (c₀ : ℤ)
    (hJ₀ : ((flagSheaf p (valFlag v (l + ∑ i, μ i)) ((l + ∑ i, μ i : ℕ) : ℤ)).comap
      (flagModelπ p 𝔠 c₀)).IsInvertible)
    (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔠 c₀)
    (hgν : letI := residueComplexAlgebra p v.support
      g ≫ normModelν p 𝔠 c₀ = gaussModelMap (K := X.residueField v.support) p
        (X.fromSpecResidueField v.support) (fromSpecResidueField_structure v) 𝔠 c₀)
    (hgη : fieldPt g = genericPoint (normModel p 𝔠 c₀))
    (hg : letI := residueComplexAlgebra p v.support
      g ≫ normModelStructure p 𝔠 c₀ =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X])))) :
    letI := residueComplexAlgebra p v.support
    ∃ (c : normModel p 𝔠 c₀),
      (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v)).center =
        c ∧
      normModelπ p 𝔠 c₀ c ∈ ((centralIdeal p).support : Set (productLine p)) ∧
      coheight c = 1 ∧
      ∃ (_ : IsDiscreteValuationRing ((normModel p 𝔠 c₀).presheaf.stalk c)) (β : ℝ) (hβ : 0 < β),
        fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v) =
          rescalePoint (ordPoint (normModelStructure p 𝔠 c₀) c) hβ ∧
        ∀ (𝔟 : FlagIdeal X) (b : ℤ), IsWeightBound 𝔟 b →
          (ordPoint (normModelStructure p 𝔠 c₀) c).idealVal
              ((flagSheaf p 𝔟 b).comap (normModelπ p 𝔠 c₀)) =
            ENNReal.ofReal β⁻¹ * ENNReal.ofReal (b - 𝔟.phi v) := by
  let := residueComplexAlgebra p v.support
  set N : ℕ := l + ∑ i, μ i with hN
  have hμN : ∀ i, μ i ≤ N := fun i => by
    have := Finset.single_le_sum (f := μ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hlN : l ≤ N := by omega
  let 𝔞 := valFlag v N
  have hwb : IsWeightBound 𝔞 (N : ℤ) := fun l' hl' => by
    have h1 : ¬ l' ≤ 0 := by omega
    have h2 : ¬ l' ≤ (N : ℤ) := by omega
    simp [𝔞, valFlag, h1, h2]
  obtain ⟨hJval, hcentral, H, himg, hmem⟩ := exists_gaussGerms_model v 𝔠 c₀ 𝔞 N g hgν hg
  let w := fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v)
  let spv := (specializationMap v.support_specializes_center).hom
  let spw := (specializationMap w.support_specializes_center).hom
  -- values
  have hvalH : ∀ α j, w.centerVal (H α j) = v.centerVal α + ((j : ℝ) : WithTop ℝ) := by
    intro α j
    change gaussExtension v.val ((fieldEmb g).hom (spw (H α j))) = _
    refine (congrArg (gaussExtension v.val) (himg α j)).trans ?_
    rw [gaussExtension_C_mul_X_pow]
    rfl
  have hJ : ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀)).IsInvertible := by
    rw [normModelπ, Scheme.IdealSheafData.comap_comp]
    exact isInvertible_comap_normModelν p 𝔠 c₀ hJ₀
  have hJN : w.idealVal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀)) = ENNReal.ofReal N := by
    rw [hJval (flagSheaf p 𝔞 N), idealVal_gaussPoint_flagSheaf_eq' v 𝔞 hwb, phi_valFlag]
    simp
  have hmin : ∀ x ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀)) w.center,
      ((N : ℝ) : WithTop ℝ) ≤ w.centerVal x := by
    intro x hx
    have h1 := w.idealVal_le _ hx
    rw [hJN] at h1
    cases hcv : w.centerVal x with
    | top => exact le_top
    | coe r =>
      unfold BerkovichPoint.centerValENN at h1
      rw [hcv, toENNReal_coe] at h1
      have hr : 0 ≤ r := by have := w.centerVal_nonneg x; rw [hcv] at this; exact_mod_cast this
      exact WithTop.coe_le_coe.mpr ((ENNReal.ofReal_le_ofReal_iff hr).mp h1)
  -- the pairs of germs, indexed by `Option (Fin m)`
  let hh : Option (Fin m) → (normModel p 𝔠 c₀).presheaf.stalk w.center :=
    fun o => o.elim (H 1 N) (fun i => H (a i) (N - μ i))
  let hh' : Option (Fin m) → (normModel p 𝔠 c₀).presheaf.stalk w.center :=
    fun o => o.elim (H f (N - l)) (fun i => H (b i) (N - μ i))
  have hcast : ∀ k : ℕ, k ≤ N → ((k : ℝ) : WithTop ℝ) + (((N - k : ℕ) : ℝ) : WithTop ℝ) =
      ((N : ℝ) : WithTop ℝ) := by
    intro k hk
    rw [← WithTop.coe_add]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  have hvalN : ∀ o, w.centerVal (hh o) = ((N : ℝ) : WithTop ℝ) ∧
      w.centerVal (hh' o) = ((N : ℝ) : WithTop ℝ) := by
    intro o
    cases o with
    | none =>
      refine ⟨?_, ?_⟩
      · change w.centerVal (H 1 N) = _
        rw [hvalH, centerVal_one, zero_add]
      · change w.centerVal (H f (N - l)) = _
        rw [hvalH, hf, hcast l hlN]
    | some i =>
      refine ⟨?_, ?_⟩
      · change w.centerVal (H (a i) (N - μ i)) = _
        rw [hvalH, (hab i).1, hcast _ (hμN i)]
      · change w.centerVal (H (b i) (N - μ i)) = _
        rw [hvalH, (hab i).2, hcast _ (hμN i)]
  have hideal : ∀ k : ℕ, k ≤ N → ∀ α : X.presheaf.stalk v.center,
      ((k : ℝ) : WithTop ℝ) ≤ v.centerVal α →
        α ∈ stalkIdeal (𝔞.ideal ((N : ℤ) - ((N - k : ℕ) : ℤ))) v.center := by
    intro k hk α hα
    have hk' : (N : ℤ) - ((N - k : ℕ) : ℤ) = k := by push_cast [Nat.cast_sub hk]; ring
    rw [hk']
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [show ((0 : ℕ) : ℤ) = 0 from rfl, valFlag_ideal_of_nonpos v N le_rfl, stalkIdeal_top]
      exact Submodule.mem_top
    · rw [valFlag_ideal_of_pos v (by exact_mod_cast h0) (by exact_mod_cast hk)]
      apply germ_mem_stalkIdeal_valIdeal
      rw [mem_stalkValIdeal]
      exact_mod_cast hα
  have hmemN : ∀ o, hh o ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀)) w.center ∧
      hh' o ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀)) w.center := by
    intro o
    cases o with
    | none =>
      refine ⟨hmem _ _ ?_, hmem _ _ (hideal l hlN f (le_of_eq hf.symm))⟩
      have := hideal 0 (Nat.zero_le N) 1 (by rw [centerVal_one]; simp)
      simpa using this
    | some i =>
      exact ⟨hmem _ _ (hideal _ (hμN i) _ (le_of_eq (hab i).1.symm)),
        hmem _ _ (hideal _ (hμN i) _ (le_of_eq (hab i).2.symm))⟩
  -- the images of the ratios in `ℂ(X)(t)`
  have hf0 : spv f ≠ 0 := by
    intro h0
    have : v.centerVal f = ⊤ := by
      change v.valAt (spv f) = ⊤
      rw [h0, valAt_zero]
    rw [hf] at this
    exact WithTop.coe_ne_top this
  have hX0 : polyEmb (Polynomial.X : (X.residueField v.support)[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr Polynomial.X_ne_zero
  let u : Fin m → X.residueField v.support := fun i => spv (a i) / spv (b i)
  have hratio : ∀ o, (fieldEmb g).hom (spw (hh o) / spw (hh' o)) =
      gaussFamily u (spv f) l o := by
    intro o
    rw [map_div₀]
    cases o with
    | none =>
      change (fieldEmb g).hom (spw (H 1 N)) / (fieldEmb g).hom (spw (H f (N - l))) =
        gaussRatio (spv f) l
      rw [himg, himg, map_one, Polynomial.C_1, map_one, one_mul, gaussRatio, map_pow]
      have hsplit : polyEmb (Polynomial.X : (X.residueField v.support)[X]) ^ N =
          polyEmb Polynomial.X ^ l * polyEmb Polynomial.X ^ (N - l) := by
        rw [← pow_add, Nat.add_sub_cancel' hlN]
      rw [hsplit, mul_div_mul_right _ _ (pow_ne_zero _ hX0)]
    | some i =>
      change (fieldEmb g).hom (spw (H (a i) (N - μ i))) /
        (fieldEmb g).hom (spw (H (b i) (N - μ i))) = polyEmb (Polynomial.C (u i))
      rw [himg, himg, mul_div_mul_right _ _ (pow_ne_zero _ hX0)]
      exact (map_div₀ (polyEmb.comp Polynomial.C) (spv (a i)) (spv (b i))).symm
  -- residual independence of the ratios for the normalized Gauss point
  let := residueComplexAlgebra (normModelStructure p 𝔠 c₀) (fieldPt g)
  let φ : (normModel p 𝔠 c₀).residueField (fieldPt g) →ₐ[ℂ]
      FractionRing (X.residueField v.support)[X] :=
    { (fieldEmb g).hom with
      commutes' := fun c => by
        have h := congrArg (fun ψ => ψ.hom c) (residueComplexHom_fieldEmb
          (normModelStructure p 𝔠 c₀) g hg)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h }
  have hRI := ResiduallyIndependent.comp_equiv
    (residuallyIndependent_gaussExtension v.val hind hf0 hl hf) (finSuccEquiv m)
  let := residueComplexAlgebra (normModelStructure p 𝔠 c₀) w.support
  have hind' : ResiduallyIndependent w.val (fun i : Fin (m + 1) =>
      spw (hh (finSuccEquiv m i)) / spw (hh' (finSuccEquiv m i))) := by
    intro P hP
    change gaussExtension v.val (φ (MvPolynomial.aeval _ P)) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have : (fun i : Fin (m + 1) => φ (spw (hh (finSuccEquiv m i)) / spw (hh' (finSuccEquiv m i)))) =
        gaussFamily u (spv f) l ∘ finSuccEquiv m := by
      funext i
      exact hratio _
    rw [this]
    exact hRI P hP
  -- the centre is not the generic point
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : w.center ≠ genericPoint (normModel p 𝔠 c₀) := by
    intro hη
    have hne : H 1 N ≠ 0 := by
      intro h0
      have := (hvalN none).1
      change w.centerVal (H 1 N) = _ at this
      rw [h0, centerVal_zero] at this
      exact WithTop.top_ne_coe this
    have h0 := (w.centerVal_eq_zero_iff _).mpr (isUnit_of_eq_genericPoint hη hne)
    have := (hvalN none).1
    change w.centerVal (H 1 N) = _ at this
    rw [h0] at this
    have : (0 : ℝ) = N := by exact_mod_cast this
    linarith
  have hdim : topologicalKrullDim (normModel p 𝔠 c₀) ≤ ((m + 1 : ℕ) : WithBot ℕ∞) + 1 := by
    have := topologicalKrullDim_normModel_le p 𝔠 c₀ (m + 1) hdimX
    simpa using this
  obtain ⟨h1, h2, β, hβ, val, hwv, hF⟩ := reesCenter' (normModelStructure p 𝔠 c₀)
    (normModel_stalk_isIntegrallyClosed p 𝔠 c₀) hdim w hgη hc
    ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔠 c₀)) hJ
    (fun i => hh (finSuccEquiv m i)) (fun i => hh' (finSuccEquiv m i))
    (fun i => (hmemN _).1) (fun i => (hmemN _).2)
    (fun i => (hvalN _).1.trans (hvalN _).2.symm)
    (fun i x hx => by rw [(hvalN _).2]; exact hmin x hx)
    (fun i => by rw [(hvalN _).2]; exact WithTop.coe_ne_top) hind'
  let := h2
  have hresc : w = rescalePoint (ordPoint (normModelStructure p 𝔠 c₀) w.center) hβ :=
    hwv.trans (eq_rescalePoint_ordPoint (normModelStructure p 𝔠 c₀) h1 val hβ hF)
  refine ⟨w.center, rfl, hcentral, h1, h2, β, hβ, hresc, fun 𝔟 b' hb' => ?_⟩
  have hval := hJval (flagSheaf p 𝔟 b')
  rw [idealVal_gaussPoint_flagSheaf_eq' v 𝔟 hb'] at hval
  have hval' : w.idealVal ((flagSheaf p 𝔟 b').comap (normModelπ p 𝔠 c₀)) =
      ENNReal.ofReal (b' - 𝔟.phi v) := hval
  have hval2 : ENNReal.ofReal β * (ordPoint (normModelStructure p 𝔠 c₀) w.center).idealVal
      ((flagSheaf p 𝔟 b').comap (normModelπ p 𝔠 c₀)) = ENNReal.ofReal (b' - 𝔟.phi v) := by
    rw [← idealVal_rescalePoint _ hβ, ← hresc]
    exact hval'
  rw [← hval2, ← mul_assoc, ENNReal.ofReal_inv_of_pos hβ,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hβ).ne' ENNReal.ofReal_ne_top, one_mul]


/-- **Rees points on every dominating model**: `exists_reesPoint_of_lift` for the normalized
Gauss lift of `exists_gaussNormMap`. -/
theorem exists_reesPoint_of_model (v : BerkovichPoint p) (hv : v.support = genericPoint X)
    {m : ℕ} (hdimX : topologicalKrullDim X ≤ (m + 1 : ℕ))
    (a b : Fin m → X.presheaf.stalk v.center) (μ : Fin m → ℕ)
    (f : X.presheaf.stalk v.center) (l : ℕ)
    (hab : ∀ i, v.centerVal (a i) = ((μ i : ℝ) : WithTop ℝ) ∧
      v.centerVal (b i) = ((μ i : ℝ) : WithTop ℝ))
    (hl : 0 < l) (hf : v.centerVal f = ((l : ℝ) : WithTop ℝ))
    (hind : letI := residueComplexAlgebra p v.support
      ResiduallyIndependent v.val (fun i =>
        (specializationMap v.support_specializes_center).hom (a i) /
          (specializationMap v.support_specializes_center).hom (b i)))
    (𝔠 : FlagIdeal X) (c₀ : ℤ)
    (hJ₀ : ((flagSheaf p (valFlag v (l + ∑ i, μ i)) ((l + ∑ i, μ i : ℕ) : ℤ)).comap
      (flagModelπ p 𝔠 c₀)).IsInvertible) :
    letI := residueComplexAlgebra p v.support
    ∃ (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔠 c₀)
      (hg : g ≫ normModelStructure p 𝔠 c₀ =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X]))))
      (c : normModel p 𝔠 c₀),
      g ≫ normModelν p 𝔠 c₀ = gaussModelMap (K := X.residueField v.support) p
        (X.fromSpecResidueField v.support) (fromSpecResidueField_structure v) 𝔠 c₀ ∧
      fieldPt g = genericPoint (normModel p 𝔠 c₀) ∧
      (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v)).center =
        c ∧
      normModelπ p 𝔠 c₀ c ∈ ((centralIdeal p).support : Set (productLine p)) ∧
      coheight c = 1 ∧
      ∃ (_ : IsDiscreteValuationRing ((normModel p 𝔠 c₀).presheaf.stalk c)) (β : ℝ) (hβ : 0 < β),
        fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v) =
          rescalePoint (ordPoint (normModelStructure p 𝔠 c₀) c) hβ ∧
        ∀ (𝔟 : FlagIdeal X) (b : ℤ), IsWeightBound 𝔟 b →
          (ordPoint (normModelStructure p 𝔠 c₀) c).idealVal
              ((flagSheaf p 𝔟 b).comap (normModelπ p 𝔠 c₀)) =
            ENNReal.ofReal β⁻¹ * ENNReal.ofReal (b - 𝔟.phi v) := by
  let := residueComplexAlgebra p v.support
  obtain ⟨g, hgν, hgη⟩ := exists_gaussNormMap v hv 𝔠 c₀
  have hg : g ≫ normModelStructure p 𝔠 c₀ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X]))) := by
    rw [normModelStructure, ← Category.assoc, hgν, gaussModelMap_structure]
  obtain ⟨c, hc⟩ := exists_reesPoint_of_lift v hdimX a b μ f l hab hl hf hind 𝔠 c₀ hJ₀ g hgν hgη hg
  exact ⟨g, hg, c, hgν, hgη, hc⟩

/-- **Rees points of divisorial points on every dominating model** ([BJ22, `lem:tcdiv`]): for
`v = s · ord_F ∈ X^Div` there are a flag ideal `𝔞` with weight bound `N` such that on the
normalized model of every `(𝔠, c₀)` on which `(t^N 𝔞) · 𝒪` is invertible, `σ(v) = β · ordPoint c`
for a codimension-one DVR point `c` of the central fibre, with
`ord_c((t^b 𝔟) · 𝒪) = β⁻¹ (b - φ_𝔟(v))` for all flag ideals `𝔟` with weight bound `b`. -/
theorem exists_reesPoint_of_divisorial (v : BerkovichPoint p) (hv : v ∈ divisorialSet p) :
    letI := residueComplexAlgebra p v.support
    ∃ (𝔞 : FlagIdeal X) (N : ℕ), IsWeightBound 𝔞 (N : ℤ) ∧ ∀ (𝔠 : FlagIdeal X) (c₀ : ℤ),
      ((flagSheaf p 𝔞 N).comap (flagModelπ p 𝔠 c₀)).IsInvertible →
      ∃ (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔠 c₀)
        (hg : g ≫ normModelStructure p 𝔠 c₀ =
          Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X]))))
        (c : normModel p 𝔠 c₀),
        g ≫ normModelν p 𝔠 c₀ = gaussModelMap (K := X.residueField v.support) p
          (X.fromSpecResidueField v.support) (fromSpecResidueField_structure v) 𝔠 c₀ ∧
        fieldPt g = genericPoint (normModel p 𝔠 c₀) ∧
        (fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v)).center =
          c ∧
        normModelπ p 𝔠 c₀ c ∈ ((centralIdeal p).support : Set (productLine p)) ∧
        coheight c = 1 ∧
        ∃ (_ : IsDiscreteValuationRing ((normModel p 𝔠 c₀).presheaf.stalk c)) (β : ℝ) (hβ : 0 < β),
          fieldBerkovichPoint (normModelStructure p 𝔠 c₀) g hg (berkovichGaussExtension v) =
            rescalePoint (ordPoint (normModelStructure p 𝔠 c₀) c) hβ ∧
          ∀ (𝔟 : FlagIdeal X) (b : ℤ), IsWeightBound 𝔟 b →
            (ordPoint (normModelStructure p 𝔠 c₀) c).idealVal
                ((flagSheaf p 𝔟 b).comap (normModelπ p 𝔠 c₀)) =
              ENNReal.ofReal β⁻¹ * ENNReal.ofReal (b - 𝔟.phi v) := by
  obtain ⟨E, s, hs, rfl⟩ := hv
  obtain ⟨m, a, b, μ, f, l, hdim, hab, hl, hf, hind⟩ :=
    exists_reesData_of_primeDivisor (p := p) E s hs
  set N : ℕ := l + ∑ i, μ i with hN
  have hwb : IsWeightBound (valFlag (E.ordVal p s hs) N) (N : ℤ) := fun l' hl' => by
    have h1 : ¬ l' ≤ 0 := by omega
    have h2 : ¬ l' ≤ (N : ℤ) := by omega
    simp [valFlag, h1, h2]
  exact ⟨valFlag (E.ordVal p s hs) N, N, hwb, fun 𝔠 c₀ hJ =>
    exists_reesPoint_of_model (E.ordVal p s hs) E.isGenericPoint_image hdim a b μ f l hab hl hf
      hind 𝔠 c₀ hJ⟩

end SGPT.NAPotential.ThinApprox.BJ
