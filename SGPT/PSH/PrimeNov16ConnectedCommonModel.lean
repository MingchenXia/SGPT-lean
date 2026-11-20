import SGPT.PSH.PrimeNov16GraphManifold
import SGPT.PSH.PrimeNov16IsoOverLift
import SGPT.Unibranch.OriginalProperBimeromorphicNative
import SGPT.Foundations.Analysis.Pending.AnalyticModelDomination

/-! Actual noncompact connected smooth common models from the SAME native graph resolution.
No desired common model, inverse, atlas or properness certificate is supplied.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16ConnectedCommonModel
open Set Filter CategoryTheory AlgebraicGeometry TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaResolutionSpaceComplex HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspace HironakaEmbeddedNativeMorphism
  HironakaReducedComplexAnalyticSpaces BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification
  OriginalProperBimeromorphicNative
open scoped Topology Manifold ContDiff ProductComplexManifold

variable {n : ℕ} {X Y₀ Y₁ : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- The two original modifications construct a genuine connected noncompact
smooth common model with BOTH complete analytic-modification dictionaries. -/
theorem exists_actual_connected_common_model {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (M : CMfd.{0} n) (_ : ConnectedSpace M) (g₀ : M → Y₀) (g₁ : M → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
      c₀ ∘ g₀ = c₁ ∘ g₁ := by
  classical
  obtain ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀, hs₁, hr₀, hr₁, hl₀, hl₁,
    V, _hVdim, hVclosure, hVF, hGreg, M, hMconn, ⟨E⟩⟩ :=
    PrimeNov16GraphManifold.exists_actual_graph_manifold hc₀ hc₁
  let : ConnectedSpace M := hMconn
  let A := ofClosedAnalytic V.carrier V.analytic
  let R := OriginalNativeHSGlobalResolution.source A
  let ρ : R ⟶ A := OriginalNativeHSGlobalResolution.projection A
  let q : wholeModel (n := n) M ⟶ A := E.hom ≫ ρ
  let p₀ : A ⟶ wholeModel (n := n) Y₀ := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ProductComplexManifold.contMDiff_fst (n := n) (m := n))
      (fun _ _ => mem_univ _))
    (actualSubspaceMap_point (ProductComplexManifold.contMDiff_fst (n := n) (m := n))
      (fun _ _ => mem_univ _)))
  let p₁ : A ⟶ wholeModel (n := n) Y₁ := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ProductComplexManifold.contMDiff_snd (n := n) (m := n))
      (fun _ _ => mem_univ _))
    (actualSubspaceMap_point (ProductComplexManifold.contMDiff_snd (n := n) (m := n))
      (fun _ _ => mem_univ _)))
  let g₀ : M → Y₀ := nativePointMap (q ≫ p₀)
  let g₁ : M → Y₁ := nativePointMap (q ≫ p₁)
  have hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀ :=
    nativePointMap_contMDiff (q ≫ p₀)
  have hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ :=
    nativePointMap_contMDiff (q ≫ p₁)
  let Q : M → V.carrier := fun z => q.hom.left.base ⟨z, mem_univ z⟩
  have hQproper : IsProperMap Q :=
    (OriginalNativeHSGlobalResolution.proper A).comp
      ((isoHomeomorph E).isProperMap.comp (Homeomorph.Set.univ M).symm.isProperMap)
  have hp₀ : IsProperMap (fun p : V.carrier => p.val.1) :=
    AnalyticFibreProductProperProjections.isProperMap_fst_of_closed_fibreProduct
      hc₀.1.continuous hc₁.2.1 V.isClosed_carrier hVF
  have hp₁ : IsProperMap (fun p : V.carrier => p.val.2) :=
    AnalyticFibreProductProperProjections.isProperMap_snd_of_closed_fibreProduct
      hc₀.2.1 hc₁.1.continuous V.isClosed_carrier hVF
  have hgp₀ : IsProperMap g₀ := hp₀.comp hQproper
  have hgp₁ : IsProperMap g₁ := hp₁.comp hQproper
  have hbase (z : M) : c₀ (g₀ z) = c₁ (g₁ z) := hVF (Q z).property
  let π : M → X := c₀ ∘ g₀
  have hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π := hc₀.1.comp hg₀
  have hπproper : IsProperMap π := hc₀.2.1.comp hgp₀
  let U : Opens X := ⟨Bᶜ, hBc.isOpen_compl⟩
  have hs₀U : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : U => s₀ x.val) := by
    intro x
    exact (hs₀.contMDiffAt (hBc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  have hs₁U : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : U => s₁ x.val) := by
    intro x
    exact (hs₁.contMDiffAt (hBc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  let γ : U → Y₀ × Y₁ := fun x => (s₀ x.val, s₁ x.val)
  have hγ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n+n)) ∞ γ :=
    ProductComplexManifold.contMDiff_prodMk hs₀U hs₁U
  have hγS (x : U) : c₀ (γ x).1 = c₁ (γ x).2 ∧ c₀ (γ x).1 ∉ B := by
    change c₀ (s₀ x.val) = c₁ (s₁ x.val) ∧ c₀ (s₀ x.val) ∉ B
    rw [hr₀ x.val x.property, hr₁ x.val x.property]
    exact ⟨rfl, x.property⟩
  have hγV (x : U) : γ x ∈ V.carrier := hVclosure.symm ▸ subset_closure (hγS x)
  let F : wholeModel (n := n) U ⟶ A := ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hγ (fun x _ => hγV x))
    (actualSubspaceMap_point hγ (fun x _ => hγV x)))
  have hregular (v : V.carrier)
      (hv : c₀ v.val.1 = c₁ v.val.2 ∧ c₀ v.val.1 ∉ B) :
      intrinsicRegularAtDim A.obj v n := by
    obtain ⟨O, i, hi, hp, hx⟩ := exists_native_chart V.carrier (hGreg _ hv)
    exact ⟨O, i, hi, hp, hx⟩
  have hF : range F.hom.left.base ⊆ intrinsicRegularLocus A.obj := by
    rintro _ ⟨u, rfl⟩
    exact ⟨n, hregular _ (hγS u.val)⟩
  obtain ⟨L, hL⟩ := PrimeNov16IsoOverLift.exists_native_lift ρ
    (OriginalNativeHSGlobalResolution.originalReg A) E F hF
  let σ : U → M := nativePointMap L
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ :=
    nativePointMap_contMDiff L
  have hQσ (x : U) : (Q (σ x)).val = γ x :=
    congrArg (fun H : wholeModel (n := n) U ⟶ A =>
      (H.hom.left.base ⟨x, mem_univ x⟩).val) hL
  have hπσ (x : U) : π (σ x) = x.val := by
    change c₀ (Q (σ x)).val.1 = x.val
    rw [hQσ x]
    exact hr₀ x.val x.property
  have hQgraph (z : M) (hz : π z ∉ B) : (Q z).val = (s₀ (π z), s₁ (π z)) := by
    apply Prod.ext
    · exact (hl₀ (g₀ z) hz).symm
    · change g₁ z = s₁ (π z)
      have heq : π z = c₁ (g₁ z) := hbase z
      rw [heq]
      exact (hl₁ (g₁ z) (heq ▸ hz)).symm
  have hπinj {w z : M} (hw : π w ∉ B) (hz : π z ∉ B)
      (heq : π w = π z) : w = z := by
    have hQeq : Q w = Q z := Subtype.ext (by rw [hQgraph w hw, hQgraph z hz, heq])
    have hwreg : Q w ∈ intrinsicRegularLocus A.obj := ⟨n, hregular _ ⟨hbase w, hw⟩⟩
    have hzreg : Q z ∈ intrinsicRegularLocus A.obj := ⟨n, hregular _ ⟨hbase z, hz⟩⟩
    have hEeq := PrimeNov16IsoOverLift.injOn_preimage
      (OriginalNativeHSGlobalResolution.originalReg A) hwreg hzreg hQeq
    exact congrArg Subtype.val ((isoHomeomorph E).injective hEeq)
  have hsubrange : Bᶜ ⊆ range π := fun x hx => ⟨σ ⟨x, hx⟩, hπσ ⟨x, hx⟩⟩
  have hdense : Dense (range π) := (interior_eq_empty_iff_dense_compl.mp hBi).mono hsubrange
  have hrange : range π = univ := hπproper.isClosed_range.closure_eq.symm.trans hdense.closure_eq
  have hsurj : Function.Surjective π := Set.range_eq_univ.mp hrange
  let t : X → M := fun x => Classical.choose (hsurj x)
  have hright (x : X) : π (t x) = x := Classical.choose_spec (hsurj x)
  have hsame : (fun x : U => t x.val) = σ := by
    funext x
    exact hπinj (w := t x.val) (z := σ x)
      (by rw [hright x.val]; exact x.property)
      (by rw [hπσ x]; exact x.property)
      ((hright x.val).trans (hπσ x).symm)
  have ht : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ t Bᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : U => t x.val) := hsame.symm ▸ hσ
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest (⟨x, hx⟩ : U))).contMDiffWithinAt
  let D : Set M := π ⁻¹' B
  have hDc : IsClosed D := hBc.preimage hπ.continuous
  have hDa : IsComplexAnalyticSubset (n := n) D :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ hBa
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hBi).nonempty
  have htD : t x ∉ D := by
    change π (t x) ∉ B
    rw [hright x]
    exact hx
  have hDproper : D ≠ univ := fun h => htD (h.symm ▸ mem_univ (t x))
  have hDi : interior D = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    exact fun hint => hDproper (hDa.eq_univ_of_interior_nonempty hint)
  have hπmod : IsAnalyticModification (n := n) π := by
    refine ⟨hπ, hπproper, D, B, t, hDc, hDa, hDi, hBc, hBa, hBi, rfl,
      ht, (fun x _ => hright x), ?_⟩
    intro z hz
    exact hπinj (w := t (π z)) (z := z)
      (by rw [hright (π z)]; exact hz) hz (hright (π z))
  have hover : c₀ ∘ g₀ = c₁ ∘ g₁ := funext hbase
  exact ⟨M, hMconn, g₀, g₁,
    AnalyticModelDomination.isAnalyticModification_of_holomorphic_over hc₀ hπmod hg₀ rfl,
    AnalyticModelDomination.isAnalyticModification_of_holomorphic_over hc₁ hπmod hg₁ hover.symm,
    hover⟩

end SGPT.PSH.PrimeNov16ConnectedCommonModel
