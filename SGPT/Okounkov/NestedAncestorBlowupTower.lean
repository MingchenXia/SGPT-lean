import SGPT.Okounkov.FlagLiftingTail
import SGPT.Okounkov.AmbientIntrinsicBlowupTower
import SGPT.Okounkov.IntrinsicModificationRestriction
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.BlowupTowerTransforms
import SGPT.Foundations.Analysis.Pending.HironakaAdmissibleCalculus
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- The actual smooth thin centre in the lowest carrier gives a genuine
smooth thin centre in every containing ancestor, with the same whole image. -/
theorem closedSubmanifoldCentre_in_nestedAncestor
    {n k l : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N S : Set X} (hkn : k ≤ n) (hlk : l ≤ k)
    (hN : IsClosedConnectedSubmanifold n N k)
    (hS : IsClosedConnectedSubmanifold n S l) (hSN : S ⊆ N)
    (C : Set S)
    (hC : letI := SubmanifoldChartedSpace.chartedSpace (hlk.trans hkn) hS.2.2
      IsClosedSubmanifold l C) (hCi : interior C = ∅) :
    letI := SubmanifoldChartedSpace.chartedSpace hkn hN.2.2
    let CN : Set N := Subtype.val ⁻¹' (Subtype.val '' C)
    IsClosedSubmanifold k CN ∧ interior CN = ∅ ∧
      Subtype.val '' CN = Subtype.val '' C := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hkn hN.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN.2.2
  let hNS := regularAtDim_subtype_of_nested hkn hlk hN.2.2 hS.2.2 hSN
  let E : Set N := Subtype.val ⁻¹' S
  let := SubmanifoldChartedSpace.chartedSpace hlk hNS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hlk hNS
  let := SubmanifoldChartedSpace.chartedSpace (hlk.trans hkn) hS.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hlk.trans hkn) hS.2.2
  let e : E ≃ₜ S := nestedCarrierHomeomorph hSN
  have he : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel l) ∞ e :=
    contMDiff_nestedCarrierHomeomorph hkn hlk hN hS hSN
  have hef : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel l) ∞ e.symm :=
    contMDiff_nestedCarrierHomeomorph_symm hkn hlk hN hS hSN
  let D : Set E := e ⁻¹' C
  have hD : IsClosedSubmanifold l D :=
    MarkedIdealBiholomorphism.isClosedSubmanifold_preimage he hef
      e.apply_symm_apply e.symm_apply_apply hC
  have hDi : interior D = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hsub : e '' interior D ⊆ C := by
      rintro _ ⟨y, hy, rfl⟩
      exact (show y ∈ D from interior_subset hy)
    have hmem : e z ∈ interior C :=
      interior_maximal hsub (e.isOpenMap _ isOpen_interior) ⟨z, hz, rfl⟩
    rw [hCi] at hmem
    exact hmem
  have hEc : IsClosed E := hS.1.preimage continuous_subtype_val
  obtain ⟨hA, hAi, _⟩ :=
    closedSubmanifoldCentre_ambient_and_restrictedIdeal hlk hEc hNS D hD hDi
  have hAD : (Subtype.val '' D : Set N) = Subtype.val ⁻¹' (Subtype.val '' C) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e y, hy, rfl⟩
    · rintro ⟨y, hy, hyz⟩
      refine ⟨e.symm y, ?_, ?_⟩
      · change e (e.symm y) ∈ C
        rwa [e.apply_symm_apply]
      · apply Subtype.ext
        exact hyz
  have himage : (Subtype.val : N → X) '' (Subtype.val ⁻¹' (Subtype.val '' C)) =
      Subtype.val '' C := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, hSN y.2⟩, ⟨y, hy, rfl⟩, rfl⟩
  rw [hAD] at hA hAi
  exact ⟨hA, hAi, himage⟩

/-- One original intrinsic blowup manufactures every strict ancestor and every
literal restricted blowup; no ancestor-transform data are supplied. -/
theorem exists_ambientRealization_preserving_smoothAncestors
    {n r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X)
    (N : Fin (r + 1) → Set X) (d : Fin (r + 1) → ℕ)
    (hNa : Antitone N) (hda : Antitone d) (hN0 : N 0 = univ) (hd0 : d 0 = n)
    (hN : ∀ j, IsClosedConnectedSubmanifold n (N j) (d j))
    (C : Set (N (Fin.last r)))
    {Nt : Type u} [TopologicalSpace Nt]
    [ChartedSpace (ComplexModel (d (Fin.last r))) Nt]
    [IsComplexManifold (d (Fin.last r)) Nt] {b : Nt → N (Fin.last r)}
    (hb : let hk : ∀ j, d j ≤ n := fun j => hd0 ▸ hda (Fin.zero_le j)
      letI := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hN _).2.2
      IsBlowupAlong (d (Fin.last r)) C b) :
    let hk : ∀ j, d j ≤ n := fun j => hd0 ▸ hda (Fin.zero_le j)
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : ConnectedSpace Y)
      (_ : KahlerBackground n Y) (a : Y → X) (S : Fin (r + 1) → Set Y),
      IsBlowupAlong n (Subtype.val '' C) a ∧ IsBlowupSequence n X Y a ∧
      (∀ j, S j = strictTransform n a (N j)) ∧ Antitone S ∧ S 0 = univ ∧
      ∃ hS : ∀ j, IsClosedConnectedSubmanifold n (S j) (d j),
        ∃ hi : ∀ j, ∀ y ∈ S j, a y ∈ N j,
          (∀ j,
            letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
            letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hS j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hS j).2.2
            let aj : S j → N j := fun y => ⟨a y, hi j y y.2⟩
            IsBlowupAlong (d j) (Subtype.val ⁻¹' (Subtype.val '' C)) aj ∧
              IsAnalyticModification (n := d j) aj ∧ a '' S j = N j) ∧
          letI := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hS _).2.2
          ∃ (e : Nt → S (Fin.last r)) (f : S (Fin.last r) → Nt),
            ContMDiff 𝓘(ℂ, ComplexModel (d (Fin.last r)))
              𝓘(ℂ, ComplexModel (d (Fin.last r))) ∞ e ∧
            ContMDiff 𝓘(ℂ, ComplexModel (d (Fin.last r)))
              𝓘(ℂ, ComplexModel (d (Fin.last r))) ∞ f ∧
            f ∘ e = id ∧ e ∘ f = id ∧
            a ∘ ((Subtype.val : S (Fin.last r) → Y) ∘ e) =
              (Subtype.val : N (Fin.last r) → X) ∘ b := by
  classical
  let hk : ∀ j, d j ≤ n := fun j => hd0 ▸ hda (Fin.zero_le j)
  let : ConnectedSpace X := connectedSpace_iff_univ.mpr (by
    simpa only [hN0] using (hN 0).2.1)
  let := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hN _).2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk (Fin.last r)) (hN _).2.2
  obtain ⟨Y, topY, chartsY, complexY, compactY, omegaY, a, L, hL,
    ha, haseq, _hLc, _hLgeo, hLstrict, _hiL, e, f, he, hf,
    _hre, _hbf, hfe, hef, _himageL, hcomm⟩ :=
    exists_ambientRealization_of_intrinsicBlowup omegaX (hk (Fin.last r))
      (hN _).1 (hN _).2.2 C hb
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  let connectedY : ConnectedSpace Y := BlowupConnected.connectedSpace_of_isBlowupAlong ha
  let S : Fin (r + 1) → Set Y := fun j => strictTransform n a (N j)
  have hfamily : ∀ j,
      ∃ hj : IsClosedConnectedSubmanifold n (S j) (d j),
        ∃ hij : ∀ y ∈ S j, a y ∈ N j,
          letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
          letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
          letI := SubmanifoldChartedSpace.chartedSpace (hk j) hj.2.2
          letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) hj.2.2
          let aj : S j → N j := fun y => ⟨a y, hij y y.2⟩
          IsBlowupAlong (d j) (Subtype.val ⁻¹' (Subtype.val '' C)) aj ∧
            IsAnalyticModification (n := d j) aj ∧ a '' S j = N j := by
    intro j
    have hlk : d (Fin.last r) ≤ d j := hda (Fin.le_last j)
    have hSN : N (Fin.last r) ⊆ N j := hNa (Fin.le_last j)
    let := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
    let : ConnectedSpace (N j) := isConnected_iff_connectedSpace.mp (hN j).2.1
    let Cj : Set (N j) := Subtype.val ⁻¹' (Subtype.val '' C)
    obtain ⟨hCj, hCji, hCjimage⟩ :=
      closedSubmanifoldCentre_in_nestedAncestor (hk j) hlk (hN j) (hN _) hSN C hb.1 hb.2.1
    have haj : IsBlowupAlong n (Subtype.val '' Cj) a := by
      rwa [hCjimage]
    have hclosure : N j ⊆ closure (N j \ Subtype.val '' Cj) := by
      intro x hx
      let p : N j := ⟨x, hx⟩
      have hp : p ∈ closure Cjᶜ :=
        (interior_eq_empty_iff_dense_compl.mp hCji).closure_eq ▸ mem_univ p
      have himg : Subtype.val '' closure Cjᶜ ⊆ closure (Subtype.val '' Cjᶜ) :=
        image_closure_subset_closure_image continuous_subtype_val
      apply closure_mono ?_ (himg ⟨p, hp, rfl⟩)
      rintro y ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      rintro ⟨c, hc, hcz⟩
      exact hz (Subtype.val_injective hcz ▸ hc)
    have hgeo : BlowupStrictSubmanifold.geoStrictTransform a (Subtype.val '' Cj) (N j) = S j :=
      BlowupStrictIdeal.geoStrictTransform_eq_strictTransform haj hclosure
    let data : Set Y → Prop := fun T =>
      ∃ hreg : ∀ y ∈ T, RegularAtDim (n := n) T y (d j),
        ∃ hij : ∀ y ∈ T, a y ∈ N j,
          letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
          letI := SubmanifoldChartedSpace.chartedSpace (hk j) hreg
          IsBlowupAlong (d j) Cj (fun y : T => (⟨a y, hij y y.2⟩ : N j))
    have hdataGeo : data (BlowupStrictSubmanifold.geoStrictTransform a (Subtype.val '' Cj) (N j)) :=
        isBlowupAlong_closedSubmanifold_corestriction (hk j) (hN j).1 (hN j).2.2
          Cj hCj hCji haj
    have hdata : data (S j) := (congrArg data hgeo).mp hdataGeo
    obtain ⟨hreg, hij, hablow⟩ := hdata
    let := SubmanifoldChartedSpace.chartedSpace (hk j) hreg
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) hreg
    let aj : S j → N j := fun y => ⟨a y, hij y y.2⟩
    have hajmod : IsAnalyticModification (n := d j) aj :=
      PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hablow
    let : ConnectedSpace (S j) := BlowupConnected.connectedSpace_of_isBlowupAlong hablow
    have hconn : IsConnected (S j) := isConnected_iff_connectedSpace.mpr inferInstance
    have himage : a '' S j = N j := by
      apply Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact hij y hy
      · intro x hx
        obtain ⟨y, hy⟩ :=
          AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hajmod ⟨x, hx⟩
        exact ⟨y.1, y.2, congrArg Subtype.val hy⟩
    exact ⟨⟨isClosed_closure, hconn, hreg⟩, hij, hablow, hajmod, himage⟩
  choose hS hi hprops using hfamily
  have hSa : Antitone S := fun i j hij =>
    HironakaAdmissibleCalculus.strictTransform_mono a (hNa hij)
  have hS0 : S 0 = univ := by
    change strictTransform n a (N 0) = univ
    rw [hN0]
    exact BlowupTowerTransforms.strictTransform_univ ha
  refine ⟨Y, topY, chartsY, complexY, compactY, connectedY, omegaY, a, S,
    ha, haseq, fun _ => rfl, hSa, hS0, hS, hi, hprops, ?_⟩
  have hLS : L = S (Fin.last r) := hLstrict
  clear _hLgeo hLstrict _himageL
  subst L
  exact ⟨e, f, he, hf, hfe, hef, hcomm⟩

/-- The original finite intrinsic predicate internally supplies an ambient
finite sequence with every smooth ancestor and every literal restricted sequence. -/
theorem exists_ambientTower_preserving_smoothAncestors
    {n r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X)
    (N : Fin (r + 1) → Set X) (d : Fin (r + 1) → ℕ)
    (hNa : Antitone N) (hda : Antitone d) (hN0 : N 0 = univ) (hd0 : d 0 = n)
    (hN : ∀ j, IsClosedConnectedSubmanifold n (N j) (d j))
    {Nt : Type u} [TopologicalSpace Nt]
    [ChartedSpace (ComplexModel (d (Fin.last r))) Nt]
    [IsComplexManifold (d (Fin.last r)) Nt] {q : Nt → N (Fin.last r)}
    (hq : let hk : ∀ j, d j ≤ n := fun j => hd0 ▸ hda (Fin.zero_le j)
      letI := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hN _).2.2
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk (Fin.last r)) (hN _).2.2
      IsBlowupSequence (d (Fin.last r)) (N (Fin.last r)) Nt q) :
    let hk : ∀ j, d j ≤ n := fun j => hd0 ▸ hda (Fin.zero_le j)
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : ConnectedSpace Y)
      (_ : KahlerBackground n Y) (p : Y → X) (S : Fin (r + 1) → Set Y),
      IsBlowupSequence n X Y p ∧
      (∀ j, S j = strictTransform n p (N j)) ∧ Antitone S ∧ S 0 = univ ∧
      ∃ hS : ∀ j, IsClosedConnectedSubmanifold n (S j) (d j),
        ∃ hi : ∀ j, ∀ y ∈ S j, p y ∈ N j,
          (∀ j,
            letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
            letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hS j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hS j).2.2
            let pj : S j → N j := fun y => ⟨p y, hi j y y.2⟩
            IsBlowupSequence (d j) (N j) (S j) pj ∧
              IsAnalyticModification (n := d j) pj ∧ p '' S j = N j) ∧
          letI := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hS _).2.2
          ∃ (e : Nt → S (Fin.last r)) (f : S (Fin.last r) → Nt),
            ContMDiff 𝓘(ℂ, ComplexModel (d (Fin.last r)))
              𝓘(ℂ, ComplexModel (d (Fin.last r))) ∞ e ∧
            ContMDiff 𝓘(ℂ, ComplexModel (d (Fin.last r)))
              𝓘(ℂ, ComplexModel (d (Fin.last r))) ∞ f ∧
            f ∘ e = id ∧ e ∘ f = id ∧
            p ∘ ((Subtype.val : S (Fin.last r) → Y) ∘ e) =
              (Subtype.val : N (Fin.last r) → X) ∘ q := by
  classical
  let hk : ∀ j, d j ≤ n := fun j => hd0 ▸ hda (Fin.zero_le j)
  let connectedX : ConnectedSpace X := connectedSpace_iff_univ.mpr (by
    simpa only [hN0] using (hN 0).2.1)
  let := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hN _).2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk (Fin.last r)) (hN _).2.2
  induction hq with
  | refl =>
      refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance,
        connectedX, omegaX, id, N, IsBlowupSequence.refl, ?_, hNa, hN0,
        hN, (fun _ _ hy => hy), ?_, id, id, contMDiff_id, contMDiff_id, rfl, rfl, rfl⟩
      · intro j
        simp only [strictTransform, exceptionalLocus_id,
          preimage_id, sdiff_empty, (hN j).1.closure_eq]
      · intro j
        let := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
        change IsBlowupSequence (d j) (N j) (N j) id ∧
          IsAnalyticModification (n := d j) id ∧ id '' N j = N j
        exact ⟨IsBlowupSequence.refl, isAnalyticModification_identity, image_id (N j)⟩
  | @step N0 N1 topN0 chartsN0 complexN0 topN1 chartsN1 complexN1 q0 C b _ hb ih =>
      obtain ⟨W0, topW0, chartsW0, complexW0, compactW0, connectedW0, omegaW0,
        p0, S0, hp0, hstrict0, hS0a, hS00, hS0, hi0, hprops0,
        e0, f0, he0, hf0, hfe0, hef0, hcomm0⟩ := ih
      let := topW0
      let := chartsW0
      let := complexW0
      let := compactW0
      let := connectedW0
      let := SubmanifoldChartedSpace.chartedSpace (hk (Fin.last r)) (hS0 _).2.2
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk (Fin.last r)) (hS0 _).2.2
      have hb' : IsBlowupAlong (d (Fin.last r)) (f0 ⁻¹' C) (e0 ∘ b) :=
        MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse hf0 he0
          (fun z => congrFun hfe0 z) (fun z => congrFun hef0 z) hb
      obtain ⟨W1, topW1, chartsW1, complexW1, compactW1, connectedW1, omegaW1,
        a, S1, ha, _haseq, hstrict1, hS1a, hS10, hS1, hi1, hprops1,
        e1, f1, he1, hf1, hfe1, hef1, hcomm1⟩ :=
        exists_ambientRealization_preserving_smoothAncestors omegaW0 S0 d
          hS0a hda hS00 hd0 hS0 (f0 ⁻¹' C) hb'
      let := topW1
      let := chartsW1
      let := complexW1
      let := compactW1
      let := connectedW1
      have hp1 : IsBlowupSequence n X W1 (p0 ∘ a) :=
        IsBlowupSequence.step p0 (Subtype.val '' (f0 ⁻¹' C)) a hp0 ha
      have hstrict : ∀ j, S1 j = strictTransform n (p0 ∘ a) (N j) := by
        intro j
        rw [StrictTransformComposition.strictTransform_comp hp0.contMDiff ha.contMDiff,
          ← hstrict0 j]
        exact hstrict1 j
      let hi : ∀ j, ∀ y ∈ S1 j, (p0 ∘ a) y ∈ N j :=
        fun j y hy => hi0 j (a y) (hi1 j y hy)
      have hprops : ∀ j,
          letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
          letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
          letI := SubmanifoldChartedSpace.chartedSpace (hk j) (hS1 j).2.2
          letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hS1 j).2.2
          let pj : S1 j → N j := fun y => ⟨(p0 ∘ a) y, hi j y y.2⟩
          IsBlowupSequence (d j) (N j) (S1 j) pj ∧
            IsAnalyticModification (n := d j) pj ∧ (p0 ∘ a) '' S1 j = N j := by
        intro j
        let := SubmanifoldChartedSpace.chartedSpace (hk j) (hN j).2.2
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hN j).2.2
        let := SubmanifoldChartedSpace.chartedSpace (hk j) (hS0 j).2.2
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hS0 j).2.2
        let := SubmanifoldChartedSpace.chartedSpace (hk j) (hS1 j).2.2
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hk j) (hS1 j).2.2
        let p0j : S0 j → N j := fun y => ⟨p0 y, hi0 j y y.2⟩
        let a1j : S1 j → S0 j := fun y => ⟨a y, hi1 j y y.2⟩
        obtain ⟨hp0j, hmod0j, _himage0j⟩ := hprops0 j
        obtain ⟨ha1j, hmod1j, _himage1j⟩ := hprops1 j
        have hpj : IsBlowupSequence (d j) (N j) (S1 j) (p0j ∘ a1j) :=
          IsBlowupSequence.step p0j
            (Subtype.val ⁻¹' (Subtype.val '' (f0 ⁻¹' C))) a1j hp0j ha1j
        have hmodj : IsAnalyticModification (n := d j) (p0j ∘ a1j) :=
          AnalyticModificationComposition.isAnalyticModification_comp hmod0j hmod1j
        have himage : (p0 ∘ a) '' S1 j = N j := by
          apply Subset.antisymm
          · rintro _ ⟨y, hy, rfl⟩; exact hi j y hy
          · intro x hx
            obtain ⟨y, hy⟩ :=
              AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hmodj ⟨x, hx⟩
            exact ⟨y.1, y.2, congrArg Subtype.val hy⟩
        exact ⟨hpj, hmodj, himage⟩
      have hcomm : (p0 ∘ a) ∘ ((Subtype.val : S1 (Fin.last r) → W1) ∘ e1) =
          (Subtype.val : N (Fin.last r) → X) ∘ (q0 ∘ b) := by
        calc
          (p0 ∘ a) ∘ ((Subtype.val : S1 (Fin.last r) → W1) ∘ e1) =
              p0 ∘ (a ∘ ((Subtype.val : S1 (Fin.last r) → W1) ∘ e1)) := rfl
          _ = p0 ∘ ((Subtype.val : S0 (Fin.last r) → W0) ∘ (e0 ∘ b)) :=
            congrArg (fun F => p0 ∘ F) hcomm1
          _ = (p0 ∘ ((Subtype.val : S0 (Fin.last r) → W0) ∘ e0)) ∘ b := rfl
          _ = (Subtype.val : N (Fin.last r) → X) ∘ (q0 ∘ b) :=
            congrArg (fun F => F ∘ b) hcomm0
      exact ⟨W1, topW1, chartsW1, complexW1, compactW1, connectedW1, omegaW1,
        p0 ∘ a, S1, hp1, hstrict, hS1a, hS10, hS1, hi, hprops,
        e1, f1, he1, hf1, hfe1, hef1, hcomm⟩

end SGPT.Okounkov
