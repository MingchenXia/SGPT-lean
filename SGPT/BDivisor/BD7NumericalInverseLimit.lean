import SGPT.BDivisor.BD7NumericalTransitions
import SGPT.BDivisor.CofinalLinearFamiliesTopology
import SGPT.BDivisor.BDDangFavreWeil
import SGPT.GAGA.OkoCloseDXMain
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor

/-- A pointwise linear identification respecting the transitions identifies the limits. -/
def compatibleLinearFamilies_congr {I : Type*} [Preorder I]
    {V W : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (p : ∀ ⦃i j : I⦄, i ≤ j → V j →ₗ[ℝ] V i)
    (q : ∀ ⦃i j : I⦄, i ≤ j → W j →ₗ[ℝ] W i)
    (e : ∀ i, V i ≃ₗ[ℝ] W i)
    (square : ∀ ⦃i j : I⦄ (h : i ≤ j) (v : V j), e i (p h v) = q h (e j v)) :
    compatibleLinearFamilies (R := ℝ) p ≃ₗ[ℝ] compatibleLinearFamilies (R := ℝ) q where
  toFun a := ⟨fun i => e i (a.val i), fun i j h => by
    change q h (e j (a.val j)) = e i (a.val i)
    rw [← square h, a.property i j h]⟩
  invFun a := ⟨fun i => (e i).symm (a.val i), fun i j h => by
    apply (e i).injective
    change e i (p h ((e j).symm (a.val j))) = e i ((e i).symm (a.val i))
    rw [square h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, a.property i j h]⟩
  left_inv a := Subtype.ext (funext fun i => (e i).symm_apply_apply (a.val i))
  right_inv a := Subtype.ext (funext fun i => (e i).apply_symm_apply (a.val i))
  map_add' a b := Subtype.ext (funext fun i => (e i).map_add (a.val i) (b.val i))
  map_smul' c a := Subtype.ext (funext fun i => (e i).map_smul c (a.val i))

section PushforwardSquare

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame
open scoped Manifold ContDiff

variable {m : ℕ} {U V S T : Type}
variable [TopologicalSpace U] [ChartedSpace (ComplexModel (m + 1)) U]
    [IsComplexManifold (m + 1) U] [CompactSpace U]
variable [TopologicalSpace V] [ChartedSpace (ComplexModel (m + 1)) V]
    [IsComplexManifold (m + 1) V] [CompactSpace V]
variable [TopologicalSpace S] [ChartedSpace (ComplexModel (m + 1)) S]
    [IsComplexManifold (m + 1) S] [CompactSpace S]
variable [TopologicalSpace T] [ChartedSpace (ComplexModel (m + 1)) T]
    [IsComplexManifold (m + 1) T] [CompactSpace T]

local notation "I" => 𝓘(ℂ, ComplexModel (m + 1))
local notation "frame" => canonicalBasis (m + 1)
local notation "positive" => Nat.succ_pos m

private theorem classPushforward_eq_of_map_eq {g g' : U → V} (h : g = g')
    (hg : ContMDiff I I ∞ g) (hg' : ContMDiff I I ∞ g') :
    classPushforward hg frame positive = classPushforward hg' frame positive := by
  subst g'
  rfl

/-- A point-map square is a pushforward square on Bott--Chern classes. -/
theorem classPushforward_transition_square
    {q : U → V} {k : S → T} {eU : U → S} {eV : V → T}
    (hq : ContMDiff I I ∞ q) (hk : ContMDiff I I ∞ k)
    (heU : ContMDiff I I ∞ eU) (heV : ContMDiff I I ∞ eV)
    (h : ∀ x, eV (q x) = k (eU x)) (a : RealBottChern (m + 1) U) :
    classPushforward heV frame positive (classPushforward hq frame positive a) =
      classPushforward hk frame positive (classPushforward heU frame positive a) := by
  rw [← classPushforward_comp frame positive heV hq a,
    ← classPushforward_comp frame positive hk heU a]
  have congrPush {g g' : U → T} (hgg' : g = g')
      (hg : ContMDiff I I ∞ g) (hg' : ContMDiff I I ∞ g') :
      classPushforward hg frame positive a = classPushforward hg' frame positive a := by
    subst g'
    rfl
  exact congrPush (funext h) _ _

open SGPT.Okounkov.OF13
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- The actual current pushforward restricted to the Néron--Severi spaces. -/
def neronSeveriPushforward {g : U → V} (hg : IsAnalyticModification (n := m + 1) g) :
    DFAlg.neronSeveri (m + 1) U →ₗ[ℝ] DFAlg.neronSeveri (m + 1) V :=
  ((classPushforward hg.1 frame positive).comp (DFAlg.neronSeveri (m + 1) U).subtype).codRestrict
    (DFAlg.neronSeveri (m + 1) V)
    (fun a => DFAlg.classPushforward_mem_neronSeveri_of_isAnalyticModification hg a.property)

private theorem diffeoBCPush_inverse (e : U ≃ₘ⟮I, I⟯ V) (a : RealBottChern (m + 1) U) :
    classPushforward e.symm.contMDiff frame positive (classPushforward e.contMDiff frame positive a) =
      a := by
  rw [← classPushforward_comp frame positive e.symm.contMDiff e.contMDiff]
  have H {g : U → U} (h : g = id) (hg : ContMDiff I I ∞ g) :
      classPushforward hg frame positive a = a := by
    subst g
    exact classPushforward_id frame positive a
  exact H (funext e.symm_apply_apply) _

/-- A biholomorphism identifies Néron--Severi spaces by its actual pushforward. -/
def neronSeveriDiffeoEquiv (e : U ≃ₘ⟮I, I⟯ V) :
    DFAlg.neronSeveri (m + 1) U ≃ₗ[ℝ] DFAlg.neronSeveri (m + 1) V :=
  { neronSeveriPushforward (isAnalyticModification_of_diffeomorph e) with
    invFun := neronSeveriPushforward (isAnalyticModification_of_diffeomorph e.symm)
    left_inv := fun a => Subtype.ext (diffeoBCPush_inverse e a.val)
    right_inv := fun a => Subtype.ext (diffeoBCPush_inverse e.symm a.val) }

end PushforwardSquare

namespace BD7

open Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open scoped Manifold ContDiff

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {d : ℕ}

local instance indexPointTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g

local instance indexPointCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance indexPointManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

/-- Algebraic integrality supplies connectedness of the actual native point space. -/
theorem smoothProjectiveNativeConnected {S : Scheme.{0}}
    (g : S ⟶ Spec (.of ℂ)) (n : ℕ) (EG : ClosedProjectiveEmbedding g)
    [IsIntegral S] [SmoothOfRelativeDimension n g] : ConnectedSpace (SchemeComplexPoint g) := by
  letI := EG.locallyOfFiniteType
  letI : Nonempty (SchemeComplexPoint g) := integralFiniteTypeSchemeComplexPoint_nonempty g
  exact SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral g EG n

abbrev SmoothModelNumericalClasses (A : SmoothAlgebraicModel f d) :=
  OriginalIntegralCurveDegreeQuotient_bd7 (A.p ≫ f) A.embedding

section CofinalLimit

variable [IsIntegral X] [SmoothOfRelativeDimension d f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)

local notation "Book" => BookBlowupModel (f := f) (d := d)
local notation "Models" => SmoothAlgebraicModel f d
local notation "N" => SmoothModelNumericalClasses (f := f) (d := d)

/-- Restrict the classes of all smooth projective models to the chosen tower algebraizations,
then take the modelwise Chern class. -/
def smoothModelNumericalInverseLimitEquiv
    {S : BookBlowupModel (f := f) (d := d) → Type*}
    [∀ π : BookBlowupModel (f := f) (d := d), AddCommGroup (S π)]
    [∀ π : BookBlowupModel (f := f) (d := d), Module ℝ (S π)]
    (E : ClosedProjectiveEmbedding f)
    (alg : ∀ π : Book, BookModelAlgebraization (f := f) (d := d) π)
    (push : ∀ ⦃A B : Models⦄, A ≤ B → N B →ₗ[ℝ] N A)
    (pushRefl : ∀ (A : Models) (v : N A), push (le_refl A) v = v)
    (pushTrans : ∀ ⦃A B C : Models⦄ (h : A ≤ B) (k : B ≤ C) (v : N C),
      push (h.trans k) v = push h (push k v))
    (bookPush : ∀ ⦃π τ : Book⦄, π ≤ τ → S τ →ₗ[ℝ] S π)
    (chern : ∀ π : Book, N (alg π).A ≃ₗ[ℝ] S π)
    (square : ∀ ⦃π τ : Book⦄ (h : π ≤ τ) (v : N (alg τ).A),
      chern π (push (bookModelAlgebraization_monotone E alg h) v) =
        bookPush h (chern τ v)) :
    compatibleLinearFamilies (R := ℝ) (I := Models) (E := N) push ≃ₗ[ℝ]
      compatibleLinearFamilies (R := ℝ) (I := Book) (E := S) bookPush := by
  let F : Book → Models := fun π => (alg π).A
  let mono : Monotone F := bookModelAlgebraization_monotone E alg
  let restricted : ∀ ⦃π τ : Book⦄, π ≤ τ → N (F τ) →ₗ[ℝ] N (F π) :=
    fun {π τ} h => push (A := F π) (B := F τ) (mono h)
  let e₁ :
      compatibleLinearFamilies (R := ℝ) (I := Models) (E := N) push ≃ₗ[ℝ]
      compatibleLinearFamilies (R := ℝ) (I := Book) (E := fun π => N (F π)) restricted :=
    compatibleLinearFamiliesCofinalEquiv (R := ℝ) (I := Models) (E := N) (J := Book)
      (fun {i j} h => push (A := i) (B := j) h)
      pushRefl (fun {i j k} h q x => pushTrans (A := i) (B := j) (C := k) h q x)
      F mono (fun a b => ModelSystem.Model.exists_le_le a b)
      (fun A => bookModelAlgebraization_cofinal E alg A)
  let e₂ :
      compatibleLinearFamilies (R := ℝ) (I := Book) (E := fun π => N (F π)) restricted ≃ₗ[ℝ]
      compatibleLinearFamilies (R := ℝ) (I := Book) (E := S) bookPush :=
    compatibleLinearFamilies_congr (I := Book) (V := fun π => N (F π)) (W := S)
      (fun {i j} h => restricted (π := i) (τ := j) h)
      (fun {i j} h => bookPush (π := i) (τ := j) h) chern
      (fun {i j} h v => square (π := i) (τ := j) h v)
  exact e₁.trans e₂

end CofinalLimit

section ActualBookSquare

open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy CanonicalCurrentFrame
open SGPT.Okounkov.OF13

variable {m : ℕ} [IsIntegral X] [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)
local notation "Book₊" => BookBlowupModel (f := f) (d := m + 1)
/-- The actual book transition on algebraic Bott--Chern incarnations. -/
def bookNeronSeveriPushforward ⦃π τ : Book₊⦄ (h : π ≤ τ) :
    DFAlg.neronSeveri (m + 1) τ.1.carrier →ₗ[ℝ] DFAlg.neronSeveri (m + 1) π.1.carrier :=
  neronSeveriPushforward (Modification.Dominates.isAnalyticModification
    (show π.1 ≤ τ.1 from h))

local notation "hnorm" => normalizationProjectiveForCurves_bd7

/-- The canonical all-integral degree-one numerical Chern class on a chosen tower,
transported along its actual algebraization. -/
def bookModelNumericalChern
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (π : Book₊) :
    SmoothModelNumericalClasses (algebraize π).A ≃ₗ[ℝ] DFAlg.neronSeveri (m + 1) π.1.carrier := by
  let A := (algebraize π).A
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI : CompactSpace (SchemeComplexPoint (A.p ≫ f)) :=
    (algebraize π).e.symm.toHomeomorph.compactSpace
  letI : ConnectedSpace (SchemeComplexPoint (A.p ≫ f)) :=
    smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  exact (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m hnorm).trans
    (neronSeveriDiffeoEquiv (algebraize π).e)

local notation "M₊" => SmoothAlgebraicModel f (m + 1)

/-- Analytic modification pushforward transported to the algebraic numerical quotient.
Its characterization by algebraic prime cycles is a separate required input. -/
def smoothModelTransportedAnalyticPushforward (E : ClosedProjectiveEmbedding f) {A B : M₊} (h : A ≤ B) :
    SmoothModelNumericalClasses B →ₗ[ℝ] SmoothModelNumericalClasses A := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  exact transportedAnalyticPushforward
    (q := A.homOfLE h) (hq := SmoothAlgebraicModel.homOfLE_structure h)
    (hmod := SmoothAlgebraicModel.homOfLE_analyticModification h E)
    (B.p ≫ f) (A.p ≫ f) B.embedding A.embedding (m := m) hnorm

/-- The numerical Chern square for the transported pushforward and the actual book map. -/
theorem bookModelNumericalChern_transport_square
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    {π τ : Book₊} (h : π ≤ τ)
    (v : SmoothModelNumericalClasses (algebraize τ).A) :
    bookModelNumericalChern algebraize π
      (smoothModelTransportedAnalyticPushforward E
        (bookModelAlgebraization_monotone E algebraize h) v) =
      bookNeronSeveriPushforward h (bookModelNumericalChern algebraize τ v) := by
  let A := (algebraize π).A
  let B := (algebraize τ).A
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  let hA : A ≤ B := bookModelAlgebraization_monotone E algebraize h
  let hk := Modification.Dominates.isAnalyticModification (show π.1 ≤ τ.1 from h)
  have hBC :
      classPushforward (algebraize π).e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m hnorm
          (smoothModelTransportedAnalyticPushforward E hA v)).val =
      classPushforward hk.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (classPushforward (algebraize τ).e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (integralNumericalEquivNS_bd7 (B.p ≫ f) B.embedding m hnorm v).val) := by
    simp only [smoothModelTransportedAnalyticPushforward,
      numericalChern_transportedAnalyticPushforward]
    exact classPushforward_transition_square
      (SmoothAlgebraicModel.homOfLE_analyticModification hA E).1 hk.1
      (algebraize τ).e.contMDiff (algebraize π).e.contMDiff
      (bookModelAlgebraization_transition E algebraize h) _
  exact Subtype.ext hBC

include E in
/-- The actual selected scheme morphisms satisfy the transition identity on complex points. -/
theorem smoothModelComplexPointMap_homOfLE_refl (A : M₊) :
    schemeComplexPointMap (A.p ≫ f) (A.p ≫ f) (A.homOfLE (le_refl A))
      (SmoothAlgebraicModel.homOfLE_structure (le_refl A)) = id := by
  funext z
  apply Subtype.ext
  change z.val ≫ A.homOfLE (le_refl A) = z.val
  rw [SmoothAlgebraicModel.homOfLE_refl E A, Category.comp_id]

include E in
/-- The actual selected scheme morphisms satisfy the transition composition on complex points. -/
theorem smoothModelComplexPointMap_homOfLE_trans {A B C : M₊} (h : A ≤ B) (k : B ≤ C) :
    schemeComplexPointMap (C.p ≫ f) (A.p ≫ f) (A.homOfLE (h.trans k))
      (SmoothAlgebraicModel.homOfLE_structure (h.trans k)) =
    schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) (A.homOfLE h)
      (SmoothAlgebraicModel.homOfLE_structure h) ∘
    schemeComplexPointMap (C.p ≫ f) (B.p ≫ f) (B.homOfLE k)
      (SmoothAlgebraicModel.homOfLE_structure k) := by
  funext z
  apply Subtype.ext
  change z.val ≫ A.homOfLE (h.trans k) = (z.val ≫ B.homOfLE k) ≫ A.homOfLE h
  rw [SmoothAlgebraicModel.homOfLE_trans E h k, Category.assoc]

local notation "N₊" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "transport" => smoothModelTransportedAnalyticPushforward E

theorem smoothModelTransportedAnalyticPushforward_refl (A : M₊) (v : N₊ A) :
    transport (le_refl A) v = v := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  apply (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m hnorm).injective
  apply Subtype.ext
  simp only [smoothModelTransportedAnalyticPushforward, numericalChern_transportedAnalyticPushforward]
  rw [classPushforward_eq_of_map_eq (smoothModelComplexPointMap_homOfLE_refl E A) _
    (contMDiff_id (I := 𝓘(ℂ, ComplexModel (m + 1))) (n := ∞))]
  exact classPushforward_id (canonicalBasis (m + 1)) (Nat.succ_pos m) _

theorem smoothModelTransportedAnalyticPushforward_trans {A B C : M₊}
    (h : A ≤ B) (k : B ≤ C) (v : N₊ C) :
    transport (h.trans k) v = transport h (transport k v) := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := C.embedding.isSeparated
  letI := C.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := C.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  letI := smoothProjectiveNativeConnected (C.p ≫ f) (m + 1) C.embedding
  apply (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m hnorm).injective
  apply Subtype.ext
  simp only [smoothModelTransportedAnalyticPushforward, numericalChern_transportedAnalyticPushforward]
  let hh := (SmoothAlgebraicModel.homOfLE_analyticModification h E).1
  let hk := (SmoothAlgebraicModel.homOfLE_analyticModification k E).1
  rw [classPushforward_eq_of_map_eq (smoothModelComplexPointMap_homOfLE_trans E h k) _ (hh.comp hk)]
  exact classPushforward_comp (canonicalBasis (m + 1)) (Nat.succ_pos m) hh hk _

/-- With the literal algebraic cycle transitions, the coordinatewise Chern map identifies
their projective limit with the book's compatible Néron--Severi incarnations. The
comparison input is discharged by the residue-weighted prime formula. -/
def originalNumericalInverseLimitChernEquiv
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (pushOriginal : ∀ ⦃A B : M₊⦄, A ≤ B → N₊ B →ₗ[ℝ] N₊ A)
    (pushComparison : ∀ ⦃A B : M₊⦄ (h : A ≤ B),
      pushOriginal h = smoothModelTransportedAnalyticPushforward E h) :
    compatibleLinearFamilies (R := ℝ) (I := M₊) (E := N₊) pushOriginal ≃ₗ[ℝ]
      compatibleLinearFamilies (R := ℝ) (I := Book₊)
        (E := fun π => DFAlg.neronSeveri (m + 1) π.1.carrier) bookNeronSeveriPushforward := by
  have hRefl (A : M₊) (v : N₊ A) : pushOriginal (le_refl A) v = v := by
    rw [pushComparison (le_refl A)]
    exact smoothModelTransportedAnalyticPushforward_refl E A v
  have hTrans ⦃A B C : M₊⦄ (h : A ≤ B) (k : B ≤ C) (v : N₊ C) :
      pushOriginal (h.trans k) v = pushOriginal h (pushOriginal k v) := by
    simp only [pushComparison]
    exact smoothModelTransportedAnalyticPushforward_trans E h k v
  let chern := bookModelNumericalChern algebraize
  have hSquare ⦃π τ : Book₊⦄ (h : π ≤ τ) (v : N₊ (algebraize τ).A) :
      chern π (pushOriginal (bookModelAlgebraization_monotone E algebraize h) v) =
        bookNeronSeveriPushforward h (chern τ v) := by
    rw [pushComparison (bookModelAlgebraization_monotone E algebraize h)]
    exact bookModelNumericalChern_transport_square E algebraize h v
  exact smoothModelNumericalInverseLimitEquiv
    (E := E) (alg := algebraize) (push := pushOriginal) (pushRefl := hRefl)
    (pushTrans := fun {A B C} h k v => hTrans (A := A) (B := B) (C := C) h k v) (S := fun π : Book₊ => DFAlg.neronSeveri (m + 1) π.1.carrier)
    (bookPush := bookNeronSeveriPushforward)
    (chern := chern) (square := fun {π τ} h v => hSquare (π := π) (τ := τ) h v)

theorem originalNumericalInverseLimitChernEquiv_apply
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (pushOriginal : ∀ ⦃A B : M₊⦄, A ≤ B → N₊ B →ₗ[ℝ] N₊ A)
    (pushComparison : ∀ ⦃A B : M₊⦄ (h : A ≤ B),
      pushOriginal h = smoothModelTransportedAnalyticPushforward E h)
    (v : compatibleLinearFamilies (R := ℝ) pushOriginal) (π : Book₊) :
    (originalNumericalInverseLimitChernEquiv E algebraize pushOriginal pushComparison v).val π =
      bookModelNumericalChern algebraize π (v.val (algebraize π).A) := by
  unfold originalNumericalInverseLimitChernEquiv smoothModelNumericalInverseLimitEquiv
  rfl

theorem originalNumericalInverseLimitChernEquiv_tendsto {T : Type*}
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (pushOriginal : ∀ ⦃A B : M₊⦄, A ≤ B → N₊ B →ₗ[ℝ] N₊ A)
    (pushComparison : ∀ ⦃A B : M₊⦄ (h : A ≤ B),
      pushOriginal h = smoothModelTransportedAnalyticPushforward E h)
    (u : T → compatibleLinearFamilies (R := ℝ) pushOriginal) (v : compatibleLinearFamilies (R := ℝ) pushOriginal)
    (l : Filter T) :
    (∀ A, Tendsto (fun t => (u t).val A) l
      (@nhds _ (euclideanTopology (N₊ A)) (v.val A))) ↔
    (∀ π : Book₊, Tendsto (fun t =>
      (originalNumericalInverseLimitChernEquiv E algebraize pushOriginal
        pushComparison (u t)).val π) l
      (@nhds _ (euclideanTopology (DFAlg.neronSeveri (m + 1) π.1.carrier))
        ((originalNumericalInverseLimitChernEquiv E algebraize pushOriginal
          pushComparison v).val π))) := by
  simp only [originalNumericalInverseLimitChernEquiv_apply]
  exact compatibleLinearFamilies_tendsto_iff_cofinal_chern
    (I := M₊) (J := Book₊) (E := N₊)
    (B := fun π => DFAlg.neronSeveri (m + 1) π.1.carrier)
    (fun {A B} h => pushOriginal (A := A) (B := B) h) (fun π => (algebraize π).A)
    (bookModelAlgebraization_cofinal E algebraize)
    (fun π => (bookModelNumericalChern algebraize π).toLinearMap)
    (fun π => (bookModelNumericalChern algebraize π).injective) u v l

open SGPT.Hodge.BDivChain.NativeDraft

/-- The book already presents the same compatible Néron--Severi incarnations as
a submodule of its Bott--Chern Weil b-divisors. -/
def bookCompatibleNeronSeveriEquivAlgebraicWeil
    [ConnectedSpace (SchemeComplexPoint f)] :
    compatibleLinearFamilies (R := ℝ) (I := Book₊)
        (E := fun π => DFAlg.neronSeveri (m + 1) π.1.carrier) bookNeronSeveriPushforward ≃ₗ[ℝ]
      DFAlg.algebraicWeilFamilies m (SchemeComplexPoint f) where
  toFun a := ⟨⟨fun π => (a.val π).val, fun π τ h => by
      rw [DFAlg.classPushforwardAny_eq π τ h]
      exact congrArg Subtype.val (a.property π τ h)⟩, fun π => (a.val π).property⟩
  invFun a := ⟨fun π => ⟨a.val.val π, a.property π⟩, fun π τ h => by
    apply Subtype.ext
    have hcompat := a.val.property π τ h
    rw [DFAlg.classPushforwardAny_eq π τ h] at hcompat
    exact hcompat⟩
  left_inv a := Subtype.ext (funext fun π => Subtype.ext rfl)
  right_inv a := Subtype.ext (Subtype.ext rfl)
  map_add' a b := Subtype.ext (Subtype.ext rfl)
  map_smul' c a := Subtype.ext (Subtype.ext rfl)

/-- The resulting Chern identification lands in the book's existing algebraic Weil
b-divisor submodule, with the same literal Bott--Chern incarnations. -/
def originalNumericalAlgebraicWeilEquiv [ConnectedSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (pushOriginal : ∀ ⦃A B : M₊⦄, A ≤ B → N₊ B →ₗ[ℝ] N₊ A)
    (pushComparison : ∀ ⦃A B : M₊⦄ (h : A ≤ B),
      pushOriginal h = smoothModelTransportedAnalyticPushforward E h) :
    compatibleLinearFamilies (R := ℝ) pushOriginal ≃ₗ[ℝ] DFAlg.algebraicWeilFamilies m (SchemeComplexPoint f) :=
  (originalNumericalInverseLimitChernEquiv E algebraize pushOriginal pushComparison).trans
    bookCompatibleNeronSeveriEquivAlgebraicWeil

theorem originalNumericalAlgebraicWeilEquiv_apply [ConnectedSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (pushOriginal : ∀ ⦃A B : M₊⦄, A ≤ B → N₊ B →ₗ[ℝ] N₊ A)
    (pushComparison : ∀ ⦃A B : M₊⦄ (h : A ≤ B),
      pushOriginal h = smoothModelTransportedAnalyticPushforward E h)
    (v : compatibleLinearFamilies (R := ℝ) pushOriginal) (π : Book₊) :
    (originalNumericalAlgebraicWeilEquiv E algebraize pushOriginal pushComparison v).val.val π =
      (bookModelNumericalChern algebraize π (v.val (algebraize π).A)).val := by
  unfold originalNumericalAlgebraicWeilEquiv
  rw [LinearEquiv.trans_apply]
  change ((originalNumericalInverseLimitChernEquiv E algebraize pushOriginal pushComparison v).val π).val = _
  rw [originalNumericalInverseLimitChernEquiv_apply]

theorem originalNumericalAlgebraicWeilEquiv_tendsto [ConnectedSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)
    (algebraize : ∀ π : Book₊, BookModelAlgebraization (f := f) (d := m + 1) π)
    (pushOriginal : ∀ ⦃A B : M₊⦄, A ≤ B → N₊ B →ₗ[ℝ] N₊ A)
    (pushComparison : ∀ ⦃A B : M₊⦄ (h : A ≤ B),
      pushOriginal h = smoothModelTransportedAnalyticPushforward E h)
    {T : Type*} (u : T → compatibleLinearFamilies (R := ℝ) pushOriginal)
    (v : compatibleLinearFamilies (R := ℝ) pushOriginal) (l : Filter T) :
    (∀ A, Tendsto (fun t => (u t).val A) l
      (@nhds _ (euclideanTopology (N₊ A)) (v.val A))) ↔
    (∀ π : Book₊, Tendsto (fun t =>
      (originalNumericalAlgebraicWeilEquiv E algebraize pushOriginal pushComparison (u t)).val.val π) l
      (@nhds _ (euclideanTopology (RealBottChern (m + 1) π.1.carrier))
        ((originalNumericalAlgebraicWeilEquiv E algebraize pushOriginal pushComparison v).val.val π))) := by
  simp only [originalNumericalAlgebraicWeilEquiv_apply]
  exact compatibleLinearFamilies_tendsto_iff_cofinal_chern
    (I := M₊) (J := Book₊) (E := N₊)
    (B := fun π => RealBottChern (m + 1) π.1.carrier)
    (fun {A B} h => pushOriginal (A := A) (B := B) h) (fun π => (algebraize π).A)
    (bookModelAlgebraization_cofinal E algebraize)
    (fun π => (DFAlg.neronSeveri (m + 1) π.1.carrier).subtype.comp
      (bookModelNumericalChern algebraize π).toLinearMap)
    (fun π => Subtype.val_injective.comp (bookModelNumericalChern algebraize π).injective) u v l

end ActualBookSquare

end BD7
end SGPT.BDivisor
