import SGPT.GAGA.CoreOkaModules

/-!
# Coherent sheaves as subquotients of free modules: kernels, images, cokernels

Infrastructure of lane SERRE-CORE (Serre's GAGA, towards source `lma:GAGA`). Source for the
mathematics: Grauert--Remmert, *Coherent analytic sheaves*, Ch. 1--2 (kernels, images and
cokernels of morphisms of coherent sheaves are coherent).

A coherent analytic sheaf on an open set `Ω` of a complex normed space is presented as a
subquotient `F = M/N` of a free module `𝒪^ι`, with `N ⊆ M ⊆ 𝒪^ι` coherent germ modules
(`Subquotient`). All sheaves of Serre's hyperplane induction are of this form. A morphism
`F → G` is a matrix `A` of holomorphic functions with `A(M_F) ⊆ M_G` and `A(N_F) ⊆ N_G`
(`Subquotient.Hom`); it induces the maps of stalks `M_{F,y}/N_{F,y} → M_{G,y}/N_{G,y}`.

On a space with Oka's property (e.g. `ℂⁿ`) the kernel `(M_F ∩ A⁻¹(N_G))/N_F`, the image
`(N_G + A(M_F))/N_G` and the cokernel `M_G/(N_G + A(M_F))` are again subquotients
(`Subquotient.ker`, `im`, `coker`). Exactness of `F → G → H` at `G` is the stalkwise equality
`ker = im` inside `M_G` (`Subquotient.Exact`); injectivity and surjectivity are the
vanishing of the kernel and of the cokernel. We prove the exactness of
`0 → ker φ → F → G → coker φ → 0` and the factorisation `F ↠ im φ ↪ G`
(`exact_kerι`, `exact_cokerπ`, `injective_kerι`, `surjective_cokerπ`, `surjective_toIm`,
`injective_imι`, `imι_comp_toIm`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf

namespace SGPT.GAGA.Core

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### The identity matrix -/

section IdMatrix

variable {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι]

/-- The identity matrix. -/
def idMatrix (ι : Type) [DecidableEq ι] : ι → ι → X → ℂ :=
  fun i j _ => if i = j then 1 else 0

@[simp] theorem matApply_idMatrix (a : ι → X → ℂ) : matApply (idMatrix ι) a = a := by
  funext i x
  simp [matApply, idMatrix]

theorem holAt_idMatrix (y : X) (i j : ι) : HolAt (idMatrix (X := X) ι i j) y :=
  holAt_const _ y

end IdMatrix

/-! ### Subquotients -/

/-- A coherent analytic sheaf on `Ω`, presented as the subquotient `M/N` of `𝒪^ι` by coherent
germ modules `N ⊆ M`. -/
structure Subquotient (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (Ω : Set X) where
  /-- The rank of the ambient free module. -/
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- The numerator. -/
  M : GermModule X ι
  /-- The denominator. -/
  N : GermModule X ι
  coherent_M : M.IsCoherentOn Ω
  coherent_N : N.IsCoherentOn Ω
  le : N.LeOn M Ω

attribute [instance] Subquotient.fintype Subquotient.decEq

namespace Subquotient

variable {Ω : Set X}

/-- A morphism of subquotients: a matrix of holomorphic functions mapping numerator to
numerator and denominator to denominator. -/
structure Hom (F G : Subquotient X Ω) where
  /-- The matrix `𝒪^{ι_F} → 𝒪^{ι_G}`. -/
  A : G.ι → F.ι → X → ℂ
  holAt : ∀ x ∈ Ω, ∀ i j, HolAt (A i j) x
  map_M : ∀ y ∈ Ω, ∀ a, F.M.mem y a → G.M.mem y (matApply A a)
  map_N : ∀ y ∈ Ω, ∀ a, F.N.mem y a → G.N.mem y (matApply A a)

/-- Two morphisms induce the same map of sheaves: their difference maps the numerator of the
source into the denominator of the target. -/
def Hom.Equiv {F G : Subquotient X Ω} (φ ψ : Hom F G) : Prop :=
  ∀ y ∈ Ω, ∀ a, F.M.mem y a → G.N.mem y (fun i x => matApply φ.A a i x - matApply ψ.A a i x)

/-- The identity morphism. -/
def Hom.id (F : Subquotient X Ω) : Hom F F where
  A := idMatrix F.ι
  holAt x _ := holAt_idMatrix x
  map_M y _ a ha := by rwa [matApply_idMatrix]
  map_N y _ a ha := by rwa [matApply_idMatrix]

/-- Composition of morphisms: the product of matrices. -/
def Hom.comp {F G H : Subquotient X Ω} (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  A := GermModule.matMul ψ.A φ.A
  holAt x hx i k := HolAt.fintype_sum fun j => (ψ.holAt x hx i j).mul (φ.holAt x hx j k)
  map_M y hy a ha := by
    have h := ψ.map_M y hy _ (φ.map_M y hy a ha)
    rwa [matApply_matApply] at h
  map_N y hy a ha := by
    have h := ψ.map_N y hy _ (φ.map_N y hy a ha)
    rwa [matApply_matApply] at h

/-- `φ` is injective: its kernel `M_F ∩ A⁻¹(N_G)` is `N_F`. -/
def Injective {F G : Subquotient X Ω} (φ : Hom F G) : Prop :=
  (F.M.inf (G.N.comap φ.A)).EqOn F.N Ω

/-- `φ` is surjective: `N_G + A(M_F) = M_G`. -/
def Surjective {F G : Subquotient X Ω} (φ : Hom F G) : Prop :=
  (G.N.sup (F.M.map φ.A)).EqOn G.M Ω

/-- `F → G → H` is exact at `G`: the kernel of `ψ` equals the image of `φ`, stalkwise. -/
def Exact {F G H : Subquotient X Ω} (φ : Hom F G) (ψ : Hom G H) : Prop :=
  (G.M.inf (H.N.comap ψ.A)).EqOn (G.N.sup (F.M.map φ.A)) Ω

/-- A short exact sequence `0 → F → G → H → 0`. -/
def ShortExact {F G H : Subquotient X Ω} (φ : Hom F G) (ψ : Hom G H) : Prop :=
  Injective φ ∧ Exact φ ψ ∧ Surjective ψ

section Constructions

variable (hX : OkaProperty X)

/-- The kernel `(M_F ∩ A⁻¹(N_G))/N_F` of a morphism. -/
abbrev ker {F G : Subquotient X Ω} (φ : Hom F G) : Subquotient X Ω where
  ι := F.ι
  M := F.M.inf (G.N.comap φ.A)
  N := F.N
  coherent_M := GermModule.IsCoherentOn.inf hX F.coherent_M
    (GermModule.IsCoherentOn.comap hX G.coherent_N φ.holAt)
  coherent_N := F.coherent_N
  le y hy a ha := ⟨F.le y hy a ha, (F.coherent_N y hy).holTupleAt_of_mem ha, φ.map_N y hy a ha⟩

/-- The image `(N_G + A(M_F))/N_G` of a morphism. -/
abbrev im {F G : Subquotient X Ω} (φ : Hom F G) : Subquotient X Ω where
  ι := G.ι
  M := G.N.sup (F.M.map φ.A)
  N := G.N
  coherent_M := G.coherent_N.sup (F.coherent_M.map φ.holAt)
  coherent_N := G.coherent_N
  le := GermModule.le_sup_left (F.coherent_M.map φ.holAt)

/-- The cokernel `M_G/(N_G + A(M_F))` of a morphism. -/
abbrev coker {F G : Subquotient X Ω} (φ : Hom F G) : Subquotient X Ω where
  ι := G.ι
  M := G.M
  N := G.N.sup (F.M.map φ.A)
  coherent_M := G.coherent_M
  coherent_N := G.coherent_N.sup (F.coherent_M.map φ.holAt)
  le := GermModule.sup_le G.coherent_M G.le (GermModule.map_le G.coherent_M φ.map_M)

variable {hX}

/-- The inclusion of the kernel. -/
abbrev kerι {F G : Subquotient X Ω} (φ : Hom F G) : Hom (ker hX φ) F where
  A := idMatrix F.ι
  holAt x _ := holAt_idMatrix x
  map_M y _ a ha := by rw [matApply_idMatrix]; exact ha.1
  map_N y _ a ha := by rwa [matApply_idMatrix]

/-- The projection onto the cokernel. -/
abbrev cokerπ {F G : Subquotient X Ω} (φ : Hom F G) : Hom G (coker φ) where
  A := idMatrix G.ι
  holAt x _ := holAt_idMatrix x
  map_M y _ a ha := by rwa [matApply_idMatrix]
  map_N y hy a ha := by
    rw [matApply_idMatrix]
    exact GermModule.le_sup_left (F.coherent_M.map φ.holAt) y hy a ha

/-- The corestriction `F → im φ`. -/
abbrev toIm {F G : Subquotient X Ω} (φ : Hom F G) : Hom F (im φ) where
  A := φ.A
  holAt := φ.holAt
  map_M y hy _ ha := GermModule.le_sup_right G.coherent_N y hy _
    (GermModule.mem_map_of_mem ha)
  map_N := φ.map_N

/-- The inclusion `im φ → G`. -/
abbrev imι {F G : Subquotient X Ω} (φ : Hom F G) : Hom (im φ) G where
  A := idMatrix G.ι
  holAt x _ := holAt_idMatrix x
  map_M y hy a ha := by
    rw [matApply_idMatrix]
    exact GermModule.sup_le G.coherent_M G.le (GermModule.map_le G.coherent_M φ.map_M)
      y hy a ha
  map_N y _ a ha := by rwa [matApply_idMatrix]

/-- `0 → ker φ → F` is exact: the kernel inclusion is injective. -/
theorem injective_kerι {F G : Subquotient X Ω} (φ : Hom F G) :
    Injective (kerι (hX := hX) φ) := by
  intro y hy a
  constructor
  · rintro ⟨-, -, ha⟩
    rwa [matApply_idMatrix] at ha
  · intro ha
    refine ⟨(ker hX φ).le y hy a ha, (F.coherent_N y hy).holTupleAt_of_mem ha, ?_⟩
    rwa [matApply_idMatrix]

/-- `ker φ → F → G` is exact. -/
theorem exact_kerι {F G : Subquotient X Ω} (φ : Hom F G) :
    Exact (kerι (hX := hX) φ) φ := by
  have hK := (ker hX φ).coherent_M
  refine GermModule.LeOn.antisymm (fun y hy a ha => ?_) ?_
  · refine ⟨fun _ _ => 0, a, (F.coherent_N y hy).zero_mem, ?_,
      fun _ => Eventually.of_forall fun x => by simp⟩
    exact ⟨a, ha, fun i => by rw [matApply_idMatrix]⟩
  · refine GermModule.sup_le hK (ker hX φ).le ?_
    exact GermModule.map_le hK fun y _ a ha => by rwa [matApply_idMatrix]

/-- `F → G → coker φ` is exact. -/
theorem exact_cokerπ {F G : Subquotient X Ω} (φ : Hom F G) :
    Exact φ (cokerπ φ) := by
  refine GermModule.LeOn.antisymm (fun y hy a ha => ?_) (fun y hy a ha => ?_)
  · have h : (G.N.sup (F.M.map φ.A)).mem y (matApply (idMatrix G.ι) a) := ha.2.2
    rwa [matApply_idMatrix] at h
  · refine ⟨(coker φ).le y hy a ha, (G.coherent_M y hy).holTupleAt_of_mem
      ((coker φ).le y hy a ha), ?_⟩
    show (G.N.sup (F.M.map φ.A)).mem y (matApply (idMatrix G.ι) a)
    rwa [matApply_idMatrix]

/-- `G → coker φ → 0` is exact: the projection is surjective. -/
theorem surjective_cokerπ {F G : Subquotient X Ω} (φ : Hom F G) :
    Surjective (cokerπ φ) := by
  refine GermModule.LeOn.antisymm ?_ (fun y hy a ha => ?_)
  · exact GermModule.sup_le G.coherent_M (coker φ).le
      (GermModule.map_le G.coherent_M fun y _ a ha => by
        show G.M.mem y (matApply (idMatrix G.ι) a)
        rwa [matApply_idMatrix])
  · refine ⟨fun _ _ => 0, a, ((coker φ).coherent_N y hy).zero_mem, ⟨a, ha, fun i => ?_⟩,
      fun _ => Eventually.of_forall fun x => by simp⟩
    show a i =ᶠ[𝓝 y] matApply (idMatrix G.ι) a i
    rw [matApply_idMatrix]

/-- The corestriction `F → im φ` is surjective. -/
theorem surjective_toIm {F G : Subquotient X Ω} (φ : Hom F G) : Surjective (toIm φ) := by
  intro y _ a
  show (G.N.sup (F.M.map φ.A)).mem y a ↔ (G.N.sup (F.M.map φ.A)).mem y a
  exact Iff.rfl

/-- The inclusion `im φ → G` is injective. -/
theorem injective_imι {F G : Subquotient X Ω} (φ : Hom F G) : Injective (imι φ) := by
  refine GermModule.LeOn.antisymm (fun y _ a ha => ?_) (fun y hy a ha => ?_)
  · have h : G.N.mem y (matApply (idMatrix G.ι) a) := ha.2.2
    rwa [matApply_idMatrix] at h
  · refine ⟨(im φ).le y hy a ha, (G.coherent_N y hy).holTupleAt_of_mem ha, ?_⟩
    show G.N.mem y (matApply (idMatrix G.ι) a)
    rwa [matApply_idMatrix]

/-- `φ` factors as `F ↠ im φ ↪ G`. -/
theorem imι_comp_toIm {F G : Subquotient X Ω} (φ : Hom F G) :
    ((imι φ).comp (toIm φ)).A = φ.A := by
  funext i k x
  simp [Hom.comp, GermModule.matMul, idMatrix]

/-- The kernel of the corestriction `F → im φ` is the kernel of `φ`, and the kernel of a
morphism vanishes iff the morphism is injective. -/
theorem injective_iff_ker_eqOn {F G : Subquotient X Ω} (φ : Hom F G) :
    Injective φ ↔ ((ker hX φ).M).EqOn (ker hX φ).N Ω :=
  Iff.rfl

end Constructions

end Subquotient

end SGPT.GAGA.Core
