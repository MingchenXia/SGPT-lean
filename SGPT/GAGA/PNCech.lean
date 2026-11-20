import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.BigOperators

/-!
# Čech complexes of a finite cover: the algebra

Infrastructure of lane SERRE-PN (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145).

Serre's proof uses cohomology only through the Čech complex of one fixed finite cover
`(K_i)_{i ∈ I}`. This file contains the algebra, for an arbitrary finite linearly ordered index
type `I` and an arbitrary ring `k`.

* `CechSystem k I`: a *coefficient system*, i.e. `k`-modules `Γ(s)` for the finite subsets
  `s ⊆ I` (to be thought of as the sections over `K_s = ⋂_{i ∈ s} K_i`) with restriction maps
  `Γ(s) → Γ(t)` for `s ⊆ t`, compatible with composition.
* `cechCochain Γ q`: the alternating `q`-cochains, families `(c_s)` with `c_s ∈ Γ(s)`
  supported on the subsets with `q + 1` elements. `cechD Γ` is the Čech differential
  `(d c)_t = ∑_{j ∈ t} ε(j, t) c_{t ∖ j}|_t` with `ε(j, t) = (-1)^{#{i ∈ t : i < j}}`
  (`cechSign`); `cechD_cechD` is `d ∘ d = 0`.
* `cechComplex Γ : CochainComplex (ModuleCat k) ℕ` and its cohomology `cechH Γ q`, with
  Mathlib's homology of complexes. `cechClass Γ q` is the class map from the concrete
  cocycles `ker d` onto `cechH Γ q`; its kernel is the coboundaries
  (`cechClass_surjective`, `cechClass_eq_zero_iff`, `cechClass_injective_zero`).
* A morphism of coefficient systems induces maps on cohomology (`cechHMap`), and a short
  exact sequence of coefficient systems induces the long exact cohomology sequence
  (`cechδ`, `cechH_exact₁`, `cechH_exact₂`, `cechH_exact₃`), by Mathlib's homology sequence.
* `cechH_subsingleton`: the cohomology vanishes in degrees `q ≥ #I`.

Blueprint: `claude-serre-pn.tex`, nodes `claude-serre-pn:cech-complex`,
`claude-serre-pn:cech-les`.
-/

set_option autoImplicit false

open CategoryTheory

universe u v

namespace SGPT.GAGA.PN

/-! ### Signs -/

section Sign

variable {I : Type} [LinearOrder I]

/-- The sign `(-1)^{#{i ∈ t : i < j}}` of the element `j` of `t`. -/
def cechSign (t : Finset I) (j : I) : ℤ :=
  (-1) ^ (t.filter (· < j)).card

theorem cechSign_erase_of_lt {t : Finset I} {j j' : I} (h : j' < j) :
    cechSign (t.erase j) j' = cechSign t j' := by
  unfold cechSign
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp [not_lt.2 h.le]

theorem cechSign_erase_of_gt {t : Finset I} {j j' : I} (hj' : j' ∈ t) (h : j' < j) :
    cechSign (t.erase j') j = -cechSign t j := by
  unfold cechSign
  rw [Finset.filter_erase]
  have hmem : j' ∈ t.filter (· < j) := Finset.mem_filter.2 ⟨hj', h⟩
  rw [← Finset.card_erase_add_one hmem, pow_succ]
  ring

/-- Removing two elements in the two possible orders gives opposite signs. -/
theorem cechSign_mul_swap {t : Finset I} {j j' : I} (hj : j ∈ t) (hj' : j' ∈ t)
    (hne : j ≠ j') :
    cechSign t j * cechSign (t.erase j) j' = -(cechSign t j' * cechSign (t.erase j') j) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [cechSign_erase_of_gt hj h, cechSign_erase_of_lt h]
    ring
  · rw [cechSign_erase_of_lt h, cechSign_erase_of_gt hj' h]
    ring

end Sign

/-! ### Coefficient systems -/

/-- A coefficient system on the finite subsets of `I`: modules `obj s` with restriction maps
`obj s → obj t` for `s ⊆ t`, compatible with composition. For a cover `(K_i)_{i ∈ I}` and a
sheaf, `obj s` is the module of sections over `⋂_{i ∈ s} K_i`. -/
structure CechSystem (k : Type u) [Ring k] (I : Type) where
  /-- The module attached to a finite subset. -/
  obj : Finset I → Type v
  [addCommGroup : ∀ s, AddCommGroup (obj s)]
  [module : ∀ s, Module k (obj s)]
  /-- The restriction maps. -/
  res : ∀ {s t : Finset I}, s ⊆ t → obj s →ₗ[k] obj t
  res_comp : ∀ {s t r : Finset I} (h₁ : s ⊆ t) (h₂ : t ⊆ r) (x : obj s),
    res h₂ (res h₁ x) = res (h₁.trans h₂) x

attribute [instance] CechSystem.addCommGroup CechSystem.module

namespace CechSystem

variable {k : Type u} [Ring k] {I : Type}

/-- A morphism of coefficient systems: linear maps commuting with the restrictions. -/
structure Hom (Γ Δ : CechSystem.{u, v} k I) where
  /-- The components. -/
  app : ∀ s, Γ.obj s →ₗ[k] Δ.obj s
  naturality : ∀ {s t : Finset I} (h : s ⊆ t) (x : Γ.obj s),
    app t (Γ.res h x) = Δ.res h (app s x)

/-- A short exact sequence `0 → Γ₁ → Γ₂ → Γ₃ → 0` of coefficient systems: exact on every
nonempty subset. -/
structure ShortExact {Γ₁ Γ₂ Γ₃ : CechSystem.{u, v} k I} (φ : Hom Γ₁ Γ₂) (ψ : Hom Γ₂ Γ₃) :
    Prop where
  injective : ∀ s : Finset I, s.Nonempty → Function.Injective (φ.app s)
  exact : ∀ s : Finset I, s.Nonempty → Function.Exact (φ.app s) (ψ.app s)
  surjective : ∀ s : Finset I, s.Nonempty → Function.Surjective (ψ.app s)

theorem res_congr (Γ : CechSystem.{u, v} k I) {s s' t : Finset I} (h : s = s') (hs : s ⊆ t)
    (hs' : s' ⊆ t) (c : ∀ s, Γ.obj s) : Γ.res hs (c s) = Γ.res hs' (c s') := by
  subst h
  rfl

end CechSystem

/-! ### Cochains and the differential -/

section Complex

variable {k : Type u} [Ring k] {I : Type} [LinearOrder I]
variable (Γ : CechSystem.{u, v} k I)

/-- The Čech differential on families: `(d c)_t = ∑_{j ∈ t} ε(j, t) c_{t ∖ j}|_t`. -/
def cechD : (∀ s, Γ.obj s) →ₗ[k] (∀ s, Γ.obj s) where
  toFun c t := ∑ j ∈ t, cechSign t j • Γ.res (Finset.erase_subset j t) (c (t.erase j))
  map_add' c c' := by
    funext t
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext t
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

theorem cechD_apply (c : ∀ s, Γ.obj s) (t : Finset I) :
    cechD Γ c t = ∑ j ∈ t, cechSign t j • Γ.res (Finset.erase_subset j t) (c (t.erase j)) :=
  rfl

/-- **`d ∘ d = 0`** for the Čech differential. -/
theorem cechD_cechD (c : ∀ s, Γ.obj s) : cechD Γ (cechD Γ c) = 0 := by
  funext t
  have hsub : ∀ j j' : I, (t.erase j).erase j' ⊆ t := fun j j' =>
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have h1 : ∀ j ∈ t, cechSign t j • Γ.res (Finset.erase_subset j t) (cechD Γ c (t.erase j)) =
      ∑ j' ∈ t.erase j, (cechSign t j * cechSign (t.erase j) j') •
        Γ.res (hsub j j') (c ((t.erase j).erase j')) := by
    intro j _
    rw [cechD_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_zsmul, Γ.res_comp, smul_smul]
  rw [cechD_apply, Finset.sum_congr rfl h1, Finset.sum_sigma']
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨j, j'⟩ hx
    obtain ⟨hj, hj'⟩ := Finset.mem_sigma.1 hx
    have hne : j' ≠ j := Finset.ne_of_mem_erase hj'
    have hj't : j' ∈ t := Finset.mem_of_mem_erase hj'
    simp only
    rw [cechSign_mul_swap hj hj't hne.symm,
      Γ.res_congr Finset.erase_right_comm (hsub j j') (hsub j' j) c, neg_smul, neg_add_cancel]
  · rintro ⟨j, j'⟩ hx _ heq
    obtain ⟨-, hj'⟩ := Finset.mem_sigma.1 hx
    exact Finset.ne_of_mem_erase hj' (congrArg Sigma.fst heq)
  · rintro ⟨j, j'⟩ hx
    obtain ⟨hj, hj'⟩ := Finset.mem_sigma.1 hx
    exact Finset.mem_sigma.2 ⟨Finset.mem_of_mem_erase hj',
      Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hj').symm, hj⟩⟩
  · rintro ⟨j, j'⟩ _
    rfl

/-- The alternating Čech `q`-cochains: families supported on the subsets with `q + 1`
elements. -/
def cechCochain (q : ℕ) : Submodule k (∀ s, Γ.obj s) where
  carrier := {c | ∀ s : Finset I, s.card ≠ q + 1 → c s = 0}
  add_mem' := fun {a b} ha hb s hs => by
    rw [Pi.add_apply, ha s hs, hb s hs, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun a c hc s hs => by
    rw [Pi.smul_apply, hc s hs, smul_zero]

omit [LinearOrder I] in
theorem mem_cechCochain {q : ℕ} {c : ∀ s, Γ.obj s} :
    c ∈ cechCochain Γ q ↔ ∀ s : Finset I, s.card ≠ q + 1 → c s = 0 :=
  Iff.rfl

theorem cechD_mem {q : ℕ} {c : ∀ s, Γ.obj s} (hc : c ∈ cechCochain Γ q) :
    cechD Γ c ∈ cechCochain Γ (q + 1) := by
  intro t ht
  rw [cechD_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hcard : (t.erase j).card ≠ q + 1 := by
    rw [Finset.card_erase_of_mem hj]
    omega
  rw [hc _ hcard, map_zero, smul_zero]

/-- The Čech differential `C^q → C^{q+1}`. -/
def cechDq (q : ℕ) : cechCochain Γ q →ₗ[k] cechCochain Γ (q + 1) :=
  (cechD Γ).restrict fun _ hc => cechD_mem Γ hc

@[simp] theorem cechDq_coe (q : ℕ) (c : cechCochain Γ q) :
    (cechDq Γ q c : ∀ s, Γ.obj s) = cechD Γ c :=
  rfl

theorem cechDq_comp_cechDq (q : ℕ) : cechDq Γ (q + 1) ∘ₗ cechDq Γ q = 0 :=
  LinearMap.ext fun c => Subtype.ext (cechD_cechD Γ c.1)

/-- The Čech complex of a coefficient system. -/
noncomputable def cechComplex : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of k (cechCochain Γ q))
    (fun q => ModuleCat.ofHom (cechDq Γ q)) fun q => by
      exact ModuleCat.hom_ext (cechDq_comp_cechDq Γ q)

@[simp] theorem cechComplex_d (q : ℕ) :
    (cechComplex Γ).d q (q + 1) = ModuleCat.ofHom (cechDq Γ q) :=
  CochainComplex.of_d (fun q => ModuleCat.of k (cechCochain Γ q))
    (fun q => ModuleCat.ofHom (cechDq Γ q)) q

/-- The Čech cohomology of a coefficient system. -/
noncomputable def cechH (q : ℕ) : ModuleCat.{v} k :=
  (cechComplex Γ).homology q

/-! ### The class map from concrete cocycles -/

/-- The inclusion of the concrete cocycles into the cochains, as a morphism of modules. -/
noncomputable def cechCocycleι (q : ℕ) :
    ModuleCat.of k (LinearMap.ker (cechDq Γ q)) ⟶ (cechComplex Γ).X q :=
  ModuleCat.ofHom (LinearMap.ker (cechDq Γ q)).subtype

theorem cechCocycleι_d (q : ℕ) : cechCocycleι Γ q ≫ (cechComplex Γ).d q (q + 1) = 0 := by
  rw [cechComplex_d]
  exact ModuleCat.hom_ext (LinearMap.ext fun z => z.2)

/-- The concrete cocycles `ker (d : C^q → C^{q+1})` map to the cycles of the Čech complex. -/
noncomputable def cechCyclesLift (q : ℕ) :
    ModuleCat.of k (LinearMap.ker (cechDq Γ q)) ⟶ (cechComplex Γ).cycles q :=
  (cechComplex Γ).liftCycles (cechCocycleι Γ q) (q + 1) (by simp) (cechCocycleι_d Γ q)

theorem iCycles_cechCyclesLift (q : ℕ) (z : LinearMap.ker (cechDq Γ q)) :
    ((cechComplex Γ).iCycles q).hom ((cechCyclesLift Γ q).hom z) = z.1 := by
  have h := (cechComplex Γ).liftCycles_i (cechCocycleι Γ q) (q + 1) (by simp)
    (cechCocycleι_d Γ q)
  exact congrArg (fun m => m.hom z) h

theorem iCycles_injective (q : ℕ) :
    Function.Injective ((cechComplex Γ).iCycles q).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem cechD_iCycles (q : ℕ) (x : (cechComplex Γ).cycles q) :
    cechDq Γ q (((cechComplex Γ).iCycles q).hom x) = 0 := by
  have h := (cechComplex Γ).iCycles_d q (q + 1)
  rw [cechComplex_d] at h
  exact congrArg (fun m => m.hom x) h

theorem cechCyclesLift_surjective (q : ℕ) : Function.Surjective (cechCyclesLift Γ q).hom := by
  intro x
  refine ⟨⟨((cechComplex Γ).iCycles q).hom x, cechD_iCycles Γ q x⟩, ?_⟩
  exact iCycles_injective Γ q (iCycles_cechCyclesLift Γ q _)

theorem cechCyclesLift_injective (q : ℕ) : Function.Injective (cechCyclesLift Γ q).hom := by
  intro z z' h
  have h' := congrArg ((cechComplex Γ).iCycles q).hom h
  rw [iCycles_cechCyclesLift, iCycles_cechCyclesLift] at h'
  exact Subtype.ext h'

/-- **The class map**: a concrete `q`-cocycle defines a class in the Čech cohomology. -/
noncomputable def cechClass (q : ℕ) : LinearMap.ker (cechDq Γ q) →ₗ[k] cechH Γ q :=
  (cechCyclesLift Γ q ≫ (cechComplex Γ).homologyπ q).hom

theorem cechClass_apply (q : ℕ) (z : LinearMap.ker (cechDq Γ q)) :
    cechClass Γ q z = ((cechComplex Γ).homologyπ q).hom ((cechCyclesLift Γ q).hom z) :=
  rfl

/-- Every cohomology class is the class of a cocycle. -/
theorem cechClass_surjective (q : ℕ) : Function.Surjective (cechClass Γ q) := by
  have h1 : Function.Surjective ((cechComplex Γ).homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  intro x
  obtain ⟨y, rfl⟩ := h1 x
  obtain ⟨z, rfl⟩ := cechCyclesLift_surjective Γ q y
  exact ⟨z, rfl⟩

theorem cechCyclesLift_d (q : ℕ) (c : cechCochain Γ q) (hc : cechDq Γ (q + 1) (cechDq Γ q c) = 0) :
    (cechCyclesLift Γ (q + 1)).hom ⟨cechDq Γ q c, hc⟩ =
      ((cechComplex Γ).toCycles q (q + 1)).hom c := by
  apply iCycles_injective Γ (q + 1)
  rw [iCycles_cechCyclesLift]
  have h := (cechComplex Γ).toCycles_i q (q + 1)
  rw [cechComplex_d] at h
  exact (congrArg (fun m => m.hom c) h).symm

/-- **The kernel of the class map is the coboundaries** (positive degrees). -/
theorem cechClass_eq_zero_iff (q : ℕ) (z : LinearMap.ker (cechDq Γ (q + 1))) :
    cechClass Γ (q + 1) z = 0 ↔ ∃ c : cechCochain Γ q, cechDq Γ q c = z.1 := by
  constructor
  · intro hz
    have hex : (ShortComplex.mk ((cechComplex Γ).toCycles q (q + 1))
        ((cechComplex Γ).homologyπ (q + 1))
        ((cechComplex Γ).toCycles_comp_homologyπ q (q + 1))).Exact :=
      ShortComplex.exact_of_g_is_cokernel _
        ((cechComplex Γ).homologyIsCokernel q (q + 1) (by simp))
    obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex
      ((cechCyclesLift Γ (q + 1)).hom z) hz
    refine ⟨c, ?_⟩
    have h1 := congrArg ((cechComplex Γ).iCycles (q + 1)).hom hc
    rw [iCycles_cechCyclesLift] at h1
    rw [← h1]
    have h := (cechComplex Γ).toCycles_i q (q + 1)
    rw [cechComplex_d] at h
    exact (congrArg (fun m => m.hom c) h).symm
  · rintro ⟨c, hc⟩
    have hc2 : cechDq Γ (q + 1) (cechDq Γ q c) = 0 := by rw [hc]; exact z.2
    have hz : z = ⟨cechDq Γ q c, hc2⟩ := Subtype.ext hc.symm
    have h1 : (cechCyclesLift Γ (q + 1)).hom z = ((cechComplex Γ).toCycles q (q + 1)).hom c :=
      (congrArg (cechCyclesLift Γ (q + 1)).hom hz).trans (cechCyclesLift_d Γ q c hc2)
    show ((cechComplex Γ).homologyπ (q + 1)).hom ((cechCyclesLift Γ (q + 1)).hom z) = 0
    rw [h1]
    exact congrArg (fun m => m.hom c) ((cechComplex Γ).toCycles_comp_homologyπ q (q + 1))

/-- In degree zero the class map is injective: `H⁰` is the module of `0`-cocycles. -/
theorem cechClass_injective_zero : Function.Injective (cechClass Γ 0) := by
  have h1 : Function.Injective ((cechComplex Γ).homologyπ 0).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact h1.comp (cechCyclesLift_injective Γ 0)

/-- The Čech cohomology vanishes if every cocycle is a coboundary. -/
theorem cechH_subsingleton_of_exact (q : ℕ)
    (h : ∀ z : cechCochain Γ (q + 1), cechDq Γ (q + 1) z = 0 →
      ∃ c : cechCochain Γ q, cechDq Γ q c = z) :
    Subsingleton (cechH Γ (q + 1)) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨zx, rfl⟩ := cechClass_surjective Γ (q + 1) x
  obtain ⟨zy, rfl⟩ := cechClass_surjective Γ (q + 1) y
  have hx := (cechClass_eq_zero_iff Γ q zx).2 (h zx.1 zx.2)
  have hy := (cechClass_eq_zero_iff Γ q zy).2 (h zy.1 zy.2)
  rw [hx, hy]

omit [LinearOrder I] in
/-- **Vanishing above the number of sets**: there are no cochains in degrees `q ≥ #I`. -/
theorem cechCochain_eq_bot [Fintype I] {q : ℕ} (hq : Fintype.card I ≤ q) :
    cechCochain Γ q = ⊥ := by
  refine le_bot_iff.1 fun c hc => ?_
  rw [Submodule.mem_bot]
  funext s
  exact hc s (by have := Finset.card_le_univ s; omega)

/-- **Vanishing above the number of sets**: `Ȟ^q = 0` for `q ≥ #I`. -/
theorem cechH_subsingleton [Fintype I] {q : ℕ} (hq : Fintype.card I ≤ q) :
    Subsingleton (cechH Γ q) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨zx, rfl⟩ := cechClass_surjective Γ q x
  obtain ⟨zy, rfl⟩ := cechClass_surjective Γ q y
  have h0 : ∀ z : LinearMap.ker (cechDq Γ q), z = 0 := fun z =>
    Subtype.ext (Subtype.ext (funext fun s =>
      z.1.2 s (by have := Finset.card_le_univ s; omega)))
  rw [h0 zx, h0 zy]

/-! ### The augmentation `Γ(∅) → Ȟ⁰` -/

theorem sum_cechSign_of_card_two {t : Finset I} (ht : t.card = 2) :
    ∑ j ∈ t, cechSign t j = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · have h1 : ({x, y} : Finset I).filter (· < x) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hi
      · exact lt_irrefl _ hi
      · exact lt_asymm h hi
    have h2 : ({x, y} : Finset I).filter (· < y) = {x} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hi⟩
        · rfl
        · exact absurd hi (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩
    simp [cechSign, h1, h2]
  · have h1 : ({x, y} : Finset I).filter (· < y) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hi
      · exact lt_asymm h hi
      · exact lt_irrefl _ hi
    have h2 : ({x, y} : Finset I).filter (· < x) = {y} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hi⟩
        · exact absurd hi (lt_irrefl _)
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h⟩
    simp [cechSign, h1, h2]

/-- The restrictions of a global section `g ∈ Γ(∅)` to the sets `K_i`, as a family. -/
def cechAugFamily : Γ.obj ∅ →ₗ[k] (∀ s, Γ.obj s) :=
  LinearMap.pi fun s => if s.card = 1 then Γ.res (Finset.empty_subset s) else 0

omit [LinearOrder I] in
theorem cechAugFamily_apply (g : Γ.obj ∅) (s : Finset I) :
    cechAugFamily Γ g s = if s.card = 1 then Γ.res (Finset.empty_subset s) g else 0 := by
  simp only [cechAugFamily, LinearMap.pi_apply]
  split_ifs <;> rfl

omit [LinearOrder I] in
theorem cechAugFamily_mem (g : Γ.obj ∅) : cechAugFamily Γ g ∈ cechCochain Γ 0 := by
  intro s hs
  rw [cechAugFamily_apply, if_neg hs]

theorem cechD_cechAugFamily (g : Γ.obj ∅) : cechD Γ (cechAugFamily Γ g) = 0 := by
  funext t
  by_cases ht : t.card = 2
  · rw [cechD_apply]
    have h : ∀ j ∈ t, cechSign t j • Γ.res (Finset.erase_subset j t)
        (cechAugFamily Γ g (t.erase j)) = cechSign t j • Γ.res (Finset.empty_subset t) g := by
      intro j hj
      rw [cechAugFamily_apply, if_pos (by rw [Finset.card_erase_of_mem hj, ht]), Γ.res_comp]
    rw [Finset.sum_congr rfl h, ← Finset.sum_smul, sum_cechSign_of_card_two ht, zero_smul]
    rfl
  · exact cechD_mem Γ (cechAugFamily_mem Γ g) t ht

/-- **The augmentation** `Γ(∅) → Z⁰`: a global section gives the `0`-cocycle of its
restrictions. -/
def cechAug : Γ.obj ∅ →ₗ[k] LinearMap.ker (cechDq Γ 0) :=
  ((cechAugFamily Γ).codRestrict (cechCochain Γ 0) (cechAugFamily_mem Γ)).codRestrict _
    fun g => Subtype.ext (cechD_cechAugFamily Γ g)

@[simp] theorem cechAug_coe_apply (g : Γ.obj ∅) (s : Finset I) :
    ((cechAug Γ g : cechCochain Γ 0) : ∀ s, Γ.obj s) s =
      if s.card = 1 then Γ.res (Finset.empty_subset s) g else 0 :=
  cechAugFamily_apply Γ g s

/-- **`0`-cocycles agree on overlaps**: if `d z = 0` for a `0`-cochain `z`, then the
restrictions of `z_{i}` and `z_{k}` to `{i, k}` coincide. -/
theorem cechCocycle_zero_res {z : cechCochain Γ 0} (hz : cechDq Γ 0 z = 0) {i k : I}
    (hik : i ≠ k) :
    Γ.res (Finset.singleton_subset_iff.2 (Finset.mem_insert_self i {k})) (z.1 {i}) =
      Γ.res (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self k))) (z.1 {k}) := by
  have hd : cechD Γ z.1 {i, k} = 0 := congrFun (congrArg Subtype.val hz) {i, k}
  rw [cechD_apply, Finset.sum_pair hik] at hd
  have he1 : ({i, k} : Finset I).erase i = {k} := by
    rw [Finset.erase_insert (Finset.notMem_singleton.2 hik)]
  have he2 : ({i, k} : Finset I).erase k = {i} := by
    rw [Finset.erase_insert_of_ne hik, Finset.erase_singleton, insert_empty_eq]
  rw [Γ.res_congr he1 (Finset.erase_subset i _)
      (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))),
    Γ.res_congr he2 (Finset.erase_subset k _)
      (Finset.singleton_subset_iff.2 (Finset.mem_insert_self i {k}))] at hd
  have hs : cechSign {i, k} i + cechSign {i, k} k = 0 := by
    rw [← Finset.sum_pair hik]
    exact sum_cechSign_of_card_two (Finset.card_pair hik)
  have hsq : cechSign ({i, k} : Finset I) k * cechSign {i, k} k = 1 := by
    unfold cechSign
    rw [← mul_pow]
    norm_num
  have hεi : cechSign ({i, k} : Finset I) i = -cechSign {i, k} k := eq_neg_of_add_eq_zero_left hs
  rw [hεi, neg_smul, neg_add_eq_zero] at hd
  have h2 := congrArg (fun x => cechSign ({i, k} : Finset I) k • x) hd
  simp only [smul_smul, hsq, one_smul] at h2
  exact h2.symm

end Complex

/-! ### Functoriality and the long exact sequence -/

section Functoriality

variable {k : Type u} [Ring k] {I : Type} [LinearOrder I]
variable {Γ Δ : CechSystem.{u, v} k I}

/-- The map on families induced by a morphism of coefficient systems. -/
def cechMapTot (φ : CechSystem.Hom Γ Δ) : (∀ s, Γ.obj s) →ₗ[k] (∀ s, Δ.obj s) :=
  LinearMap.pi fun s => (φ.app s).comp (LinearMap.proj s)

omit [LinearOrder I] in
@[simp] theorem cechMapTot_apply (φ : CechSystem.Hom Γ Δ) (c : ∀ s, Γ.obj s) (s : Finset I) :
    cechMapTot φ c s = φ.app s (c s) :=
  rfl

theorem cechD_cechMapTot (φ : CechSystem.Hom Γ Δ) (c : ∀ s, Γ.obj s) :
    cechD Δ (cechMapTot φ c) = cechMapTot φ (cechD Γ c) := by
  funext t
  simp only [cechD_apply, cechMapTot_apply, map_sum, map_zsmul, φ.naturality]

/-- The map on `q`-cochains induced by a morphism of coefficient systems. -/
def cechMapq (φ : CechSystem.Hom Γ Δ) (q : ℕ) : cechCochain Γ q →ₗ[k] cechCochain Δ q :=
  (cechMapTot φ).restrict fun c hc s hs => by
    rw [cechMapTot_apply, hc s hs, map_zero]

omit [LinearOrder I] in
@[simp] theorem cechMapq_coe (φ : CechSystem.Hom Γ Δ) (q : ℕ) (c : cechCochain Γ q)
    (s : Finset I) : (cechMapq φ q c : ∀ s, Δ.obj s) s = φ.app s (c.1 s) :=
  rfl

theorem cechDq_cechMapq (φ : CechSystem.Hom Γ Δ) (q : ℕ) (c : cechCochain Γ q) :
    cechDq Δ q (cechMapq φ q c) = cechMapq φ (q + 1) (cechDq Γ q c) :=
  Subtype.ext (cechD_cechMapTot φ c.1)

/-- The chain map induced by a morphism of coefficient systems. -/
noncomputable def cechMap (φ : CechSystem.Hom Γ Δ) : cechComplex Γ ⟶ cechComplex Δ :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (cechMapq φ q)) fun q => by
    rw [cechComplex_d, cechComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun c => cechDq_cechMapq φ q c)

@[simp] theorem cechMap_f (φ : CechSystem.Hom Γ Δ) (q : ℕ) :
    (cechMap φ).f q = ModuleCat.ofHom (cechMapq φ q) :=
  rfl

/-- The map on Čech cohomology induced by a morphism of coefficient systems. -/
noncomputable def cechHMap (φ : CechSystem.Hom Γ Δ) (q : ℕ) : cechH Γ q ⟶ cechH Δ q :=
  HomologicalComplex.homologyMap (cechMap φ) q

/-- The map on concrete cocycles induced by a morphism of coefficient systems. -/
def cechCocycleMap (φ : CechSystem.Hom Γ Δ) (q : ℕ) :
    LinearMap.ker (cechDq Γ q) →ₗ[k] LinearMap.ker (cechDq Δ q) :=
  (cechMapq φ q).restrict fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [cechDq_cechMapq, hz, map_zero]

/-- The class map is natural. -/
theorem cechHMap_cechClass (φ : CechSystem.Hom Γ Δ) (q : ℕ) (z : LinearMap.ker (cechDq Γ q)) :
    (cechHMap φ q).hom (cechClass Γ q z) = cechClass Δ q (cechCocycleMap φ q z) := by
  have h3 : (HomologicalComplex.cyclesMap (cechMap φ) q).hom ((cechCyclesLift Γ q).hom z) =
      (cechCyclesLift Δ q).hom (cechCocycleMap φ q z) := by
    apply iCycles_injective Δ q
    rw [iCycles_cechCyclesLift]
    have h5 := congrArg (fun m => m.hom ((cechCyclesLift Γ q).hom z))
      (HomologicalComplex.cyclesMap_i (cechMap φ) q)
    refine h5.trans ?_
    show cechMapq φ q (((cechComplex Γ).iCycles q).hom ((cechCyclesLift Γ q).hom z)) = _
    rw [iCycles_cechCyclesLift]
    rfl
  have h2 := congrArg (fun m => m.hom ((cechCyclesLift Γ q).hom z))
    (HomologicalComplex.homologyπ_naturality (cechMap φ) q)
  refine h2.trans ?_
  show ((cechComplex Δ).homologyπ q).hom
    ((HomologicalComplex.cyclesMap (cechMap φ) q).hom ((cechCyclesLift Γ q).hom z)) = _
  rw [h3]
  rfl

variable {Γ₁ Γ₂ Γ₃ : CechSystem.{u, v} k I} {φ : CechSystem.Hom Γ₁ Γ₂}
  {ψ : CechSystem.Hom Γ₂ Γ₃}

omit [LinearOrder I] in
theorem cechMapq_injective (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    Function.Injective (cechMapq φ q) := by
  intro c c' hcc
  refine Subtype.ext (funext fun s => ?_)
  by_cases hs : s.card = q + 1
  · have hne : s.Nonempty := Finset.card_pos.1 (by omega)
    exact h.injective s hne (congrFun (congrArg Subtype.val hcc) s)
  · rw [c.2 s hs, c'.2 s hs]

omit [LinearOrder I] in
theorem cechMapq_exact (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    Function.Exact (cechMapq φ q) (cechMapq ψ q) := by
  classical
  intro c
  constructor
  · intro hc
    have hc' : ∀ s : Finset I, ψ.app s (c.1 s) = 0 := fun s =>
      congrFun (congrArg Subtype.val hc) s
    have hex : ∀ s : Finset I, s.card = q + 1 → ∃ x : Γ₁.obj s, φ.app s x = c.1 s := fun s hs =>
      (h.exact s (Finset.card_pos.1 (by omega)) (c.1 s)).1 (hc' s)
    refine ⟨⟨fun s => if hs : s.card = q + 1 then (hex s hs).choose else 0, fun s hs => ?_⟩,
      Subtype.ext (funext fun s => ?_)⟩
    · exact dif_neg hs
    · by_cases hs : s.card = q + 1
      · rw [cechMapq_coe]
        simp only [dif_pos hs]
        exact (hex s hs).choose_spec
      · rw [cechMapq_coe]
        simp only [dif_neg hs]
        rw [map_zero, c.2 s hs]
  · rintro ⟨b, rfl⟩
    refine Subtype.ext (funext fun s => ?_)
    by_cases hs : s.card = q + 1
    · exact (h.exact s (Finset.card_pos.1 (by omega)) _).2 ⟨b.1 s, rfl⟩
    · rw [cechMapq_coe, cechMapq_coe, b.2 s hs, map_zero, map_zero]
      rfl

omit [LinearOrder I] in
theorem cechMapq_surjective (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    Function.Surjective (cechMapq ψ q) := by
  classical
  intro c
  have hex : ∀ s : Finset I, s.card = q + 1 → ∃ x : Γ₂.obj s, ψ.app s x = c.1 s := fun s hs =>
    h.surjective s (Finset.card_pos.1 (by omega)) (c.1 s)
  refine ⟨⟨fun s => if hs : s.card = q + 1 then (hex s hs).choose else 0, fun s hs => ?_⟩,
    Subtype.ext (funext fun s => ?_)⟩
  · exact dif_neg hs
  · by_cases hs : s.card = q + 1
    · rw [cechMapq_coe]
      simp only [dif_pos hs]
      exact (hex s hs).choose_spec
    · rw [cechMapq_coe]
      simp only [dif_neg hs]
      rw [map_zero, c.2 s hs]

theorem cechMap_comp_eq_zero (h : CechSystem.ShortExact φ ψ) : cechMap φ ≫ cechMap ψ = 0 := by
  ext q : 1
  rw [HomologicalComplex.comp_f, cechMap_f, cechMap_f]
  exact ModuleCat.hom_ext (LinearMap.ext fun c => (cechMapq_exact h q _).2 ⟨c, rfl⟩)

/-- The short complex of Čech complexes of a short exact sequence of coefficient systems. -/
noncomputable def cechShortComplex (h : CechSystem.ShortExact φ ψ) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk (cechMap φ) (cechMap ψ) (cechMap_comp_eq_zero h)

/-- A short exact sequence of coefficient systems gives a short exact sequence of Čech
complexes. -/
theorem cechShortComplex_shortExact (h : CechSystem.ShortExact φ ψ) :
    (cechShortComplex h).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q =>
    ModuleCat.shortComplex_shortExact _ (cechMapq_exact h q) (cechMapq_injective h q)
      (cechMapq_surjective h q)

/-- The connecting homomorphism `Ȟ^q(Γ₃) → Ȟ^{q+1}(Γ₁)` of a short exact sequence of
coefficient systems. -/
noncomputable def cechδ (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    cechH Γ₃ q ⟶ cechH Γ₁ (q + 1) :=
  (cechShortComplex_shortExact h).δ q (q + 1) rfl

/-- **Long exact sequence**, exactness at `Ȟ^q(Γ₂)`. -/
theorem cechH_exact₂ (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    Function.Exact (cechHMap φ q).hom (cechHMap ψ q).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechShortComplex_shortExact h).homology_exact₂ q)

/-- **Long exact sequence**, exactness at `Ȟ^q(Γ₃)`. -/
theorem cechH_exact₃ (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    Function.Exact (cechHMap ψ q).hom (cechδ h q).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechShortComplex_shortExact h).homology_exact₃ q (q + 1) rfl)

/-- **Long exact sequence**, exactness at `Ȟ^{q+1}(Γ₁)`. -/
theorem cechH_exact₁ (h : CechSystem.ShortExact φ ψ) (q : ℕ) :
    Function.Exact (cechδ h q).hom (cechHMap φ (q + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechShortComplex_shortExact h).homology_exact₁ q (q + 1) rfl)

/-- **Long exact sequence**, the beginning: `Ȟ⁰(Γ₁) → Ȟ⁰(Γ₂)` is injective. -/
theorem cechHMap_injective_zero (h : CechSystem.ShortExact φ ψ) :
    Function.Injective (cechHMap φ 0).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := cechClass_surjective Γ₁ 0 x
  rw [cechHMap_cechClass] at hx
  have h0 : cechCocycleMap φ 0 z = 0 :=
    cechClass_injective_zero Γ₂ (by rw [hx, map_zero])
  have hz : z = 0 := by
    apply Subtype.ext
    apply cechMapq_injective h 0
    have h1 : cechMapq φ 0 z.1 = 0 := congrArg Subtype.val h0
    exact h1.trans (map_zero (cechMapq φ 0)).symm
  rw [hz, map_zero]

end Functoriality

end SGPT.GAGA.PN
