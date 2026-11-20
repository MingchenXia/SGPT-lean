import SGPT.TestCurve.TCEncSeparating

/-!
# The filtration of a test configuration is exhaustive

Source: `rmk:PhongSturm`, `rmk:NApotential:L862` ([BHJ17, §2.5]: the filtration induced by a test
configuration is a `ℤ`-filtration). For `s ∈ H⁰(X, L^m)` the invariant extension `s̄` is a section
of `𝓛^m` over `𝓧 ∖ 𝓧₀ = {t ≠ 0}`, and `tᴺ s̄` extends to `𝓧` for `N ≫ 0`; hence `s ∈ 𝓕^{-N}`.

## Main results

* `exists_extension_pow_smul`: on an integral quasi-compact scheme `Z`, for `τ ∈ Γ(Z, 𝒪)` with
  `D(τ) ≠ ∅` and a section `x` of `M^m` over `D(τ)` (`M` a line bundle), `τᴺ x` extends to a global
  section for some `N` (clearing denominators on a finite affine cover refining an atlas, and
  gluing; on an integral scheme sections agreeing on a nonempty open agree).
* `TestConfiguration.sbar`: the invariant extension `s̄ = q^* s ∈ Γ(𝓧 ∖ 𝓧₀, 𝓛^m)`, glued from
  the sections with coefficients `q^♯ s_j` in the frames `ε_j^m`.
* `TestConfiguration.exists_piece_eq_top`: `𝓕^μ H⁰(X, L^m) = H⁰(X, L^m)` for some `μ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite

/-! ### Extension of sections across the zero locus of a function -/

section Extension

variable {Z : Scheme.{0}} {M : Z.Modules}

theorem bundle_map_map (m : ℕ) {U V W : Z.Opens} (h1 : W ≤ V) (h2 : V ≤ U)
    (s : bundleSections (bundleTensorPower M m) U) :
    (bundleTensorPower M m).val.map (homOfLE h1).op
        ((bundleTensorPower M m).val.map (homOfLE h2).op s) =
      (bundleTensorPower M m).val.map (homOfLE (h1.trans h2)).op s :=
  (PresheafOfModules.map_comp_apply _ (homOfLE h2).op (homOfLE h1).op s).symm

theorem presheaf_map_map {U V W : Z.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (r : Γ(Z, U)) :
    Z.presheaf.map (homOfLE h1).op (Z.presheaf.map (homOfLE h2).op r) =
      Z.presheaf.map (homOfLE (h1.trans h2)).op r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- On an integral scheme, restriction of sections of `M^m` from an open contained in a chart to
a nonempty smaller open is injective. -/
theorem restrict_injective_of_frame [IsIntegral Z] {U W Q : Z.Opens} (e : LocalBundleFrame M U)
    (m : ℕ) (hW : W ≤ U) (hQ : Q ≤ W) (hne : (Q : Set Z).Nonempty) :
    Function.Injective ((bundleTensorPower M m).val.map (homOfLE hQ).op) := by
  intro s s' h
  apply ((e.tensorPower m).coefficients (homOfLE hW)).injective
  have : Nonempty Q := ⟨⟨hne.some, hne.some_mem⟩⟩
  apply map_injective_of_isIntegral (X := Z) (homOfLE hQ)
  have h1 := (e.tensorPower m).coefficients_restrict (homOfLE hW) (homOfLE hQ) s
  have h2 := (e.tensorPower m).coefficients_restrict (homOfLE hW) (homOfLE hQ) s'
  exact h1.symm.trans ((congrArg ((e.tensorPower m).coefficients (homOfLE hQ ≫ homOfLE hW)) h).trans
    h2)

/-- Sections over an open without points agree. -/
theorem sections_eq_of_empty {W : Z.Opens} (m : ℕ) (hW : ¬ (W : Set Z).Nonempty)
    (s s' : bundleSections (bundleTensorPower M m) W) : s = s' := by
  apply TopCat.Presheaf.IsSheaf.section_ext (F := (bundleTensorPower M m).val.presheaf)
    (bundleTensorPower M m).isSheaf
  intro x hx
  exact absurd ⟨x, hx⟩ hW

/-- **Clearing denominators for sections of a line bundle**: on an integral quasi-compact scheme
`Z`, for `τ ∈ Γ(Z, 𝒪)` with `D(τ) ≠ ∅` and a section `x` of `M^m` over `D(τ)`, some `τᴺ x` is the
restriction of a global section. -/
theorem exists_extension_pow_smul [IsIntegral Z] [CompactSpace Z] (b : LineBundleAtlas M) (m : ℕ)
    (τ : Γ(Z, ⊤)) (hD : (Z.basicOpen τ : Set Z).Nonempty)
    (x : bundleSections (bundleTensorPower M m) (Z.basicOpen τ)) :
    ∃ (N : ℕ) (σ : bundlePowerGlobalSections M m),
      ((bundleTensorPower M m).val.map (homOfLE (le_top : Z.basicOpen τ ≤ ⊤)).op σ :
          bundleSections (bundleTensorPower M m) (Z.basicOpen τ)) =
        (Z.presheaf.map (homOfLE (le_top : Z.basicOpen τ ≤ ⊤)).op τ ^ N :
          Γ(Z, Z.basicOpen τ)) • x := by
  classical
  -- affine opens inside charts
  have hloc : ∀ z : Z, ∃ (i : b.I) (A : Z.Opens), IsAffineOpen A ∧ z ∈ A ∧ A ≤ b.opens i := by
    intro z
    obtain ⟨i, hi⟩ := b.covers z
    obtain ⟨_, ⟨A, hA, rfl⟩, hzA, hAi⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open hi (b.opens i).isOpen
    exact ⟨i, A, hA, hzA, hAi⟩
  choose ci cA hcA hzA hAi using hloc
  -- a finite subcover
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun z => (cA z : Set Z))
    (fun z => (cA z).isOpen) (fun z _ => Set.mem_iUnion.mpr ⟨z, hzA z⟩)
  -- clearing denominators on each affine
  let τA : ∀ z, Γ(Z, cA z) := fun z => Z.presheaf.map (homOfLE le_top).op τ
  have hBeq : ∀ z, Z.basicOpen (τA z) = cA z ⊓ Z.basicOpen τ := fun z => Scheme.basicOpen_res _ _ _
  have hBD : ∀ z, Z.basicOpen (τA z) ≤ Z.basicOpen τ := fun z => (hBeq z).le.trans inf_le_right
  have hBA : ∀ z, Z.basicOpen (τA z) ≤ cA z := fun z => Z.basicOpen_le _
  let hc : ∀ z, Γ(Z, Z.basicOpen (τA z)) := fun z =>
    ((b.frame (ci z)).tensorPower m).coefficients (homOfLE ((hBA z).trans (hAi z)))
      ((bundleTensorPower M m).val.map (homOfLE (hBD z)).op x)
  have hloc2 : ∀ z, ∃ (n : ℕ) (y : Γ(Z, cA z)),
      Z.presheaf.map (homOfLE (hBA z)).op y =
        (Z.presheaf.map (homOfLE (hBA z)).op (τA z)) ^ n * hc z := by
    intro z
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Z (cA z) (hcA z) (τA z) (hc z)
    exact ⟨n, y, hy⟩
  choose n y hy using hloc2
  set N := S.sup n with hN
  let y' : ∀ z, Γ(Z, cA z) := fun z => τA z ^ (N - n z) * y z
  have hy' : ∀ z ∈ S, Z.presheaf.map (homOfLE (hBA z)).op (y' z) =
      (Z.presheaf.map (homOfLE (hBA z)).op (τA z)) ^ N * hc z := by
    intro z hz
    have hnN : n z ≤ N := Finset.le_sup hz
    simp only [y', map_mul, map_pow, hy z, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnN]
  -- the restriction of `τ` to the basic opens
  have hτB : ∀ z, Z.presheaf.map (homOfLE (hBA z)).op (τA z) =
      Z.presheaf.map (homOfLE (le_top : Z.basicOpen (τA z) ≤ ⊤)).op τ := by
    intro z
    simp only [τA]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  -- the local sections
  let σl : ∀ z, bundleSections (bundleTensorPower M m) (cA z) := fun z =>
    (((b.frame (ci z)).tensorPower m).coefficients (homOfLE (hAi z))).symm (y' z)
  have hkey : ∀ z ∈ S, ((bundleTensorPower M m).val.map (homOfLE (hBA z)).op (σl z) :
      bundleSections (bundleTensorPower M m) (Z.basicOpen (τA z))) =
      (Z.presheaf.map (homOfLE (le_top : Z.basicOpen (τA z) ≤ ⊤)).op τ ^ N :
        Γ(Z, Z.basicOpen (τA z))) •
        (show bundleSections (bundleTensorPower M m) (Z.basicOpen (τA z)) from
          (bundleTensorPower M m).val.map (homOfLE (hBD z)).op x) := by
    intro z hz
    apply (((b.frame (ci z)).tensorPower m).coefficients
      (homOfLE ((hBA z).trans (hAi z)))).injective
    have h1 := ((b.frame (ci z)).tensorPower m).coefficients_restrict (homOfLE (hAi z))
      (homOfLE (hBA z)) (σl z)
    rw [show homOfLE (hBA z) ≫ homOfLE (hAi z) = homOfLE ((hBA z).trans (hAi z)) from rfl] at h1
    rw [h1, LinearEquiv.map_smul]
    simp only [σl, LinearEquiv.apply_symm_apply]
    erw [hy' z hz]
    rw [hτB z]
    rfl
  -- composition of restrictions
  have hres : ∀ {U V W : Z.Opens} (h1 : W ≤ V) (h2 : V ≤ U)
      (s : bundleSections (bundleTensorPower M m) U),
      (bundleTensorPower M m).val.map (homOfLE h1).op
          ((bundleTensorPower M m).val.map (homOfLE h2).op s) =
        (bundleTensorPower M m).val.map (homOfLE (h1.trans h2)).op s := by
    intro U V W h1 h2 s
    exact (PresheafOfModules.map_comp_apply _ (homOfLE h2).op (homOfLE h1).op s).symm
  have hresZ : ∀ {U V W : Z.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (r : Γ(Z, U)),
      Z.presheaf.map (homOfLE h1).op (Z.presheaf.map (homOfLE h2).op r) =
        Z.presheaf.map (homOfLE (h1.trans h2)).op r := by
    intro U V W h1 h2 r
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  -- the local sections are `τᴺ x` on every open inside `D(τ|_A)`
  have hkeyQ : ∀ z ∈ S, ∀ (Q : Z.Opens) (hQ : Q ≤ Z.basicOpen (τA z)),
      ((bundleTensorPower M m).val.map (homOfLE (hQ.trans (hBA z))).op (σl z) :
        bundleSections (bundleTensorPower M m) Q) =
      (Z.presheaf.map (homOfLE (le_top : Q ≤ ⊤)).op τ ^ N : Γ(Z, Q)) •
        (show bundleSections (bundleTensorPower M m) Q from
          (bundleTensorPower M m).val.map (homOfLE (hQ.trans (hBD z))).op x) := by
    intro z hz Q hQ
    rw [← hres hQ (hBA z), hkey z hz, PresheafOfModules.map_smul, hres hQ (hBD z), map_pow]
    congr 2
    exact hresZ hQ le_top τ
  -- gluing over the finite subcover
  have hcover : (⊤ : Z.Opens) ≤ iSup (fun z : S => cA z) := by
    intro p _
    have hp := hS (Set.mem_univ p)
    simp only [Set.mem_iUnion] at hp
    obtain ⟨z, hz, hpz⟩ := hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hpz⟩
  have hcompat : TopCat.Presheaf.IsCompatible (bundleTensorPower M m).val.presheaf
      (fun z : S => cA z) (fun z => σl z) := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩
    by_cases hne : ((cA z ⊓ cA z' : Z.Opens) : Set Z).Nonempty
    · obtain ⟨p, hp⟩ := nonempty_preirreducible_inter (cA z ⊓ cA z').isOpen
        (Z.basicOpen τ).isOpen hne hD
      have hQ1 : cA z ⊓ cA z' ⊓ Z.basicOpen τ ≤ Z.basicOpen (τA z) := by
        rw [hBeq]; exact inf_le_inf_right _ inf_le_left
      have hQ2 : cA z ⊓ cA z' ⊓ Z.basicOpen τ ≤ Z.basicOpen (τA z') := by
        rw [hBeq]; exact inf_le_inf_right _ inf_le_right
      apply restrict_injective_of_frame (b.frame (ci z)) m (inf_le_left.trans (hAi z))
        (inf_le_left : cA z ⊓ cA z' ⊓ Z.basicOpen τ ≤ cA z ⊓ cA z') ⟨p, hp⟩
      erw [hres, hres]
      rw [hkeyQ z hz _ hQ1, hkeyQ z' hz' _ hQ2]
    · exact sections_eq_of_empty m hne _ _
  let Sh : TopCat.Sheaf AddCommGrpCat Z :=
    ⟨(bundleTensorPower M m).val.presheaf, (bundleTensorPower M m).isSheaf⟩
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' Sh (fun z : S => cA z) ⊤
    (fun _ => homOfLE le_top) hcover (fun z => σl z) hcompat
  refine ⟨N, σ, ?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext (F := (bundleTensorPower M m).val.presheaf)
    (bundleTensorPower M m).isSheaf
  intro p hp
  have hp' := hS (Set.mem_univ p)
  simp only [Set.mem_iUnion] at hp'
  obtain ⟨z, hz, hpz⟩ := hp'
  have hpB : p ∈ Z.basicOpen (τA z) := by rw [hBeq]; exact ⟨hpz, hp⟩
  refine ⟨Z.basicOpen (τA z), hBD z, hpB, ?_⟩
  have hσz : (bundleTensorPower M m).val.map (homOfLE (le_top : cA z ≤ ⊤)).op σ = σl z :=
    hσ ⟨z, hz⟩
  erw [hres, ← hres (hBA z) le_top, hσz]
  rw [hkeyQ z hz _ le_rfl]
  erw [PresheafOfModules.map_smul]
  rw [map_pow]
  congr 2
  exact (hresZ (hBD z) le_top τ).symm

end Extension

/-! ### The invariant extension `s̄` -/

namespace TestConfiguration

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

theorem overOpen_inf_le (V V' : X.Opens) :
    overOpen T.coord V ⊓ overOpen T.coord V' ≤ overOpen T.coord (V ⊓ V') := by
  rintro y ⟨⟨u, hu, rfl⟩, ⟨u', hu', hy⟩⟩
  have : u' = u := (offCentral T.toLine).ι.isOpenEmbedding.injective hy
  subst this
  exact ⟨u', ⟨hu, hu'⟩, rfl⟩

theorem offCentral_le_iSup :
    offCentral T.toLine ≤ iSup (fun j : a.I => overOpen T.coord (a.opens j)) := by
  intro y hy
  obtain ⟨j, hj⟩ := a.covers (T.coord.base ⟨y, hy⟩)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ⟨y, hy⟩, hj, rfl⟩

/-- The local pieces of `s̄`: the sections of `𝓛^m` over `q⁻¹(V_j)` with coefficient `q^♯ s_j`
in the frame `ε_j^m`. -/
def sbarLocal {m : ℕ} (s : SectionSpace f L m) (j : a.I) :
    bundleSections (bundleTensorPower T.line m) (overOpen T.coord (a.opens j)) :=
  (((T.frame j).tensorPower m).coefficients (𝟙 _)).symm
    (pullFun T.coord (a.opens j) (atlasPowerGlobalCoefficients a m j s))

theorem sbarLocal_coeff {m : ℕ} (s : SectionSpace f L m) (j : a.I) :
    ((T.frame j).tensorPower m).coefficients (𝟙 _) (T.sbarLocal s j) =
      pullFun T.coord (a.opens j) (atlasPowerGlobalCoefficients a m j s) :=
  LinearEquiv.apply_symm_apply _ _

/-- The pulled-back coefficients obey the transition law of the frames `ε_j` on
`q⁻¹(V_j) ∩ q⁻¹(V_k)`. -/
theorem pull_transition {m : ℕ} (s : SectionSpace f L m) (j k : a.I) :
    transitionFun (T.frame j) (T.frame k)
        (homOfLE (inf_le_left : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
          overOpen T.coord (a.opens j)))
        (homOfLE (inf_le_right : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
          overOpen T.coord (a.opens k))) ^ m *
      T.space.presheaf.map (homOfLE (inf_le_left : overOpen T.coord (a.opens j) ⊓
          overOpen T.coord (a.opens k) ≤ overOpen T.coord (a.opens j))).op
        (pullFun T.coord (a.opens j) (atlasPowerGlobalCoefficients a m j s)) =
    T.space.presheaf.map (homOfLE (inf_le_right : overOpen T.coord (a.opens j) ⊓
          overOpen T.coord (a.opens k) ≤ overOpen T.coord (a.opens k))).op
        (pullFun T.coord (a.opens k) (atlasPowerGlobalCoefficients a m k s)) := by
  have hρ : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
      overOpen T.coord (a.opens j ⊓ a.opens k) := T.overOpen_inf_le _ _
  -- the transition law on `X`
  have hX := LocalBundleFrame.global_coefficients_transition (a.frame j) (a.frame k)
    (homOfLE (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j))
    (homOfLE (inf_le_right : a.opens j ⊓ a.opens k ≤ a.opens k)) m s
  change X.presheaf.map _ (atlasPowerGlobalCoefficients a m k s) =
    (transitionFun (a.frame j) (a.frame k) _ _) ^ m *
      X.presheaf.map _ (atlasPowerGlobalCoefficients a m j s) at hX
  -- pulled back by `q`
  have hX' := congrArg (pullFun T.coord (a.opens j ⊓ a.opens k)) hX
  rw [map_mul, map_pow, pullFun_restrict, pullFun_restrict, ← T.frame_transition j k] at hX'
  -- restricted to the intersection
  have hX'' := congrArg (T.space.presheaf.map (homOfLE hρ).op) hX'
  rw [map_mul, map_pow, presheaf_map_map, presheaf_map_map] at hX''
  have htrR := localBundleFrameTransition_restrict (T.frame j) (T.frame k)
    (homOfLE (overOpen_mono T.coord (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)))
    (homOfLE (overOpen_mono T.coord (inf_le_right : a.opens j ⊓ a.opens k ≤ a.opens k)))
    (homOfLE hρ)
  have htr' : T.space.presheaf.map (homOfLE hρ).op (transitionFun (T.frame j) (T.frame k)
      (homOfLE (overOpen_mono T.coord (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)))
      (homOfLE (overOpen_mono T.coord (inf_le_right : a.opens j ⊓ a.opens k ≤ a.opens k)))) =
      transitionFun (T.frame j) (T.frame k)
        (homOfLE (inf_le_left : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
          overOpen T.coord (a.opens j)))
        (homOfLE (inf_le_right : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
          overOpen T.coord (a.opens k))) :=
    htrR.symm
  rw [htr'] at hX''
  exact hX''.symm

theorem sbarLocal_compatible {m : ℕ} (s : SectionSpace f L m) :
    TopCat.Presheaf.IsCompatible (bundleTensorPower T.line m).val.presheaf
      (fun j : a.I => overOpen T.coord (a.opens j)) (T.sbarLocal s) := by
  intro j k
  have hl : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
      overOpen T.coord (a.opens j) := inf_le_left
  have hr : overOpen T.coord (a.opens j) ⊓ overOpen T.coord (a.opens k) ≤
      overOpen T.coord (a.opens k) := inf_le_right
  apply (((T.frame k).tensorPower m).coefficients (homOfLE hr)).injective
  have hR := ((T.frame k).tensorPower m).coefficients_restrict (𝟙 _) (homOfLE hr)
    (T.sbarLocal s k)
  have hL := LocalBundleFrame.tensorPower_coefficients_transition (T.frame j) (T.frame k)
    (homOfLE hl) (homOfLE hr) m
    ((bundleTensorPower T.line m).val.map (homOfLE hl).op (T.sbarLocal s j))
  have hL' := ((T.frame j).tensorPower m).coefficients_restrict (𝟙 _) (homOfLE hl)
    (T.sbarLocal s j)
  rw [T.sbarLocal_coeff] at hR hL'
  simp only [Category.comp_id] at hR hL'
  erw [hR, hL, hL']
  exact T.pull_transition s j k

theorem sbar_exists {m : ℕ} (s : SectionSpace f L m) :
    ∃! x : bundleSections (bundleTensorPower T.line m) (offCentral T.toLine), ∀ j : a.I,
      (bundleTensorPower T.line m).val.map
        (homOfLE (overOpen_le_offCentral T.coord (a.opens j))).op x = T.sbarLocal s j := by
  let Sh : TopCat.Sheaf AddCommGrpCat T.space :=
    ⟨(bundleTensorPower T.line m).val.presheaf, (bundleTensorPower T.line m).isSheaf⟩
  exact TopCat.Sheaf.existsUnique_gluing' Sh
    (fun j : a.I => overOpen T.coord (a.opens j)) (offCentral T.toLine)
    (fun j => homOfLE (overOpen_le_offCentral T.coord (a.opens j))) T.offCentral_le_iSup
    (T.sbarLocal s) (T.sbarLocal_compatible s)

/-- **The invariant extension** `s̄ = q^* s ∈ Γ(𝓧 ∖ 𝓧₀, 𝓛^m)` of `s ∈ H⁰(X, L^m)`. -/
def sbar {m : ℕ} (s : SectionSpace f L m) :
    bundleSections (bundleTensorPower T.line m) (offCentral T.toLine) :=
  Classical.choose (T.sbar_exists s).exists

theorem sbar_restrict {m : ℕ} (s : SectionSpace f L m) (j : a.I) :
    (bundleTensorPower T.line m).val.map
        (homOfLE (overOpen_le_offCentral T.coord (a.opens j))).op (T.sbar s) =
      T.sbarLocal s j :=
  Classical.choose_spec (T.sbar_exists s).exists j

/-- **Every section lies in some `𝓕^λ`**: `tᴺ s̄` extends to `𝓧` for `N ≫ 0`
(`exists_extension_pow_smul`), so `s ∈ 𝓕^{-N}`. -/
theorem exists_mem_piece [IsIntegral T.space] [Nonempty X] {m : ℕ} (s : SectionSpace f L m) :
    ∃ lam : ℤ, s ∈ T.piece lam m := by
  have : CompactSpace T.space := QuasiCompact.compactSpace_of_compactSpace T.toLine
  obtain ⟨j0, hj0⟩ := T.exists_nonempty_overOpen
  have hD : (T.space.basicOpen (tFun T.toLine) : Set T.space).Nonempty :=
    hj0.mono (overOpen_le_offCentral T.coord (a.opens j0))
  obtain ⟨N, σ, hσ⟩ := exists_extension_pow_smul T.atlas m (tFun T.toLine) hD (T.sbar s)
  refine ⟨-N, σ, fun j => ?_⟩
  simp only [neg_neg, zpow_natCast]
  change ((T.frame j).tensorPower m).coefficients (𝟙 _)
    ((bundleTensorPower T.line m).val.map (homOfLE le_top).op σ) = _
  rw [← bundle_map_map m (overOpen_le_offCentral T.coord (a.opens j)) le_top σ]
  erw [hσ, PresheafOfModules.map_smul, T.sbar_restrict]
  rw [LinearEquiv.map_smul, T.sbarLocal_coeff, map_pow]
  congr 1
  rw [Units.val_pow_eq_pow_val, tUnit_val]
  congr 1
  exact presheaf_map_map _ _ _

/-- **`𝓕` is exhaustive**: for an integral test configuration of `(X, L)` with `X ≠ ∅` and
`H⁰(X, L^m)` finite dimensional, `𝓕^μ H⁰(X, L^m) = H⁰(X, L^m)` for some `μ`. -/
theorem exists_piece_eq_top [IsIntegral T.space] [Nonempty X] (m : ℕ)
    [FiniteDimensional ℂ (SectionSpace f L m)] : ∃ μ : ℤ, T.piece μ m = ⊤ := by
  let B := Module.finBasis ℂ (SectionSpace f L m)
  choose lam hlam using fun i => T.exists_mem_piece (B i)
  refine ⟨-∑ i, |lam i|, eq_top_iff.mpr ?_⟩
  rw [← B.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine T.piece_anti ?_ m (hlam i)
  have h1 : |lam i| ≤ ∑ k, |lam k| :=
    Finset.single_le_sum (f := fun k => |lam k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 := neg_abs_le (lam i)
  linarith

end TestConfiguration

end SGPT.TestCurve.TCEnc
