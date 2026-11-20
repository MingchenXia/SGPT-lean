import SGPT.Unibranch.FNHTheorem
import SGPT.Unibranch.FNSAdapter

/-!
# The Runge half of `[FN80, Thm. 5.3.1]` for every analytic set

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Theorem 5.3.1, first half (`[FN80]`); SGPT `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`).

`FNH.hartogsRunge_of_charts` needs branched-covering charts, i.e. pure dimension. `[FN80]` treat the
pure-dimensional pieces `S_j` separately; here we use the **suspension** instead: for `X`
closed analytic in a polydisc of `ℂⁿ`, `X̃ = ⋃ₖ X⁽ᵏ⁾ × (ℂ^{n-k} × 0) ∩ Δ'` is closed analytic and
pure `n`-dimensional in a polydisc `Δ'` of `ℂ^{n+n}`, `blk1 : X̃ → X`, and `x ↦ (x, 0)` maps `X`
into `X̃`. The Hartogs domain over `X̃` for `φ ∘ blk1` is Runge, and the linear map
`(w, z) ↦ (w, (z, 0))` transports the Runge property back to `X` (linear maps send hulls into
hulls).

* `hartogsRunge_of_hasLocalEquationsOn`: `FNS.HartogsRunge X φ` for every closed analytic `X` in
  a polydisc and `φ ∈ WP(X)`, given the local parametrization theorem;
* `hartogsRungeOfEquations_of_charts : FNL.LocalCoveringCharts → FNS.HartogsRungeOfEquations`
  (the interface; `FNS.localFNExtension_of_hartogsRunge` then gives `FNA.LocalFNExtension`
  without the suspension at the level of extensions).
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron
open SGPT.Unibranch.FNR SGPT.Unibranch.FNL
open SGPT.Unibranch.FNS (zpart mkPt zpart_apply mkPt_zero mkPt_succ zpart_mkPt mkPt_zpart
  hartogsDomain HartogsRunge)
open AnalyticDimensionBasics RegularPointDimension

variable {n : ℕ}

/-- `(w, z) ↦ (w, (z, 0))`, from `ℂ × ℂⁿ` to `ℂ × ℂ^{n+n}`. -/
def suspendW : ComplexModel (n + 1) →L[ℂ] ComplexModel (n + n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => mkPt (FNA.inl (zpart x)) (x 0)
      map_add' := fun x y => ext_zpart (by simp) (by simp [zpart_add])
      map_smul' := fun c x => ext_zpart (by simp) (by simp [zpart_smul]) }

@[simp] theorem suspendW_zero (x : ComplexModel (n + 1)) : suspendW x 0 = x 0 := by
  simp [suspendW]

@[simp] theorem zpart_suspendW (x : ComplexModel (n + 1)) :
    zpart (suspendW x) = FNA.inl (zpart x) := by
  simp [suspendW]

/-- **`[FN80, Thm. 5.3.1]`, first half, for every analytic set.** Let `X` be a closed analytic
subset of an open polydisc `Δ(a, r) ⊆ ℂⁿ` and `φ ∈ WP(X)`. Given the local parametrization
theorem, the Hartogs domain `{(w, z) : z ∈ X, φ(z) + log |w| < 0}` is Runge in `X × ℂ`. -/
theorem hartogsRunge_of_hasLocalEquationsOn (hC : FNL.LocalCoveringCharts) {X : Set (ComplexModel n)}
    {a : ComplexModel n} {r : Fin n → ℝ} (hXΔ : X ⊆ FNA.polydisc a r)
    (hloc : HasLocalEquationsOn X (FNA.polydisc a r)) {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) : HartogsRunge X φ := by
  -- the suspension of `X` (as in `FNA.extension_of_pure`)
  let Ω : Opens (ComplexModel n) := ⟨FNA.polydisc a r, FNA.isOpen_polydisc a r⟩
  have hCan : IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) :=
    FNA.isComplexAnalyticSubset_of_hasLocalEquationsOn (Ω := Ω) hloc
  have himage : Subtype.val '' ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) = X := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro hy
      exact ⟨⟨y, hXΔ hy⟩, hy, rfl⟩
  set S := FNA.dimPieces ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) with hSdef
  have hU : (⋃ k, S k) = X := (FNA.iUnion_dimPieces hCan).trans himage
  set r' : Fin (n + n) → ℝ := Fin.append r (fun _ => 1) with hr'def
  set a' : ComplexModel (n + n) := FNA.inl a with ha'def
  set Δ' := FNA.polydisc a' r' with hΔ'def
  have hmemΔ' : ∀ w, w ∈ Δ' ↔ FNA.blk1 w ∈ FNA.polydisc a r ∧ ∀ i : Fin n, ‖FNA.blk2 w i‖ < 1 := by
    intro w
    simp only [hΔ'def, FNA.polydisc, mem_ofPred_eq, ha'def, FNA.blk1_apply, FNA.blk2_apply]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa [hr'def, -Fin.natAdd_eq_addNat] using h (Fin.castAdd n i)
      · simpa [hr'def, -Fin.natAdd_eq_addNat] using h (Fin.natAdd n i)
    · rintro ⟨h1, h2⟩ j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [hr'def, -Fin.natAdd_eq_addNat] using h1 i
      · simpa [hr'def, -Fin.natAdd_eq_addNat] using h2 i
  have hΔ'Ω : Δ' ⊆ FNA.blk1 ⁻¹' (Ω : Set (ComplexModel n)) := fun w hw =>
    ((hmemΔ' w).mp hw).1
  set X' := FNA.suspension S ∩ Δ' with hX'def
  have hX'eq : HasLocalEquationsOn X' Δ' :=
    FNA.hasLocalEquationsOn_inter_sets ((FNA.hasLocalEquationsOn_suspension hCan).mono hΔ'Ω)
      (fun x hx => ⟨Δ', FNA.isOpen_polydisc a' r', hx, 0, Fin.elim0, fun i => i.elim0,
        fun y hy => by simp [hy]⟩)
  have hX'pure : IsPureDim (n := n + n) (M := ComplexModel (n + n)) X' n := by
    intro p j hp
    have hpΔ : p ∈ Δ' := hp.2.1.2
    have hp' : RegularAtDim (n := n + n) (FNA.suspension S) p j := by
      refine regularAtDim_of_inter_eq (FNA.isOpen_polydisc a' r') hpΔ ?_ hp
      ext w
      simp only [hX'def, mem_inter_iff]
      tauto
    exact FNA.isPureDim_suspension S (fun k y hy U hUy => FNA.dimPieces_hS hCan k y hy U hUy) p j hp'
  have hmapX' : MapsTo FNA.blk1 X' X := by
    intro w hw
    rw [← hU]
    exact FNA.blk1_mem_of_mem_suspension hw.1
  have hinl : ∀ x ∈ X, FNA.inl x ∈ X' := by
    intro x hx
    refine ⟨FNA.inl_mem_suspension (by rwa [hU]), (hmemΔ' _).mpr ⟨by rw [FNA.blk1_inl]; exact hXΔ hx,
      fun i => ?_⟩⟩
    simp
  -- the Runge property over the suspension
  have hcharts : ∀ z ∈ X', HasCoveringChartAt X' z univ := fun z hz =>
    hC (n + n) n X' Δ' z (FNA.isOpen_polydisc a' r') hz hz.2 hX'eq
      (isPureDim_inter_open (FNA.isOpen_polydisc a' r') hX'pure) univ isOpen_univ (mem_univ z)
  have hR' : HartogsRunge X' (fun w => φ (FNA.blk1 w)) :=
    hartogsRunge_of_charts (a := a') (r := r') inter_subset_right hX'eq hcharts
      (FNA.isWeaklyPSHOn_comp hφ FNA.blk1 hmapX')
  -- transport back to `X`
  intro K hK hKΩ x ⟨hxK, hxX⟩
  have hΦK : (suspendW : ComplexModel (n + 1) →L[ℂ] ComplexModel (n + n + 1)) '' K ⊆
      hartogsDomain X' (fun w => φ (FNA.blk1 w)) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyX, c, h1, h2⟩ := hKΩ hy
    refine ⟨?_, c, ?_, ?_⟩
    · rw [zpart_suspendW]; exact hinl _ hyX
    · simp only [zpart_suspendW, FNA.blk1_inl]; exact h1
    · rw [suspendW_zero]; exact h2
  have hxX' : zpart (suspendW x) ∈ X' := by
    rw [zpart_suspendW]; exact hinl _ hxX
  obtain ⟨-, c, h1, h2⟩ := hR' _ (hK.image suspendW.continuous) hΦK
    ⟨image_polyHull_subset_clm suspendW K ⟨x, hxK, rfl⟩, hxX'⟩
  simp only [zpart_suspendW, FNA.blk1_inl] at h1
  rw [suspendW_zero] at h2
  exact ⟨hxX, c, h1, h2⟩

/-- **the interface `HartogsRungeOfEquations`** (the Runge half of `[FN80, Thm. 5.3.1]` for
global equations), given the local parametrization theorem; no shrinking is needed (`r' = r`). -/
theorem hartogsRungeOfEquations_of_charts (hC : FNL.LocalCoveringCharts) :
    FNS.HartogsRungeOfEquations := by
  intro n a r V m h φ hr hV hrV hh _ hφ
  refine ⟨r, hr, fun _ => le_rfl, ?_⟩
  have hsub : FNA.polydisc a r ⊆ V := (FNA.polydisc_subset_closedPolydisc a r).trans hrV
  refine hartogsRunge_of_hasLocalEquationsOn hC (fun z hz => hz.1) ?_ hφ
  intro z hz
  refine ⟨FNA.polydisc a r, FNA.isOpen_polydisc a r, hz, m, h, fun l => (hh l).mono hsub,
    fun y hy => ?_⟩
  exact ⟨fun hy' => hy'.2, fun hy' => ⟨hy, hy'⟩⟩

/-- The route through the adapter: `FNS.localFNExtension_of_hartogsRunge`. -/
theorem localFNExtension_of_charts' (hC : FNL.LocalCoveringCharts) : FNA.LocalFNExtension :=
  FNS.localFNExtension_of_hartogsRunge (hartogsRungeOfEquations_of_charts hC)

end SGPT.Unibranch.FNH
