import SGPT.Unibranch.FNPUnion
import SGPT.Foundations.Analysis.Pending.LocalStatementAssembly

/-!
# FN80 §5.3: local branched-covering charts of pure-dimensional analytic sets

Source: `[FN80]` Theorem 5.3.1, proof: "In a small neighborhood of `p`, we can represent
`S_j × ℂ` as a branched covering of `Δ^{j+1}` relative to suitable coordinates in `ℂ^{n+1}`
(as in Lemma 5.2)" — the local parametrization theorem for pure-dimensional analytic sets
(Grauert–Remmert; Gunning–Rossi III.B; Demailly, *Complex analytic and differential
geometry*, II.4.19 and III.2.6 for a common direction for all local components).

`localCoveringCharts` proves `SGPT.Unibranch.FNL.LocalCoveringCharts` (the statement fixed by
lane FNL in `FNLChart`): a set `Y ⊆ ℂᴺ` with local holomorphic equations on an open set `Ω`,
of pure dimension `d` there, has at every point `p ∈ Y ∩ Ω` and inside every neighbourhood
`O` of `p` a branched-covering chart (`FNL.HasCoveringChartAt Y p O`).

Proof.
1. The germ `B = Y - p` at `0` is analytic; it is a finite irredundant union of irreducible
   germs `A_i` (`exists_irreducible_decomposition_euclidean`).
2. Each `A_i` carries parametrization data of dimension `d` (`dim_eq_of_isPureDim`: a regular
   point of `A_i` away from the other components is a regular point of `Y ∩ Ω`).
3. One linear change of coordinates `L` puts all `A_i` in Noether position over the same `ℂᵈ`
   (`IrreducibleGermSheetBound.exists_parametrizationData_near`).
4. `FNP.exists_isBranchedCovering_iUnion` makes `L⁻¹B` a branched covering on a small
   polydisc; it is translated to `L⁻¹p` (`IsBranchedCovering.translate`) and restricted to a
   polydisc centred at `L⁻¹p` inside `L⁻¹O` (`FNL.IsBranchedCovering.exists_restrict_pdisc`);
   the local equations of `Y` are transported by `L`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNP

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
open SGPT.Unibranch.FNL

variable {n k : ℕ}

/-! ### Translating a branched covering -/

theorem fibre_translate (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (v : ComplexModel n) (z : ComplexModel k) :
    FNL.fibre {u | u - v ∈ X} π z = (fun x => x + v) '' FNL.fibre X π (z - π v) := by
  ext u
  constructor
  · rintro ⟨hu, huz⟩
    refine ⟨u - v, ⟨hu, ?_⟩, by simp⟩
    have huz' : π u = z := huz
    show π (u - v) = z - π v
    rw [map_sub, huz']
  · rintro ⟨x, ⟨hx, hxz⟩, rfl⟩
    have hxz' : π x = z - π v := hxz
    refine ⟨by simpa using hx, ?_⟩
    show π (x + v) = z
    rw [map_add, hxz', sub_add_cancel]

/-- A branched covering translated by `v` is a branched covering of the translated base. -/
theorem IsBranchedCovering.translate {X : Set (ComplexModel n)}
    {π : ComplexModel n →L[ℂ] ComplexModel k} {D : Set (ComplexModel k)} {deg : ℕ}
    {δ : ComplexModel k → ℂ} (hX : IsBranchedCovering X π D deg δ) (v : ComplexModel n) :
    IsBranchedCovering {u | u - v ∈ X} π {z | z - π v ∈ D} deg (fun z => δ (z - π v)) where
  isOpen_base := hX.isOpen_base.preimage (continuous_id.sub continuous_const)
  mapsTo := fun u hu => by
    show π u - π v ∈ D
    rw [← map_sub]
    exact hX.mapsTo hu
  isCompact_inter_preimage := fun K hKD hK => by
    have hK' : IsCompact ((fun z => z - π v) '' K) :=
      hK.image (continuous_id.sub continuous_const)
    have hsub : (fun z => z - π v) '' K ⊆ D := by
      rintro _ ⟨z, hz, rfl⟩
      exact hKD hz
    have hc := (hX.isCompact_inter_preimage _ hsub hK').image
      (continuous_id.add continuous_const : Continuous fun x : ComplexModel n => x + v)
    convert hc using 1
    ext u
    constructor
    · rintro ⟨hu, huK⟩
      refine ⟨u - v, ⟨hu, π u, huK, ?_⟩, by simp⟩
      simp [map_sub]
    · rintro ⟨x, ⟨hx, z, hz, hzx⟩, rfl⟩
      refine ⟨by simpa using hx, ?_⟩
      have hzx' : z - π v = π x := hzx
      show π (x + v) ∈ K
      rw [map_add, ← hzx', sub_add_cancel]
      exact hz
  finite_fibre := fun z hz => by
    rw [fibre_translate]
    exact (hX.finite_fibre _ hz).image _
  differentiableOn_disc := hX.differentiableOn_disc.comp
    (differentiableOn_id.sub_const _) fun _ hz => hz
  frequently_disc_ne := fun z hz => by
    have h := hX.frequently_disc_ne _ hz
    have hm : map (fun w => w - π v) (𝓝 z) = 𝓝 (z - π v) :=
      (Homeomorph.subRight (π v)).map_nhds_eq z
    rw [← hm] at h
    exact Filter.frequently_map.mp h
  ncard_fibre := fun z hz hδz => by
    rw [fibre_translate, Set.ncard_image_of_injective _ (add_left_injective v)]
    exact hX.ncard_fibre _ hz hδz
  local_graph := fun x hx hδx => by
    have hδx' : δ (π (x - v)) ≠ 0 := by rwa [map_sub]
    obtain ⟨U, V, g, hUo, hVo, hxU, hxV, hUD, hg, hgX, hVX⟩ := hX.local_graph (x - v) hx hδx'
    refine ⟨{w | w - π v ∈ U}, {u | u - v ∈ V}, fun w => g (w - π v) + v,
      hUo.preimage (continuous_id.sub continuous_const),
      hVo.preimage (continuous_id.sub continuous_const), ?_, hxV, fun w hw => hUD hw,
      ((hg.comp (differentiableOn_id.sub_const _) fun _ hw => hw).add_const v),
      fun w hw => ?_, fun y hy => ?_⟩
    · show π x - π v ∈ U
      rw [← map_sub]
      exact hxU
    · obtain ⟨h1, h2⟩ := hgX _ hw
      refine ⟨by simpa using h1, ?_⟩
      rw [map_add, h2, sub_add_cancel]
    · obtain ⟨h1, h2⟩ := hVX (y - v) ⟨hy.1, hy.2⟩
      rw [map_sub] at h1 h2
      exact ⟨h1, by simp only [h2, sub_add_cancel]⟩
  subset_closure_generic := fun u hu => by
    rw [_root_.mem_closure_iff]
    intro o ho huo
    obtain ⟨x, hxo, hxX, hxδ⟩ := _root_.mem_closure_iff.1 (hX.subset_closure_generic hu)
      {y | y + v ∈ o} (ho.preimage (continuous_id.add continuous_const)) (by simpa using huo)
    refine ⟨x + v, hxo, by simpa using hxX, ?_⟩
    show δ (π (x + v) - π v) ≠ 0
    rw [map_add, add_sub_cancel_right]
    exact hxδ

/-! ### The dimension of the local components -/

/-- **The local irreducible components of a pure `d`-dimensional set carry parametrization data
of dimension `d`.**  (Pure-dimensional form of TN
`GermComponentDimension.dim_eq_of_parametrizationData`.) -/
theorem dim_eq_of_isPureDim {N d : ℕ} {Y Ω : Set (ComplexModel N)} (hΩ : IsOpen Ω)
    {p : ComplexModel N} (hpΩ : p ∈ Ω)
    (hpure : AnalyticDimensionBasics.IsPureDim (n := N) (M := ComplexModel N) (Y ∩ Ω) d)
    {r : ℕ} {A : Fin r → Set (ComplexModel N)} (hA : ∀ i, IsIrreducibleGerm (A i))
    (hcover : {w | w + p ∈ Y} =ᶠ[𝓝 0] (⋃ i, A i))
    (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j))
    (i : Fin r) {L : ComplexModel N ≃L[ℂ] ComplexModel N}
    (P : ParametrizationData (L ⁻¹' A i)) (S : SetsData P) :
    P.dim = d := by
  obtain ⟨Ωp, hΩpo, hΩp0, hΩp⟩ :=
    GermComponentDimension.exists_pure_nhds_dim (hA i) fun ε hε =>
      GermComponentDimension.exists_regularAtDim_near_zero L S hε
  have hT : Tendsto (fun w : ComplexModel N => w + p) (𝓝 0) (𝓝 p) :=
    (continuous_add_const p).tendsto' 0 p (zero_add p)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.1
    ((Filter.eventuallyEq_set.mp hcover).and (hT.eventually (hΩ.mem_nhds hpΩ)))
  obtain ⟨O', hO'o, hO'sub, hne, hdisj⟩ :=
    GermComponentDimension.exists_isOpen_disjoint_others hA hpw i (isOpen_ball.inter hΩpo)
      ⟨mem_ball_self hρ, hΩp0⟩
  obtain ⟨z, hzO', hzA⟩ := hne
  obtain ⟨y, hyO', hyreg⟩ :=
    _root_.mem_closure_iff.mp ((hΩp O' hO'o (hO'sub.trans inter_subset_right)).2 ⟨hzA, hzO'⟩)
      O' hO'o hzO'
  have hB : {w | w + p ∈ Y} ∩ O' = A i ∩ O' := by
    ext w
    constructor
    · rintro ⟨hw, hwO⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (((hρs w (hO'sub hwO).1).1).mp hw)
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hwO⟩
      · have : w ∈ O' ∩ A j := ⟨hwO, hj⟩
        rw [hdisj j hji] at this
        exact absurd this (notMem_empty w)
    · rintro ⟨hw, hwO⟩
      exact ⟨((hρs w (hO'sub hwO).1).1).mpr (mem_iUnion.2 ⟨i, hw⟩), hwO⟩
  have hyB : RegularAtDim (n := N) (M := ComplexModel N) {w | w + p ∈ Y} y P.dim :=
    RegularPointDimension.regularAtDim_of_inter_eq hO'o hyO'
      (by rw [hB, inter_assoc, inter_self]) hyreg
  have hset : {w : ComplexModel N | w + p ∈ Y} = {z | z - (-p) ∈ Y} := by
    ext w
    simp [sub_neg_eq_add]
  rw [hset, AnalyticLocalStatement.regularAtDim_translate_iff] at hyB
  have hyΩ : y - -p ∈ Ω := by
    rw [sub_neg_eq_add]
    exact (hρs y (hO'sub hyO').1).2
  have hyYΩ : RegularAtDim (n := N) (M := ComplexModel N) (Y ∩ Ω) (y - -p) P.dim :=
    RegularPointDimension.regularAtDim_of_inter_eq hΩ hyΩ (by rw [inter_assoc, inter_self]) hyB
  exact hpure _ _ hyYΩ

/-! ### The local parametrization theorem -/

/-- **The local parametrization theorem** (`[FN80]` §5.3; Grauert–Remmert): a set with local
holomorphic equations on an open set `Ω ⊆ ℂᴺ`, of pure dimension `d` there, has a
branched-covering chart at every point of `Y ∩ Ω`, inside every neighbourhood. -/
theorem localCoveringCharts : LocalCoveringCharts := by
  unfold LocalCoveringCharts
  intro N d Y Ω p hΩ hpY hpΩ hYeq hpure O hO hpO
  classical
  -- the germ of `Y` at `p`, moved to `0`
  set B : Set (ComplexModel N) := {w | w + p ∈ Y} with hBdef
  have hT : Tendsto (fun w : ComplexModel N => w + p) (𝓝 0) (𝓝 p) :=
    (continuous_add_const p).tendsto' 0 p (zero_add p)
  have hBg : IsAnalyticGerm B := by
    obtain ⟨W, hWo, hpW, m, g, hg, hgW⟩ := hYeq p hpΩ
    have hW : ∀ᶠ w in 𝓝 (0 : ComplexModel N), w + p ∈ W := hT.eventually (hWo.mem_nhds hpW)
    refine ⟨m, fun j w => g j (w + p), fun j => ?_, ?_⟩
    · exact hW.mono fun w hw =>
        ((hg j).differentiableAt (hWo.mem_nhds hw)).comp w (differentiableAt_id.add_const p)
    · exact hW.mono fun w hw => hgW (w + p) hw
  obtain ⟨r, A, hAirr, -, hBA, hpw⟩ := exists_irreducible_decomposition_euclidean hBg
  -- every component carries parametrization data of dimension `d`
  have hP₀ : ∀ i, ∃ (L : ComplexModel N ≃L[ℂ] ComplexModel N)
      (P : ParametrizationData (L ⁻¹' A i)), P.dim = d := by
    intro i
    obtain ⟨L, ⟨P⟩⟩ := IrreducibleGermSheetBound.exists_noetherParametrizationData (hAirr i)
    exact ⟨L, P, dim_eq_of_isPureDim hΩ hpΩ hpure hAirr hBA hpw i P
      (nonempty_setsData P).some⟩
  choose L₀ P₀ hP₀d using hP₀
  have h0B : (0 : ComplexModel N) ∈ ⋃ i, A i :=
    (hBA.mem_iff.self_of_nhds).1 (by simpa [hBdef] using hpY)
  obtain ⟨i₀, -⟩ := mem_iUnion.1 h0B
  have hdN : d ≤ N := hP₀d i₀ ▸ (P₀ i₀).dim_le
  -- one direction for all components
  obtain ⟨L, P, hPd, -⟩ :=
    IrreducibleGermSheetBound.exists_parametrizationData_near hAirr P₀ hP₀d hdN 0 one_pos
  have hgL : ∀ i, IsAnalyticGerm (L ⁻¹' A i) := fun i =>
    GermParametrization.isAnalyticGerm_preimage L (hAirr i).1
  have hirrL : ∀ i, IsIrreducibleGerm (L ⁻¹' A i) := fun i => by
    refine (isIrreducibleGerm_iff_isPrime (hgL i)).2 ?_
    rw [← GermParametrization.map_vanishingIdeal_comapEquiv]
    have : (vanishingIdeal (A i)).IsPrime :=
      (isIrreducibleGerm_iff_isPrime (hAirr i).1).1 (hAirr i)
    exact Ideal.map_isPrime_of_equiv _
  have hcov : ∀ i, CoverData (L ⁻¹' A i) d := fun i =>
    coverData_of_parametrizationData (hirrL i) (P i) (nonempty_setsData (P i)).some (hPd i)
  have hpwL : Pairwise fun i j => ¬ (L ⁻¹' A i ≤ᶠ[𝓝 0] L ⁻¹' A j) := by
    intro i j hij hle
    apply hpw hij
    have h := (GermParametrization.tendsto_linearEquiv_nhds_zero L.symm).eventually hle
    refine h.mono fun z hz hzA => ?_
    have hz' : L.symm z ∈ L ⁻¹' A i → L.symm z ∈ L ⁻¹' A j := hz
    have hzA' : z ∈ A i := hzA
    have hzB : L.symm z ∈ L ⁻¹' A j := hz' (by simpa using hzA')
    show z ∈ A j
    simpa using hzB
  -- a ball on which `B` is the union of the components and `B + p ⊆ O ∩ Ω`
  have hT' : ∀ᶠ w in 𝓝 (0 : ComplexModel N), w + p ∈ O ∩ Ω :=
    hT.eventually ((hO.inter hΩ).mem_nhds ⟨hpO, hpΩ⟩)
  obtain ⟨ρB, hρB, hρBs⟩ := Metric.eventually_nhds_iff_ball.1
    ((Filter.eventuallyEq_set.mp hBA).and hT')
  have hN₀ : (L : ComplexModel N → ComplexModel N) ⁻¹' ball 0 ρB ∈ 𝓝 (0 : ComplexModel N) := by
    have hL : Tendsto L (𝓝 0) (𝓝 0) := GermParametrization.tendsto_linearEquiv_nhds_zero L
    exact hL (ball_mem_nhds 0 hρB)
  obtain ⟨η, s, hη, hs, hΔN, deg, δ, hX₀⟩ :=
    exists_isBranchedCovering_iUnion hcov hgL hpwL hN₀
  set Δ := polydisc N d η s with hΔdef
  set q : ComplexModel N := L.symm p with hqdef
  have hLq : L q = p := by simp [hqdef]
  -- translate to `q`
  have hX₁ := IsBranchedCovering.translate hX₀ q
  have hqX₁ : q ∈ {u | u - q ∈ (⋃ i, L ⁻¹' A i) ∩ Δ} := by
    show q - q ∈ (⋃ i, L ⁻¹' A i) ∩ Δ
    rw [sub_self]
    refine ⟨?_, GermParametrizationData.zero_mem_polydisc hη hs⟩
    simpa using h0B
  have hO₁ : IsOpen {u : ComplexModel N | u - q ∈ Δ} :=
    (isOpen_polydisc _ _ _ _).preimage (continuous_id.sub continuous_const)
  have hO₁sub : ∀ u ∈ {u : ComplexModel N | u - q ∈ Δ},
      L u ∈ O ∩ Ω ∧ (L (u - q) ∈ B ↔ L (u - q) ∈ ⋃ i, A i) := by
    intro u hu
    have h := hρBs (L (u - q)) (hΔN hu)
    have hLu : L (u - q) + p = L u := by rw [map_sub, hLq, sub_add_cancel]
    rw [hLu] at h
    exact ⟨h.2, h.1⟩
  have hqO₁ : q ∈ {u : ComplexModel N | u - q ∈ Δ} := by
    show q - q ∈ Δ
    rw [sub_self]
    exact GermParametrizationData.zero_mem_polydisc hη hs
  obtain ⟨ρ, hρ, hρO, D', hD', hX₂⟩ :=
    FNL.IsBranchedCovering.exists_restrict_pdisc hX₁ hdN hqX₁ hO₁ hqO₁
  have himage : (L.symm : ComplexModel N → ComplexModel N) '' Y = L ⁻¹' Y :=
    L.image_symm_eq_preimage Y
  have hset : {u | u - q ∈ (⋃ i, L ⁻¹' A i) ∩ Δ} ∩ pdisc q ρ = L.symm '' Y ∩ pdisc q ρ := by
    rw [himage]
    ext u
    constructor
    · rintro ⟨⟨hu, -⟩, hup⟩
      refine ⟨?_, hup⟩
      have h := hO₁sub u (hρO hup)
      have hLu : L (u - q) + p = L u := by rw [map_sub, hLq, sub_add_cancel]
      have : L (u - q) ∈ B := h.2.2 (by simpa using hu)
      show L u ∈ Y
      rw [← hLu]
      exact this
    · rintro ⟨hu, hup⟩
      refine ⟨⟨?_, hρO hup⟩, hup⟩
      have h := hO₁sub u (hρO hup)
      have hLu : L (u - q) + p = L u := by rw [map_sub, hLq, sub_add_cancel]
      have hB : L (u - q) ∈ B := by
        show L (u - q) + p ∈ Y
        rw [hLu]
        exact hu
      simpa using h.2.1 hB
  rw [hset] at hX₂
  unfold HasCoveringChartAt
  refine ⟨L.symm, d, hdN, ρ, D', _, _, hρ, ?_, hD', hX₂, ?_⟩
  · intro u hu
    rw [L.image_symm_eq_preimage O]
    exact (hO₁sub u (hρO hu)).1.1
  · -- local equations, transported by `L`
    intro x hx
    obtain ⟨W, hWo, hxW, m, g, hg, hgW⟩ := hYeq (L x) (hO₁sub x (hρO hx)).1.2
    refine ⟨(L : ComplexModel N → ComplexModel N) ⁻¹' W ∩ pdisc q ρ,
      (hWo.preimage L.continuous).inter (isOpen_pdisc _ _), ⟨hxW, hx⟩, m,
      fun j y => g j (L y), fun j => ?_, fun y hy => ?_⟩
    · exact (hg j).comp L.differentiable.differentiableOn fun y hy => hy.1
    · rw [himage]
      exact ⟨fun h => (hgW (L y) hy.1).1 h.1, fun h => ⟨(hgW (L y) hy.1).2 h, hy.2⟩⟩

end SGPT.Unibranch.FNP
