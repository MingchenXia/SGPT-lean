import SGPT.Unibranch.PD2Components
import SGPT.Unibranch.PDThetaLimsup
import SGPT.Unibranch.PDThetaForms
import SGPT.Unibranch.PDFNReduction
import SGPT.Unibranch.ComplexSpaceThetaFiberDomain
import SGPT.Unibranch.ComplexSpaceProperDiscCriterion
import SGPT.Unibranch.ComplexSpaceUnibranchPSHDensity

/-!
# `cor:PSH` for general `θ`: the pull-back `PSH(X, θ) → PSH(Y, π^*θ)` is bijective

Source `cor:PSH` (Appendix B): let `π : Y → X` be a proper bimeromorphic morphism, `X` unibranch,
and `θ` a smooth closed real `(1,1)`-form on `X` (`PD.IsLocallyClosedOneOne θ`). Then
`π^* : PSH(X, θ) → PSH(Y, π^*θ)` is a bijection (`PD.corPSH_bijective`). Compactness and the
Kähler condition of the book's statement are not needed.

Injectivity, the forward map and the reduction of surjectivity to the descent are lane PD's
(`PD.thetaPSHPullback`, `PD.thetaPSHPullback_bijective_iff`). Here we prove the descent: for
`u ∈ PSH(Y, π^*θ)` with upper semicontinuous descent `v` (`v ∘ π = u`, which exists since the
fibres of `π` are connected), `v ∈ PSH(X, θ)` (`isThetaPSH_of_descent`). Following the book
("after subtracting a local potential of `θ` we may assume `θ = 0`"): at `x ∈ X` take a local
embedding `e` with a local potential `g` of `θ` (`IsLocallyClosedOneOne.exists_local_potential`)
and show that `w = g + v ∘ e` is psh on the local model `V_e` by `thm:FN` (`FNH.isPSH_of_disc`):

* **Gauge lemma** (`IsThetaPSH.plurisubharmonicOn_gauge_add`). Along a holomorphic domain probe
  `Λ : D → Y` whose composite with `π` has a holomorphic lift `G` into `e`, the function
  `g ∘ G + u ∘ Λ` is psh: near each point, a local potential `g_Y` of `π^*θ` with `g_Y + u` psh
  (the definition of `PSH(Y, π^*θ)`) and a holomorphic lift `G_Y` of `Λ` give
  `ddᶜ(g ∘ G) = G^*θ = Λ^*π^*θ = ddᶜ(g_Y ∘ G_Y)` (pull-back of forms to domains,
  `SpaceForm.pullbackToDomain`, and `HolomorphicDDC.smoothDDC_comp`), so `g ∘ G - g_Y ∘ G_Y` is
  pluriharmonic and `g ∘ G + u ∘ Λ = (g_Y ∘ G_Y + u ∘ Λ) + (g ∘ G - g_Y ∘ G_Y)`.
* **Discs** (`discPullback_gauge_pshAt_zero`): for a disc `f : Δ → V_e`, after a finite ramified
  cover the germ of `f` lifts to `Y` (`exists_ramified_disk_lift`: `f(t^k) = π(λ(t))`), so
  `t ↦ w(f(t^k)) = g(f(t^k)) + u(λ(t))` is subharmonic by the gauge lemma, and subharmonicity
  descends along `t ↦ t^k` (`RamifiedPower.discPshOn_of_comp_pow`); all centres by recentring.
  With `thm:FN` (2) ⇒ (1) this gives condition 2 of `def:unibranch:L105` for `w`.
* **Component clause** (`isPSH_gauge`): the set `S` of points near which `v ≡ -∞` is clopen in `X`
  (pole propagation on the unibranch models `V_e`); a component of `V_e` is an open connected
  component, so if `w ≡ -∞` on one then `S ≠ ∅`, and `u ≡ -∞` on the nonempty clopen `π⁻¹(S)`,
  which is impossible for a `π^*θ`-psh function (`PD2.IsThetaPSH.exists_ne_bot_of_isClopen`).

Lane PD2, blueprint `pd2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces

namespace SGPT.Unibranch.PD2

open SourceReducedComplexSpace

noncomputable section

private theorem modelPullback_at' {Z : SourceReducedComplexSpace} {m : ℕ}
    {U : Opens (ComplexModel m)} (F : domainSpace U ⟶ Z) (φ : Z.obj.left → EReal)
    (c : (univ : Set U)) : modelPullback F.hom.left φ c.val.val = φ (F.hom.left.base c) := by
  dsimp only [modelPullback]
  split_ifs with hc
  · rfl
  · exact False.elim (hc c.val.property)

private theorem discPullback_apply_of_mem {Z : SourceReducedComplexSpace} (f : unitDisc ⟶ Z)
    (φ : Z.obj.left → EReal) {t : ℂ} (ht : discCoordinate t ∈ unitDiscOpens) :
    discPullback f φ t = φ (f.hom.left.base ⟨⟨discCoordinate t, ht⟩, trivial⟩) := by
  unfold discPullback modelPullback
  rw [dif_pos ht]
  rfl

private theorem smoothDDC_sub' {n : ℕ} {h f : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) (hf : ContDiffOn ℝ ∞ f U)
    {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => h y - f y) z = smoothDDC h z - smoothDDC f z := by
  simp only [sub_eq_add_neg]
  rw [smoothDDC_add hU hh hf.neg hz, smoothDDC_neg hU hf hz]

/-! ### The gauge lemma -/

/-- **Gauge lemma.** Let `u ∈ PSH(Y, π^*θ)`, `e` a local embedding of `X` carrying a smooth local
potential `g` of `θ` (`θ = (ddᶜ g)|_V`), and `Λ : U → Y` a holomorphic map from a domain whose
composite `π ∘ Λ` lands in the image of `e`, with ambient coordinates `G` (`e(G(z)) = π(Λ(z))`).
Then `z ↦ g(G(z)) + u(Λ(z))` is plurisubharmonic on `U`. -/
theorem IsThetaPSH.plurisubharmonicOn_gauge_add {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (π : Y ⟶ X) {u : Y.obj.left → EReal}
    (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u)
    {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ} (hg : ContDiffOn ℝ ∞ g e.ambient)
    (hres : θ.RestrictsTo e (smoothDDC g))
    {m : ℕ} {U : Opens (ComplexModel m)} (Λ : domainSpace U ⟶ Y)
    (G : ComplexModel m → ComplexModel e.dim)
    (hG : ∀ c : (univ : Set U), ∃ b : e.carrier, b.val.val = G c.val.val ∧
      e.toPoint b = π.hom.left.base (Λ.hom.left.base c)) :
    PlurisubharmonicOn (fun z => (g (G z) : EReal) + modelPullback Λ.hom.left u z) U := by
  intro z hz
  let c : (univ : Set U) := ⟨⟨z, hz⟩, trivial⟩
  -- the holomorphic lift of `π ∘ Λ` into `e`
  obtain ⟨b₀, -, hb₀⟩ := hG c
  obtain ⟨W₁, hW₁, hzW₁, hW₁U, G₁, hG₁, hmaps₁, hfac₁⟩ :=
    LocalEmbedding.exists_contDiffOn_factor (Λ ≫ π).hom.left (Over.w (Λ ≫ π).hom) e c
      ⟨b₀, hb₀⟩
  have hGG₁ : ∀ w ∈ W₁, G₁ w = G w := by
    intro w hw
    let q : (univ : Set U) := ⟨⟨w, hW₁U hw⟩, trivial⟩
    obtain ⟨b₁, hb₁, hpb₁⟩ := hfac₁ q hw
    obtain ⟨b, hb, hpb⟩ := hG q
    have hbb : b₁ = b := e.toPoint_injective (hpb₁.trans hpb.symm)
    exact hb₁.symm.trans ((congrArg (fun a : e.carrier => a.val.val) hbb).trans hb)
  -- the local potential of `π^*θ` at `Λ(z)` and the holomorphic lift of `Λ`
  obtain ⟨eY, heY, -, gY, hgY, hresY, hpshY⟩ := hu (Λ.hom.left.base c)
  obtain ⟨W₂, hW₂, hzW₂, hW₂U, G₂, hG₂, hmaps₂, hfac₂⟩ :=
    LocalEmbedding.exists_contDiffOn_factor Λ.hom.left (Over.w Λ.hom) eY c heY
  let V : Opens (ComplexModel m) := ⟨W₂, hW₂⟩
  have hcarrier : ∀ a : (univ : Set V),
      (⟨G₂ a.val.val, hmaps₂ a.val.property⟩ : eY.ambient) ∈ eY.carrier := by
    intro a
    obtain ⟨b, hb, -⟩ := hfac₂ ⟨⟨a.val.val, hW₂U a.val.property⟩, trivial⟩ a.val.property
    have hval : (⟨G₂ a.val.val, hmaps₂ a.val.property⟩ : eY.ambient) = b.val :=
      Subtype.ext hb.symm
    rw [hval]
    exact b.property
  let M := analyticModelMorphism isComplexAnalyticSubset_univ eY.analytic G₂ hG₂ hmaps₂ hcarrier
  let corrected : eY.carrier → EReal := fun b => (gY b.val.val : EReal) + u (eY.toPoint b)
  have hcorrected := discPshOn_modelPullback hpshY.2 M.hom.left (Over.w M.hom)
  have hrep : ∀ w ∈ W₂, modelPullback M.hom.left corrected w =
      (gY (G₂ w) : EReal) + modelPullback Λ.hom.left u w := by
    intro w hw
    let a : (univ : Set V) := ⟨⟨w, hw⟩, trivial⟩
    let b : (univ : Set U) := ⟨⟨w, hW₂U hw⟩, trivial⟩
    rw [modelPullback_at' M corrected a, modelPullback_at' Λ u b]
    obtain ⟨q, hq, hpq⟩ := hfac₂ b hw
    have hMq : M.hom.left.base a = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hq.symm
    change (gY ((M.hom.left.base a).val.val) : EReal) + u (eY.toPoint (M.hom.left.base a)) = _
    rw [hMq, hq, hpq]
    rfl
  have hpCorr : PlurisubharmonicOn
      (fun w => (gY (G₂ w) : EReal) + modelPullback Λ.hom.left u w) W₂ :=
    (hcorrected.congr hrep).plurisubharmonicOn hW₂
  -- the two potentials have the same `ddᶜ` along the probe
  let W : Set (ComplexModel m) := W₁ ∩ W₂
  have hW : IsOpen W := hW₁.inter hW₂
  have hzW : z ∈ W := ⟨hzW₁, hzW₂⟩
  have hs₁ : ContDiffOn ℝ ∞ (fun y => g (G₁ y)) W :=
    (hg.comp (hG₁.restrict_scalars ℝ) hmaps₁).mono inter_subset_left
  have hs₂ : ContDiffOn ℝ ∞ (fun y => gY (G₂ y)) W :=
    (hgY.comp (hG₂.restrict_scalars ℝ) hmaps₂).mono inter_subset_right
  have hddc : ∀ w ∈ W, smoothDDC (fun y => g (G₁ y) - gY (G₂ y)) w = 0 := by
    intro w hw
    rw [smoothDDC_sub' hW hs₁ hs₂ hw, sub_eq_zero]
    have h1 := HolomorphicDDC.smoothDDC_comp hW₁ e.ambient.isOpen hG₁ hg hmaps₁ hw.1
    have h2 := HolomorphicDDC.smoothDDC_comp hW₂ eY.ambient.isOpen hG₂ hgY hmaps₂ hw.2
    have h3 := SpaceForm.pullbackToDomain_eq_of_restrictsTo θ (Λ ≫ π) hres hW₁ hW₁U
      (hG₁.differentiableOn (by simp)) hfac₁ hw.1
    have h4 := SpaceForm.pullbackToDomain_eq_of_restrictsTo (SpaceForm.pullback θ π) Λ hresY
      hW₂ hW₂U (hG₂.differentiableOn (by simp)) hfac₂ hw.2
    have h5 := SpaceForm.pullbackToDomain_pullback θ π Λ (hW₂U hw.2)
    rw [h1, h2]
    exact h3.symm.trans (h5.symm.trans h4)
  have hH : PlurisubharmonicOn (fun y => ((g (G₁ y) - gY (G₂ y) : ℝ) : EReal)) W :=
    plurisubharmonicOn_coe_of_smoothDDC_eq_zero hW (hs₁.sub hs₂) hddc
  apply ((hpCorr z hzW₂).add (hH z hzW)).congr
  filter_upwards [hW.mem_nhds hzW] with y hy
  rw [hGG₁ y hy.1, add_comm (gY (G₂ y) : EReal), corrected_add_sub, add_comm]

/-! ### Discs in the local model -/

open Classical in
/-- **Disc germs.** With `v ∘ π = u ∈ PSH(Y, π^*θ)`, and `g` a local potential of `θ` on the local
embedding `e`, the pull-back of `w = g + v ∘ e` by every holomorphic disc in the local model
satisfies the disc criterion near the centre. -/
theorem discPullback_gauge_pshAt_zero {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u)
    {v : X.obj.left → EReal} (hvu : ∀ y, v (π.hom.left.base y) = u y)
    {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ} (hg : ContDiffOn ℝ ∞ g e.ambient)
    (hres : θ.RestrictsTo e (smoothDDC g))
    (husc : UpperSemicontinuous (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c)))
    (f : unitDisc ⟶ sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic) :
    PlurisubharmonicAt
      (discPullback f (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c))) 0 := by
  set w : e.carrier → EReal := fun c => (g c.val.val : EReal) + v (e.toPoint c) with hw_def
  obtain ⟨r, hr, hr1, k, hk, Λ, hlift⟩ :=
    exists_ramified_disk_lift π hπ (f ≫ PD.embeddingMorphism e)
  let P := smallDiskInclusion r hr1 ≫ discPowerMorphism k hk
  let G : ComplexModel 1 → ComplexModel e.dim := fun z =>
    if hz : z ∈ smallDiskOpens r then
      (f.hom.left.base (P.hom.left.base ⟨⟨z, hz⟩, trivial⟩)).val.val
    else 0
  have hGval : ∀ c : (univ : Set (smallDiskOpens r)),
      G c.val.val = (f.hom.left.base (P.hom.left.base c)).val.val := by
    intro c
    simp only [G]
    rw [dif_pos c.val.property]
  have hG : ∀ c : (univ : Set (smallDiskOpens r)), ∃ b : e.carrier, b.val.val = G c.val.val ∧
      e.toPoint b = π.hom.left.base (Λ.hom.left.base c) :=
    fun c => ⟨f.hom.left.base (P.hom.left.base c), (hGval c).symm, (hlift c).symm⟩
  have hpsh := IsThetaPSH.plurisubharmonicOn_gauge_add θ π hu hg hres Λ G hG
  have hraw := SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn hpsh
  have hscalar := hraw.comp_affine discCoordinate 0
  have hdomain : (fun z : ℂ => 0 + discCoordinate z) ⁻¹'
      (smallDiskOpens r : Set (ComplexModel 1)) = ball 0 r := by
    ext z
    simp [smallDiskOpens, norm_discCoordinate]
  rw [hdomain] at hscalar
  have heq : EqOn (fun z : ℂ => (g (G (0 + discCoordinate z)) : EReal) +
        modelPullback Λ.hom.left u (0 + discCoordinate z))
      (fun z : ℂ => discPullback f w (z ^ k)) (ball 0 r) := by
    intro z hz
    have hzD : discCoordinate z ∈ smallDiskOpens r := by
      simpa [smallDiskOpens, norm_discCoordinate, mem_ball_zero_iff] using hz
    let q : (univ : Set (smallDiskOpens r)) := ⟨⟨discCoordinate z, hzD⟩, trivial⟩
    have hzUnit : z ∈ ball (0 : ℂ) 1 := ball_subset_ball hr1 hz
    have hzPow : z ^ k ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hzUnit) (Nat.ne_of_gt hk)
    have hzPowD := discCoordinate_mem_unitDiscOpens hzPow
    have hpoint : P.hom.left.base q =
        (⟨⟨discCoordinate (z ^ k), hzPowD⟩, trivial⟩ : (univ : Set unitDiscOpens)) := by
      apply Subtype.ext
      apply Subtype.ext
      change ((discPowerMorphism k hk).hom.left.base
        ((smallDiskInclusion r hr1).hom.left.base q)).val.val = _
      rw [discPowerMorphism_apply]
      change discCoordinate ((discCoordinate z 0) ^ k) = discCoordinate (z ^ k)
      rw [discCoordinate_apply_zero]
    have hL : (g (G (0 + discCoordinate z)) : EReal) +
        modelPullback Λ.hom.left u (0 + discCoordinate z) =
        (g (f.hom.left.base (P.hom.left.base q)).val.val : EReal) + u (Λ.hom.left.base q) := by
      have h0 : (0 : ComplexModel 1) + discCoordinate z = q.val.val := zero_add _
      rw [h0, hGval q, modelPullback_at' Λ u q]
    have hR : discPullback f w (z ^ k) =
        (g (f.hom.left.base (P.hom.left.base q)).val.val : EReal) + u (Λ.hom.left.base q) := by
      rw [discPullback_apply_of_mem f w hzPowD, ← hpoint, ← hvu]
      change (g (f.hom.left.base (P.hom.left.base q)).val.val : EReal) +
          v (e.toPoint (f.hom.left.base (P.hom.left.base q))) = _
      rw [show e.toPoint (f.hom.left.base (P.hom.left.base q)) =
        π.hom.left.base (Λ.hom.left.base q) from (hlift q).symm]
    exact hL.trans hR.symm
  have hrawPow := hscalar.congr heq
  have hRk : r ^ k ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hr.le hr1 k
  have htarget := RamifiedPower.discPshOn_of_comp_pow k hk hr
    ((discPullback_upperSemicontinuousOn f husc).mono (ball_subset_ball hRk)) hrawPow
  exact ⟨ball 0 (r ^ k), isOpen_ball, mem_ball_self (pow_pos hr k), htarget⟩

/-- The corrected function `w = g + v ∘ e` is upper semicontinuous on the local model. -/
theorem upperSemicontinuous_gauge {X : SourceReducedComplexSpace} {v : X.obj.left → EReal}
    (hv : UpperSemicontinuous v) {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ}
    (hg : ContDiffOn ℝ ∞ g e.ambient) :
    UpperSemicontinuous (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c)) := by
  intro c
  have hcoords : Continuous (fun b : e.carrier => b.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hgC : Continuous (fun b : e.carrier => ((g b.val.val : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp
      (hg.continuousOn.comp_continuous hcoords (fun b => b.val.property))
  have hve : UpperSemicontinuous (fun b : e.carrier => v (e.toPoint b)) :=
    UpperSemicontinuous.comp hv e.isOpenEmbedding_toPoint.continuous
  exact UpperSemicontinuousAt.add' hgC.continuousAt.upperSemicontinuousAt (hve c)
    (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))

/-- **Condition 2 of `def:unibranch:L105` for `w = g + v ∘ e`.** Near every point of the local
model, `w` is the restriction of an ambient psh function (by the disc germs and `thm:FN`). -/
theorem isLocallyAmbientPSHAt_gauge {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (π : Y ⟶ X) (hπ : IsProperBimeromorphic π)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u)
    {v : X.obj.left → EReal} (hvusc : UpperSemicontinuous v)
    (hvu : ∀ y, v (π.hom.left.base y) = u y)
    {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ} (hg : ContDiffOn ℝ ∞ g e.ambient)
    (hres : θ.RestrictsTo e (smoothDDC g)) (c : e.carrier) :
    (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsLocallyAmbientPSHAt
      (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c)) c := by
  have husc := upperSemicontinuous_gauge hvusc hg (e := e)
  have hne_top : ∀ c : e.carrier, (g c.val.val : EReal) + v (e.toPoint c) ≠ ⊤ := by
    intro c
    obtain ⟨y, hy⟩ := hπ.surjective (e.toPoint c)
    have hv : v (e.toPoint c) ≠ ⊤ := by
      rw [← hy, hvu]
      exact hu.ne_top y
    exact EReal.add_ne_top (EReal.coe_ne_top _) hv
  have hdisc : ∀ f : unitDisc ⟶ sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic,
      (∃ t ∈ ball (0 : ℂ) 1,
        discPullback f (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c)) t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn
        (discPullback f (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c)))
        (ball (0 : ℂ) 1) := fun f hn =>
    SGPT.PSH.subharmonicOn_of_disc (SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn
      (plurisubharmonicOn_discPullback_of_zero_germs _
        (fun f' => discPullback_gauge_pshAt_zero θ π hπ hu hvu hg hres husc f') f)) hn
  exact FNA.isLocallyAmbientPSHAt_of_disc
    (X := sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic)
    (φ := fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c))
    FNH.localFNExtension hne_top husc hdisc c

/-! ### The component clause -/

/-- The locus where the descent `v` is locally identically `-∞` is closed (hence clopen). -/
theorem isClosed_setOf_eventually_eq_bot_descent {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (hθ : PD.IsLocallyClosedOneOne θ) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u)
    {v : X.obj.left → EReal} (hvusc : UpperSemicontinuous v)
    (hvu : ∀ y, v (π.hom.left.base y) = u y) :
    IsClosed {x : X.obj.left | ∀ᶠ y in 𝓝 x, v y = ⊥} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨e, ⟨c, rfl⟩, -, g, hg, hres⟩ := hθ.exists_local_potential x
  have hV := hX.of_openImmersion (PD.embeddingMorphism e) e.isOpenImmersion
  have hloc := isLocallyAmbientPSHAt_gauge θ π hπ hu hvusc hvu hg hres
  have hcl := isClosed_setOf_eventually_eq_bot_of_isUnibranch hV hloc
  set T : Set e.carrier :=
    {c' | ∀ᶠ c'' in 𝓝 c', (g c''.val.val : EReal) + v (e.toPoint c'') = ⊥} with hT
  have hsub : e.toPoint ⁻¹' {x | ∀ᶠ y in 𝓝 x, v y = ⊥} ⊆ T := by
    intro c' hc'
    have hc'' : ∀ᶠ c'' in 𝓝 c', v (e.toPoint c'') = ⊥ :=
      (e.isOpenEmbedding_toPoint.continuous.continuousAt (x := c')).tendsto.eventually hc'
    filter_upwards [hc''] with c'' h
    rw [h]
    exact EReal.add_bot _
  have hcT : c ∈ T := by
    have hcl' : closure T ⊆ T := hcl.closure_subset
    apply hcl'
    apply closure_mono hsub
    exact e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_subset_closure_preimage hx
  have hvc : ∀ᶠ c'' in 𝓝 c, v (e.toPoint c'') = ⊥ := by
    filter_upwards [hcT] with c'' h
    rcases EReal.add_eq_bot_iff.mp h with h' | h'
    · exact absurd h' (EReal.coe_ne_bot _)
    · exact h'
  show ∀ᶠ y in 𝓝 (e.toPoint c), v y = ⊥
  rw [← e.isOpenEmbedding_toPoint.map_nhds_eq c]
  exact eventually_map.mpr hvc

/-- **`w = g + v ∘ e` is psh on the local model** (`def:unibranch:L105`, both conditions). -/
theorem isPSH_gauge {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (hθ : PD.IsLocallyClosedOneOne θ) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u)
    {v : X.obj.left → EReal} (hvusc : UpperSemicontinuous v)
    (hvu : ∀ y, v (π.hom.left.base y) = u y)
    {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ} (hg : ContDiffOn ℝ ∞ g e.ambient)
    (hres : θ.RestrictsTo e (smoothDDC g)) :
    (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).IsPSH
      (fun c : e.carrier => (g c.val.val : EReal) + v (e.toPoint c)) := by
  refine ⟨?_, isLocallyAmbientPSHAt_gauge θ π hπ hu hvusc hvu hg hres⟩
  intro Z hZ
  by_contra hcon
  push Not at hcon
  set S : Set X.obj.left := {x | ∀ᶠ y in 𝓝 x, v y = ⊥} with hS
  have hSc : IsClopen S :=
    ⟨isClosed_setOf_eventually_eq_bot_descent θ hθ π hπ hX hu hvusc hvu,
      isOpen_setOfPred_eventually_nhds⟩
  have hV := hX.of_openImmersion (PD.embeddingMorphism e) e.isOpenImmersion
  obtain ⟨c, hc⟩ := hZ.1.2.1
  have hZK := hV.eq_connectedComponent_of_isIrreducibleComponent hZ c hc
  have hZo : IsOpen Z := by
    let hlc := hV.locallyConnectedSpace
    rw [hZK]
    exact isOpen_connectedComponent
  have hcS : e.toPoint c ∈ S := by
    show ∀ᶠ y in 𝓝 (e.toPoint c), v y = ⊥
    rw [← e.isOpenEmbedding_toPoint.map_nhds_eq c]
    refine eventually_map.mpr ?_
    filter_upwards [hZo.mem_nhds hc] with c' hc'
    rcases EReal.add_eq_bot_iff.mp (hcon c' hc') with h' | h'
    · exact absurd h' (EReal.coe_ne_bot _)
    · exact h'
  obtain ⟨y₀, hy₀⟩ := hπ.surjective (e.toPoint c)
  have hA : IsClopen (π.hom.left.base ⁻¹' S) :=
    hSc.preimage π.hom.left.base.hom.continuous
  obtain ⟨y, hyS, hyu⟩ :=
    IsThetaPSH.exists_ne_bot_of_isClopen hu hA ⟨y₀, by rw [mem_preimage, hy₀]; exact hcS⟩
  apply hyu
  rw [← hvu]
  exact (show ∀ᶠ y' in 𝓝 (π.hom.left.base y), v y' = ⊥ from hyS).self_of_nhds

/-- **Source `cor:PSH`, surjectivity: the descent is `θ`-psh.** Let `π : Y → X` be proper
bimeromorphic onto a unibranch complex space, `θ` a smooth closed real `(1,1)`-form on `X`,
`u ∈ PSH(Y, π^*θ)` and `v` upper semicontinuous with `v ∘ π = u`. Then `v ∈ PSH(X, θ)`. -/
theorem isThetaPSH_of_descent {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (hθ : PD.IsLocallyClosedOneOne θ) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u)
    {v : X.obj.left → EReal} (hvusc : UpperSemicontinuous v)
    (hvu : ∀ y, v (π.hom.left.base y) = u y) : X.IsThetaPSH θ v := by
  intro x
  obtain ⟨e, hx, hconn, g, hg, hres⟩ := hθ.exists_local_potential x
  exact ⟨e, hx, hconn, g, hg, hres, isPSH_gauge θ hθ π hπ hX hu hvusc hvu hg hres⟩

/-- **Source `cor:PSH`, descent.** Every `u ∈ PSH(Y, π^*θ)` is `v ∘ π` for a unique
`v ∈ PSH(X, θ)`. -/
theorem existsUnique_thetaPSH_descent {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (hθ : PD.IsLocallyClosedOneOne θ) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u) :
    ∃! v : X.obj.left → EReal, X.IsThetaPSH θ v ∧ ∀ y, v (π.hom.left.base y) = u y := by
  obtain ⟨v, ⟨hvusc, hvu⟩, -⟩ := hu.exists_unique_usc_descent_of_isProperBimeromorphic θ π hπ hX
  refine ⟨v, ⟨isThetaPSH_of_descent θ hθ π hπ hX hu hvusc hvu, hvu⟩, ?_⟩
  intro w hw
  funext x
  obtain ⟨y, rfl⟩ := hπ.surjective x
  rw [hw.2 y, hvu y]

end

end SGPT.Unibranch.PD2

namespace SGPT.Unibranch.PD

open SourceReducedComplexSpace

/-- **Source `cor:PSH`.** Let `π : Y → X` be a proper bimeromorphic morphism of complex spaces with
`X` unibranch, and `θ` a smooth closed real `(1,1)`-form on `X`. Then the pull-back
`π^* : PSH(X, θ) → PSH(Y, π^*θ)`, `φ ↦ φ ∘ π`, is a bijection. (The book assumes `X`, `Y` compact
Kähler; this is not needed.) -/
theorem corPSH_bijective {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) (θ : SpaceForm X 2)
    (hθ : IsLocallyClosedOneOne θ) : Function.Bijective (thetaPSHPullback θ π hπ hX) := by
  rw [thetaPSHPullback_bijective_iff]
  intro ψ hψ
  obtain ⟨v, ⟨hv, hvψ⟩, -⟩ := PD2.existsUnique_thetaPSH_descent θ hθ π hπ hX hψ
  exact ⟨v, hv, hvψ⟩

/-- **Source `cor:PSH`**, as an equivalence `PSH(X, θ) ≃ PSH(Y, π^*θ)` given by the pull-back. -/
noncomputable def corPSHEquiv {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) (θ : SpaceForm X 2)
    (hθ : IsLocallyClosedOneOne θ) :
    {φ : X.obj.left → EReal // X.IsThetaPSH θ φ} ≃
      {ψ : Y.obj.left → EReal // Y.IsThetaPSH (SpaceForm.pullback θ π) ψ} :=
  Equiv.ofBijective (thetaPSHPullback θ π hπ hX) (corPSH_bijective π hπ hX θ hθ)

@[simp] theorem corPSHEquiv_apply {X Y : SourceReducedComplexSpace} (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) (θ : SpaceForm X 2)
    (hθ : IsLocallyClosedOneOne θ) (φ : {φ : X.obj.left → EReal // X.IsThetaPSH θ φ})
    (y : Y.obj.left) :
    (corPSHEquiv π hπ hX θ hθ φ).val y = φ.val (π.hom.left.base y) := rfl

end SGPT.Unibranch.PD
