import SGPT.Okounkov.TranscendentalWNKeyStatement
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.Pending.BlowupIsomorphismOff
import SGPT.Foundations.Analysis.Pending.ExceptionalFibres

/-!
# Geometry of the central fibre for the key equality (package WN-KEY)

Blueprint `claude-tok-wn-key`, nodes `tok-wn-key:kahler-restriction` and
`tok-wn-key:exceptional-connected`: the two facts that make the continuity of restricted
volumes (`tok-wn:restricted-perturbation`, proved in `TranscendentalWNRestricted` for a connected
compact `V` mapping to `𝒳` with Kähler restriction) applicable on the deformation `𝒳` along the
strict transform `X'` and along the exceptional divisor `ℰ`.

* `injective_fderiv_coordinateMap_of_leftInverse`, `isKahler_pullback_of_leftInverse`: a
  holomorphic map `f : V → M` with a holomorphic left inverse `g` (`g ∘ f = id`) is an
  immersion, so the pullback of a Kähler form is Kähler (the pattern of TN's
  `SubmanifoldKahlerRestriction`, with the left inverse `g` in place of the flattening
  coordinates);
* `isKahler_pullback_centralSection`: for the lift `ι'` of `x ↦ (x, 0)` (image `X'`), `π_X ∘ μ`
  is a left inverse, so `ι'^*η'` is Kähler for every Kähler form `η'` of `𝒳`;
* `interior_centralFibre_eq_empty`: `X₀ = μ⁻¹(X × {0})` has empty interior;
* `isPreconnected_centralFibre`: `X₀` is connected.  Proof: if `X₀ ⊆ A ∪ B` with `A`, `B` closed
  and `X₀ ∩ A ∩ B = ∅`, separate `X₀ ∩ A` and `X₀ ∩ B` by disjoint open `U`, `V` (`𝒳` is compact
  Hausdorff); by properness of `π_{ℙ¹} ∘ μ` some disc `W ∋ 0` has `(π_{ℙ¹} μ)⁻¹(W) ⊆ U ∪ V`; the
  set `N = μ⁻¹(X × (W \ {0})) ≅ X × (W \ {0})` is connected, so it lies in `U` (say), and since
  `X₀` has empty interior, `X₀ ⊆ closure N ⊆ closure U`, which misses `V`; so `X₀ ∩ B = ∅`;
* `connectedSpace_exceptional`: **`ℰ` is connected** (if `Z ≠ ∅`).  Proof: `X₀ = X' ∪ ℰ`,
  `X' ∩ ℰ = ι'(Z)` is connected and nonempty, and a clopen splitting of `ℰ` not containing
  `ι'(Z)` would split `X₀`.  (No description of the exceptional fibres `ℙ(N_{Z|X} ⊕ 𝒪)` is
  needed.)
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

/-! ### Immersions with a holomorphic left inverse -/

section LeftInverse

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  {f : V → M} {g : M → V}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
  (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ g)
  (hgf : ∀ x, g (f x) = x)

include hf hg hgf in
/-- **A holomorphic map with a holomorphic left inverse is an immersion**: its coordinate
representatives have injective real differentials. -/
theorem injective_fderiv_coordinateMap_of_leftInverse (e : ComplexChart k V)
    (d : ComplexChart n M) {z : ComplexModel k} (hz : z ∈ coordinateDomain f e d) :
    Function.Injective (fderiv ℝ (coordinateMap f e d) z) := by
  set L := coordinateMap g d e with hL
  set y := coordinateMap f e d z with hy
  have hzt : z ∈ e.val.target := hz.1
  have hfz : f (e.val.symm z) ∈ d.val.source := hz.2
  have hyL : y ∈ coordinateDomain g d e := by
    refine ⟨coordinateMap_mem_target hz, ?_⟩
    show g (d.val.symm (d.val (f (e.val.symm z)))) ∈ e.val.source
    rw [d.val.left_inv hfz, hgf]
    exact e.val.map_target hzt
  have hleft : L ∘ coordinateMap f e d =ᶠ[𝓝 z] id := by
    filter_upwards [(coordinateDomain_isOpen hf e d).mem_nhds hz] with ζ hζ
    show e.val (g (d.val.symm (d.val (f (e.val.symm ζ))))) = ζ
    rw [d.val.left_inv hζ.2, hgf, e.val.right_inv hζ.1]
  have hfd : DifferentiableAt ℝ (coordinateMap f e d) z :=
    (coordinateMap_contDiffAt_real hf e d hz).differentiableAt (by simp)
  have hLd : DifferentiableAt ℝ L y :=
    (coordinateMap_contDiffAt_real hg d e hyL).differentiableAt (by simp)
  have hcomp : (fderiv ℝ L y).comp (fderiv ℝ (coordinateMap f e d) z) =
      ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp z hLd hfd, hleft.fderiv_eq, fderiv_id]
  intro a b hab
  have h := congrArg (fderiv ℝ L y) hab
  have ha := congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k => T a) hcomp
  have hb := congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k => T b) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
  rw [← ha, ← hb, h]

include hf hg hgf in
/-- The pullback of a Hermitian form along a holomorphic map with a holomorphic left inverse is
Hermitian. -/
theorem isHermitian_pullback_of_leftInverse {β : SmoothRealForm n M 2} (hβ : β.IsHermitian) :
    (SmoothRealForm.pullback hf β).IsHermitian := by
  intro e z hz
  set d := complexChartAt (n := n) (f (e.val.symm z)) with hd
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  have hinj := injective_fderiv_coordinateMap_of_leftInverse hf hg hgf e d hzd
  set D := fderiv ℝ (coordinateMap f e d) z with hD
  have hDI : ∀ v, D (Complex.I • v) = Complex.I • D v := fun v =>
    coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  have hvec : ∀ u v : ComplexModel k, (⇑D ∘ ![u, v]) = ![D u, D v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  obtain ⟨hβ11, hβpos⟩ := hβ d _ (coordinateMap_mem_target hzd)
  rw [SmoothRealForm.pullback_coeff hf β e d hzd]
  refine ⟨fun u v => ?_, fun u hu => ?_⟩
  · simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← hD]
    rw [hvec, hvec, hDI, hDI]
    exact hβ11 (D u) (D v)
  · simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ← hD]
    rw [hvec, hDI]
    refine hβpos (D u) ?_
    intro h0
    exact hu (hinj (h0.trans (map_zero D).symm))

include hg hgf in
/-- **The pullback of a Kähler form along a holomorphic map with a holomorphic left inverse is
Kähler.** -/
theorem isKahler_pullback_of_leftInverse (a : ClosedRealOneOneForm n M) (ha : a.val.IsKahler) :
    (ClosedRealOneOneForm.pullback hf a).val.IsKahler :=
  ⟨isHermitian_pullback_of_leftInverse hf hg hgf ha.1,
    (ClosedRealOneOneForm.pullback hf a).property.1⟩

end LeftInverse

/-! ### The deformation: `X'` and `ℰ` -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`ι'^*η'` is Kähler** for the lift `ι'` of `x ↦ (x, 0)` and every Kähler form `η'` of `𝒳`:
`π_X ∘ μ` is a holomorphic left inverse of `ι'`. -/
theorem isKahler_pullback_centralSection (hμ : IsNormalConeDeformation F μ)
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) (w : KahlerBackground (m + 1 + 1) 𝒳) :
    (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler :=
  isKahler_pullback_of_leftInverse hι (contMDiff_deformationProjX F hμ.contMDiff)
    (fun x => by rw [hμι]) w.form w.isKahler

/-! ### The central fibre has empty interior and is connected -/

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- `{0}` is not open in `ℙ¹`. -/
theorem not_isOpen_singleton_projectiveZero :
    ¬ IsOpen ({projectiveZero} : Set ProjectiveLine) := by
  intro h
  have h1 : IsOpen (SGPT.Toric.projectiveLineHomeomorph ⁻¹' {projectiveZero}) :=
    h.preimage SGPT.Toric.projectiveLineHomeomorph.continuous
  have h2 : SGPT.Toric.projectiveLineHomeomorph ⁻¹' {projectiveZero} =
      {((0 : ℂ) : OnePoint ℂ)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, projectiveZero]
    exact SGPT.Toric.projectiveLineHomeomorph.injective.eq_iff
  rw [h2] at h1
  have h3 : IsOpen (((↑) : ℂ → OnePoint ℂ) ⁻¹' {((0 : ℂ) : OnePoint ℂ)}) :=
    h1.preimage OnePoint.continuous_coe
  have h4 : (((↑) : ℂ → OnePoint ℂ) ⁻¹' {((0 : ℂ) : OnePoint ℂ)}) = {(0 : ℂ)} := by
    ext x
    simp
  rw [h4] at h3
  exact not_isOpen_singleton (0 : ℂ) h3

/-- **`X₀ = μ⁻¹(X × {0})` has empty interior.**  An open subset of `X₀` meeting `𝒳 \ ℰ` would
map (by the inverse of `μ` off the centre) to an open subset of `X × ℙ¹` inside `X × {0}`, and
`ℰ` has empty interior (TN `ExceptionalFibres.interior_preimage_eq_empty`). -/
theorem interior_centralFibre_eq_empty (hμ : IsNormalConeDeformation F μ) :
    interior (centralFibre F μ) = ∅ := by
  obtain ⟨s, hs, hsμ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hμ
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  set O := interior (centralFibre F μ) with hOdef
  have hO : IsOpen O := isOpen_interior
  by_cases hsub : O ⊆ exceptionalSet F μ
  · have hzi : z ∈ interior (μ ⁻¹' deformationCentre F) :=
      interior_mono hsub (by rw [hOdef, interior_interior]; exact hz)
    rw [ExceptionalFibres.interior_preimage_eq_empty hμ] at hzi
    exact hzi
  · obtain ⟨z', hz'O, hz'E⟩ := not_subset.mp hsub
    have hq : μ z' ∈ (deformationCentre F)ᶜ := hz'E
    have hW : IsOpen (s ⁻¹' O) := hO.preimage hs.continuous
    have hsz' : s ⟨μ z', hq⟩ = z' := hsec z' hq
    have hmem : (⟨μ z', hq⟩ : (⟨(deformationCentre F)ᶜ, hμ.1.1.isOpen_compl⟩ :
        TopologicalSpace.Opens (F.carrier × ProjectiveLine))) ∈ s ⁻¹' O := by
      show s ⟨μ z', hq⟩ ∈ O
      rw [hsz']
      exact hz'O
    have hWX : IsOpen (Subtype.val '' (s ⁻¹' O) : Set (F.carrier × ProjectiveLine)) :=
      (hμ.1.1.isOpen_compl).isOpenMap_subtype_val _ hW
    have hsubX : Subtype.val '' (s ⁻¹' O) ⊆ centralBase F := by
      rintro _ ⟨q, hqO, rfl⟩
      have h1 : s q ∈ centralFibre F μ := interior_subset hqO
      have h2 : μ (s q) = q.1 := congrFun hsμ q
      rw [centralFibre, mem_preimage, h2] at h1
      exact h1
    have hslice : IsOpen ((fun p : ProjectiveLine => ((μ z').1, p)) ⁻¹'
        (Subtype.val '' (s ⁻¹' O))) :=
      hWX.preimage (continuous_const.prodMk continuous_id)
    have hz'X : μ z' ∈ Subtype.val '' (s ⁻¹' O) := ⟨_, hmem, rfl⟩
    have h0 : (μ z').2 = projectiveZero := (hsubX hz'X).2
    have hsl : (fun p : ProjectiveLine => ((μ z').1, p)) ⁻¹' (Subtype.val '' (s ⁻¹' O)) =
        {projectiveZero} := by
      ext p
      constructor
      · intro hp
        exact (hsubX hp).2
      · intro hp
        rw [mem_singleton_iff] at hp
        rw [mem_preimage, hp, ← h0]
        exact hz'X
    exact not_isOpen_singleton_projectiveZero (hsl ▸ hslice)

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- A punctured disc in `ℂ` is preconnected. -/
theorem isPreconnected_ball_diff_zero {r : ℝ} :
    IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) := by
  have himg : (fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) ''
      (Ioo 0 r ×ˢ univ) = Metric.ball (0 : ℂ) r \ {0} := by
    ext w
    constructor
    · rintro ⟨⟨a, t⟩, ⟨ha, -⟩, rfl⟩
      have hnorm : ‖(a : ℂ) * Complex.exp (t * Complex.I)‖ = a := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ha.1]
      refine ⟨by rw [Metric.mem_ball, dist_zero_right, hnorm]; exact ha.2, ?_⟩
      rw [mem_singleton_iff, ← norm_eq_zero, hnorm]
      exact ha.1.ne'
    · rintro ⟨hw, hw0⟩
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [mem_singleton_iff] at hw0
      exact ⟨(‖w‖, Complex.arg w), ⟨⟨norm_pos_iff.mpr hw0, hw⟩, mem_univ _⟩,
        Complex.norm_mul_exp_arg_mul_I w⟩
  rw [← himg]
  exact ((isPreconnected_Ioo).prod isPreconnected_univ).image _ (by fun_prop)

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- Every open neighbourhood of `0` in `ℙ¹` contains an open neighbourhood `W` of `0` with
`W \ {0}` preconnected (the image of a disc of the affine chart). -/
theorem exists_open_punctured_preconnected {O : Set ProjectiveLine} (hO : IsOpen O)
    (h0 : projectiveZero ∈ O) :
    ∃ W : Set ProjectiveLine, IsOpen W ∧ W ⊆ O ∧ projectiveZero ∈ W ∧
      IsPreconnected (W \ {projectiveZero}) := by
  set φ := SGPT.Toric.projectiveLineHomeomorph
  have hO' : IsOpen (((↑) : ℂ → OnePoint ℂ) ⁻¹' (φ ⁻¹' O)) :=
    (hO.preimage φ.continuous).preimage OnePoint.continuous_coe
  have h0' : (0 : ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) ⁻¹' (φ ⁻¹' O) := h0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO' 0 h0'
  refine ⟨φ '' (((↑) : ℂ → OnePoint ℂ) '' Metric.ball 0 r), ?_, ?_, ?_, ?_⟩
  · exact φ.isOpenMap _ (OnePoint.isOpenMap_coe _ Metric.isOpen_ball)
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact hball hw
  · exact ⟨_, ⟨0, Metric.mem_ball_self hr, rfl⟩, rfl⟩
  · have heq : φ '' (((↑) : ℂ → OnePoint ℂ) '' Metric.ball 0 r) \ {projectiveZero} =
        (fun w : ℂ => φ (w : OnePoint ℂ)) '' (Metric.ball 0 r \ {0}) := by
      ext p
      constructor
      · rintro ⟨⟨_, ⟨w, hw, rfl⟩, rfl⟩, hp⟩
        refine ⟨w, ⟨hw, fun hw0 => hp ?_⟩, rfl⟩
        rw [mem_singleton_iff] at hw0 ⊢
        rw [hw0]
        rfl
      · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
        refine ⟨⟨_, ⟨w, hw, rfl⟩, rfl⟩, fun hp => hw0 ?_⟩
        rw [mem_singleton_iff] at hp ⊢
        exact OnePoint.coe_injective (φ.injective hp)
    rw [heq]
    exact isPreconnected_ball_diff_zero.image _
      (φ.continuous.comp OnePoint.continuous_coe).continuousOn

/-- **`X₀` is connected**: the general fibres `X_τ ≅ X` are connected and degenerate to `X₀`
(properness of `π_{ℙ¹} ∘ μ`, and `X₀` has empty interior). -/
theorem isPreconnected_centralFibre (hμ : IsNormalConeDeformation F μ) :
    IsPreconnected (centralFibre F μ) := by
  have := compactSpace_normalCone F hμ
  obtain ⟨s, hs, hsμ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hμ
  set X0 := centralFibre F μ with hX0
  set p : 𝒳 → ProjectiveLine := fun z => (μ z).2 with hpdef
  have hp : Continuous p := continuous_snd.comp hμ.continuous
  have hmemX0 : ∀ z, z ∈ X0 ↔ p z = projectiveZero := by
    intro z
    simp [hX0, centralFibre, centralBase, hpdef]
  have hX0c : IsClosed X0 := (isClosed_centralBase F).preimage hμ.continuous
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro A B hA hB hAB hdisj
  have hd : Disjoint (X0 ∩ A) (X0 ∩ B) := by
    rw [Set.disjoint_iff]
    rintro z ⟨⟨h1, h2⟩, ⟨-, h3⟩⟩
    have : z ∈ X0 ∩ (A ∩ B) := ⟨h1, h2, h3⟩
    rw [hdisj] at this
    exact this
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation (hX0c.inter hA) (hX0c.inter hB) hd
  set K : Set 𝒳 := (U ∪ V)ᶜ with hKdef
  have hK : IsCompact (p '' K) := ((hU.union hV).isClosed_compl.isCompact).image hp
  have h0K : projectiveZero ∉ p '' K := by
    rintro ⟨z, hzK, hz0⟩
    apply hzK
    have hz : z ∈ X0 := (hmemX0 z).mpr hz0
    rcases hAB hz with h | h
    · exact Or.inl (hAU ⟨hz, h⟩)
    · exact Or.inr (hBV ⟨hz, h⟩)
  obtain ⟨W, hWo, hWsub, hW0, hWconn⟩ :=
    exists_open_punctured_preconnected hK.isClosed.isOpen_compl h0K
  let Ap : Set (⟨(deformationCentre F)ᶜ, hμ.1.1.isOpen_compl⟩ :
      TopologicalSpace.Opens (F.carrier × ProjectiveLine)) :=
    Subtype.val ⁻¹' (univ ×ˢ (W \ {projectiveZero}))
  have hprodC : univ ×ˢ (W \ {projectiveZero}) ⊆ ((deformationCentre F)ᶜ :
      Set (F.carrier × ProjectiveLine)) := by
    rintro q ⟨-, -, hq0⟩ hqC
    exact hq0 ((mem_deformationCentre_iff F).mp hqC).2
  have hApconn : IsPreconnected Ap := by
    have himg : (Subtype.val : _ → F.carrier × ProjectiveLine) '' Ap =
        univ ×ˢ (W \ {projectiveZero}) := by
      ext q
      constructor
      · rintro ⟨q', hq', rfl⟩
        exact hq'
      · intro hq
        exact ⟨⟨q, hprodC hq⟩, hq, rfl⟩
    have h1 : IsPreconnected ((Subtype.val : _ → F.carrier × ProjectiveLine) '' Ap) := by
      rw [himg]
      exact isPreconnected_univ.prod hWconn
    exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp h1
  set N : Set 𝒳 := s '' Ap with hN
  have hNconn : IsPreconnected N := hApconn.image s hs.continuous.continuousOn
  have hNUV : N ⊆ U ∪ V := by
    rintro _ ⟨q, hq, rfl⟩
    by_contra hcon
    have hqK : s q ∈ K := hcon
    have hpq : p (s q) = q.1.2 := by
      simp only [hpdef]
      rw [show μ (s q) = q.1 from congrFun hsμ q]
    exact hWsub hq.2.1 ⟨s q, hqK, hpq.symm ▸ rfl⟩
  -- every point of `X₀` in an open set `G` forces `G` to meet `N`
  have hmeet : ∀ G : Set 𝒳, IsOpen G → ∀ z ∈ G, z ∈ X0 → (G ∩ N).Nonempty := by
    intro G hG z hzG hz
    have hGp : IsOpen (G ∩ p ⁻¹' W) := hG.inter (hWo.preimage hp)
    have hzGp : z ∈ G ∩ p ⁻¹' W := ⟨hzG, by rw [mem_preimage, (hmemX0 z).mp hz]; exact hW0⟩
    have hnot : ¬ (G ∩ p ⁻¹' W ⊆ X0) := by
      intro hsub
      have : z ∈ interior X0 := interior_maximal hsub hGp hzGp
      rw [hX0, interior_centralFibre_eq_empty F hμ] at this
      exact this
    obtain ⟨z', ⟨hz'G, hz'W⟩, hz'X0⟩ := not_subset.mp hnot
    have hp' : p z' ≠ projectiveZero := fun h => hz'X0 ((hmemX0 z').mpr h)
    have hq : μ z' ∈ univ ×ˢ (W \ {projectiveZero}) := ⟨mem_univ _, hz'W, hp'⟩
    refine ⟨z', hz'G, ⟨⟨μ z', hprodC hq⟩, hq, hsec z' (hprodC hq)⟩⟩
  rcases hNconn.subset_or_subset hU hV hUV hNUV with hNU | hNV
  · left
    intro z hz
    rcases hAB hz with h | h
    · exact h
    · exfalso
      obtain ⟨z', hz'V, hz'N⟩ := hmeet V hV z (hBV ⟨hz, h⟩) hz
      exact Set.disjoint_left.mp hUV (hNU hz'N) hz'V
  · right
    intro z hz
    rcases hAB hz with h | h
    · exfalso
      obtain ⟨z', hz'U, hz'N⟩ := hmeet U hU z (hAU ⟨hz, h⟩) hz
      exact Set.disjoint_left.mp hUV hz'U (hNV hz'N)
    · exact h

/-- **The exceptional divisor `ℰ` is connected.**  `X₀ = X' ∪ ℰ` is connected
(`isPreconnected_centralFibre`) and `X' ∩ ℰ = ι'(Z)` is connected and nonempty; a splitting of
`ℰ` by two closed sets, one of which misses `ι'(Z)`, would split `X₀`. -/
theorem isConnected_exceptionalSet (hμ : IsNormalConeDeformation F μ) :
    IsConnected (exceptionalSet F μ) := by
  obtain ⟨ι, hι, hμι, hrange, hpre⟩ := exists_centralSection F hμ
  have hZ := F.smooth.level_closed_connected (1 : Fin (m + 2))
  set Z := F.flag (1 : Fin (m + 2))
  set S := ι '' Z with hS
  have hSE : S ⊆ exceptionalSet F μ := by
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ ι ⁻¹' exceptionalSet F μ := by rw [hpre]; exact hx
    exact this
  have hSconn : IsConnected S := hZ.2.image ι hι.continuous.continuousOn
  have hX'E : strictCentralFibre F μ ∩ exceptionalSet F μ ⊆ S := by
    rintro z ⟨hzX', hzE⟩
    rw [← hrange] at hzX'
    obtain ⟨x, rfl⟩ := hzX'
    have : x ∈ ι ⁻¹' exceptionalSet F μ := hzE
    rw [hpre] at this
    exact ⟨x, this, rfl⟩
  refine ⟨hSconn.nonempty.mono hSE, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv hdisj
  have hEc := isClosed_exceptionalSet F hμ
  have hX'c : IsClosed (strictCentralFibre F μ) := isClosed_strictCentralFibre F
  -- `S` lies in one of the two pieces
  have hSuv : S ⊆ u ∨ S ⊆ v := by
    have hS2 := hSconn.2
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hS2
    exact hS2 u v hu hv (hSE.trans huv) (by
      rw [eq_empty_iff_forall_notMem]
      intro z hz
      have : z ∈ exceptionalSet F μ ∩ (u ∩ v) := ⟨hSE hz.1, hz.2⟩
      rw [hdisj] at this
      exact this)
  -- the general step, applied with `(u, v)` or `(v, u)`
  have key : ∀ u v : Set 𝒳, IsClosed u → IsClosed v → exceptionalSet F μ ⊆ u ∪ v →
      exceptionalSet F μ ∩ (u ∩ v) = ∅ → S ⊆ u → exceptionalSet F μ ⊆ u := by
    intro u v hu hv huv hdisj hSu
    have hpre0 := isPreconnected_centralFibre F hμ
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre0
    have hcov : centralFibre F μ ⊆ (strictCentralFibre F μ ∪ exceptionalSet F μ ∩ u) ∪
        exceptionalSet F μ ∩ v := by
      intro z hz
      rw [centralFibre_eq_union F hμ] at hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inl hz)
      · rcases huv hz with h | h
        · exact Or.inl (Or.inr ⟨hz, h⟩)
        · exact Or.inr ⟨hz, h⟩
    have hempty : centralFibre F μ ∩ ((strictCentralFibre F μ ∪ exceptionalSet F μ ∩ u) ∩
        (exceptionalSet F μ ∩ v)) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨-, hz1, hzE, hzv⟩
      have hzu : z ∈ u := by
        rcases hz1 with hz1 | hz1
        · exact hSu (hX'E ⟨hz1, hzE⟩)
        · exact hz1.2
      have : z ∈ exceptionalSet F μ ∩ (u ∩ v) := ⟨hzE, hzu, hzv⟩
      rw [hdisj] at this
      exact this
    rcases hpre0 _ _ (hX'c.union (hEc.inter hu)) (hEc.inter hv) hcov hempty with h | h
    · intro z hz
      have hz0 : z ∈ centralFibre F μ := by
        rw [centralFibre_eq_union F hμ]; exact Or.inr hz
      rcases h hz0 with h1 | h1
      · exact hSu (hX'E ⟨h1, hz⟩)
      · exact h1.2
    · exfalso
      obtain ⟨y, hy⟩ := hSconn.nonempty
      have hy0 : y ∈ centralFibre F μ := by
        rw [centralFibre_eq_union F hμ]; exact Or.inr (hSE hy)
      have : y ∈ exceptionalSet F μ ∩ (u ∩ v) := ⟨hSE hy, hSu hy, (h hy0).2⟩
      rw [hdisj] at this
      exact this
  rcases hSuv with hSu | hSv
  · exact Or.inl (key u v hu hv huv hdisj hSu)
  · refine Or.inr (key v u hv hu (fun z hz => (huv hz).symm) ?_ hSv)
    rw [inter_comm v u]
    exact hdisj

/-- **`ℰ` is a connected space** (with the subspace topology of its submanifold atlas). -/
theorem connectedSpace_exceptional (hμ : IsNormalConeDeformation F μ) :
    ConnectedSpace (exceptionalSet F μ) :=
  isConnected_iff_connectedSpace.mp (isConnected_exceptionalSet F hμ)

end Deformation

end SGPT.Okounkov.TranscendentalWN
