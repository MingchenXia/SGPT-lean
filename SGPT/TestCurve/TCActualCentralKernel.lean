import SGPT.TestCurve.TCLineCoordinateDivision

/-! Actual original central-fibre restriction kernel in every degree.
Blueprint: tc-actual-central-kernel.tex. Surjectivity is a separate Serre step. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCOko
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a) [IsIntegral X]

/-- Actual original affine division and uniqueness glue on EVERY original open. -/
theorem centralFiber_line_division (E : ClosedProjectiveEmbedding f)
    {N : T.space.Modules} (b : LineBundleAtlas N) (V : T.space.Opens) (s : Γ(N,V))
    (hzero : (((Scheme.Modules.pullbackPushforwardAdjunction (centralFiberInclusion T)).unit.app N).val.app
      (op V) s) = 0) :
    ∃ u : Γ(N,V), T.space.presheaf.map V.leTop.op (tFun T.toLine) • u = s := by
  classical
  let r := tFun T.toLine
  let j := centralFiberInclusion T
  let P := (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj N)
  let η := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N
  let I := Σ i : b.I, {U : T.space.affineOpens // U.val ≤ V ⊓ b.opens i}
  let U (i : I) : T.space.Opens := i.2.val.val
  let k (i : I) : U i ⟶ V := homOfLE (i.2.property.trans inf_le_left)
  have hcover : V ≤ iSup U := by
    intro x hx
    obtain ⟨i,hxi⟩ := b.covers x
    obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ V ⊓ b.opens i from ⟨hx,hxi⟩)
    exact Opens.mem_iSup.mpr ⟨⟨i,⟨⟨W,hW⟩,hWV⟩⟩,hxW⟩
  have hlocal (i : I) : ∃ u : Γ(N,U i),
      T.space.presheaf.map (U i).leTop.op r • u = N.presheaf.map (k i).op s := by
    let l : U i ⟶ b.opens i.1 := homOfLE (i.2.property.trans inf_le_right)
    let e := bundleHomRestrictionIso N (SheafOfModules.unit T.space.ringCatSheaf) l (b.frame i.1)
    apply centralFiber_affine_line_division T i.2.val e (N.presheaf.map (k i).op s)
    have hn := PresheafOfModules.naturality_apply η.val (k i).op s
    change η.val.app (op (U i)) (N.presheaf.map (k i).op s) =
      P.presheaf.map (k i).op (η.val.app (op V) s) at hn
    have hz : η.val.app (op V) s = 0 := hzero
    rw [hz,map_zero] at hn
    exact hn
  choose u hu using hlocal
  have hcompat : TopCat.Presheaf.IsCompatible N.presheaf U u := by
    intro i q
    apply line_scalar_injective_on_open b r (totalCoordinate_regular_on_open T E) (U i ⊓ U q)
    change T.space.presheaf.map (U i ⊓ U q).leTop.op r •
      N.presheaf.map (Opens.infLELeft (U i) (U q)).op (u i) =
      T.space.presheaf.map (U i ⊓ U q).leTop.op r •
      N.presheaf.map (Opens.infLERight (U i) (U q)).op (u q)
    rw [← scalarSection_restrict,← scalarSection_restrict,hu i,hu q]
    simp only [← ConcreteCategory.comp_apply,← Functor.map_comp,← op_comp]
    rfl
  let S : TopCat.Sheaf AddCommGrpCat T.space := ⟨N.presheaf,N.isSheaf⟩
  obtain ⟨v,hv,_⟩ := S.existsUnique_gluing' U V k hcover u hcompat
  refine ⟨v,?_⟩
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp (hcover hx)
  refine ⟨U i,(k i).le,hxi,?_⟩
  rw [scalarSection_restrict,hv i,hu i]

/-- The actual original modulo-t quotient has no extra kernel, in EVERY degree. -/
theorem ker_centralFiberRestriction_eq_range_tMul (E : ClosedProjectiveEmbedding f) (m : ℕ) :
    LinearMap.ker (centralFiberRestriction T m) = LinearMap.range (tMul T m) := by
  apply le_antisymm
  · intro s hs
    let N := bundleTensorPower T.line m
    let η := ((Scheme.Modules.pullbackPushforwardAdjunction (centralFiberInclusion T)).unit.app N).val.app (op ⊤)
    let μ := (originalLinePullbackPowerIso (centralFiberInclusion T) T.atlas m).hom.val.app (op ⊤)
    have hres : μ (η s) = 0 := LinearMap.mem_ker.mp hs
    let e := originalLinePullbackPowerIso (centralFiberInclusion T) T.atlas m
    have hinj : Function.Injective μ := by
      intro u v he
      have hi := congrArg (fun z => e.inv.val.app (op ⊤) z) he
      change ((e.hom ≫ e.inv).val.app (op ⊤)) u =
        ((e.hom ≫ e.inv).val.app (op ⊤)) v at hi
      rw [e.hom_inv_id] at hi
      exact hi
    have hη : η s = 0 := hinj (hres.trans μ.hom.map_zero.symm)
    obtain ⟨u,hu⟩ := centralFiber_line_division T E (T.atlas.tensorPower m) ⊤ s hη
    refine ⟨u,?_⟩
    change tFun T.toLine • u = s
    have ht : (⊤ : T.space.Opens).leTop.op = 𝟙 (op ⊤) := Subsingleton.elim _ _
    have htop : T.space.presheaf.map (𝟙 (op ⊤)) (tFun T.toLine) = tFun T.toLine :=
      congrArg (fun z => z (tFun T.toLine)) (T.space.presheaf.map_id (op ⊤))
    rw [ht,htop] at hu
    exact hu
  · exact range_tMul_le_ker_centralFiberRestriction T m

/-- The actual modulo-t map to the entire central-fibre H0 is injective in EVERY degree. -/
theorem centralFiberQuotientRestriction_injective (E : ClosedProjectiveEmbedding f) (m : ℕ) :
    Function.Injective (centralFiberQuotientRestriction T m) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' (LinearMap.range (tMul T m))
    (centralFiberRestriction T m) (ker_centralFiberRestriction_eq_range_tMul T E m).symm

end SGPT.TestCurve.CentralFiber
