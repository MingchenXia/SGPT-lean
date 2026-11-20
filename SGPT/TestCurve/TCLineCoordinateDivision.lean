import SGPT.TestCurve.TCActualCentralZero

/-! Original line-section division by the actual central coordinate.
Blueprint: tc-line-coordinate-division.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open SGPT.LineBundle SGPT.TestCurve.TCEnc
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

/-- Literal global scalar multiplication commutes with every true module restriction. -/
theorem scalarSection_restrict {Y : Scheme.{0}} (N : Y.Modules) (r : Γ(Y, ⊤))
    {U V : Y.Opens} (k : V ⟶ U) (s : Γ(N,U)) :
    N.presheaf.map k.op (Y.presheaf.map U.leTop.op r • s) =
      Y.presheaf.map V.leTop.op r • N.presheaf.map k.op s := by
  change N.val.map k.op (_ • s) = _
  rw [N.val.map_smul]
  congr 1
  change Y.presheaf.map k.op (Y.presheaf.map U.leTop.op r) = _
  rw [← CommRingCat.comp_apply,← Functor.map_comp]
  rfl

/-- Actual all-open regularity gives all-open multiplication injectivity on ANY true line. -/
theorem line_scalar_injective_on_open {Y : Scheme.{0}} {N : Y.Modules}
    (b : LineBundleAtlas N) (r : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, Y.presheaf.map U.leTop.op r ∈ nonZeroDivisors Γ(Y,U))
    (V : Y.Opens) :
    Function.Injective (fun s : Γ(N,V) => Y.presheaf.map V.leTop.op r • s) := by
  intro s t h
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨i,hxi⟩ := b.covers x
  let W := V ⊓ b.opens i
  let k : W ⟶ V := homOfLE inf_le_left
  let l : W ⟶ b.opens i := homOfLE inf_le_right
  refine ⟨W,inf_le_left,⟨hx,hxi⟩,?_⟩
  apply ((b.frame i).coefficients l).injective
  have hr := congrArg (fun u => (b.frame i).coefficients l (N.presheaf.map k.op u)) h
  rw [scalarSection_restrict,scalarSection_restrict] at hr
  have hs : (b.frame i).coefficients l (Y.presheaf.map W.leTop.op r • N.presheaf.map k.op s) =
      Y.presheaf.map W.leTop.op r * (show Γ(Y,W) from (b.frame i).coefficients l (N.presheaf.map k.op s)) :=
    ((b.frame i).coefficients l).map_smul _ _
  have ht : (b.frame i).coefficients l (Y.presheaf.map W.leTop.op r • N.presheaf.map k.op t) =
      Y.presheaf.map W.leTop.op r * (show Γ(Y,W) from (b.frame i).coefficients l (N.presheaf.map k.op t)) :=
    ((b.frame i).coefficients l).map_smul _ _
  rw [hs,ht] at hr
  exact (mul_cancel_left_mem_nonZeroDivisors (hreg W)).mp hr

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- Actual pullback zero on a genuinely framed affine open produces original t-division. -/
theorem centralFiber_affine_line_division {N : T.space.Modules}
    (U : T.space.affineOpens) (e : LocalBundleFrame N U.val) (s : Γ(N,U.val))
    (hzero : (((Scheme.Modules.pullbackPushforwardAdjunction (centralFiberInclusion T)).unit.app N).val.app
      (op U.val) s) = 0) :
    ∃ u : Γ(N,U.val), T.space.presheaf.map U.val.leTop.op (tFun T.toLine) • u = s := by
  let j := centralFiberInclusion T
  have hc := matePullbackFrame_coefficient_simple j e (𝟙 U.val) s
  rw [hzero,map_zero] at hc
  have hk : e.coefficients (𝟙 U.val) s ∈ RingHom.ker (j.app U.val).hom := hc.symm
  rw [centralFiberInclusion_affine_kernel,Ideal.mem_span_singleton] at hk
  obtain ⟨q,hq⟩ := hk
  refine ⟨(e.coefficients (𝟙 U.val)).symm q,?_⟩
  apply (e.coefficients (𝟙 U.val)).injective
  have he : e.coefficients (𝟙 U.val)
      (T.space.presheaf.map U.val.leTop.op (tFun T.toLine) • (e.coefficients (𝟙 U.val)).symm q) =
      T.space.presheaf.map U.val.leTop.op (tFun T.toLine) *
        (show Γ(T.space,U.val) from e.coefficients (𝟙 U.val) ((e.coefficients (𝟙 U.val)).symm q)) :=
    (e.coefficients (𝟙 U.val)).map_smul _ _
  exact he.trans ((congrArg (fun z => T.space.presheaf.map U.val.leTop.op (tFun T.toLine) * z)
    ((e.coefficients (𝟙 U.val)).apply_symm_apply q)).trans hq.symm)

end SGPT.TestCurve.CentralFiber
