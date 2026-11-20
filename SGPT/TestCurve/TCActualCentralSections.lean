import SGPT.TestCurve.TCActualCentralIntrinsicCech
import SGPT.TestCurve.TCActualCentralRestriction

/-! Genuine Cech-glued maps on EVERY actual central H0 section and literal
original section restriction equivariance, before quotient representation transport. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

private theorem powerSection_eq_of_pullOpenCoefficients
    {Y Z : Scheme.{0}} {M : Y.Modules} {N : Z.Modules}
    (b : LineBundleAtlas M) (b' : LineBundleAtlas N) (g : Z ⟶ Y) (m : ℕ)
    (s t : bundlePowerGlobalSections N m)
    (h : ∀ i j,
      Z.presheaf.map (homOfLE (inf_le_right : pullOpen b b' g i j ≤ b'.opens j)).op
        (atlasPowerGlobalCoefficients b' m j s) =
      Z.presheaf.map (homOfLE (inf_le_right : pullOpen b b' g i j ≤ b'.opens j)).op
        (atlasPowerGlobalCoefficients b' m j t)) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (F := (bundleTensorPower N m).val.presheaf) (bundleTensorPower N m).isSheaf
  intro x _hx
  obtain ⟨i,hi⟩ := b.covers (g x)
  obtain ⟨j,hj⟩ := b'.covers x
  refine ⟨pullOpen b b' g i j,le_top,⟨hi,hj⟩,?_⟩
  apply (((b'.frame j).tensorPower m).coefficients (homOfLE inf_le_right)).injective
  have hs := LocalBundleFrame.global_coefficients_restrict (b'.frame j) m
    (homOfLE (inf_le_right : pullOpen b b' g i j ≤ b'.opens j)) s
  have ht := LocalBundleFrame.global_coefficients_restrict (b'.frame j) m
    (homOfLE (inf_le_right : pullOpen b b' g i j ≤ b'.opens j)) t
  exact hs.trans ((h i j).trans ht.symm)

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- The actual original restriction reads SAME original coefficients in the genuine central frames. -/
theorem centralFiberRestriction_coefficients (m : ℕ)
    (s : SectionSpace T.structureMap T.line m) (i : T.atlas.I) :
    atlasPowerGlobalCoefficients (centralActionAtlas T) m i (centralFiberRestriction T m s) =
      (centralFiberInclusion T).app (T.atlas.opens i) (atlasPowerGlobalCoefficients T.atlas m i s) := by
  let j := centralFiberInclusion T
  let U := T.atlas.opens i
  let N := bundleTensorPower T.line m
  let P := (Scheme.Modules.pullback j).obj N
  let Q := bundleTensorPower (centralFiberLine T) m
  let e := originalLinePullbackPowerIso j T.atlas m
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N
  let su : Γ(N,U) := N.presheaf.map (homOfLE le_top).op s
  have heta := PresheafOfModules.naturality_apply eta.val (homOfLE (le_top : U ≤ ⊤)).op s
  change eta.val.app (op U) su = P.presheaf.map (homOfLE le_top).op (eta.val.app (op ⊤) s) at heta
  have he := PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op (eta.val.app (op ⊤) s)
  change e.hom.val.app (op (j ⁻¹ᵁ U))
      (P.presheaf.map (homOfLE le_top).op (eta.val.app (op ⊤) s)) =
    Q.presheaf.map (homOfLE le_top).op (e.hom.val.app (op ⊤) (eta.val.app (op ⊤) s)) at he
  change ((matePullbackFrame j (T.atlas.frame i)).tensorPower m).coefficients (𝟙 _)
    (Q.presheaf.map (homOfLE le_top).op
      (e.hom.val.app (op ⊤) (eta.val.app (op ⊤) s))) = _
  rw [← he,← heta]
  rw [originalLinePullbackPowerIso_coefficients]
  exact matePullbackFrame_coefficient_simple j ((T.atlas.frame i).tensorPower m) (𝟙 _) su

variable (Λ : GeomLinearization T)

/-- Genuine geometric map on arbitrary actual central H0, constructed by actual Cech gluing. -/
def centralActSection (c : ℂˣ) (m : ℕ) (s : centralFiberSectionSpace T m) :
    centralFiberSectionSpace T m :=
  Classical.choose (exists_cechPullSection (centralActionAtlas T) (centralActionAtlas T)
    (centralActAt T Λ.action c) (centralPhiAt T Λ c) (centralPhiAt_isCechHom T Λ c) m s)

/-- Exact original-frame reader of the actual Cech-glued central section. -/
theorem centralActSection_coefficients (c : ℂˣ) (m : ℕ)
    (s : centralFiberSectionSpace T m) (i j : T.atlas.I) :
    (centralFiberScheme T).presheaf.map (homOfLE
      (inf_le_right : pullOpen (centralActionAtlas T) (centralActionAtlas T)
        (centralActAt T Λ.action c) i j ≤ (centralActionAtlas T).opens j)).op
      (atlasPowerGlobalCoefficients (centralActionAtlas T) m j (centralActSection T Λ c m s)) =
    (centralActAt T Λ.action c).appLE ((centralActionAtlas T).opens i)
      (pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j)
      inf_le_left (atlasPowerGlobalCoefficients (centralActionAtlas T) m i s) *
        centralPhiAt T Λ c i j ^ m :=
  Classical.choose_spec (exists_cechPullSection (centralActionAtlas T) (centralActionAtlas T)
    (centralActAt T Λ.action c) (centralPhiAt T Λ c) (centralPhiAt_isCechHom T Λ c) m s) i j

private def totalAtlasPhiAt (c : ℂˣ) (i j : T.atlas.I) :
    Γ(T.space, pullOpen T.atlas T.atlas (Λ.action.actAt c) i j) :=
  Λ.phiAt c (.inl i) (.inl j)

private theorem originalActSection_coefficients (c : ℂˣ) (m : ℕ)
    (s : SectionSpace T.structureMap T.line m) (i j : T.atlas.I) :
    T.space.presheaf.map (homOfLE (inf_le_right :
      pullOpen T.atlas T.atlas (Λ.action.actAt c) i j ≤ T.atlas.opens j)).op
      (atlasPowerGlobalCoefficients T.atlas m j (Λ.actSection c m s)) =
    (Λ.action.actAt c).appLE (T.atlas.opens i)
      (pullOpen T.atlas T.atlas (Λ.action.actAt c) i j) inf_le_left
        (atlasPowerGlobalCoefficients T.atlas m i s) * totalAtlasPhiAt T Λ c i j ^ m :=
  Classical.choose_spec (exists_cechPullSection T.extAtlas T.extAtlas (Λ.action.actAt c)
    (Λ.phiAt c) (Λ.isCechHom_phiAt c) m s) (.inl i) (.inl j)

/-- Literal restriction equivariance of the genuine geometric central section map, ALL degrees.
No surjectivity, central lift, quotient representation or target equivariance premise. -/
theorem centralFiberRestriction_actSection (c : ℂˣ) (m : ℕ)
    (s : SectionSpace T.structureMap T.line m) :
    centralActSection T Λ c m (centralFiberRestriction T m s) =
      centralFiberRestriction T m (Λ.actSection c m s) := by
  apply powerSection_eq_of_pullOpenCoefficients (centralActionAtlas T) (centralActionAtlas T)
    (centralActAt T Λ.action c) m
  intro i j
  have hle : pullOpen (centralActionAtlas T) (centralActionAtlas T)
      (centralActAt T Λ.action c) i j ≤
      centralFiberInclusion T ⁻¹ᵁ pullOpen T.atlas T.atlas (Λ.action.actAt c) i j := by
    rintro x ⟨hx,hy⟩
    refine ⟨?_,hy⟩
    change (centralFiberInclusion T ≫ Λ.action.actAt c) x ∈ T.atlas.opens i
    rw [← centralActAt_inclusion]
    exact hx
  have hh := congrArg ((centralFiberInclusion T).appLE _ _ hle)
    (originalActSection_coefficients T Λ c m s i j)
  rw [appLE_of_res,map_mul,map_pow,appLE_appLE] at hh
  have htarget : pullOpen (centralActionAtlas T) (centralActionAtlas T)
      (centralActAt T Λ.action c) i j ≤
      (centralActAt T Λ.action c ≫ centralFiberInclusion T) ⁻¹ᵁ T.atlas.opens i := by
    rintro x ⟨hx,_hy⟩
    exact hx
  rw [appLE_congr_hom (centralActAt_inclusion T Λ.action c).symm _ _ _ htarget] at hh
  rw [centralActSection_coefficients,centralFiberRestriction_coefficients,
    centralFiberRestriction_coefficients]
  rw [centralPhiAt,Scheme.Hom.app_eq_appLE,Scheme.Hom.app_eq_appLE]
  rw [appLE_appLE,appLE_res]
  simpa only [totalAtlasPhiAt] using hh.symm

end SGPT.TestCurve.CentralFiber
