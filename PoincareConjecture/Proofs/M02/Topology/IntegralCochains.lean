import PoincareConjecture.Proofs.M02.Topology.IntegralChainCoordinates
import PoincareConjecture.Proofs.M02.Topology.SingularOneCocycles
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped BigOperators Simplicial

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def integralDualComplex (C : ChainComplex (ModuleCat.{u} Int) Nat) :
    CochainComplex (ModuleCat.{u} Int) Nat :=
  C.linearYonedaObj Int integralCoefficient.{u}

def integralDualMap {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : C ⟶ D) : integralDualComplex D ⟶ integralDualComplex C :=
  let F := ((linearYoneda Int (ModuleCat.{u} Int)).obj integralCoefficient).rightOp
  (HomologicalComplex.unopFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat)).map
    ((F.mapHomologicalComplex (ComplexShape.down Nat)).map f).op

def integralDualHomotopy {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    {f g : C ⟶ D} (H : Homotopy f g) :
    Homotopy (integralDualMap f) (integralDualMap g) :=
  let F := ((linearYoneda Int (ModuleCat.{u} Int)).obj integralCoefficient).rightOp
  (F.mapHomotopy H).unop

def integralDualHomotopyEquiv {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (e : HomotopyEquiv C D) :
    HomotopyEquiv (integralDualComplex D) (integralDualComplex C) where
  hom := integralDualMap e.hom
  inv := integralDualMap e.inv
  homotopyHomInvId := by
    simpa [integralDualMap, integralDualComplex, ChainComplex.linearYonedaObj,
      HomologicalComplex.unopFunctor] using! integralDualHomotopy e.homotopyInvHomId
  homotopyInvHomId := by
    simpa [integralDualMap, integralDualComplex, ChainComplex.linearYonedaObj,
      HomologicalComplex.unopFunctor] using! integralDualHomotopy e.homotopyHomInvId

def IntegralDegreewiseSplit
    (S : ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat)) : Prop :=
  forall n : Nat,
    Exists fun r : S.X₂.X n ⟶ S.X₁.X n =>
    Exists fun s : S.X₃.X n ⟶ S.X₂.X n =>
      S.f.f n ≫ r = 𝟙 _ ∧ s ≫ S.g.f n = 𝟙 _ ∧
        r ≫ S.f.f n + S.g.f n ≫ s = 𝟙 _

def integralDualSequence
    (S : ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat)) :
    ShortComplex (CochainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralDualMap S.g) (integralDualMap S.f) (by
    ext n phi
    change S.X₃.X n ⟶ integralCoefficient at phi
    change S.f.f n ≫ S.g.f n ≫ phi = 0
    rw [← Category.assoc]
    have h := congrArg (fun f => f.f n) S.zero
    change S.f.f n ≫ S.g.f n = 0 at h
    rw [h, zero_comp])

theorem integralDualSequence_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat))
    (hS : IntegralDegreewiseSplit S) : (integralDualSequence S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  obtain ⟨r, s, hfr, hsg, hid⟩ := hS n
  let T := (integralDualSequence S).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.up Nat) n)
  let e : T.Splitting :=
    { r := ModuleCat.ofHom (Linear.leftComp Int integralCoefficient s)
      s := ModuleCat.ofHom (Linear.leftComp Int integralCoefficient r)
      f_r := by
        ext phi
        change S.X₃.X n ⟶ integralCoefficient at phi
        change s ≫ S.g.f n ≫ phi = phi
        rw [← Category.assoc, hsg, Category.id_comp]
      s_g := by
        ext phi
        change S.X₁.X n ⟶ integralCoefficient at phi
        change S.f.f n ≫ r ≫ phi = phi
        rw [← Category.assoc, hfr, Category.id_comp]
      id := by
        ext phi
        change S.X₂.X n ⟶ integralCoefficient at phi
        change S.g.f n ≫ s ≫ phi + r ≫ S.f.f n ≫ phi = phi
        rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
          add_comm, hid, Category.id_comp] }
  exact e.shortExact

abbrev integralCochains (X : Type u) [TopologicalSpace X] :
    CochainComplex (ModuleCat.{u} Int) Nat :=
  integralDualComplex (integralChains X)

abbrev integralCohomology (X : Type u) [TopologicalSpace X] (q : Nat) :
    ModuleCat.{u} Int :=
  (integralCochains X).homology q

variable {X : Type u} [TopologicalSpace X]

abbrev integralRelativeCochains (A : Set X) :
    CochainComplex (ModuleCat.{u} Int) Nat :=
  integralDualComplex (integralRelativeChains A)

abbrev integralRelativeCohomology (A : Set X) (q : Nat) : ModuleCat.{u} Int :=
  (integralRelativeCochains A).homology q

abbrev integralSupportCohomology (K : Set X) (q : Nat) : ModuleCat.{u} Int :=
  integralRelativeCohomology Kᶜ q

def integralSupportCohomologyPushforward {K L : Set X} (hKL : K ⊆ L) (q : Nat) :
    integralSupportCohomology K q ⟶ integralSupportCohomology L q :=
  HomologicalComplex.homologyMap
    (integralDualMap (integralRelativeMap (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from
        fun _ hx h => hx (hKL h)))) q

def integralHomologyCohomologyPairing
    (C : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) :
    C.homology n →ₗ[Int]
      ((integralDualComplex C).homology n →ₗ[Int] ULift.{u} Int) := by
  let S := C.sc n
  let T := (integralDualComplex C).sc n
  let Z := S.moduleCatLeftHomologyData.K
  let W := T.moduleCatLeftHomologyData.K
  let B : Submodule Int Z := LinearMap.range S.moduleCatToCycles
  let D : Submodule Int W := LinearMap.range T.moduleCatToCycles
  letI : Module Int (Z ⧸ B) := Submodule.Quotient.module B
  letI : Module Int (W ⧸ D) := Submodule.Quotient.module D
  let E : Z →ₗ[Int] (W →ₗ[Int] ULift.{u} Int) :=
    { toFun := fun z =>
        { toFun := fun phi => (show C.X n ⟶ integralCoefficient from phi.val) z.val
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := by
        intro z w
        apply LinearMap.ext
        intro phi
        exact (show C.X n ⟶ integralCoefficient from phi.val).hom.map_add
          (show C.X n from z.val) (show C.X n from w.val)
      map_smul' := by
        intro a z
        apply LinearMap.ext
        intro phi
        exact (show C.X n ⟶ integralCoefficient from phi.val).hom.map_smul
          a (show C.X n from z.val) }
  have hD (z : Z) : D ≤ LinearMap.ker (E z) := by
    rintro _ ⟨psi, rfl⟩
    change (show C.X ((ComplexShape.up Nat).prev n) ⟶ integralCoefficient from psi)
      (C.d n ((ComplexShape.up Nat).prev n) z.val) = 0
    have hz : C.d n ((ComplexShape.up Nat).prev n) z.val = 0 := z.property
    rw [hz, map_zero]
  let ED : Z →ₗ[Int] (W ⧸ D →ₗ[Int] ULift.{u} Int) :=
    { toFun := fun z => D.liftQ (E z) (hD z)
      map_add' := by
        intro z w
        apply D.linearMap_qext
        apply LinearMap.ext
        intro phi
        exact congrArg (fun f : W →ₗ[Int] ULift.{u} Int => f phi) (E.map_add z w)
      map_smul' := by
        intro a z
        apply D.linearMap_qext
        apply LinearMap.ext
        intro phi
        exact congrArg (fun f : W →ₗ[Int] ULift.{u} Int => f phi) (E.map_smul a z) }
  have hB : B ≤ LinearMap.ker ED := by
    rintro _ ⟨c, rfl⟩
    apply D.linearMap_qext
    apply LinearMap.ext
    intro phi
    change (show C.X n ⟶ integralCoefficient from phi.val)
      (C.d ((ComplexShape.down Nat).prev n) n c) = 0
    have hp : C.d ((ComplexShape.down Nat).prev n) n ≫
        (show C.X n ⟶ integralCoefficient from phi.val) = 0 := phi.property
    exact congrArg (fun f => f c) hp
  let EQ : Z ⧸ B →ₗ[Int] (W ⧸ D →ₗ[Int] ULift.{u} Int) := B.liftQ ED hB
  exact (EQ.compl₂ T.moduleCatHomologyIso.toLinearEquiv.toLinearMap).comp
    S.moduleCatHomologyIso.toLinearEquiv.toLinearMap

theorem integral_cohomology_one_isZero
    (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X] :
    IsZero (integralCohomology X 1) := by
  classical
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro phi hphi
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let C := integralChains X
  let ph : C.X 1 ⟶ integralCoefficient := phi
  have hprev : (ComplexShape.up Nat).prev 1 = 0 :=
    (ComplexShape.up Nat).prev_eq' (show (ComplexShape.up Nat).Rel 0 1 from rfl)
  have hnext : (ComplexShape.up Nat).next 1 = 2 :=
    (ComplexShape.up Nat).next_eq' (show (ComplexShape.up Nat).Rel 1 2 from rfl)
  change (integralCochains X).d 1 ((ComplexShape.up Nat).next 1) phi = 0 at hphi
  rw [hnext] at hphi
  have hclosed : C.d 2 1 ≫ ph = 0 := hphi
  let f : Y.obj (Opposite.op (SimplexCategory.mk 1)) -> ULift.{u} Int :=
    fun s => ph (Y.ιChainComplex (R := integralCoefficient.{u}) s (ULift.up 1))
  have hf (s : Y.obj (Opposite.op (SimplexCategory.mk 2))) :
      (∑ j : Fin 3, ((-1 : Int) ^ j.val) • f (Y.δ j s)) = 0 := by
    let ev : (integralCoefficient.{u} ⟶ (Y.chainComplex integralCoefficient).X 1) →+
        ULift.{u} Int :=
      { toFun := fun p => ph.hom (p.hom (ULift.up 1))
        map_zero' := ph.hom.map_zero
        map_add' := fun p q => ph.hom.map_add _ _ }
    have h := congrArg ev (SSet.ιChainComplex_d Y integralCoefficient s)
    have hz : ev (Y.ιChainComplex s ≫ (Y.chainComplex integralCoefficient).d 2 1) = 0 := by
      exact congrArg (fun p : C.X 2 ⟶ integralCoefficient =>
        p (Y.ιChainComplex (R := integralCoefficient.{u}) s (ULift.up 1))) hclosed
    rw [hz, map_sum] at h
    simpa only [map_zsmul, ev, f] using! h.symm
  obtain ⟨g, hg⟩ := singular_one_cocycle_is_coboundary (TopCat.of X) f hf
  let G : C(integralSimplex 0, X) -> ULift.{u} Int := fun s =>
    g (((TopCat.of X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk 0))).symm s)
  let psi : C.X 0 ⟶ integralCoefficient := ModuleCat.ofHom
    ((Finsupp.lsum Int (fun s : C(integralSimplex 0, X) =>
      (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight (G s))).comp
        (integralChainCoordinates X 0).toLinearMap)
  have hpsi (s : C(integralSimplex 0, X)) :
      psi (integralSingularGenerator s (ULift.up 1)) = G s := by
    change (Finsupp.lsum Int (fun t : C(integralSimplex 0, X) =>
      (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight (G t)))
        (integralChainCoordinates X 0 (integralSingularGenerator s (ULift.up 1))) = G s
    rw [integralChainCoordinates_generator]
    simp
  have hgen (s : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
      psi (Y.ιChainComplex (R := integralCoefficient.{u}) s (ULift.up 1)) = g s := by
    simpa [Y, G, integralSingularGenerator] using!
      hpsi ((TopCat.of X).toSSetObjEquiv _ s)
  have hedge (s : C(integralSimplex 1, X)) :
      (C.d 1 0 ≫ psi) (integralSingularGenerator s (ULift.up 1)) =
        ph (integralSingularGenerator s (ULift.up 1)) := by
    let t := ((TopCat.of X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm s
    have hs := hg t
    change f t = g (Y.δ 0 t) - g (Y.δ 1 t) at hs
    let ev : (integralCoefficient.{u} ⟶ (Y.chainComplex integralCoefficient).X 0) →+
        ULift.{u} Int :=
      { toFun := fun p => psi.hom (p.hom (ULift.up 1))
        map_zero' := psi.hom.map_zero
        map_add' := fun p q => psi.hom.map_add _ _ }
    have hev (r : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
        ev (Y.ιChainComplex r) = g r := hgen r
    change ev (Y.ιChainComplex t ≫ (Y.chainComplex integralCoefficient).d 1 0) = f t
    rw [SSet.ιChainComplex_d, map_sum]
    simpa [map_zsmul, Fin.sum_univ_succ, hev, sub_eq_add_neg] using hs.symm
  have hlinear : C.d 1 0 ≫ psi = ph := by
    apply ConcreteCategory.hom_ext
    intro c
    rw [integral_chain_finite_representation 1 c]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro s _
    let a := integralChainCoordinates X 1 c s
    have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
      apply ULift.ext
      simp
    change (C.d 1 0 ≫ psi) (integralSingularGenerator s a) =
      ph (integralSingularGenerator s a)
    rw [ha]
    change (C.d 1 0 ≫ psi).hom
      ((integralSingularGenerator s).hom (a.down • (ULift.up 1 : ULift.{u} Int))) =
        ph.hom ((integralSingularGenerator s).hom
          (a.down • (ULift.up 1 : ULift.{u} Int)))
    rw [(integralSingularGenerator s).hom.map_smul, (C.d 1 0 ≫ psi).hom.map_smul,
      ph.hom.map_smul]
    rw [hedge]
  change Exists fun p : (integralCochains X).X ((ComplexShape.up Nat).prev 1) =>
    (integralCochains X).d ((ComplexShape.up Nat).prev 1) 1 p = phi
  rw [hprev]
  exact ⟨psi, hlinear⟩

end PoincareConjecture.Proofs.M02.Topology
