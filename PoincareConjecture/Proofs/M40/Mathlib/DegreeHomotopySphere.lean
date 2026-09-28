import PoincareConjecture.Proofs.M40.Mathlib.DegreeHomotopy
import PoincareConjecture.Proofs.M02.HomotopyHomologyIso
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.Topology.HomotopyGroupHomeomorph
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

set_option autoImplicit false

noncomputable section

open CategoryTheory Set Metric
open scoped Topology unitInterval ContinuousMap

universe u v w

namespace PoincareConjecture.Proofs.M40.Topology

open M02 M02.Topology

theorem exists_cube_boundary_sphere_quotient_at (n : Nat)
    (s : sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1) :
    ∃ q : C((Fin (n + 1) → unitInterval),
        sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1),
      _root_.Topology.IsQuotientMap q ∧
      (∀ a b, q a = q b ↔ a = b ∨
        (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1)))) ∧
      q (fun _ => 0) = s := by
  obtain ⟨q, hq, hfiber⟩ := exists_cube_boundary_sphere_quotient n
  let b := q (fun _ => 0)
  let R := Submodule.reflection (Real ∙ (b.val - s.val))ᗮ
  let e : sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1 ≃ₜ
      sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1 :=
    R.toHomeomorph.subtype (fun z => by
      simp only [mem_sphere_zero_iff_norm]
      change ‖z‖ = 1 ↔ ‖R z‖ = 1
      rw [R.norm_map])
  have heb : e b = s := by
    apply Subtype.ext
    exact Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp b.property).trans
        (mem_sphere_zero_iff_norm.mp s.property).symm)
  let q' : C((Fin (n + 1) → unitInterval),
      sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1) :=
    ⟨fun z => e (q z), e.continuous.comp q.continuous⟩
  have hq' : _root_.Topology.IsQuotientMap q' :=
    .of_surjective_continuous
      (show Function.Surjective q' from e.surjective.comp hq.surjective) q'.continuous
  refine ⟨q', hq', ?_, heb⟩
  intro a b
  exact (e.injective.eq_iff).trans (hfiber a b)

theorem exists_homotopyEquiv_threeSphere_of_homology_bijective
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (eS : S ≃ₜ sphere (0 : EuclideanSpace Real (Fin 4)) 1)
    (f : C(S, S))
    (hbij : Function.Bijective
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of Int (ULift.{u} Int)) 3)) :
    ∃ e : S ≃ₕ S, e.toFun = f := by
  haveI : SimplyConnectedSpace (sphere (0 : EuclideanSpace Real (Fin 4)) 1) :=
    sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  haveI : PathConnectedSpace S :=
    eS.symm.surjective.pathConnectedSpace eS.symm.continuous
  have hlow (x : S) (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 2) :
      Subsingleton (HomotopyGroup.Pi k S x) := by
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · haveI : Subsingleton (HomotopyGroup.Pi 1
          (sphere (0 : EuclideanSpace Real (Fin 4)) 1) (eS x)) :=
        sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 1) (by simp) (eS x)
      exact (homotopyGroupHomeomorph 0 eS x).injective.subsingleton
    · haveI : Subsingleton (HomotopyGroup.Pi 2
          (sphere (0 : EuclideanSpace Real (Fin 4)) 1) (eS x)) :=
        sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 2) (by simp) (eS x)
      exact (homotopyGroupHomeomorph 1 eS x).injective.subsingleton
  obtain ⟨q, hq, hfiber⟩ := exists_cube_boundary_sphere_quotient 2
  let qX := (eS.symm : C(_, S)).comp q
  have hqX : _root_.Topology.IsQuotientMap qX :=
    .of_surjective_continuous (eS.symm.surjective.comp hq.surjective) qX.continuous
  have hXfiber (a b : Fin 3 → unitInterval) : qX a = qX b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin 3) ∧ b ∈ Cube.boundary (Fin 3)) :=
    (eS.symm.injective.eq_iff).trans (hfiber a b)
  obtain ⟨r, hr, hrfiber, hrbase⟩ :=
    exists_cube_boundary_sphere_quotient_at 2 (eS (f (qX (fun _ => 0))))
  let qY := (eS.symm : C(_, S)).comp r
  have hqY : _root_.Topology.IsQuotientMap qY :=
    .of_surjective_continuous (eS.symm.surjective.comp hr.surjective) qY.continuous
  have hYfiber (a b : Fin 3 → unitInterval) : qY a = qY b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin 3) ∧ b ∈ Cube.boundary (Fin 3)) :=
    (eS.symm.injective.eq_iff).trans (hrfiber a b)
  have hbase : f (qX (fun _ => 0)) = qY (fun _ => 0) := by
    change _ = eS.symm (r (fun _ => 0))
    rw [hrbase, eS.symm_apply_apply]
  apply exists_homotopyEquiv_of_cube_quotients 2 qX hqX hXfiber qY hqY hYfiber f hbase
  exact homotopyGroupPostcomp_bijective_of_homologyMap_bijective
    (TopCat.of S) (TopCat.of S) 1 (TopCat.ofHom f) (qX (fun _ => 0))
    (hlow _) (hlow _) hbij

theorem homologyMap_bijective_conjugate
    {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
    (eX : X ≃ₕ S) (eY : Y ≃ₕ S) (f : C(X, Y))
    (hbij : Function.Bijective
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of Int (ULift.{u} Int)) 3)) :
    Function.Bijective
      (SSet.homologyMap
        (TopCat.toSSet.map (TopCat.ofHom (eY.toFun.comp (f.comp eX.invFun))))
        (ModuleCat.of Int (ULift.{u} Int)) 3) := by
  let R := ModuleCat.of Int (ULift.{u} Int)
  haveI : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R 3) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  haveI : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom eX.invFun)) R 3) :=
    singularHomologyMap_isIso_of_homotopyEquiv
      (X := TopCat.of S) (Y := TopCat.of X) R 3 eX.symm
  haveI : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom eY.toFun)) R 3) :=
    singularHomologyMap_isIso_of_homotopyEquiv
      (X := TopCat.of Y) (Y := TopCat.of S) R 3 eY
  haveI : IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (eY.toFun.comp (f.comp eX.invFun)))) R 3) := by
    change IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom eX.invFun ≫ TopCat.ofHom f ≫
        TopCat.ofHom eY.toFun)) R 3)
    rw [Functor.map_comp, Functor.map_comp, SSet.homologyMap_comp,
      SSet.homologyMap_comp]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

theorem exists_homotopyEquiv_of_conjugate
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    {S : Type w} [TopologicalSpace S]
    (eX : X ≃ₕ S) (eY : Y ≃ₕ S) (f : C(X, Y))
    (he : ∃ e : S ≃ₕ S, e.toFun = eY.toFun.comp (f.comp eX.invFun)) :
    ∃ e : X ≃ₕ Y, e.toFun = f := by
  obtain ⟨e, he⟩ := he
  let E := eX.trans (e.trans eY.symm)
  have hEf : E.toFun.Homotopic f := by
    change (eY.invFun.comp (e.toFun.comp eX.toFun)).Homotopic f
    rw [he]
    change ((eY.invFun.comp eY.toFun).comp
      (f.comp (eX.invFun.comp eX.toFun))).Homotopic f
    exact (eY.left_inv.comp (ContinuousMap.Homotopic.refl _)).trans
      ((ContinuousMap.Homotopic.refl f).comp eX.left_inv)
  exact ⟨homotopyEquivOfHomotopic E f hEf.symm, rfl⟩

end PoincareConjecture.Proofs.M40.Topology
