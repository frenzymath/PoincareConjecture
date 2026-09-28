import PoincareConjecture.Proofs.M02.HurewiczInjectivity
import PoincareConjecture.Proofs.M02.HurewiczRepresentatives
import PoincareConjecture.Proofs.M02.Topology.CubeHomotopyLifting

set_option autoImplicit false

noncomputable section

open CategoryTheory Set
open scoped Topology unitInterval ContinuousMap

universe u v w

namespace PoincareConjecture.Proofs.M40.Topology

open M02 M02.Topology

theorem homotopyGroupPostcomp_bijective_of_homologyMap_bijective
    (X Y : TopCat.{u}) [PathConnectedSpace X] [PathConnectedSpace Y]
    (n : Nat) (f : X ⟶ Y) (x : X)
    (hX : ∀ k : Nat, 1 ≤ k → k ≤ n + 1 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hY : ∀ k : Nat, 1 ≤ k → k ≤ n + 1 →
      Subsingleton (HomotopyGroup.Pi k Y (f x)))
    (hbij : Function.Bijective
      (SSet.homologyMap (TopCat.toSSet.map f)
        (ModuleCat.of Int (ULift.{u} Int)) (n + 2))) :
    Function.Bijective (homotopyGroupPostcomp (n + 1) f.hom x) := by
  let R := ModuleCat.of Int (ULift.{u} Int)
  let F := SSet.homologyMap (TopCat.toSSet.map f) R (n + 2)
  let HX := homotopyGroupSingularHomologyMap R X (n + 1) x
  let HY := homotopyGroupSingularHomologyMap R Y (n + 1) (f x)
  have hHX := homotopyGroupSingularHomologyMap_injective X x n hX
  have hHY := homotopyGroupSingularHomologyMap_injective Y (f x) n hY
  have hsurj := homotopyGroupSingularHomologyMap_surjective X x (n + 1) hX
  letI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).mpr hbij
  have hnatural (a : HomotopyGroup.Pi (n + 2) X x) :
      HX a ≫ F = HY (homotopyGroupPostcomp (n + 1) f.hom x a) := by
    exact homotopyGroupSingularHomologyMap_naturality R f (n + 1) x a
  constructor
  · intro a b hab
    apply hHX
    apply (cancel_mono F).mp
    exact (hnatural a).trans ((congrArg HY hab).trans (hnatural b).symm)
  · intro b
    obtain ⟨a, ha⟩ := hsurj (HY b ≫ inv F)
    change HX a = HY b ≫ inv F at ha
    refine ⟨a, hHY ?_⟩
    change HY (homotopyGroupPostcomp (n + 1) f.hom x a) = HY b
    rw [← hnatural, ha, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem homotopyRel_of_cube_quotient
    {S : Type u} [TopologicalSpace S]
    {Y : Type v} [TopologicalSpace Y]
    (n : Nat) (q : C((Fin (n + 1) → unitInterval), S))
    (hq : _root_.Topology.IsQuotientMap q)
    (hfiber : ∀ a b, q a = q b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))))
    (f g : C(S, Y))
    (H : (f.comp q).HomotopyRel (g.comp q) (Cube.boundary (Fin (n + 1)))) :
    Nonempty (f.HomotopyRel g {q (fun _ => 0)}) := by
  let HC : C((Fin (n + 1) → unitInterval), C(unitInterval, Y)) :=
    (H.toHomotopy.toContinuousMap.comp
      ⟨Prod.swap, continuous_swap⟩).curry
  have hfactor : Function.FactorsThrough HC q := by
    intro a b hab
    rcases (hfiber a b).mp hab with rfl | ⟨ha, hb⟩
    · rfl
    · ext t
      exact (H.eq_fst t ha).trans
        ((congrArg f hab).trans (H.eq_fst t hb).symm)
  let G := hq.lift HC hfactor
  have hG (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
      G (q z) t = H (t, z) :=
    congrArg (fun a : C(unitInterval, Y) => a t)
      (ContinuousMap.congr_fun (hq.lift_comp HC hfactor) z)
  refine ⟨{ toFun := fun p => G p.2 p.1
            continuous_toFun := (G.continuous.comp continuous_snd).eval continuous_fst
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro s
    obtain ⟨z, rfl⟩ := hq.surjective s
    exact (hG z 0).trans (H.apply_zero z)
  · intro s
    obtain ⟨z, rfl⟩ := hq.surjective s
    exact (hG z 1).trans (H.apply_one z)
  · intro t s hs
    have hs' : s = q (fun _ => 0) := hs
    rw [hs']
    exact (hG _ t).trans (H.eq_fst t ⟨0, Or.inl rfl⟩)

theorem exists_homotopyEquiv_of_cube_quotients
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (n : Nat)
    (qX : C((Fin (n + 1) → unitInterval), X))
    (hqX : _root_.Topology.IsQuotientMap qX)
    (hXfiber : ∀ a b, qX a = qX b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))))
    (qY : C((Fin (n + 1) → unitInterval), Y))
    (hqY : _root_.Topology.IsQuotientMap qY)
    (hYfiber : ∀ a b, qY a = qY b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))))
    (f : C(X, Y))
    (hbase : f (qX (fun _ => 0)) = qY (fun _ => 0))
    (hbij : Function.Bijective (homotopyGroupPostcomp n f (qX (fun _ => 0)))) :
    ∃ e : X ≃ₕ Y, e.toFun = f := by
  let zero : Fin (n + 1) → unitInterval := fun _ => 0
  have hz : zero ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  let a : GenLoop (Fin (n + 1)) Y (f (qX zero)) :=
    ⟨qY, fun z hz' =>
      ((hYfiber z zero).mpr (Or.inr ⟨hz', hz⟩)).trans hbase.symm⟩
  obtain ⟨b, hb⟩ := hbij.2 (Quotient.mk _ a)
  obtain ⟨b, rfl⟩ := Quotient.exists_rep b
  obtain ⟨H⟩ : GenLoop.Homotopic (genLoopPostcomp n f (qX zero) b) a :=
    Quotient.exact hb
  obtain ⟨g, hgcomp, hgbase⟩ := exists_genLoop_quotient_map n qY hqY hYfiber b
  have hfg : (f.comp g).comp qY = f.comp b.val := by
    rw [ContinuousMap.comp_assoc, hgcomp]
  obtain ⟨R⟩ := homotopyRel_of_cube_quotient n qY hqY hYfiber
    (f.comp g) (ContinuousMap.id Y)
    (H.cast hfg.symm (by rfl))
  have hgfbase : (g.comp f) (qX zero) = qX zero := by
    change g (f (qX zero)) = qX zero
    rw [hbase]
    exact hgbase
  let L : (f.comp (g.comp f)).Homotopy f :=
    (R.toHomotopy.compContinuousMap f).cast (by rfl) (by ext x; rfl)
  have hLfixed (t : unitInterval) : L (t, qX zero) = f (qX zero) := by
    change R (t, f (qX zero)) = f (qX zero)
    rw [hbase]
    exact (R.eq_fst t (Set.mem_singleton _)).trans
      ((congrArg f hgbase).trans hbase)
  exact ⟨{ toFun := f
           invFun := g
           left_inv := homotopic_of_cube_quotient_postcomp_injective
             n qX hqX hXfiber f hbij.1 (g.comp f) hgfbase L hLfixed
           right_inv := ⟨R.toHomotopy⟩ }, rfl⟩

def homotopyEquivOfHomotopic
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (e : X ≃ₕ Y) (f : C(X, Y)) (h : f.Homotopic e.toFun) : X ≃ₕ Y where
  toFun := f
  invFun := e.invFun
  left_inv := ((ContinuousMap.Homotopic.refl e.invFun).comp h).trans e.left_inv
  right_inv := (h.comp (ContinuousMap.Homotopic.refl e.invFun)).trans e.right_inv

end PoincareConjecture.Proofs.M40.Topology
