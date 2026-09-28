import PoincareConjecture.Proofs.M59.Mathlib.CubeTransport

set_option autoImplicit false

open scoped Topology unitInterval

open Topology

namespace GenLoop.HomotopyAlong

noncomputable def sphereHomotopyLift
    {N S X : Type*} [Finite N] [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    (q : C((N → I), S)) (hq : Function.Surjective q)
    (hfiber : ∀ v w, q v = q w ↔ v = w ∨
      (v ∈ Cube.boundary N ∧ w ∈ Cube.boundary N))
    {x y : X} {p : Path x y} {a : GenLoop N X x} {b : GenLoop N X y}
    (H : HomotopyAlong p a b) (f g : C(S, X))
    (ha : ∀ v, a v = f (q v)) (hb : ∀ v, b v = g (q v)) :
    {K : f.Homotopy g // ∀ t v, K (t, q v) = H.toHomotopy (t, v)} := by
  let Q : C(I × (N → I), I × S) :=
    ⟨fun v => (v.1, q v.2), continuous_fst.prodMk (q.continuous.comp continuous_snd)⟩
  have hQ : IsQuotientMap Q := by
    apply IsQuotientMap.of_surjective_continuous _ Q.continuous
    rintro ⟨t, s⟩
    obtain ⟨v, rfl⟩ := hq s
    exact ⟨(t, v), rfl⟩
  have hfactor : Function.FactorsThrough H.toHomotopy.toContinuousMap Q := by
    rintro ⟨t, v⟩ ⟨s, w⟩ heq
    have ht : t = s := congrArg Prod.fst heq
    have hvw : q v = q w := congrArg Prod.snd heq
    subst s
    rcases (hfiber v w).mp hvw with rfl | ⟨hv, hw⟩
    · rfl
    · exact (H.boundary_path t ⟨v, hv⟩).trans (H.boundary_path t ⟨w, hw⟩).symm
  let F := hQ.lift H.toHomotopy.toContinuousMap hfactor
  have hF (t : I) (v : N → I) : F (t, q v) = H.toHomotopy (t, v) :=
    ContinuousMap.congr_fun (hQ.lift_comp H.toHomotopy.toContinuousMap hfactor) (t, v)
  refine ⟨{ toContinuousMap := F, map_zero_left := ?_, map_one_left := ?_ }, hF⟩
  · intro s
    obtain ⟨v, rfl⟩ := hq s
    exact (hF 0 v).trans ((H.toHomotopy.apply_zero v).trans (ha v))
  · intro s
    obtain ⟨v, rfl⟩ := hq s
    exact (hF 1 v).trans ((H.toHomotopy.apply_one v).trans (hb v))

noncomputable def sphereHomotopy
    {N S X : Type*} [Finite N] [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    (q : C((N → I), S)) (hq : Function.Surjective q)
    (hfiber : ∀ v w, q v = q w ↔ v = w ∨
      (v ∈ Cube.boundary N ∧ w ∈ Cube.boundary N))
    {x y : X} {p : Path x y} {a : GenLoop N X x} {b : GenLoop N X y}
    (H : HomotopyAlong p a b) (f g : C(S, X))
    (ha : ∀ v, a v = f (q v)) (hb : ∀ v, b v = g (q v)) : f.Homotopy g :=
  (H.sphereHomotopyLift q hq hfiber f g ha hb).val

theorem sphereHomotopy_apply
    {N S X : Type*} [Finite N] [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    (q : C((N → I), S)) (hq : Function.Surjective q)
    (hfiber : ∀ v w, q v = q w ↔ v = w ∨
      (v ∈ Cube.boundary N ∧ w ∈ Cube.boundary N))
    {x y : X} {p : Path x y} {a : GenLoop N X x} {b : GenLoop N X y}
    (H : HomotopyAlong p a b) (f g : C(S, X))
    (ha : ∀ v, a v = f (q v)) (hb : ∀ v, b v = g (q v)) (t : I) (v : N → I) :
    H.sphereHomotopy q hq hfiber f g ha hb (t, q v) = H.toHomotopy (t, v) :=
  (H.sphereHomotopyLift q hq hfiber f g ha hb).property t v

theorem descend_sphere
    {N S X : Type*} [Finite N] [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    (q : C((N → I), S)) (hq : Function.Surjective q)
    (hfiber : ∀ v w, q v = q w ↔ v = w ∨
      (v ∈ Cube.boundary N ∧ w ∈ Cube.boundary N))
    {x y : X} {p : Path x y} {a : GenLoop N X x} {b : GenLoop N X y}
    (H : HomotopyAlong p a b) (f g : C(S, X))
    (ha : ∀ v, a v = f (q v)) (hb : ∀ v, b v = g (q v)) : f.Homotopic g :=
  ⟨H.sphereHomotopy q hq hfiber f g ha hb⟩

end GenLoop.HomotopyAlong
