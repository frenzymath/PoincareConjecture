import PoincareConjecture.Proofs.M59.Mathlib.CubeSphereHomotopy
import Mathlib.Topology.Maps.Proper.Basic








set_option autoImplicit false

open Topology
open scoped Topology unitInterval

noncomputable section

namespace PoincareConjecture.Proofs.M59



structure CubeBoundaryQuotient (N S : Type*) [TopologicalSpace S] where
  map : C((N → I), S)
  pole : S
  surjective : Function.Surjective map
  boundary_collapsed : ∀ v ∈ Cube.boundary N, map v = pole
  exact_fibers : ∀ v w, map v = map w ↔
    v = w ∨ (v ∈ Cube.boundary N ∧ w ∈ Cube.boundary N)

namespace CubeBoundaryQuotient

variable {N S X : Type*} [Finite N] [Nonempty N]
  [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
  (q : CubeBoundaryQuotient N S) {x : X}

omit [Finite N] [Nonempty N] in


theorem isQuotientMap : IsQuotientMap q.map :=
  IsQuotientMap.of_surjective_continuous q.surjective q.map.continuous

omit [Finite N] [Nonempty N] [T2Space S] in


theorem factorsThrough (g : GenLoop N X x) : Function.FactorsThrough g.val q.map := by
  intro v w h
  rcases (q.exact_fibers v w).mp h with rfl | ⟨hv, hw⟩
  · rfl
  · exact (GenLoop.boundary g v hv).trans (GenLoop.boundary g w hw).symm



def descend (g : GenLoop N X x) : C(S, X) :=
  q.isQuotientMap.lift g.val (q.factorsThrough g)

omit [Finite N] [Nonempty N] in


theorem descend_map (g : GenLoop N X x) (v : N → I) :
    q.descend g (q.map v) = g v :=
  ContinuousMap.congr_fun (q.isQuotientMap.lift_comp g.val (q.factorsThrough g)) v

omit [Finite N] in


theorem descend_pole (g : GenLoop N X x) : q.descend g q.pole = x := by
  let i : N := Classical.choice inferInstance
  have hz : (fun _ : N => (0 : I)) ∈ Cube.boundary N := ⟨i, Or.inl rfl⟩
  exact (congrArg (q.descend g) (q.boundary_collapsed _ hz).symm).trans
    ((q.descend_map g _).trans (GenLoop.boundary g _ hz))



def pullback (f : C(S, X)) : GenLoop N X (f q.pole) :=
  ⟨f.comp q.map, fun v hv => congrArg f (q.boundary_collapsed v hv)⟩

omit [Nonempty N] in


theorem exists_based_descend (f : C(S, X)) (p : Path (f q.pole) x) :
    ∃ g : GenLoop N X x, f.Homotopic (q.descend g) := by
  let g := GenLoop.boundaryTransport p (q.pullback f)
  refine ⟨g, (GenLoop.boundaryTransportHomotopy p (q.pullback f)).descend_sphere
    q.map q.surjective q.exact_fibers f (q.descend g) (fun _ => rfl) ?_⟩
  intro v
  exact (q.descend_map g v).symm

omit [Nonempty N] in


theorem descend_homotopic {f g : GenLoop N X x} (h : GenLoop.Homotopic f g) :
    (q.descend f).Homotopic (q.descend g) := by
  obtain ⟨H⟩ := h
  exact (GenLoop.HomotopyAlong.ofRel H).descend_sphere
    q.map q.surjective q.exact_fibers _ _
    (fun v => (q.descend_map f v).symm) (fun v => (q.descend_map g v).symm)

omit [Finite N] [Nonempty N] in


theorem continuous_descend : Continuous (q.descend : GenLoop N X x → C(S, X)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let Q := Prod.map (id : GenLoop N X x → GenLoop N X x) q.map
  have hproper : IsProperMap Q := isProperMap_id.prodMap q.map.continuous.isProperMap
  have hQ : IsQuotientMap Q := hproper.isClosedMap.isQuotientMap hproper.continuous
    (Function.Surjective.prodMap Function.surjective_id q.surjective)
  apply hQ.continuous_iff.mpr
  have heq : (fun v : GenLoop N X x × (N → I) =>
      q.descend v.1 (q.map v.2)) = fun v => v.1 v.2 := by
    funext v
    exact q.descend_map v.1 v.2
  change Continuous (fun v : GenLoop N X x × (N → I) => q.descend v.1 (q.map v.2))
  rw [heq]
  exact continuous_eval



def descendMap : C(GenLoop N X x, C(S, X)) := ⟨q.descend, q.continuous_descend⟩

omit [Finite N] [Nonempty N] in


theorem descend_const : q.descend (GenLoop.const : GenLoop N X x) =
    ContinuousMap.const S x := by
  ext z
  obtain ⟨v, rfl⟩ := q.surjective z
  exact q.descend_map GenLoop.const v

end CubeBoundaryQuotient

end PoincareConjecture.Proofs.M59
