import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInverseChart
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Cube" => closedBall (0 : V3) 1

theorem ChartwisePLBall.exists_original_interior_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {B R : Set X}
    (b : ChartwisePLBall e B R)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) :
    ∃ Q : OpenPartialHomeomorph X V3,
      Q.source = interior B ∧ Q.target = ball (0 : V3) 1 ∧
      (∀ y, Q.symm y = b.map y) ∧
      (∀ x : B, Q x = (b.parametrization.symm x : V3)) ∧
      ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  classical
  let q : X → V3 := fun x => if hx : x ∈ B then b.parametrization.symm ⟨x,hx⟩ else 0
  have hqval (x : B) : q x = (b.parametrization.symm x : V3) := by
    simp only [q,dif_pos x.property]
  have hqCube (x : X) (hx : x ∈ B) : q x ∈ Cube := by
    rw [hqval ⟨x,hx⟩]
    exact (b.parametrization.symm ⟨x,hx⟩).property
  have hvalue (x : X) (hx : x ∈ B) : b.map (q x) = x := by
    rw [hqval ⟨x,hx⟩,b.map_eq]
    exact congrArg Subtype.val (b.parametrization.apply_symm_apply ⟨x,hx⟩)
  have hqc : ContinuousOn q B := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp b.parametrization.symm.continuous using 1
    funext x
    exact hqval x
  have hbi : InjOn b.map Cube := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (b.isEmbedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hsource (x : X) (hx : x ∈ interior B) : q x ∈ ball (0 : V3) 1 := by
    apply (b.mem_interior_iff ⟨q x,hqCube x (interior_subset hx)⟩).mp
    rw [←b.map_eq,hvalue x (interior_subset hx)]
    exact hx
  have htarget (y : V3) (hy : y ∈ ball (0 : V3) 1) : b.map y ∈ interior B :=
    b.image_ball.subset ⟨y,hy,rfl⟩
  let Q : OpenPartialHomeomorph X V3 := {
    toFun := q
    invFun := b.map
    source := interior B
    target := ball (0 : V3) 1
    map_source' := hsource
    map_target' := htarget
    left_inv' := fun x hx => hvalue x (interior_subset hx)
    right_inv' := by
      intro y hy
      exact hbi (hqCube _ (interior_subset (htarget y hy))) (ball_subset_closedBall hy)
        (hvalue _ (interior_subset (htarget y hy)))
    open_source := isOpen_interior
    open_target := isOpen_ball
    continuousOn_toFun := hqc.mono interior_subset
    continuousOn_invFun := b.piecewiseAffine.continuousOn.mono ball_subset_closedBall }
  refine ⟨Q,rfl,rfl,fun _ => rfl,hqval,?_⟩
  intro i
  let T := (e i).symm.trans Q
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  exact b.piecewiseAffine.locallyPiecewiseAffineOn_inverse_comp hbi (e i) (he i)
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) T.open_source)
    T.continuousOn
    (fun y hy => ball_subset_closedBall (Q.map_source hy.2))
    (fun _ hy => hy.1) (fun y hy => Q.left_inv hy.2)

end PoincareConjecture.M76
