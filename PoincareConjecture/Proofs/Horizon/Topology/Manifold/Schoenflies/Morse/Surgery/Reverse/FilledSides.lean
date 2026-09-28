import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.CommonDisk

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem filled_ball_subset_or_inter_eq_boundary
    (B F : E3 ≃ₜ E3)
    (havoid : Disjoint (F '' ball (0 : E3) 1) (B '' sphere (0 : E3) 1)) :
    F '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
      (B '' closedBall (0 : E3) 1) ∩ (F '' closedBall (0 : E3) 1) =
        (B '' sphere (0 : E3) 1) ∩ (F '' sphere (0 : E3) 1) := by
  have hBclosed : IsClosed (B '' closedBall (0 : E3) 1) :=
    B.isClosedMap _ isClosed_closedBall
  have hcover : F '' ball (0 : E3) 1 ⊆
      (B '' ball (0 : E3) 1) ∪ (B '' closedBall (0 : E3) 1)ᶜ := by
    intro y hy
    by_cases hball : y ∈ B '' ball (0 : E3) 1
    · exact Or.inl hball
    right
    rintro ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hx)
      (le_of_not_gt fun h => hball ⟨x, mem_ball_zero_iff.mpr h, rfl⟩)
    exact disjoint_left.mp havoid hy ⟨x, mem_sphere_zero_iff_norm.mpr hnorm, rfl⟩
  have hconn : IsPreconnected (F '' ball (0 : E3) 1) :=
    (convex_ball (0 : E3) 1).isPreconnected.image F F.continuous.continuousOn
  have hsep : Disjoint (B '' ball (0 : E3) 1) (B '' closedBall (0 : E3) 1)ᶜ :=
    disjoint_left.mpr fun _ hy hz => hz ((image_mono ball_subset_closedBall) hy)
  have hclosure (G : E3 ≃ₜ E3) :
      closure (G '' ball (0 : E3) 1) = G '' closedBall (0 : E3) 1 := by
    rw [← G.image_closure, closure_ball (0 : E3) (by norm_num : (1 : Real) ≠ 0)]
  rcases hconn.subset_or_subset (B.isOpenMap _ isOpen_ball) hBclosed.isOpen_compl
      hsep hcover with hin | hout
  · left
    simpa only [hclosure] using closure_mono hin
  right
  have hFoutside : F '' closedBall (0 : E3) 1 ⊆ (B '' ball (0 : E3) 1)ᶜ := by
    have h := closure_mono hout
    rwa [hclosure, closure_compl, ← B.image_interior,
      interior_closedBall (0 : E3) (by norm_num : (1 : Real) ≠ 0)] at h
  apply Subset.antisymm
  · rintro y ⟨hyB, hyF⟩
    have hsB : y ∈ B '' sphere (0 : E3) 1 := by
      obtain ⟨x, hx, rfl⟩ := hyB
      refine ⟨x, mem_sphere_zero_iff_norm.mpr ?_, rfl⟩
      exact le_antisymm (mem_closedBall_zero_iff.mp hx)
        (le_of_not_gt fun h => hFoutside hyF ⟨x, mem_ball_zero_iff.mpr h, rfl⟩)
    refine ⟨hsB, ?_⟩
    obtain ⟨x, hx, rfl⟩ := hyF
    refine ⟨x, mem_sphere_zero_iff_norm.mpr ?_, rfl⟩
    exact le_antisymm (mem_closedBall_zero_iff.mp hx)
      (le_of_not_gt fun h => disjoint_left.mp havoid
        ⟨x, mem_ball_zero_iff.mpr h, rfl⟩ hsB)
  · exact inter_subset_inter (image_mono sphere_subset_closedBall)
      (image_mono sphere_subset_closedBall)

theorem projection_mem_open_disk_of_mem_open_body
    {v : E3}
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (F : E3 ≃ₜ E3)
    (hbound : ∀ y ∈ F '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1)
    {y : E3} (hy : y ∈ F '' ball (0 : E3) 1) :
    (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1 := by
  let P := (Hemisphere.Plane v).orthogonalProjectionOnto
  have hsurj : Surjective P := fun x => ⟨x, by simp [P]⟩
  have hopen : IsOpen (P '' (F '' ball (0 : E3) 1)) :=
    P.isOpenMap hsurj _ (F.isOpenMap _ isOpen_ball)
  have hsub : P '' (F '' ball (0 : E3) 1) ⊆ A '' closedBall 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z ((image_mono ball_subset_closedBall) hz)
  have hmem := (interior_maximal hsub hopen) (mem_image_of_mem P hy)
  change P y ∈ interior (A.toHomeomorph '' closedBall 0 1) at hmem
  rwa [← A.toHomeomorph.image_interior,
    interior_closedBall (0 : Hemisphere.Plane v) (by norm_num : (1 : Real) ≠ 0)] at hmem

end Poincare.Manifold.Schoenflies.Reverse
