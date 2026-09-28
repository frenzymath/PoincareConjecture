import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAnnulusRimCircles
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedRimCircleModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentParametrization








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_original_annulus_rim_models
    {ι κ α E : Type*} [Fintype ι] [Fintype κ] [Unique κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hdim : Fintype.card ι = 2)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hfi : InjOn F (latticeHandleDomain ι κ L))
    (J B : SimplicialComplex ℝ E) (hB : B.faces.Finite)
    (hBdim : ∀ t ∈ B.faces, t.card ≤ 2)
    (hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2))
    (hBmark : B.space = F '' (hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))) :
    ∃ (C : Bool → SimplicialComplex ℝ E)
      (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (C i).space),
      (∀ i, C i ≤ B ∧ (C i).faces.Finite ∧ (gamma i).IsFinitePL ∧
        (C i).space = F '' (hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ {fun _ : κ => if i then (3 / 2 : ℝ) else -(3 / 2 : ℝ)}))) ∧
      (∀ t, t ∈ B.faces ↔ ∃ i, t ∈ (C i).faces) := by
  classical
  obtain ⟨P,hP⟩ := b.exists_marked_image_homeomorph (by omega) F hF hfi
    (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)) subset_rfl J.space hJmark
  obtain ⟨S,H,hS,hdis,hcover⟩ := exists_marked_annulus_rim_circles hdim P
  have hfull : (Subtype.val : J.space → E) ''
      (P '' {x | (x : (ι → ℝ) × (κ → ℝ)).2 ∈ sphere (0 : κ → ℝ) (3 / 2)}) = B.space := by
    rw [hBmark]
    apply Subset.antisymm
    · rintro y ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨_,⟨x,⟨x.property.1,hx⟩,rfl⟩,(hP x).symm⟩
    · rintro y ⟨_,⟨x,hx,rfl⟩,rfl⟩
      let z : sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2) :=
        ⟨x,hx.1,sphere_subset_closedBall hx.2⟩
      exact ⟨P z,⟨z,hx.2,rfl⟩,hP z⟩
  obtain ⟨C,gamma,hC,hfaces⟩ := B.exists_marked_finitePL_circle_models
    hB hBdim S H hdis (hcover.trans hfull)
  refine ⟨C,gamma,?_,hfaces⟩
  intro i
  refine ⟨(hC i).1,(hC i).2.1,(hC i).2.2.2,?_⟩
  rw [(hC i).2.2.1,hS i]
  simp only [hP]
  apply Subset.antisymm
  · rintro y ⟨x,rfl⟩
    exact ⟨_,⟨((x : ι → ℝ),fun _ : κ => if i then (3 / 2 : ℝ) else -(3 / 2 : ℝ)),
      ⟨x.property,rfl⟩,rfl⟩,rfl⟩
  · rintro y ⟨_,⟨x,⟨hx,hend⟩,rfl⟩,rfl⟩
    refine ⟨⟨x.1,hx⟩,?_⟩
    apply congrArg (F ∘ hamiltonMarkedProjection ι κ L)
    exact Prod.ext rfl hend.symm

end PoincareConjecture.M76
