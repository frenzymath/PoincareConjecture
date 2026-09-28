import PoincareConjecture.Proofs.M76.Dehn.OriginalRimFrontier
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {G M ι : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem Stage.exists_original_marked_rim_model (st : Stage e S f r C)
    (hSD : S.space = D) {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    (Fmark : Set M) (hFmark : Fmark ⊆ frontier R) (gamma : C(Q, Fmark))
    (hpair : ∀ x : Q, f x.val = (gamma x : M))
    (F : st.Carrier → G)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (st.charts i).symm) (st.charts i).target)
    (K A : SimplicialComplex ℝ G) (J : N ≃ₜ K.space)
    (hJF : ∀ x : N, (J x : G) = F x) (hAs : A.space = F '' frontier N) :
    FinitePiecewiseAffineOn (F ∘ st.sourceMap) Q ∧
      (F ∘ st.sourceMap) '' Q ⊆ A.space ∧
      ∃ j : C((F ∘ st.sourceMap) '' Q, Fmark),
        ∀ x : Q, j ⟨F (st.sourceMap x),
          mem_image_of_mem (F ∘ st.sourceMap) x.property⟩ = gamma x := by
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨B, hB, hBD, _⟩, _⟩ := hmodel
  let T := B.frontierSubcomplex D
  have hT : T.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hTQ : T.space = Q := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBD,
      frontier_closedBall _ one_ne_zero]
  have hQS : Q ⊆ S.space := fun _ hx => hSD.symm.subset (sphere_subset_closedBall hx)
  have hsourceQ := st.sourcePL.restrict_finite T hT (hTQ.subset.trans hQS)
  have hPL : FinitePiecewiseAffineOn (F ∘ st.sourceMap) Q := by
    simpa only [hTQ] using hsourceQ.finitePiecewiseAffineOn_comp T hT hFPL
  have hsourceN (x : Q) : st.sourceMap x ∈ N :=
    hDN (mem_image_of_mem st.sourceMap (hQS x.property))
  have hsourceFront (x : Q) : st.sourceMap x ∈ frontier N :=
    st.source_mem_frontier_of_original_rim hN hDN hNR (hQS x.property)
      ((hpair x).symm ▸ hFmark (gamma x).property)
  have himageA : (F ∘ st.sourceMap) '' Q ⊆ A.space := by
    rw [hAs]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem F (hsourceFront ⟨x, hx⟩)
  have himageK : (F ∘ st.sourceMap) '' Q ⊆ K.space := by
    rintro _ ⟨x, hx, rfl⟩
    change F (st.sourceMap x) ∈ K.space
    rw [← hJF ⟨st.sourceMap x, hsourceN ⟨x, hx⟩⟩]
    exact (J ⟨st.sourceMap x, hsourceN ⟨x, hx⟩⟩).property
  let inc : C((F ∘ st.sourceMap) '' Q, K.space) :=
    ⟨fun z => ⟨z, himageK z.property⟩, continuous_subtype_val.subtype_mk _⟩
  let back : C((F ∘ st.sourceMap) '' Q, N) :=
    ⟨fun z => J.symm (inc z), J.symm.continuous.comp inc.continuous⟩
  have hback (x : Q) : back ⟨F (st.sourceMap x),
      mem_image_of_mem (F ∘ st.sourceMap) x.property⟩ =
        ⟨st.sourceMap x, hsourceN x⟩ := by
    apply J.injective
    change J (J.symm (inc _)) = _
    rw [J.apply_symm_apply]
    apply Subtype.ext
    exact (hJF ⟨st.sourceMap x, hsourceN x⟩).symm
  have hmark (z : (F ∘ st.sourceMap) '' Q) : st.projection (back z) ∈ Fmark := by
    obtain ⟨x, hx, heq⟩ := z.property
    have hz : z = ⟨F (st.sourceMap x),
        mem_image_of_mem (F ∘ st.sourceMap) hx⟩ := Subtype.ext heq.symm
    rw [hz, hback ⟨x, hx⟩]
    change st.projection (st.sourceMap x) ∈ Fmark
    rw [st.source_eq x (hQS hx), hpair ⟨x, hx⟩]
    exact (gamma ⟨x, hx⟩).property
  let j : C((F ∘ st.sourceMap) '' Q, Fmark) :=
    ⟨fun z => ⟨st.projection (back z), hmark z⟩,
      (st.projection.continuous.comp
        (continuous_subtype_val.comp back.continuous)).subtype_mk _⟩
  refine ⟨hPL, himageA, j, ?_⟩
  intro x
  apply Subtype.ext
  change st.projection (back _) = (gamma x : M)
  rw [hback x]
  exact (st.source_eq x (hQS x.property)).trans (hpair x)

end Geometry.OriginalPLTower
