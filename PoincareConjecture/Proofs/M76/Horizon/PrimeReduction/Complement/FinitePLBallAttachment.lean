import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedConnectedAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSphereTopology











set_option autoImplicit false

open Set Metric Geometry

namespace Set

local notation "V3" => (Fin 3 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem IsFinitePLBallPair.isConnected_boundary_three
    {D B : Set E} (hD : IsFinitePLBallPair V3 D B) : IsConnected B := by
  obtain ⟨d, _, hdb⟩ := hD.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  let db := d.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hdb
  exact db.isConnected_of_convex_frontier
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp)




theorem IsFinitePLBallPair.exists_components_homeomorph_of_attachment
    {P D B : Set E} (hD : IsFinitePLBallPair V3 D B)
    (hP : IsClosed P) (hattach : P ∩ D = B) :
    ∃ H : ConnectedComponents P ≃ₜ ConnectedComponents (P ∪ D : Set E),
      ∀ x : P, H (ConnectedComponents.mk x) =
        ConnectedComponents.mk (⟨x, Or.inl x.property⟩ : (P ∪ D : Set E)) := by
  exact Topology.exists_components_homeomorph_closed_attachment
    hP hD.isCompact.isClosed hD.isConnected
    (hattach.symm ▸ hD.isConnected_boundary_three)




theorem IsFinitePLBallPair.exists_components_homeomorph_of_removal
    {R D B : Set E} (hD : IsFinitePLBallPair V3 D B)
    (hR : IsClosed R) (hDR : D ⊆ R)
    (hopen : IsOpen ((Subtype.val : R → E) ⁻¹' (D \ B))) :
    ∃ H : ConnectedComponents (R \ (D \ B) : Set E) ≃ₜ ConnectedComponents R,
      ∀ x : (R \ (D \ B) : Set E), H (ConnectedComponents.mk x) =
        ConnectedComponents.mk (⟨x, x.property.1⟩ : R) := by
  have himage : (Subtype.val : R → E) ''
      (((Subtype.val : R → E) ⁻¹' (D \ B))ᶜ) = R \ (D \ B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hP : IsClosed (R \ (D \ B)) :=
    himage ▸ hR.isClosedMap_subtype_val _ hopen.isClosed_compl
  have hattach : (R \ (D \ B)) ∩ D = B := by
    ext x
    constructor
    · intro hx
      by_contra hxB
      exact hx.1.2 ⟨hx.2, hxB⟩
    · intro hx
      exact ⟨⟨hDR (hD.1 hx), fun h => h.2 hx⟩, hD.1 hx⟩
  have hunion : (R \ (D \ B)) ∪ D = R := by
    apply Subset.antisymm
    · exact union_subset sdiff_subset hDR
    · intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inr hxD
      · exact Or.inl ⟨hx, fun h => hxD h.1⟩
  obtain ⟨H, hH⟩ := hD.exists_components_homeomorph_of_attachment hP hattach
  let e : ((R \ (D \ B)) ∪ D : Set E) ≃ₜ R := Homeomorph.setCongr hunion
  let G : ConnectedComponents ((R \ (D \ B)) ∪ D : Set E) ≃ₜ
      ConnectedComponents R := {
    toFun := e.continuous.connectedComponentsMap
    invFun := e.symm.continuous.connectedComponentsMap
    left_inv := by
      intro z
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
      simp only [Continuous.connectedComponentsMap_mk, e.symm_apply_apply]
    right_inv := by
      intro z
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
      simp only [Continuous.connectedComponentsMap_mk, e.apply_symm_apply]
    continuous_toFun := e.continuous.connectedComponentsMap_continuous
    continuous_invFun := e.symm.continuous.connectedComponentsMap_continuous }
  refine ⟨H.trans G, fun x => ?_⟩
  change G (H (ConnectedComponents.mk x)) = _
  rw [hH]
  rfl

end Set
