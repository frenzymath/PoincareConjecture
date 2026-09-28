import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting












set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D




theorem collarHeightLevel_eq_central_height
    (ψ : UnitTwoSphere × ℝ → E3) (u : E3) (t : ℝ) :
    collarHeightLevel ψ u t =
      {y | y ∈ range (fun q : UnitTwoSphere => ψ (q, 0)) ∧ ⟪u, y⟫_ℝ = t} := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, rfl⟩, hq⟩
  · rintro ⟨⟨q, rfl⟩, hq⟩
    exact ⟨q, hq, rfl⟩




theorem exists_regular_collar_innermost_disc (hP : PlanarSchoenfliesService)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪(u : E3), ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q ≠ 0)
    (x₀ : collarHeightLevel ψ (u : E3) t) :
    ∃ x : collarHeightLevel ψ (u : E3) t, ∃ B : BallNeighborhoodChart E2 E2,
      (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) '' B.boundary =
        ((↑) : collarHeightLevel ψ (u : E3) t → E3) '' connectedComponent x ∧
      Disjoint ((fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) '' B.inside)
        (range (fun q : UnitTwoSphere => ψ (q, 0))) ∧
      ((fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) '' B.closedRegion) ∩
        range (fun q : UnitTwoSphere => ψ (q, 0)) =
          (fun p : E2 => (heightPlaneCoordinates u).symm (p, t)) '' B.boundary := by
  classical
  let L := collarHeightLevel ψ (u : E3) t
  let ι := ConnectedComponents L
  let : Nonempty L := ⟨x₀⟩
  let : Finite ι := finite_collarHeightLevel_components ψ hψ (u : E3) t hreg
  choose r hr using (ConnectedComponents.surjective_coe :
    Surjective (ConnectedComponents.mk : L → ι))
  choose B hB using fun i : ι =>
    exists_regular_collar_component_disc hP ψ hψ u t hreg (r i)
  let lift : E2 → E3 := fun p => (heightPlaneCoordinates u).symm (p, t)
  have hlift : Injective lift := by
    intro p q hpq
    exact congrArg Prod.fst ((heightPlaneCoordinates u).symm.injective hpq)
  have hheight (p : E2) : ⟪(u : E3), lift p⟫_ℝ = t := by
    rw [← heightPlaneCoordinates_snd]
    exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (p, t))
  have hcover (y : E3) (hy : y ∈ L) : ∃ i, y ∈ lift '' (B i).boundary := by
    let z : L := ⟨y, hy⟩
    let i : ι := ConnectedComponents.mk z
    refine ⟨i, ?_⟩
    rw [hB i]
    exact ⟨z, ConnectedComponents.coe_eq_coe'.mp (hr i).symm, rfl⟩
  have hdis (i j : ι) (hij : i ≠ j) : Disjoint (B i).boundary (B j).boundary := by
    have hcomp : Disjoint (connectedComponent (r i)) (connectedComponent (r j)) := by
      apply connectedComponent_disjoint
      intro heq
      apply hij
      exact (hr i).symm.trans ((ConnectedComponents.coe_eq_coe.mpr heq).trans (hr j))
    have himage := Set.disjoint_image_of_injective
      (Subtype.val_injective : Injective ((↑) : L → E3)) hcomp
    rw [← hB i, ← hB j] at himage
    exact himage.of_image
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  obtain ⟨i, hi, hclosed⟩ := BallNeighborhoodChart.exists_innermost B
    (fun j => (B j).boundary_connected hdim) hdis
  refine ⟨r i, B i, hB i, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨p, hp, rfl⟩ hys
    have hyL : lift p ∈ L := by
      rw [show L = collarHeightLevel ψ (u : E3) t from rfl,
        collarHeightLevel_eq_central_height]
      exact ⟨hys, hheight p⟩
    obtain ⟨j, hj⟩ := hcover (lift p) hyL
    exact Set.disjoint_left.mp (hi j) hp (hlift.mem_set_image.mp hj)
  · ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hys⟩
      have hyL : lift p ∈ L := by
        rw [show L = collarHeightLevel ψ (u : E3) t from rfl,
          collarHeightLevel_eq_central_height]
        exact ⟨hys, hheight p⟩
      obtain ⟨j, hj⟩ := hcover (lift p) hyL
      have hpB : p ∈ (B i).boundary := by
        rw [← hclosed]
        exact ⟨hp, mem_iUnion.mpr ⟨j, hlift.mem_set_image.mp hj⟩⟩
      exact ⟨p, hpB, rfl⟩
    · intro hy
      refine ⟨?_, ?_⟩
      · obtain ⟨p, hp, rfl⟩ := hy
        refine ⟨p, ?_, rfl⟩
        rw [← (B i).inside_union_boundary]
        exact Or.inr hp
      · rw [hB i] at hy
        obtain ⟨z, _, rfl⟩ := hy
        have hsub : collarHeightLevel ψ (u : E3) t ⊆
            range (fun q : UnitTwoSphere => ψ (q, 0)) := by
          rw [collarHeightLevel_eq_central_height]
          exact fun _ hz => hz.1
        exact hsub z.2

end PoincareConjecture.M25.Topology3D
