import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedBallSphereModel
import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment















set_option autoImplicit false

open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsFinitePLBallPair.exists_punctured_sphere_of_disk_port_sum
    {ι : Type*} [Finite ι] {B U S T d q : Set E}
    (hB : IsFinitePLBallPair P3 B S) (hU : IsFinitePLBallPair P3 U T)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hdS : d ⊆ S) (hdT : d ⊆ T)
    (hSout : (S \ d).Nonempty) (hTout : (T \ d).Nonempty)
    (hBU : B ∩ U = d) (a r : ι → Set E)
    (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (hside : ∀ i, a i ⊆ B \ S ∨ a i ⊆ U \ T)
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) :
    let outer := (S \ (d \ q)) ∪ (T \ (d \ q))
    IsFinitePLBallPair V3 (B ∪ U) outer ∧
    ∃ (f : E → Fin 4 → ℝ) (H : (B ∪ U : Set E) ≃ₜ lower), H.IsFinitePL ∧
      (∀ x : (B ∪ U : Set E), (H x : Fin 4 → ℝ) = f x) ∧
      (∀ x : (B ∪ U : Set E), (x : E) ∈ outer ↔ (H x : Fin 4 → ℝ) ∈ seam) ∧
      (∀ i, IsFinitePLBallPair V3 (f '' a i) (f '' r i)) ∧
      (∀ i, f '' a i ⊆ lower \ seam) ∧
      (∀ i, Disjoint upper (f '' a i)) ∧
      Pairwise (fun i j => Disjoint (f '' a i) (f '' a j)) ∧
      let p := (B ∪ U) \ ⋃ i, a i \ r i
      let P := sphere \ ((upper \ seam) ∪ ⋃ i, (f '' a i) \ (f '' r i))
      ∃ (L : SimplicialComplex ℝ E) (F : p ≃ₜ P),
        L.faces.Finite ∧ L.space = p ∧ F.IsFinitePL ∧
        (∀ x : p, (F x : Fin 4 → ℝ) = f x) ∧
        (∀ i (x : p), (x : E) ∈ r i ↔ (F x : Fin 4 → ℝ) ∈ f '' r i) ∧
        (∀ i, (fun x : p => (F x : Fin 4 → ℝ)) ''
          ((Subtype.val : p → E) ⁻¹' r i) = f '' r i) ∧
        ((fun x : p => (F x : Fin 4 → ℝ)) ''
          ((Subtype.val : p → E) ⁻¹' outer) = seam) := by
  let outer := (S \ (d \ q)) ∪ (T \ (d \ q))
  have hj : IsFinitePLBallPair P3 (B ∪ U) outer :=
    hB.union_of_actual_disk_contact hU hd hdS hdT hSout hTout hBU
  let coord : P3 ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨e, he, heb⟩ := hj.exists_cube_chart coord
  have hj3 : IsFinitePLBallPair V3 (B ∪ U) outer :=
    ⟨hj.1, closedBall (0 : V3) 1, isCompact_closedBall _ _, convex_closedBall _ _,
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩, e, he, heb⟩
  have haJoined (i : ι) : a i ⊆ (B ∪ U) \ outer := by
    intro x hx
    rcases hside i with h | h
    · have hxB := h hx
      refine ⟨Or.inl hxB.1, ?_⟩
      rintro (hxS | hxT)
      · exact hxB.2 hxS.1
      · exact hxB.2 (hdS (hBU ▸ And.intro hxB.1 (hU.1 hxT.1)))
    · have hxU := h hx
      refine ⟨Or.inr hxU.1, ?_⟩
      rintro (hxS | hxT)
      · exact hxU.2 (hdT (hBU ▸ And.intro (hB.1 hxS.1) hxU.1))
      · exact hxU.2 hxT.1
  exact ⟨hj3, hj3.exists_punctured_ball_sphere_model a r ha haJoined hdis⟩

end Set
