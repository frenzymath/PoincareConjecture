import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ParityEdgeFlip
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ParityLocal
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.SimplePolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.GenericFrame











set_option autoImplicit false

open Set Filter

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}



theorem IsSimplePolygon.exists_polygonCrossingParity_ne {p : Polygon E n}
    (hp : IsSimplePolygon p) (X H : E →ₗ[ℝ] ℝ) (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    (he : ∀ j, H (p j) ≠ H (p (finRotate n j))) {v : E}
    (hvX : X v = 1) (hvH : H v = 0) :
    ∃ x y, x ∉ p.boundary ℝ ∧ y ∉ p.boundary ℝ ∧
      polygonCrossingParity p X H x ≠ polygonCrossingParity p X H y := by
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hp.three_le⟩
  obtain ⟨q, hq, _, _, havoid⟩ := exists_mem_segment_height_avoiding_finite H (he i)
    (finite_range (fun j => H (p j)))
  have hverts : ∀ j, H (p j) ≠ H q := fun j hj => havoid ⟨j, hj⟩
  have hqi : q ∈ p.edgeSet ℝ i := by rwa [polygon_edgeSet_eq_segment]
  have hother : ∀ j, j ≠ i → q ∉ p.edgeSet ℝ j := by
    intro j hji hj
    have hends := (hp.edges_inter i j hji.symm ⟨hqi, hj⟩).1
    simp only [mem_insert_iff, mem_singleton_iff] at hends
    rcases hends with hleft | hright
    · exact hverts i (congrArg H hleft).symm
    · exact hverts (finRotate n i) (congrArg H hright).symm
  obtain ⟨t, _, _, _, hx, hy, hpar⟩ := polygonCrossingParity_flip_near_edge p X H hX hH
    hcoords he i hqi hother hverts hvX hvH (U := univ) univ_mem
  refine ⟨q - t • v, q + t • v, hx, hy, ?_⟩
  intro heq
  rw [heq, CharTwo.add_self_eq_zero] at hpar
  exact zero_ne_one hpar



theorem IsSimplePolygon.not_isPreconnected_compl [FiniteDimensional ℝ E]
    {p : Polygon E n} (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2) :
    ¬IsPreconnected (p.boundary ℝ)ᶜ := by
  obtain ⟨e, hheight⟩ := exists_continuousLinearEquiv_snd_injective_comp_finite
    hdim p hp.vertices_injective
  let X : E →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp e.toContinuousLinearMap
  let H : E →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp e.toContinuousLinearMap
  have hcoords : Function.Injective (fun x => (X x, H x)) := by
    intro x y hxy
    exact e.injective hxy
  have he : ∀ j, H (p j) ≠ H (p (finRotate n j)) := by
    intro j hj
    exact hp.hasNondegenerateEdges j (congrArg p (hheight hj))
  have hvX : X (e.symm (1, 0)) = 1 := by
    change (e (e.symm (1, 0))).1 = 1
    rw [e.apply_symm_apply]
  have hvH : H (e.symm (1, 0)) = 0 := by
    change (e (e.symm (1, 0))).2 = 0
    rw [e.apply_symm_apply]
  obtain ⟨x, y, hx, hy, hne⟩ := hp.exists_polygonCrossingParity_ne X.toLinearMap H.toLinearMap
    X.continuous H.continuous hcoords he hvX hvH
  intro hpre
  exact hne (polygonCrossingParity_eq_of_isPreconnected p X.toLinearMap H.toLinearMap
    X.continuous H.continuous hcoords he hpre Subset.rfl hx hy)

end PoincareConjecture.M25.Topology3D
