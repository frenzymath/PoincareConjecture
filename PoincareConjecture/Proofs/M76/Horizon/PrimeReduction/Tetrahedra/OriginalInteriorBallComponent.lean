import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalInteriorComponent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.InnermostOriginalSphereBall









set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_interior_ball_component
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (x : X) (hx : x ∈ (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i))
    (hfront : Disjoint
      (connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x)
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))) :
    ∃ i D, D ⊆ interior (g '' convexHull ℝ (t : Set E)) ∧
      Nonempty (ChartwisePLBall e D (S i)) ∧
      Disjoint (interior D) (⋃ j, S j) ∧ (interior D).Nonempty ∧
      ∀ y ∈ interior D,
        connectedComponentIn (⋃ j, S j)ᶜ y = interior D ∧
        closure (connectedComponentIn (⋃ j, S j)ᶜ y) = D := by
  obtain ⟨i,_,hi⟩ := original_interior_component_eq_sphere
    he K hK g hg hgi S sS hS hdis ht ht4 x hx hfront
  obtain ⟨b⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  exact exists_innermost_original_sphere_ball he S sS hdis b ⟨i,hi⟩

end PoincareConjecture.M76
