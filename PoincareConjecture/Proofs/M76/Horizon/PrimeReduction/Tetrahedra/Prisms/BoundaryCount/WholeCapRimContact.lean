import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.SphereEulerCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.SphereDiskContactSeparation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem boundary_disk_rim_subset_closed_remainder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {B R D r C : Set F} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B R)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D r) (hDR : D ⊆ R)
    (hC : IsClosed C) (hcover : R ⊆ D ∪ C) : r ⊆ C := by
  have houtside : (R \ D).Nonempty := by
    by_contra hne
    have hRD : R ⊆ D := by
      intro x hx
      by_contra hxd
      exact hne ⟨x,hx,hxd⟩
    have heq : D = R := Subset.antisymm hDR hRD
    obtain ⟨J,_,hJ,hJs,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
    have hc1 := (finitePL_ball_surfaceEulerCount hD (by simp [Module.finrank_prod])
      J hJ hJs).2
    have hc2 := (finitePL_ball_boundary_surfaceEulerCount K ht ht4 hB J hJ
      (hJs.trans heq)).2
    omega
  have hN := hB.boundary_disk_complement (by simp) hD hDR houtside
  have hNC : R \ (D \ r) ⊆ C := by
    rw [←hN.closure_sdiff]
    apply closure_minimal ?_ hC
    intro x hx
    rcases hcover hx.1.1 with hxD | hxC
    · exact (hx.1.2 ⟨hxD,hx.2⟩).elim
    · exact hxC
  exact hN.1.trans hNC

theorem boundary_caps_whole_rim_contact
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Finite ι]
    (K : SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {B R U : Set F} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B R)
    (A r : ι → Set F) (hA : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i) (r i))
    (hAR : ∀ i, A i ⊆ R) (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hU : IsClosed U) (hcover : R ⊆ (⋃ i, A i) ∪ U)
    (hcontact : ∀ i, A i ∩ U ⊆ r i) : ∀ i, A i ∩ U = r i := by
  classical
  intro i
  have hrest : IsClosed ((⋃ j : {j // j ≠ i}, A j) ∪ U) :=
    (isClosed_iUnion_of_finite fun j : {j // j ≠ i} => (hA j).isCompact.isClosed).union hU
  have hcov : R ⊆ A i ∪ ((⋃ j : {j // j ≠ i}, A j) ∪ U) := by
    intro x hx
    rcases hcover hx with hxA | hxU
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hxA
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩))
    · exact Or.inr (Or.inr hxU)
  have hr := boundary_disk_rim_subset_closed_remainder K ht ht4 hB (hA i)
    (hAR i) hrest hcov
  apply Subset.antisymm (hcontact i)
  intro x hx
  refine ⟨(hA i).1 hx,?_⟩
  rcases hr hx with hxother | hxU
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hxother
    exact (disjoint_left.mp (hdis j.2.symm) ((hA i).1 hx) hj).elim
  · exact hxU

end PoincareConjecture.M76.PrismBelt
