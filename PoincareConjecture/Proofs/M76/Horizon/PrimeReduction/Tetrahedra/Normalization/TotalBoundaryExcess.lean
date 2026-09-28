import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.OriginalSelectedExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalFaceAvoidance

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

noncomputable def totalTetrahedralBoundaryExcess
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (S : Set X) : ℕ := by
  classical
  exact ∑ t ∈ hK.toFinset.filter (fun t => t.card = 4),
    boundaryComponentExcess S (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))

theorem exists_tetrahedron_of_totalBoundaryExcess_ne_zero
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (S : Set X)
    (hne : totalTetrahedralBoundaryExcess K hK g S ≠ 0) :
    ∃ t ∈ K.faces, t.card = 4 ∧ boundaryComponentExcess S (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ≠ 0 := by
  classical
  by_contra! hn
  apply hne
  unfold totalTetrahedralBoundaryExcess
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨ht,ht4⟩ := Finset.mem_filter.mp ht
  exact hn t (hK.mem_toFinset.mp ht) ht4

theorem boundaryComponentExcess_eq_zero_of_total_eq_zero
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (S : Set X)
    (hzero : totalTetrahedralBoundaryExcess K hK g S = 0)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    boundaryComponentExcess S (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) = 0 := by
  classical
  exact Finset.sum_eq_zero_iff.mp hzero t
    (Finset.mem_filter.mpr ⟨hK.mem_toFinset.mpr ht,ht4⟩)

theorem totalTetrahedralBoundaryExcess_lt_of_supported_replacement
    {E X ι κ η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    [Finite κ] [Finite η]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (N : η → Set X) (sN : ∀ j, ChartwisePLSphere e (N j))
    (hNdis : Pairwise fun j k => Disjoint (N j) (N k))
    (hsupport : (⋃ j, N j) \ interior (g '' convexHull ℝ (t : Set E)) =
      (⋃ i, S i) \ interior (g '' convexHull ℝ (t : Set E)))
    (selected : Set η)
    (hlt : boundaryComponentExcess (⋃ j ∈ selected, N j) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) <
      boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))) :
    totalTetrahedralBoundaryExcess K hK g (⋃ j ∈ selected, N j) <
      totalTetrahedralBoundaryExcess K hK g (⋃ i, S i) := by
  classical
  have hother {s : Finset E} (hs : s ∈ K.faces) (hs4 : s.card = 4) (hne : t ≠ s) :
      boundaryComponentExcess (⋃ j ∈ selected, N j) (g '' convexHull ℝ (s : Set E))
        (g '' intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) ≤
      boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (s : Set E))
        (g '' intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) := by
    have havoidT := original_tetrahedron_interior_disjoint_other_tetrahedron K hg hgi ht ht4 hs hs4 hne
    have hsections : (⋃ j, N j) ∩ g '' convexHull ℝ (s : Set E) =
        (⋃ i, S i) ∩ g '' convexHull ℝ (s : Set E) := by
      ext x
      constructor
      · rintro ⟨hx,hxB⟩
        exact ⟨(hsupport.subset ⟨hx,fun hin => disjoint_left.mp havoidT hin hxB⟩).1,hxB⟩
      · rintro ⟨hx,hxB⟩
        exact ⟨(hsupport.symm.subset ⟨hx,fun hin => disjoint_left.mp havoidT hin hxB⟩).1,hxB⟩
    exact original_selected_tetrahedral_excess_le he K hK g hg hgi Q A hmap hA
      S sS hS hdis havoid hposition hs hs4 N sN hNdis hsections selected
  unfold totalTetrahedralBoundaryExcess
  apply Finset.sum_lt_sum
  · intro s hs
    obtain ⟨hs,hs4⟩ := Finset.mem_filter.mp hs
    have hsK : s ∈ K.faces := hK.mem_toFinset.mp hs
    by_cases heq : t = s
    · subst s
      exact hlt.le
    · exact hother hsK hs4 heq
  · exact ⟨t,Finset.mem_filter.mpr ⟨hK.mem_toFinset.mpr ht,ht4⟩,hlt⟩

end PoincareConjecture.M76
