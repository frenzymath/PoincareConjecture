import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_tetrahedron_interior_disjoint_of_not_subset
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) {g : E → X}
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {t s : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hs : s ∈ K.faces) (hnot : ¬ t ⊆ s) :
    Disjoint (interior (g '' convexHull ℝ (t : Set E)))
      (g '' convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  apply disjoint_left.mpr
  rintro x hx ⟨y,hy,hyx⟩
  obtain ⟨z,hz,hzx⟩ := interior_subset hx
  have hyz : y = z := hgi (K.convexHull_subset_space hs hy)
    (K.convexHull_subset_space ht hz) (hyx.trans hzx.symm)
  have hzcommon : z ∈ convexHull ℝ ((t ∩ s : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull ht hs ⟨hz,hyz ▸ hy⟩
  have hproper : t ∩ s ⊂ t := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_left,fun h => hnot (Finset.inter_eq_left.mp h)⟩
  have hzfront := (K.indep ht).convexHull_subset_intrinsicFrontier hproper hzcommon
  have hxfront : x ∈ frontier (g '' convexHull ℝ (t : Set E)) := by
    rw [ball.frontier_eq]
    exact ⟨z,hzfront,hzx⟩
  exact hxfront.2 hx

theorem original_tetrahedron_interior_disjoint_face
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) {g : E → X}
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {t s : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hs : s ∈ K.faces) (hscard : s.card ≤ 3) :
    Disjoint (interior (g '' convexHull ℝ (t : Set E)))
      (g '' convexHull ℝ (s : Set E)) := by
  apply original_tetrahedron_interior_disjoint_of_not_subset K hg hgi ht ht4 hs
  intro hsub
  have hle := Finset.card_le_card hsub
  omega

theorem original_tetrahedron_interior_disjoint_other_tetrahedron
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) {g : E → X}
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {t s : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hs : s ∈ K.faces) (hs4 : s.card = 4) (hne : t ≠ s) :
    Disjoint (interior (g '' convexHull ℝ (t : Set E)))
      (g '' convexHull ℝ (s : Set E)) := by
  apply original_tetrahedron_interior_disjoint_of_not_subset K hg hgi ht ht4 hs
  intro hsub
  exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))

end PoincareConjecture.M76
