import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.SelectedExcessMonotonicity
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryPieces

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_selected_tetrahedral_excess_le
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
    (hNeq : (⋃ j, N j) ∩ g '' convexHull ℝ (t : Set E) =
      (⋃ i, S i) ∩ g '' convexHull ℝ (t : Set E)) (selected : Set η) :
    boundaryComponentExcess (⋃ j ∈ selected, N j) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ≤
    boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
  classical
  obtain ⟨γ,δ,hγ,hδ,C,P,n,L,owner,hC,hPdis,hPcover,hL,hLdis,howner,hfront,_⟩ :=
    exists_original_tetrahedral_boundary_pieces he K hK g hg hgi Q A hmap hA
      S sS hS hdis havoid hposition ht ht4
  let : Finite γ := hγ
  let : Finite δ := hδ
  let F := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
  let rim := fun j => g '' (L j).boundary ℝ
  have hFT : F ⊆ convexHull ℝ (t : Set E) :=
    intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hFK := hFT.trans (K.convexHull_subset_space ht)
  have hrimclosed (j) : IsClosed (rim j) :=
    ((L j).isCompact_boundary.image_of_continuousOn
      (hg.continuousOn.mono ((hL j).2.2.trans hFK))).isClosed
  have hrimconn (j) : IsConnected (rim j) := by
    obtain ⟨H⟩ := (L j).nonempty_boundary_homeomorph_circle (hL j).2.1 (hL j).1
    exact (isConnected_iff_connectedSpace.mpr (H.connectedSpace_iff.mpr inferInstance)).image
      g (hg.continuousOn.mono ((hL j).2.2.trans hFK))
  have hPsub (c) : P c ⊆ ⋃ i, S i :=
    (subset_iUnion P c).trans (hPcover.subset.trans inter_subset_right)
  have hrimowner (j) : rim j ⊆ P (owner j) := (howner j (owner j)).mpr rfl
  have hrimcover : (⋃ j, rim j) = (⋃ i, S i) ∩ g '' F := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact ⟨hPsub (owner j) (hrimowner j hj),image_mono (hL j).2.2 hj⟩
    · rintro x ⟨hx,hxF⟩
      obtain ⟨c,hc⟩ := mem_iUnion.mp (hPcover.symm.subset ⟨image_mono hFT hxF,hx⟩)
      obtain ⟨j,hj⟩ := mem_iUnion.mp ((hfront c).subset ⟨hc,hxF⟩)
      exact mem_iUnion.mpr ⟨j.val,hj⟩
  exact boundaryComponentExcess_selected_le_of_eq_section (S := ⋃ i, S i)
    (image_mono hFT) P rim owner (fun c => (hC c).2.2.2.2.2.1.isClosed)
    (fun c => (hC c).2.2.2.2.2.2) hPdis (by simpa only [inter_comm] using hPcover)
    hrimclosed hrimconn hLdis hrimcover hrimowner N (fun j => (sN j).isCompact.isClosed)
    hNdis hNeq selected

end PoincareConjecture.M76
