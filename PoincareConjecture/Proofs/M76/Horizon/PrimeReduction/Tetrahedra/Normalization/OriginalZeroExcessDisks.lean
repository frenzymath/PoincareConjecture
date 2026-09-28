import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryComponentExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryPieces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalOneBoundaryRecognition









set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_boundary_disk_pieces_of_zero_excess
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
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
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hzero : boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) = 0) :
    ∃ γ : Type u, Finite γ ∧ ∃ C : γ → SimplicialComplex ℝ E,
      (∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧
        (C c).space ⊆ convexHull ℝ (t : Set E)) ∧
      Pairwise (fun c d => Disjoint (C c).space (C d).space) ∧
      (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) ∧
      ∀ c, ((C c).space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Nonempty →
        IsFinitePLBallPair (ℝ × ℝ) (C c).space
          ((C c).space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
  classical
  obtain ⟨γ,δ,hγ,hδ,C,P,n,L,owner,hC,hPdis,hPcover,hL,hLdis,howner,hfront,hcomp⟩ :=
    exists_original_tetrahedral_boundary_pieces he K hK g hg hgi Q A hmap hA
      S sS hS hdis havoid hposition ht ht4
  let : Finite γ := hγ
  let : Finite δ := hδ
  let F := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
  let rim := fun j => g '' (L j).boundary ℝ
  have hFT : F ⊆ convexHull ℝ (t : Set E) :=
    intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hFK := hFT.trans (K.convexHull_subset_space ht)
  have hCK (c) : (C c).space ⊆ K.space := (hC c).2.2.1.trans (K.convexHull_subset_space ht)
  have hPc (c) : P c = g '' (C c).space := (hC c).2.2.2.1
  have hPclosed (c) : IsClosed (P c) := (hC c).2.2.2.2.2.1.isClosed
  have hPconn (c) : IsConnected (P c) := (hC c).2.2.2.2.2.2
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
  have hformula := boundaryComponentExcess_eq_of_finite_pieces
    (S := ⋃ i, S i) (B := g '' convexHull ℝ (t : Set E)) (F := g '' F)
    P rim owner hPclosed hPconn hPdis (by simpa only [inter_comm] using hPcover)
    hrimclosed hrimconn hLdis hrimcover hrimowner
  have hcard : (Set.range owner).ncard = Nat.card δ := by
    have hle : (Set.range owner).ncard ≤ Nat.card δ := by
      simpa only [image_univ,ncard_univ] using ncard_image_le (f := owner) (s := (univ : Set δ))
    rw [hformula] at hzero
    omega
  have hownerinj : Function.Injective owner := by
    have hi : InjOn owner univ := injOn_of_ncard_image_eq (by simp only [image_univ,ncard_univ,hcard])
    exact fun j k h => hi (mem_univ _) (mem_univ _) h
  have hCdis : Pairwise fun c d => Disjoint (C c).space (C d).space := by
    intro c d hcd
    apply disjoint_left.mpr
    intro x hxc hxd
    exact disjoint_left.mp (hPdis hcd) ((hPc c).symm ▸ mem_image_of_mem g hxc)
      ((hPc d).symm ▸ mem_image_of_mem g hxd)
  have hCcover : (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      exact ⟨(hC c).2.2.1 hc,hPsub c ((hPc c).symm ▸ mem_image_of_mem g hc)⟩
    · rintro x ⟨hxT,hxS⟩
      obtain ⟨c,hc⟩ := mem_iUnion.mp (hPcover.symm.subset ⟨mem_image_of_mem g hxT,hxS⟩)
      obtain ⟨y,hy,hyx⟩ := (hPc c).subset hc
      exact mem_iUnion.mpr ⟨c,hgi (hCK c hy) (K.convexHull_subset_space ht hxT) hyx ▸ hy⟩
  refine ⟨γ,hγ,C,fun c => ⟨(hC c).1,(hC c).2.1,(hC c).2.2.1⟩,hCdis,hCcover,?_⟩
  intro c hc
  obtain ⟨x,hxc,hxF⟩ := hc
  have hxc' : g x ∈ P c := (hPc c).symm ▸ mem_image_of_mem g hxc
  obtain ⟨j,hj⟩ := mem_iUnion.mp ((hfront c).subset ⟨hxc',mem_image_of_mem g hxF⟩)
  have hsingle : P c ∩ g '' F = rim j.val := by
    rw [hfront c]
    apply Subset.antisymm
    · intro y hy
      obtain ⟨k,hk⟩ := mem_iUnion.mp hy
      have heq : k.val = j.val := hownerinj (k.property.trans j.property.symm)
      exact heq ▸ hk
    · exact fun y hy => mem_iUnion.mpr ⟨j,hy⟩
  obtain ⟨i,hci,_⟩ := (hPconn c).exists_unique_subset_finite_disjoint_closed
    S (fun i => (sS i).isCompact.isClosed) hdis (hPsub c)
  have hdisk := original_piece_is_disk_of_single_boundary he K hK g hg hgi Q A hmap hA
    S sS hdis hedges hposition ht ht4 P hPclosed hPdis
    (by simpa only [inter_comm] using hPcover.symm.subset) c i hci
    (hC c).2.2.1 (hPc c) (L j.val) (hL j.val).1 (hL j.val).2.1 (hL j.val).2.2 hsingle
  have hsource : (C c).space ∩ F = (L j.val).boundary ℝ := by
    apply Subset.antisymm
    · rintro y ⟨hy,hyF⟩
      obtain ⟨z,hz,hzy⟩ := hsingle.subset ⟨(hPc c).symm ▸ mem_image_of_mem g hy,mem_image_of_mem g hyF⟩
      exact hgi (hFK ((hL j.val).2.2 hz)) (hCK c hy) hzy ▸ hz
    · intro y hy
      have hyP := hrimowner j.val (mem_image_of_mem g hy)
      rw [j.property,hPc c] at hyP
      obtain ⟨z,hz,hzy⟩ := hyP
      exact ⟨hgi (hCK c hz) (hFK ((hL j.val).2.2 hy)) hzy ▸ hz,(hL j.val).2.2 hy⟩
  exact hsource.symm ▸ hdisk

end PoincareConjecture.M76
