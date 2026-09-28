import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSingleBoundaryDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallPairRecognition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInwardCrossing

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_piece_is_disk_of_single_boundary
    {E X ι κ γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    [Finite κ] [Finite γ] {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (P : γ → Set X) (hP : ∀ c, IsClosed (P c))
    (hPdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : (⋃ i, S i) ∩ (g '' convexHull ℝ (t : Set E)) ⊆ ⋃ c, P c)
    (c : γ) (i : κ) (hci : P c ⊆ S i)
    {C : Set E} (hCT : C ⊆ convexHull ℝ (t : Set E)) (hPc : P c = g '' C)
    {n : ℕ} (L : Polygon E (n + 3)) (hLi : Function.Injective L)
    (hL : L.HasSimplicialEdges)
    (hLT : L.boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (hfront : P c ∩ (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) =
      g '' L.boundary ℝ) :
    IsFinitePLBallPair (ℝ × ℝ) C (L.boundary ℝ) := by
  have hLK : L.boundary ℝ ⊆ K.space := hLT.trans
    ((intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
      (K.convexHull_subset_space ht))
  have hLS : g '' L.boundary ℝ ⊆ S i :=
    hfront.symm.subset.trans (inter_subset_left.trans hci)
  obtain ⟨x,⟨hxr,hxin⟩,hxout⟩ := original_polygon_two_sided_accumulation
    K hK g hg hgi Q A hmap hA S sS hdis hedges hposition ht ht4 L hLi hLT i hLS
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  have hcoveri : S i ∩ (g '' convexHull ℝ (t : Set E)) ⊆ ⋃ c, P c := by
    rintro y ⟨hyS,hyT⟩
    exact hcover ⟨mem_iUnion.mpr ⟨i,hyS⟩,hyT⟩
  obtain ⟨y,hyc,hyin⟩ := piece_has_interior_point_of_accumulation
    P hP hPdis hcoveri c (hfront.symm.subset hxr).1 hxin
  have hyoff : y ∉ g '' L.boundary ℝ := by
    intro hy
    have hyfront := (hfront.symm.subset hy).2
    rw [←ball.frontier_eq] at hyfront
    exact hyfront.2 hyin
  have hout : ¬ S i ⊆ g '' convexHull ℝ (t : Set E) := by
    obtain ⟨z,hzS,hzout⟩ := (show (closure (S i \ (g '' convexHull ℝ (t : Set E)))).Nonempty
      from ⟨x,hxout⟩).of_closure
    exact fun h => hzout (h hzS)
  let J := L.simplicialComplex hL
  have hJ := L.finite_simplicialComplex_faces hL
  have hJs : J.space = L.boundary ℝ := L.simplicialComplex_space hL
  have hgL : PolyhedralPLInCharts e g (L.boundary ℝ) := by
    rw [←hJs]
    exact hg.restrict_finite J hJ (hJs.subset.trans hLK)
  obtain ⟨d,q,hd,hdS,hdPc,hqL⟩ :=
    (sS i).exists_original_single_boundary_piece_disk he ball.isCompact.isClosed
      P hP hPdis hcoveri c hci (by rw [hPc]; exact image_mono hCT)
      L hL hLi hgL (hgi.mono hLK) (by rw [ball.frontier_eq]; exact hfront)
      ⟨y,hyc,hyoff⟩ hout
  have hcopy := hd
  obtain ⟨_,_,_,_,_,_,⟨_,⟨D,hD,hDs,_⟩,_⟩,_⟩ := hcopy
  have hsPL : PolyhedralPLInCharts e (sS i).map d := by
    rw [←hDs]
    exact (sS i).piecewiseAffine.restrict_finite D hD (hDs.subset.trans hdS)
  have hsi : InjOn (sS i).map d := by
    intro a ha b hb hab
    rw [(sS i).map_eq ⟨a,hdS ha⟩,(sS i).map_eq ⟨b,hdS hb⟩] at hab
    exact congrArg Subtype.val ((sS i).parametrization.injective (Subtype.ext hab))
  exact isFinitePLBallPair_of_original_parametrization he K hK hg hgi
    (hCT.trans (K.convexHull_subset_space ht)) hLK hd hsPL hsi
    (hdPc.trans hPc) hqL

end PoincareConjecture.M76
