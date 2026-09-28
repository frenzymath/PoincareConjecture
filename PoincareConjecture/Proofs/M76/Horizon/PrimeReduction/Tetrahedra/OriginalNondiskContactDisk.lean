import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalDiskPieceComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryPolygons
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.RemainingPieceContactDisk

set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_nondisk_piece_contact_disk
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
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ γ : Type u, Finite γ ∧ ∃ C : γ → SimplicialComplex ℝ E,
      (∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧
        (C c).space ⊆ convexHull ℝ (t : Set E)) ∧
      Pairwise (fun c d => Disjoint (C c).space (C d).space) ∧
      (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) ∧
      let F := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
      let disk := fun c => IsFinitePLBallPair (ℝ × ℝ) (C c).space ((C c).space ∩ F)
      ∀ c, ¬ disk c → ((C c).space ∩ F).Nonempty →
        ∃ (n : ℕ) (P : Polygon E (n + 3)) (d : Set E),
          Function.Injective P ∧ P.HasSimplicialEdges ∧
          IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) ∧
          d ⊆ convexHull ℝ (t : Set E) ∧ d ∩ F = P.boundary ℝ ∧
          d ∩ g ⁻¹' (⋃ i, S i) = P.boundary ℝ ∧
          (∃ c', ¬ disk c' ∧ P.boundary ℝ ⊆ (C c').space) ∧
          ∃ ρ : Type u, Finite ρ ∧ ∃ (m : ρ → ℕ) (L : ∀ j, Polygon E (m j + 3)) (j : ρ),
            (∀ k, Function.Injective (L k) ∧ (L k).HasSimplicialEdges ∧
              (L k).boundary ℝ ⊆ F) ∧
            Pairwise (fun k l => Disjoint (g '' (L k).boundary ℝ) (g '' (L l).boundary ℝ)) ∧
            (⋃ k, g '' (L k).boundary ℝ) = (⋃ i, S i) ∩ g '' F ∧
            P.boundary ℝ = (L j).boundary ℝ := by
  classical
  let F := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
  have hFT : F ⊆ convexHull ℝ (t : Set E) :=
    intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hFK := hFT.trans (K.convexHull_subset_space ht)
  obtain ⟨γ,hγ,C,hC,hCdis,hCcover,β,hβ,B,R,hcard,hB,hR,hBcover,hinter,_⟩ :=
    exists_original_disk_piece_complement he K hK g hg hgi S sS hS hdis ht ht4
  let : Finite γ := hγ
  let : Finite β := hβ
  let disk := fun c => IsFinitePLBallPair (ℝ × ℝ) (C c).space ((C c).space ∩ F)
  let good := {c : γ // disk c}
  let bad := {c : γ // ¬ disk c}
  let cuts := ⋃ c : good, (C c).space
  obtain ⟨δ,hδ,n,P,hP,hPdis,hPphysical,hphysical⟩ :=
    exists_original_tetrahedral_boundary_polygons K hK g hgi Q A hmap hA
      havoid hposition ht ht4
  let : Finite δ := hδ
  have hwhole : (⋃ j, (P j).boundary ℝ) = F ∩ ⋃ c, (C c).space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      have hxF := (hP j).2.2 hj
      have hxS := (hphysical.subset (mem_iUnion.mpr ⟨j,mem_image_of_mem g hj⟩)).1
      exact ⟨hxF,hCcover.symm.subset ⟨hFT hxF,hxS⟩⟩
    · rintro x ⟨hxF,hxC⟩
      obtain ⟨j,y,hy,hyx⟩ := mem_iUnion.mp (hphysical.symm.subset
        ⟨(hCcover.subset hxC).2,mem_image_of_mem g hxF⟩)
      have heq := hgi (hFK ((hP j).2.2 hy)) (hFK hxF) hyx
      exact mem_iUnion.mpr ⟨j,heq ▸ hy⟩
  have hPconn (j : δ) : IsConnected ((P j).boundary ℝ) := by
    obtain ⟨H⟩ := (P j).nonempty_boundary_homeomorph_circle (hP j).2.1 (hP j).1
    exact isConnected_iff_connectedSpace.mpr (H.connectedSpace_iff.mpr inferInstance)
  have hPsub (j : δ) : (P j).boundary ℝ ⊆ ⋃ c, (C c).space :=
    (subset_iUnion _ j).trans (hwhole.subset.trans inter_subset_right)
  choose piece hpiece _ using fun j =>
    (hPconn j).exists_unique_subset_finite_disjoint_closed (fun c => (C c).space)
      (fun c => ((C c).isCompact_space_of_finite (hC c).1).isClosed) hCdis (hPsub j)
  let J := {j : δ // ¬ disk (piece j)}
  have hbadwhole : (⋃ j : J, (P j).boundary ℝ) = F ∩ ⋃ c : bad, (C c).space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact ⟨(hP j).2.2 hj,mem_iUnion.mpr ⟨⟨piece j,j.property⟩,hpiece j hj⟩⟩
    · rintro x ⟨hxF,hxC⟩
      obtain ⟨c,hxc⟩ := mem_iUnion.mp hxC
      obtain ⟨j,hxj⟩ := mem_iUnion.mp (hwhole.symm.subset
        ⟨hxF,mem_iUnion.mpr ⟨c,hxc⟩⟩)
      have hjc : piece j = c := by
        by_contra hn
        exact disjoint_left.mp (hCdis hn) (hpiece j hxj) hxc
      exact mem_iUnion.mpr ⟨⟨j,hjc ▸ c.property⟩,hxj⟩
  have hbadcut (c : bad) : Disjoint (C c).space cuts := by
    apply disjoint_left.mpr
    intro x hxc hxt
    obtain ⟨d,hxd⟩ := mem_iUnion.mp hxt
    have hcd : (c : γ) ≠ d := fun heq => c.property (heq.symm ▸ d.property)
    exact disjoint_left.mp (hCdis hcd) hxc hxd
  have hall : cuts ∪ (⋃ c : bad, (C c).space) = ⋃ c, (C c).space := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨c,hc⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨c,hc⟩
      · obtain ⟨c,hc⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨c,hc⟩
    · intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      by_cases hd : disk c
      · exact Or.inl (mem_iUnion.mpr ⟨⟨c,hd⟩,hc⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨c,hd⟩,hc⟩)
  refine ⟨γ,hγ,C,hC,hCdis,hCcover,?_⟩
  dsimp only
  intro c hc hne
  obtain ⟨x,hxc,hxF⟩ := hne
  obtain ⟨j,d,hd,hdT,hdF,hdC⟩ := exists_remaining_piece_contact_disk B R hB hR hBcover hinter
    (fun c : bad => C c) (fun c => (hC c).1) (fun c => (hC c).2.1)
    (fun c => (hC c).2.2) (fun c d hcd => hCdis (fun heq => hcd (Subtype.ext heq)))
    hbadcut (fun j : J => n j) (fun j : J => P j) (fun j => (hP j).2.1)
    (fun j => (hP j).1) (fun i j hij => hPdis (fun heq => hij (Subtype.ext heq)))
    hbadwhole ⟨x,hxF,mem_iUnion.mpr ⟨⟨c,hc⟩,hxc⟩⟩
  have hds : d ∩ g ⁻¹' (⋃ i, S i) = (P j).boundary ℝ := by
    rw [hall,hCcover] at hdC
    rw [←hdC]
    ext x
    exact ⟨fun hx => ⟨hx.1,hdT hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  exact ⟨n j,P j,d,(hP j).1,(hP j).2.1,hd,hdT,hdF,hds,
    ⟨piece j,j.property,hpiece j⟩,δ,hδ,n,P,j,hP,hPphysical,hphysical,rfl⟩

end PoincareConjecture.M76
