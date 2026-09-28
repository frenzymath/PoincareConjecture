


import PoincareConjecture.Proofs.Horizon.Topology.Connected.ClosedCover
import PoincareConjecture.Proofs.Horizon.Topology.Connected.ClosureCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Interior
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v w

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]




theorem exists_exactly_two_faces_of_coordinate_triangle_cover
    {F : Type v} {E : Type w} [Finite F] [Finite E]
    (face : F → SmoothFace M) (edge : E → SmoothEdge M)
    (face_edge : F → Fin 3 → E)
    (hboundary : ∀ f k, (face f).boundary k = edge (face_edge f k))
    (hused : ∀ i, ∃ f k, face_edge f k = i)
    (hinj : ∀ i, InjOn (edge i).map (Icc (0 : ℝ) 1))
    (hmeet : ∀ i j, i ≠ j →
      (edge i).map '' Icc (0 : ℝ) 1 ∩ (edge j).map '' Icc (0 : ℝ) 1 ⊆
        {(edge i).map 0, (edge i).map 1})
    (coordinates : F → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (basis : F → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ f, convexHull ℝ (range (basis f)) ⊆ (coordinates f).source)
    (hcarrier : ∀ f, (face f).carrier = coordinates f '' convexHull ℝ (range (basis f)))
    (hinter : ∀ f g, f ≠ g →
      (face f).carrier ∩ (face g).carrier ⊆ frontier (face f).carrier)
    (hcover : (⋃ f, (face f).carrier) = univ) (i : E) :
    ∃ f g : F, f ≠ g ∧ ∀ h : F,
      (∃ k : Fin 3, face_edge h k = i) ↔ h = f ∨ h = g := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let K : Set M := ⋃ j, (edge j).map '' Icc (0 : ℝ) 1
  have hclosed (f : F) : IsClosed (face f).carrier := (face f).isClosed_carrier
  have hregular (f : F) : closure (interior (face f).carrier) = (face f).carrier := by
    rw [hcarrier f]
    exact coordinate_triangle_closure_interior (coordinates f) (basis f) (hsource f)
  have hdisjoint : Pairwise (fun f g =>
      Disjoint (interior (face f).carrier) (interior (face g).carrier)) := by
    intro f g hfg
    exact (face f).disjoint_interiors_of_inter_subset_frontier (face g) (hinter f g hfg)
  have hbound (f : F) (k : Fin 3) :
      (edge (face_edge f k)).map '' Icc (0 : ℝ) 1 ⊆ frontier (face f).carrier := by
    rw [← hboundary f k]
    exact (face f).boundary_image_subset_frontier k
  have hK : K = ⋃ f, frontier (face f).carrier := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      obtain ⟨f, k, hk⟩ := hused j
      have hb := hbound f k
      rw [hk] at hb
      exact mem_iUnion.mpr ⟨f, hb hj⟩
    · intro z hz
      obtain ⟨f, hf⟩ := mem_iUnion.mp hz
      rw [(face f).boundary_carrier] at hf
      obtain ⟨k, hk⟩ := mem_iUnion.mp hf
      rw [hboundary f k] at hk
      exact mem_iUnion.mpr ⟨face_edge f k, hk⟩
  have hdense : Dense Kᶜ := by
    rw [hK]
    simpa only [Finset.mem_univ, iUnion_true] using
      Poincare.Topology.dense_compl_finite_frontier_union Finset.univ
        (fun f => (face f).carrier) (fun f _ => hclosed f)
  obtain ⟨f₀, k₀, hk₀⟩ := hused i
  have hedgefront : (edge i).map '' Icc (0 : ℝ) 1 ⊆ frontier (face f₀).carrier := by
    simpa only [hk₀] using hbound f₀ k₀
  have hedgechart : (edge i).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (face f₀).chart).source :=
    hedgefront.trans ((hclosed f₀).frontier_subset.trans (face f₀).carrier_subset_chart)
  let q := (edge i).map (1 / 2 : ℝ)
  have ht : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hqedge : q ∈ (edge i).map '' Icc (0 : ℝ) 1 :=
    ⟨1 / 2, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hqfront : q ∈ frontier (face f₀).carrier := hedgefront hqedge
  have havoid (j : E) (hji : j ≠ i) : q ∉ (edge j).map '' Icc (0 : ℝ) 1 := by
    intro hj
    rcases hmeet i j hji.symm ⟨hqedge, hj⟩ with hzero | hone
    · exact ht.1.ne' (hinj i ⟨ht.1.le, ht.2.le⟩ (by simp) hzero)
    · exact ht.2.ne (hinj i ⟨ht.1.le, ht.2.le⟩ (by simp) hone)
  obtain ⟨W, U, V, hWopen, hqW, _, _, _, hUpath, hVpath, _, hpartition, hqUV⟩ :=
    exists_two_sided_edge_family_neighborhood edge i (face f₀).chart (hinj i)
      hedgechart ht havoid (s := univ) Filter.univ_mem
  have hWdense : W ⊆ closure (U ∪ V) := by
    rw [← hpartition]
    intro z hz
    apply mem_closure_iff.mpr
    intro O hO hzO
    obtain ⟨w, ⟨hwO, hwW⟩, hwK⟩ :=
      hdense.inter_open_nonempty (O ∩ W) (hO.inter hWopen) ⟨z, hzO, hz⟩
    exact ⟨w, hwO, hwW, hwK⟩
  have hfront (f : F) : W ∩ frontier (face f).carrier ⊆ K := by
    intro z hz
    rw [hK]
    exact mem_iUnion.mpr ⟨f, hz.2⟩
  obtain ⟨f, g, hfg, _, _, hmembers⟩ :=
    Poincare.Topology.exists_exactly_two_closed_cover_members_of_two_sided_neighborhood
      (fun f => (face f).carrier) hclosed hregular hdisjoint hcover
      (hWopen.mem_nhds hqW) hpartition hUpath.isConnected.isPreconnected
      hVpath.isConnected.isPreconnected hUpath.nonempty hVpath.nonempty
      hqUV.1 hqUV.2 hWdense hfront ⟨f₀, hqfront⟩
  have hqnotint (h : F) : q ∉ interior (face h).carrier := by
    intro hq
    by_cases hh : h = f₀
    · subst h
      exact hqfront.2 hq
    · exact (hinter h f₀ hh ⟨interior_subset hq,
        (hclosed f₀).frontier_subset hqfront⟩).2 hq
  refine ⟨f, g, hfg, ?_⟩
  intro h
  rw [← hmembers h]
  constructor
  · rintro ⟨k, hk⟩
    have hb := hbound h k
    rw [hk] at hb
    exact (hclosed h).frontier_subset (hb hqedge)
  · intro hq
    have hqf : q ∈ frontier (face h).carrier := ⟨subset_closure hq, hqnotint h⟩
    rw [(face h).boundary_carrier] at hqf
    obtain ⟨k, hk⟩ := mem_iUnion.mp hqf
    rw [hboundary h k] at hk
    refine ⟨k, ?_⟩
    by_contra hki
    exact havoid (face_edge h k) hki hk

end PoincareConjecture.Topology.Surface
