import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.CompatibleCover
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.SupportingLines

set_option autoImplicit false
open Set
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]

private theorem connectedIntersections_segment_image (p q : Plane) :
    affineChartSegment p q '' Icc (0 : ℝ) 1 = affineSegment ℝ p q := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem connectedIntersections_edge_subset (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) : affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆
      convexHull ℝ (range b) := by
  rw [affineSegment_eq_segment]
  exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)

omit [T2Space M] in

theorem exists_coordinate_edge_subinterval
    (F : OpenPartialHomeomorph Plane M) (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3)
    {A : Set M} (hcompact : IsCompact A) (hconnected : IsPreconnected A)
    (hne : A.Nonempty)
    (hsub : A ⊆ F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) :
    ∃ a d : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ d ∈ Icc (0 : ℝ) 1 ∧ a ≤ d ∧
      A = (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' Icc a d := by
  let e : ℝ → M := F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))
  let param : M → ℝ := fun q => b.coord (i.succAbove 1) (F.symm q)
  have hsrc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈ F.source :=
    hsource (connectedIntersections_edge_subset b i
      (connectedIntersections_segment_image _ _ ▸ mem_image_of_mem _ ht))
  have hparam (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : param (e t) = t := by
    dsimp only [param, e, Function.comp_apply]
    rw [F.left_inv (hsrc t ht)]
    have hseg : affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t =
        AffineMap.lineMap (b (i.succAbove 0)) (b (i.succAbove 1)) t := by
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    rw [hseg, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    have hneq : i.succAbove 1 ≠ i.succAbove 0 := by
      intro h
      have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective h
      norm_num at h10
    rw [b.coord_apply_ne hneq, b.coord_apply_eq]
    ring
  have hinverse (q : M) (hq : q ∈ A) : param q ∈ Icc (0 : ℝ) 1 ∧ e (param q) = q := by
    have hqedge := hsub hq
    rw [← connectedIntersections_segment_image, image_image] at hqedge
    obtain ⟨t, ht, rfl⟩ := hqedge
    change param (e t) ∈ _ ∧ e (param (e t)) = e t
    rw [hparam t ht]
    exact ⟨ht, rfl⟩
  have htarget : A ⊆ F.target := by
    intro q hq
    rw [← (hinverse q hq).2]
    exact F.map_source (hsrc _ (hinverse q hq).1)
  have hcont : ContinuousOn param A :=
    (continuous_barycentric_coord b (i.succAbove 1)).comp_continuousOn
      (F.symm.continuousOn.mono htarget)
  have hC := hcompact.image_of_continuousOn hcont
  have hP := hconnected.image param hcont
  have hN := hne.image param
  have hbounds : param '' A ⊆ Icc (0 : ℝ) 1 := by
    rintro q ⟨p, hp, rfl⟩
    exact (hinverse p hp).1
  refine ⟨sInf (param '' A), sSup (param '' A), hbounds (hC.sInf_mem hN),
    hbounds (hC.sSup_mem hN), csInf_le_csSup hN hC.bddBelow hC.bddAbove, ?_⟩
  rw [← eq_Icc_of_connected_compact ⟨hN, hP⟩ hC, image_image]
  apply subset_antisymm
  · intro q hq
    exact ⟨q, hq, (hinverse q hq).2⟩
  · rintro q ⟨p, hp, rfl⟩
    change e (param p) ∈ A
    rwa [(hinverse p hp).2]

namespace CoordinateTriangleBoundaryIntersection

theorem of_isPreconnected_inter
    (F G : OpenPartialHomeomorph Plane M) (b c : AffineBasis (Fin 3) ℝ Plane)
    (hF : convexHull ℝ (range b) ⊆ F.source)
    (hG : convexHull ℝ (range c) ⊆ G.source)
    (hconnected : IsPreconnected ((F '' convexHull ℝ (range b)) ∩
      (G '' convexHull ℝ (range c))))
    (i j : Fin 3)
    (hleft : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)))
    (hright : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆
      G '' affineSegment ℝ (c (j.succAbove 0)) (c (j.succAbove 1))) :
    CoordinateTriangleBoundaryIntersection F G b c := by
  classical
  by_cases hne : ((F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c))).Nonempty
  · have hcompact := (((finite_range b).isCompact_convexHull ℝ).image_of_continuousOn
        (F.continuousOn.mono hF)).inter
      (((finite_range c).isCompact_convexHull ℝ).image_of_continuousOn (G.continuousOn.mono hG))
    obtain ⟨a, d, ha, hd, had, heq⟩ :=
      exists_coordinate_edge_subinterval F b hF i hcompact hconnected hne hleft
    obtain ⟨a', d', ha', hd', had', heq'⟩ :=
      exists_coordinate_edge_subinterval G c hG j hcompact hconnected hne hright
    exact .subsegment i j a d a' d' ha hd ha' hd'
      (by rwa [uIcc_of_le had]) (by rwa [uIcc_of_le had'])
  · exact .disjoint (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne))

theorem of_convex_chart_contact
    (F G : OpenPartialHomeomorph Plane M) (b c : AffineBasis (Fin 3) ℝ Plane)
    (hF : convexHull ℝ (range b) ⊆ F.source)
    (hG : convexHull ℝ (range c) ⊆ G.source)
    (A : Set Plane) (hconvex : Convex ℝ A)
    (hinter : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) =
      F '' (convexHull ℝ (range b) ∩ A))
    (l : Plane →ᵃ[ℝ] ℝ) (hsurj : Function.Surjective l)
    (hside : (∀ i, 0 ≤ l (b i)) ∨ (∀ i, l (b i) ≤ 0))
    (hline : A ⊆ {z | l z = 0}) (j : Fin 3)
    (hright : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆
      G '' affineSegment ℝ (c (j.succAbove 0)) (c (j.succAbove 1))) :
    CoordinateTriangleBoundaryIntersection F G b c := by
  obtain ⟨i, hi⟩ := triangle_inter_zero_subset_edge b l hsurj hside
  apply of_isPreconnected_inter F G b c hF hG ?_ i j ?_ hright
  · rw [hinter]
    exact ((convex_convexHull ℝ _).inter hconvex).isPreconnected.image F
      (F.continuousOn.mono (inter_subset_left.trans hF))
  · rw [hinter]
    exact image_mono (fun z hz => hi ⟨hz.1, hline hz.2⟩)

end CoordinateTriangleBoundaryIntersection
end PoincareConjecture.Topology.Surface
