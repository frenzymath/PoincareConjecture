import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.FaceCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.EdgeCharts
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.FixedCollar

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_relative_whole_planar_interior_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (K M : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    {g : V2 → X} (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (F : X ≃ₜ X) (W : Set X) (hW : IsOpen W) (hfix : EqOn F id W)
    (hMW : g '' M.space ⊆ W)
    (hcollar : ∀ x ∈ M.space, x ∈ interior K.space → g x ∈ S →
      Nonempty (OriginalSurfacePairChart e S (g '' K.space) (g x) false))
    (hSV : Disjoint (F '' S) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 → a ∉ M.faces →
      HasOriginalEdgeCofaceCharts e (F '' S) K g a)
    (faces : Finset (K.FaceOfCard 3))
    (hcover : ∀ s : K.FaceOfCard 3, s.1 ∉ M.faces → s ∈ faces)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s ∈ faces, ∀ i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → V2 →ᴬ[ℝ] V3)
    (hmap : ∀ s ∈ faces, MapsTo g (convexHull ℝ (s.1 : Set V2)) (Q s).source)
    (hA : ∀ s ∈ faces, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set V2)))
    (hposition : ∀ s ∈ faces, InTriangleGraphPosition (Q s) (F '' S)
      (g '' convexHull ℝ (s.1 : Set V2)) (convexHull ℝ ((A s) '' (s.1 : Set V2))))
    {x : V2} (hxK : x ∈ interior K.space) (hgx : g x ∈ F '' S) :
    Nonempty (OriginalSurfacePairChart e (F '' S) (g '' K.space) (g x) false) := by
  classical
  by_cases hxM : x ∈ M.space
  · have hxW := hMW (mem_image_of_mem g hxM)
    have hxS : g x ∈ S := by
      obtain ⟨y, hy, heq⟩ := hgx
      exact F.injective (heq.trans (hfix hxW).symm) ▸ hy
    obtain ⟨C⟩ := hcollar x hxM hxK hxS
    exact ⟨C.image_first_of_fixed_neighborhood F hW hxW hfix⟩
  · have hbound (t : Finset V2) (ht : t ∈ K.faces) : t.card ≤ 3 := by
      have hc := (K.indep ht).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      simpa only [Fintype.card_coe, Module.finrank_prod, Module.finrank_self, Nat.reduceAdd] using hc
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK (interior_subset hxK)
    have hpos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    have hnotone : s.card ≠ 1 := by
      intro hone
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      have hxv : x = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
          intrinsicInterior_subset hxs
      exact disjoint_left.mp hSV hgx ⟨v, hs, congrArg g hxv.symm⟩
    rcases (show s.card = 2 ∨ s.card = 3 by have := hbound s hs; omega) with hs2 | hs3
    · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs2
      obtain ⟨B, H, hB, hxB, hxH, hsource, hzero, hPL, hInv, hS, hT⟩ :=
        (hedges {p, q} hs hs2 (fun hsM => hxM
          (M.convexHull_subset_space hsM (intrinsicInterior_subset hxs)))).exists_whole_planar_edge_crossing K hK hgc hgi hSV
          hpq hs (by simpa only [Finset.coe_pair] using hxs) hxK hgx isOpen_univ (mem_univ _)
      exact ⟨OriginalSurfacePairChart.of_interior_planes B H hB hxB hxH hzero
        (hsource.trans inter_subset_left) hPL hInv hS hT⟩
    · let t : K.FaceOfCard 3 := ⟨s, hs, hs3⟩
      have ht : t ∈ faces := hcover t (fun hsM => hxM
        (M.convexHull_subset_space hsM (intrinsicInterior_subset hxs)))
      have hmax (u : Finset V2) (hu : u ∈ K.faces) (hsu : s ⊆ u) : u = s :=
        (Finset.eq_of_subset_of_card_le hsu (by rw [hs3]; exact hbound u hu)).symm
      have hxQ : g x ∈ (Q t).source := hmap t ht (intrinsicInterior_subset hxs)
      obtain ⟨H, hxH, hsource, hzero, hPL, hInv, hS, hT⟩ :=
        (hposition t ht).exists_whole_maximal_face_crossing K hK hgc hgi hs hmax
          (Q t) (A t) (hmap t ht) (hA t ht) hxs hgx isOpen_univ (mem_univ _)
      exact ⟨OriginalSurfacePairChart.of_interior_planes (Q t) H (hQ t ht)
        hxQ hxH hzero (hsource.trans inter_subset_right) hPL hInv hS hT⟩

theorem exists_retained_boundary_pair_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T : Set X} {y : X}
    (F : X ≃ₜ X) {W : Set X} (hW : IsOpen W) (hfix : EqOn F id W) (hyW : y ∈ W)
    (hchart : y ∈ S → Nonempty (OriginalSurfacePairChart e S T y true))
    (hy : y ∈ F '' S) : Nonempty (OriginalSurfacePairChart e (F '' S) T y true) := by
  have hyS : y ∈ S := by
    obtain ⟨z, hz, heq⟩ := hy
    exact F.injective (heq.trans (hfix hyW).symm) ▸ hz
  obtain ⟨C⟩ := hchart hyS
  exact ⟨C.image_first_of_fixed_neighborhood F hW hyW hfix⟩

end PoincareConjecture.M76
