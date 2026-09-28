import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OrientedDiskBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PolygonComplementComponents
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem planar_boundary_edge_unique_triangle
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (hcv : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty) {s : Finset E}
    (hs : s ∈ (K.frontierSubcomplex K.space).faces) (hsc : s.card = 2) :
    ∃! t : Finset E, t ∈ K.faces ∧ s ⊆ t ∧ t.card = 3 := by
  obtain ⟨t, ht, hst, htc⟩ := K.exists_full_coface_of_convex_space hK hcv hne hs.1
  have ht3 : t.card = 3 := by omega
  refine ⟨t, ⟨ht, hst, ht3⟩, ?_⟩
  rintro u ⟨hu, hsu, hu3⟩
  by_contra hut
  have hsne : (convexHull ℝ (s : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs.1)).convexHull
  obtain ⟨x, hx⟩ := hsne.intrinsicInterior (convex_convexHull ℝ _)
  have hxfront : x ∈ frontier K.space := hs.2 (intrinsicInterior_subset hx)
  have hxint := K.mem_interior_union_of_paired_facet
    (hsc.trans hdim.symm) ht hu htc (by omega) hst hsu (fun h ↦ hut h.symm) hx
  have hsub : convexHull ℝ (t : Set E) ∪ convexHull ℝ (u : Set E) ⊆ K.space :=
    union_subset (K.convexHull_subset_space ht) (K.convexHull_subset_space hu)
  exact hxfront.2 (interior_mono hsub hxint)

theorem planar_boundary_edge_iff_unique_triangle
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (hcv : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty) {s : Finset E}
    (hs : s ∈ K.faces) (hsc : s.card = 2) :
    s ∈ (K.frontierSubcomplex K.space).faces ↔
      ∃! t : Finset E, t ∈ K.faces ∧ s ⊆ t ∧ t.card = 3 := by
  refine ⟨fun hb ↦ planar_boundary_edge_unique_triangle K hK hdim hcv hne hb hsc, ?_⟩
  rintro ⟨t, ht, huniq⟩
  refine ⟨hs, ?_⟩
  intro x hx
  have hxK : x ∈ K.space := K.convexHull_subset_space hs hx
  refine ⟨subset_closure hxK, ?_⟩
  intro hxint
  obtain ⟨u, hu, v, hv, hsu, hsv, huc, hvc, huv⟩ :=
    K.hasTwoFullCofaces_of_hull_meets_interior hK hcv hs (hsc.trans hdim.symm)
      ⟨x, hx, hxint⟩
  exact huv ((huniq u ⟨hu, hsu, by omega⟩).trans (huniq v ⟨hv, hsv, by omega⟩).symm)

theorem exists_planar_boundary_cycle
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      range P = (K.frontierSubcomplex K.space).vertices ∧
      P.boundary ℝ = frontier K.space ∧
      (∀ s : Finset (ℝ × ℝ), s ∈ (K.frontierSubcomplex K.space).faces ↔
        s.Nonempty ∧ ∃ j : Fin (n + 3), s ⊆ {P j, P (finRotate (n + 3) j)}) ∧
      (∀ s : Finset (ℝ × ℝ), (s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2) ↔
        ∃ j : Fin (n + 3), s = {P j, P (finRotate (n + 3) j)}) ∧
      ∀ j : Fin (n + 3), ∃! t : Finset (ℝ × ℝ),
        t ∈ K.faces ∧ {P j, P (finRotate (n + 3) j)} ⊆ t ∧ t.card = 3 := by
  classical
  let L := K.frontierSubcomplex K.space
  have hcompact := K.isCompact_space_of_finite hK
  have hL : L.faces.Finite := K.frontierSubcomplex_finite K.space hK
  have hLspace : L.space = frontier K.space :=
    K.frontierSubcomplex_space hcompact.isClosed hcv hne rfl
  have hd : IsFinitePLBallPair (ℝ × ℝ) K.space (frontier K.space) :=
    isFinitePLBallPair_of_compact_convex hcompact hcv hne K hK rfl
  obtain ⟨m, Q, hQi, hQ, hQb⟩ := hd.exists_polygon_boundary
  have hQL : Q.boundary ℝ = L.space := hQb.trans hLspace.symm
  have hconn : IsConnected L.space := hQL ▸ Q.isConnected_boundary hQ hQi
  obtain ⟨n, P, hPi, hP, hPv, hPb, hfaces, hedges⟩ :=
    L.exists_exact_cyclic_polygon_of_polygon_carrier hL hconn Q hQ hQi hQL
  refine ⟨n, P, hPi, hP, hPv, hPb.trans hLspace, hfaces, hedges, ?_⟩
  intro j
  have he := (hedges {P j, P (finRotate (n + 3) j)}).mpr ⟨j, rfl⟩
  exact planar_boundary_edge_unique_triangle K hK (by simp) hcv hne he.1 he.2

theorem exists_planar_boundary_dart_cycle
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty) :
    ∃ (n : ℕ) (P : Polygon (ℝ × ℝ) (n + 3))
      (edge : Fin (n + 3) ≃
        {s : Finset (ℝ × ℝ) // s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2})
      (coface : Fin (n + 3) → Finset (ℝ × ℝ)),
      Function.Injective P ∧ P.boundary ℝ = frontier K.space ∧
      Equiv.Perm.IsCycle (finRotate (n + 3)) ∧
      (∀ i, (edge i).val = {P i, P (finRotate (n + 3) i)}) ∧
      (∀ i, coface i ∈ K.faces ∧ (edge i).val ⊆ coface i ∧ (coface i).card = 3) ∧
      ∀ i t, t ∈ K.faces → (edge i).val ⊆ t → t.card = 3 → t = coface i := by
  classical
  obtain ⟨n, P, hPi, _, _, hPb, _, hedges, hcofaces⟩ :=
    exists_planar_boundary_cycle K hK hcv hne
  let edges : Fin (n + 3) →
      {s : Finset (ℝ × ℝ) // s ∈ (K.frontierSubcomplex K.space).faces ∧ s.card = 2} :=
    fun i ↦ ⟨{P i, P (finRotate (n + 3) i)}, (hedges _).mpr ⟨i, rfl⟩⟩
  have heinj : Function.Injective edges := by
    intro i j hij
    have heq : ({P i, P (finRotate (n + 3) i)} : Set (ℝ × ℝ)) =
        {P j, P (finRotate (n + 3) j)} := by
      simpa only [edges, Finset.coe_pair] using
        congrArg (fun x ↦ ((x : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)))
          (congrArg Subtype.val hij)
    rcases Set.pair_eq_pair_iff.mp heq with ⟨hij, _⟩ | ⟨hij, hji⟩
    · exact hPi hij
    · have hi : i = j + 1 := by simpa only [finRotate_apply] using hPi hij
      have hj : i + 1 = j := by simpa only [finRotate_apply] using hPi hji
      have hone : (1 : Fin (n + 3)) + 1 = 2 := by
        apply Fin.ext
        norm_num [Fin.val_add, Fin.val_ofNat,
          Nat.mod_eq_of_lt (by omega : 1 < n + 3),
          Nat.mod_eq_of_lt (by omega : 2 < n + 3)]
      have htwo : (2 : Fin (n + 3)) = 0 := by
        apply add_left_cancel (a := j)
        calc
          j + 2 = (j + 1) + 1 := by rw [add_assoc, hone]
          _ = j := by rw [← hi, hj]
          _ = j + 0 := (add_zero _).symm
      have hval := congrArg Fin.val htwo
      norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hval
  have hesurj : Function.Surjective edges := by
    rintro ⟨s, hs⟩
    obtain ⟨i, hi⟩ := (hedges s).mp hs
    exact ⟨i, Subtype.ext hi.symm⟩
  let edge := Equiv.ofBijective edges ⟨heinj, hesurj⟩
  choose coface hcoface using hcofaces
  refine ⟨n, P, edge, coface, hPi, hPb, ?_, fun _ ↦ rfl, ?_, ?_⟩
  · exact isCycle_finRotate_of_le (by omega)
  · intro i
    exact (hcoface i).1
  · intro i t ht hsub hcard
    exact (hcoface i).2 t ⟨ht, hsub, hcard⟩

end PoincareConjecture.M76.OriginalTriangleCopies
