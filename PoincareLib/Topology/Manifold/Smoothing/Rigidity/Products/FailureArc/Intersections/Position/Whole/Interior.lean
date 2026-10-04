import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.FaceCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.EdgeCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FiniteCarrierFaceInteriors
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FiniteFaceCounts

/-! # Complete original-atlas crossings at every interior contact -/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_whole_planar_interior_crossing
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    {g : V2 → X} (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hSV : Disjoint S (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e S K g a)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → V2 →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set V2)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set V2)))
    (hposition : ∀ s, InTriangleGraphPosition (Q s) S
      (g '' convexHull ℝ (s.1 : Set V2)) (convexHull ℝ ((A s) '' (s.1 : Set V2))))
    {x : V2} (hxK : x ∈ interior K.space) (hgx : g x ∈ S)
    {N : Set X} (hN : IsOpen N) (hgxN : g x ∈ N) :
    ∃ (B : OpenPartialHomeomorph X V3) (H : OpenPartialHomeomorph V3 C3),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      g x ∈ B.source ∧ B (g x) ∈ H.source ∧
      H.source ⊆ B.target ∩ B.symm ⁻¹' N ∧ H (B (g x)) = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, B.symm z ∈ S ↔ (H z).2 = 0) ∧
      ∀ z ∈ H.source, B.symm z ∈ g '' K.space ↔ (H z).1.1 = 0 := by
  classical
  have hbound (t : Finset V2) (ht : t ∈ K.faces) : t.card ≤ 3 := by
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
  have hcases : s.card = 2 ∨ s.card = 3 := by have := hbound s hs; omega
  rcases hcases with hs2 | hs3
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs2
    exact (hedges {p, q} hs hs2).exists_whole_planar_edge_crossing K hK hgc hgi hSV
      hpq hs (by simpa only [Finset.coe_pair] using hxs) hxK hgx hN hgxN
  · let t : K.FaceOfCard 3 := ⟨s, hs, hs3⟩
    have hmax (u : Finset V2) (hu : u ∈ K.faces) (hsu : s ⊆ u) : u = s :=
      (Finset.eq_of_subset_of_card_le hsu (by rw [hs3]; exact hbound u hu)).symm
    have hxQ : g x ∈ (Q t).source := hmap t (intrinsicInterior_subset hxs)
    let O := (Q t).target ∩ (Q t).symm ⁻¹' N
    have hO : IsOpen O := (Q t).symm.isOpen_inter_preimage hN
    have hxO : (Q t) (g x) ∈ O := by
      refine ⟨(Q t).map_source hxQ, ?_⟩
      change (Q t).symm ((Q t) (g x)) ∈ N
      rwa [(Q t).left_inv hxQ]
    obtain ⟨H, hxH, hHO, hHzero, hHPL, hHinv, hS, htarget⟩ :=
      (hposition t).exists_whole_maximal_face_crossing K hK hgc hgi hs hmax
        (Q t) (A t) (hmap t) (hA t) hxs hgx hO hxO
    exact ⟨Q t, H, hQ t, hxQ, hxH, fun z hz => (hHO hz).1,
      hHzero, hHPL, hHinv, hS, htarget⟩

end PoincareMT.M76
