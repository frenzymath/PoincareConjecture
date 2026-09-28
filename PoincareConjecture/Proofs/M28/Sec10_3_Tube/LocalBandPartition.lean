import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalBandExtension
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalBandNoncrossing
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalBandCollar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem extend_prefix_partition_m28 (A B : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    {b s : ℝ} (hb : b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hbq : b < -A.epsilon⁻¹ / 2) (hsq : s < -B.epsilon⁻¹ / 2)
    (hgraph : range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
      range (fun q => A.coordinate_map (q, f q)))
    (hneg : B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier)
    (hwithin : A.carrier ∩ B.carrier ⊆
      A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
        B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2))
    (U L K S : Set M) (hAU : A.carrier ⊆ U) (hK : IsCompact K)
    (hfront : frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => A.coordinate_map (q, b)))
    (hdecomp : U = (L ∪ K) ∪ A.region b A.epsilon⁻¹)
    (havoid : Disjoint B.carrier S) (havoidL : Disjoint B.carrier L)
    (hupper : Disjoint (A.region b A.epsilon⁻¹) K)
    (r : ℝ) (hr : 0 < r)
    (hcollar : ∀ q t, t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
      b - r < t → t ≤ b → A.coordinate_map (q, t) ∈ K) :
    let K' := K ∪ A.closedGraphSlab_m28 (fun _ => b) f
    (∀ q, b < f q) ∧
    IsCompact K' ∧
    (frontier K' ⊆ S ∪ range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) ∧
    U ∪ B.carrier = (L ∪ K') ∪ B.region s B.epsilon⁻¹ ∧
    Disjoint K' (B.region s B.epsilon⁻¹) ∧
    U ∪ B.carrier = (U \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ ∧
    Disjoint (U \ A.aboveGraph_m28 f) (B.region s B.epsilon⁻¹) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ B.carrier,
      s - δ < (B.coordinate_inverse x).2 →
      (B.coordinate_inverse x).2 ≤ s → x ∈ K' := by
  let K' := K ∪ A.closedGraphSlab_m28 (fun _ => b) f
  have hbf (q : UnitTwoSphere) : b < f q := by
    have hz : (q, f q) ∈ A.cylinderDomain := ⟨mem_univ _, hdom q⟩
    have hxB : A.coordinate_map (q, f q) ∈ B.carrier := by
      have hx : A.coordinate_map (q, f q) ∈
          range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) := hgraph.symm ▸ mem_range_self q
      obtain ⟨p, hp⟩ := hx
      rw [← hp]
      exact B.coordinate_map_mem ⟨mem_univ _, hs⟩
    have h := (hwithin ⟨A.coordinate_map_mem hz, hxB⟩).1.2.1
    rw [A.coordinate_inverse_coordinate_map hz] at h
    exact hbq.trans h
  obtain ⟨hside, hpair, _⟩ := A.graph_half_partition_m28 B f hf hdom hs hsq hgraph hneg hwithin
  obtain ⟨hK', hfront', d, hd, hcollar'⟩ :=
    A.extend_compact_band_through_neck_m28 (fun _ => b) f continuous_const hf
      (fun _ => hb) hdom hbf K S hK hfront r hr hcollar
  have hfrontB : frontier K' ⊆ S ∪
      range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) := by
    rw [hgraph]
    exact hfront'
  have hupper' : Disjoint (A.aboveGraph_m28 f) K' := by
    apply disjoint_left.mpr
    intro x hx hmem
    rcases hmem with hxK | hxSlab
    · exact disjoint_left.mp hupper
        ⟨hx.1, (hbf _).trans hx.2, (A.coordinate_inverse_mem x hx.1).2.2⟩ hxK
    · exact hxSlab.2.2.not_gt hx.2
  have hBupper := A.successor_upper_disjoint_compact_band_m28 B f hs hsq hneg hside
    K' S hK' hfrontB havoid hupper'
  have hKU : K ⊆ U := by rw [hdecomp]; exact subset_union_right.trans subset_union_left
  have hLU : L ⊆ U := by rw [hdecomp]; exact subset_union_left.trans subset_union_left
  have hslabU : A.closedGraphSlab_m28 (fun _ => b) f ⊆ U := fun x hx => hAU hx.1
  have hnew : U ∪ B.carrier = (L ∪ K') ∪ B.region s B.epsilon⁻¹ := by
    ext x
    constructor
    · rintro (hxU | hxB)
      · rw [hdecomp] at hxU
        rcases hxU with (hxL | hxK) | hxA
        · exact Or.inl (Or.inl hxL)
        · exact Or.inl (Or.inr (Or.inl hxK))
        · have hx : x ∈ (A.carrier \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ := by
            rw [← hpair]
            exact Or.inl hxA.1
          rcases hx with hx | hx
          · exact Or.inl (Or.inr (Or.inr ⟨hx.1, hxA.2.1.le,
              le_of_not_gt (fun h => hx.2 ⟨hx.1, h⟩)⟩))
          · exact Or.inr hx
      · have hx : x ∈ (A.carrier \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ := by
          rw [← hpair]
          exact Or.inr hxB
        rcases hx with hx | hx
        · exact Or.inl (Or.inr (Or.inr ⟨hx.1,
            (hbq.trans (hwithin ⟨hx.1, hxB⟩).1.2.1).le,
            le_of_not_gt (fun h => hx.2 ⟨hx.1, h⟩)⟩))
        · exact Or.inr hx
    · rintro ((hxL | hxK | hxSlab) | hxB)
      · exact Or.inl (hLU hxL)
      · exact Or.inl (hKU hxK)
      · exact Or.inl (hslabU hxSlab)
      · exact Or.inr hxB.1
  have hAH : A.aboveGraph_m28 f ⊆ B.region s B.epsilon⁻¹ := by
    intro x hx
    have hx' : x ∈ (A.carrier \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ := by
      rw [← hpair]
      exact Or.inl hx.1
    exact hx'.elim (fun h => False.elim (h.2 hx)) id
  have hcut : U ∪ B.carrier = (U \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ := by
    ext x
    constructor
    · intro hx
      have hcov : x ∈ U ∪ B.region s B.epsilon⁻¹ := by
        rcases hx with hx | hx
        · exact Or.inl hx
        · have hx' : x ∈ (A.carrier \ A.aboveGraph_m28 f) ∪ B.region s B.epsilon⁻¹ := by
            rw [← hpair]
            exact Or.inr hx
          exact hx'.elim (fun h => Or.inl (hAU h.1)) Or.inr
      rcases hcov with hx | hx
      · by_cases ha : x ∈ A.aboveGraph_m28 f
        · exact Or.inr (hAH ha)
        · exact Or.inl ⟨hx, ha⟩
      · exact Or.inr hx
    · exact fun hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hsep : Disjoint (U \ A.aboveGraph_m28 f) (B.region s B.epsilon⁻¹) := by
    apply disjoint_left.mpr
    rintro x ⟨hxU, hxAbove⟩ hxB
    rw [hdecomp] at hxU
    rcases hxU with (hxL | hxK) | hxA
    · exact disjoint_left.mp havoidL hxB.1 hxL
    · exact disjoint_left.mp hBupper (Or.inl hxK) hxB
    · exact hxAbove ⟨hxA.1, (hside x ⟨hxA.1, hxB.1⟩).mp hxB.2.1⟩
  refine ⟨hbf, hK', hfrontB, hnew, hBupper, hcut, hsep, ?_⟩
  apply A.transfer_graph_lower_collar_m28 B f hf hdom hs hgraph hside K' d hd
  intro x hx hlow hhigh
  have h := hcollar' (A.coordinate_inverse x).1 (A.coordinate_inverse x).2
    (A.coordinate_inverse_mem x hx).2 hlow hhigh
  simpa only [Prod.mk.eta, A.coordinate_map_coordinate_inverse hx] using h

end PoincareConjecture.EpsilonNeck
