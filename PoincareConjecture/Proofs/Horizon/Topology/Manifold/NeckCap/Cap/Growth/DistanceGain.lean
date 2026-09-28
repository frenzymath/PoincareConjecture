import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.BoundaryDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem frontier_inter_nonempty_of_carrier_crossing (C : CapCertificate g)
    {S : Set M} (hS : IsConnected S)
    (hin : (S ∩ C.carrier).Nonempty) (hout : (S \ C.carrier).Nonempty) :
    (S ∩ frontier C.carrier).Nonempty := by
  by_contra h
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  have hd : Disjoint S (frontier C.carrier) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  have hclopen := isClopen_preimage_val C.carrier_open hd.symm
  obtain ⟨x, hx, hxin⟩ := hin
  have heq := hclopen.eq_univ ⟨⟨x, hx⟩, hxin⟩
  obtain ⟨y, hy, hyout⟩ := hout
  apply hyout
  have hmem : (⟨y, hy⟩ : S) ∈ Subtype.val ⁻¹' C.carrier := by
    rw [heq]
    exact mem_univ _
  exact hmem

omit [T2Space M] in

theorem complement_distance_gain_of_frontier_separation (C D : CapCertificate g)
    (hCD : C.carrier ⊆ D.carrier) {δ : ℝ≥0∞}
    (hsep : ∀ x ∈ frontier C.carrier, ∀ y ∉ D.carrier, δ ≤ g.edist x y)
    {p : M} (hp : p ∈ C.carrier) :
    (⨅ z ∈ C.carrierᶜ, g.edist p z) + δ ≤ ⨅ y ∈ D.carrierᶜ, g.edist p y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine le_iInf fun y => le_iInf fun hy => ?_
  by_contra h
  have hshort : Manifold.riemannianEDist (𝓡 3) p y <
      (⨅ z ∈ C.carrierᶜ, g.edist p z) + δ := lt_of_not_ge h
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hshort
  have hconn : IsConnected (γ '' Icc (0 : ℝ) 1) :=
    (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image γ hγ.continuousOn
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := C.frontier_inter_nonempty_of_carrier_crossing hconn
    ⟨p, ⟨0, by simp, h0⟩, hp⟩
    ⟨y, ⟨1, by simp, h1⟩, fun hc => hy (hCD hc)⟩
  have hout : γ t ∈ C.carrierᶜ := (C.carrier_open.frontier_eq ▸ hz).2
  have hleft : (⨅ z ∈ C.carrierᶜ, g.edist p z) ≤
      Manifold.pathELength (𝓡 3) γ 0 t :=
    (iInf_le_of_le (γ t) (iInf_le _ hout)).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1)
  have hright : δ ≤ Manifold.pathELength (𝓡 3) γ t 1 :=
    (hsep (γ t) hz y hy).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2)
  exact (not_lt_of_ge ((add_le_add hleft hright).trans_eq
    (Manifold.pathELength_add ht.1 ht.2))) hlength

end PoincareConjecture.CapCertificate
