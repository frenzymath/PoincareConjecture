import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactCapSide











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CappedTubeCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem exists_core_neck_confinement (T : CappedTubeCertificate g)
    (N : EpsilonNeck g) (hNU : N.carrier ⊆ T.tube.carrier)
    (hS : SmoothSphereIsotopicIn T.tube.carrier N.central_sphere
      T.tube.cylinder.middleSphere)
    (hcapN : Disjoint T.cap.carrier N.carrier) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ T.carrier ∧
      ∀ γ : ℝ → M, γ 0 ∈ T.cap.carrier → γ 1 ∈ N.central_sphere →
        ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) T.carrier →
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
          ∃ c d : ℝ, 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
            γ c ∈ N.central_sphere ∧ γ d ∈ N.central_sphere ∧
            γ t ∉ N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) := by
  obtain ⟨C, hC, hCU, hcapC, _, hfront⟩ :=
    T.exists_compact_cap_side hS (hcapN.mono_right N.central_sphere_subset)
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let D := N.coordinate_map '' (univ ×ˢ Icc (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2))
  have hD : IsCompact D := N.isCompact_coordinate_slab_intrinsic (by linarith) (by linarith)
  have hDN : D ⊆ N.carrier := N.coordinate_slab_subset_carrier_m28 (by linarith) (by linarith)
  have hmiddle : N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) ⊆ D := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  let K := C ∪ D
  refine ⟨K, hC.union hD, union_subset hCU ((hDN.trans hNU).trans T.tube_subset), ?_⟩
  intro γ hγ₀ hγ₁ hγ _hγU t ht htK
  have htC : γ t ∉ C := fun hx => htK (Or.inl hx)
  have h₀C : γ 0 ∈ C := interior_subset (hcapC hγ₀)
  have hexit : γ t ∉ N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) :=
    fun hx => htK (Or.inr (hmiddle hx))
  have hcross : ∃ c ∈ Icc (0 : ℝ) t, γ c ∈ N.central_sphere := by
    have hcomp : IsOpen Cᶜ := hC.isClosed.isOpen_compl
    have hconn : IsPreconnected (γ '' Icc (0 : ℝ) t) :=
      isPreconnected_Icc.image γ (hγ.mono (Icc_subset_Icc le_rfl ht.2))
    by_contra havoid
    push Not at havoid
    have hsubset : γ '' Icc (0 : ℝ) t ⊆ Cᶜ := by
      apply hconn.subset_of_closure_inter_subset hcomp
        ⟨γ t, ⟨t, right_mem_Icc.mpr ht.1, rfl⟩, htC⟩
      rintro x ⟨hxcl, c, hc, rfl⟩
      by_contra hcnot
      have hfc : γ c ∈ frontier Cᶜ := hcomp.frontier_eq.symm ▸ And.intro hxcl hcnot
      have hfC : γ c ∈ frontier C := by simpa only [frontier_compl] using hfc
      exact havoid c hc (hfront hfC)
    exact (hsubset ⟨0, left_mem_Icc.mpr ht.1, rfl⟩) h₀C
  obtain ⟨c, hc, hcsphere⟩ := hcross
  exact ⟨c, 1, hc.1, hc.2, ht.2, le_rfl, hcsphere, hγ₁, hexit⟩

end PoincareConjecture.CappedTubeCertificate
