import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}


theorem exists_slice_collar_in_open (B : EpsilonNeck g) {s : ℝ}
    (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (V : Set M) (hV : IsOpen V)
    (hc : ∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ V) :
    ∃ r : ℝ, 0 < r ∧ ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
      s + t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ ∧
      B.coordinate_map (q, s + t) ∈ V := by
  let U : Set RoundCylinderSpace := B.cylinderDomain ∩ B.coordinate_map ⁻¹' V
  have hU : IsOpen U := B.coordinate_map_smooth.continuousOn.isOpen_inter_preimage
    B.cylinderDomain_open hV
  let shift : RoundCylinderSpace → RoundCylinderSpace := fun p => (p.1, s + p.2)
  have hshift : Continuous shift :=
    continuous_fst.prodMk (continuous_const.add continuous_snd)
  have hzero : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ shift ⁻¹' U := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨mem_univ _, by simpa [shift] using hs⟩, by simpa [shift] using hc q⟩
  obtain ⟨u, v, _, hv, hu, hz, huv⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) (hU.preimage hshift) hzero
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hv 0 (hz (by simp))
  refine ⟨r, hr, fun q t ht => ?_⟩
  have hqt := huv (show (q, t) ∈ u ×ˢ v from
    ⟨hu (mem_univ q), hrv (by simpa [Metric.mem_ball, Real.dist_eq] using ht)⟩)
  exact ⟨hqt.1.2, hqt.2⟩



theorem exists_contained_slice_collar (A B : EpsilonNeck g) {s : ℝ}
    (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (hc : ∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
      s + t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ ∧
      B.coordinate_map (q, s + t) ∈ A.carrier :=
  B.exists_slice_collar_in_open hs A.carrier A.carrier_open hc

end PoincareConjecture.EpsilonNeck
