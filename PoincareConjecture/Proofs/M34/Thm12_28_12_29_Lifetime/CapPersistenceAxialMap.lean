import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutOpen

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

noncomputable def axialMap (f : ℝ → ℝ) (x : M) : M := by
  classical
  exact if x ∈ N.end_neck.carrier then
    N.end_neck.coordinate_map ((N.end_neck.coordinate_inverse x).1,
      f (N.end_neck.coordinate_inverse x).2) else x

theorem axialMap_eq_self_of_mem_closed_core (f : ℝ → ℝ) {x : M}
    (hx : x ∈ N.closed_core) : N.axialMap f x = x := by
  rw [N.closed_core_eq_complement_end] at hx
  simp only [axialMap, if_neg hx.2]

theorem axialMap_eq_self_on_recut {f : ℝ → ℝ} {c : ℝ}
    (hf : ∀ s ≤ c, f s = s) : EqOn (N.axialMap f) id (N.recutCarrier c) := by
  intro x hx
  rcases hx with hx | hx
  · exact N.axialMap_eq_self_of_mem_closed_core f hx
  · simp only [axialMap, if_pos hx.1, hf _ hx.2.2.le]
    exact N.end_neck.coordinate_map_coordinate_inverse hx.1

theorem axialMap_contMDiffOn {f : ℝ → ℝ} {c : ℝ} {S : Set M}
    (hc : -N.epsilon⁻¹ < c) (hc' : c < N.epsilon⁻¹) (hS : S ⊆ N.carrier)
    (hf : ContDiff ℝ ∞ f) (hfix : ∀ s ≤ c, f s = s)
    (hvalid : ∀ x ∈ S, x ∈ N.end_neck.carrier →
      f (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.axialMap f) S := by
  intro x hx
  by_cases he : x ∈ N.end_neck.carrier
  · have hinv := N.end_neck.coordinate_inverse_smooth.contMDiffAt
      (N.end_neck.carrier_open.mem_nhds he)
    have hp : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun y => ((N.end_neck.coordinate_inverse y).1,
          f (N.end_neck.coordinate_inverse y).2)) x :=
      hinv.fst.prodMk (hf.contMDiff.contMDiffAt.comp x hinv.snd)
    have hheight : f (N.end_neck.coordinate_inverse x).2 ∈
        Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
      simpa only [N.end_neck_epsilon] using hvalid x hx he
    have hm : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        N.end_neck.coordinate_map
        ((N.end_neck.coordinate_inverse x).1, f (N.end_neck.coordinate_inverse x).2) :=
      N.end_neck.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hheight⟩)
    apply ((hm.comp x hp).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [N.end_neck.carrier_open.mem_nhds he] with y hy
    simp only [axialMap, if_pos hy, Function.comp_apply]
  · have hy : x ∈ N.closed_core := by
      rw [N.closed_core_eq_complement_end]
      exact ⟨hS hx, he⟩
    have hU : N.recutCarrier c ∈ 𝓝 x :=
      (N.recutCarrier_isOpen hc hc').mem_nhds (Or.inl hy)
    apply (contMDiffAt_id.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU] with y hy
    exact N.axialMap_eq_self_on_recut hfix hy

end PoincareConjecture.CapCertificate
