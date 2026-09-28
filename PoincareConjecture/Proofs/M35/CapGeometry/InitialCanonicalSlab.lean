import PoincareConjecture.Proofs.M35.CapGeometry.InitialEvolvingNeck
import PoincareConjecture.Proofs.M35.CapGeometry.InitialRadialCap










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem initial_slab_canonical
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀, ∀ t ∈ Icc 0 theta, ∀ x : StandardCapSpace,
      StandardCanonicalAlternative E.atlas E.flow t x epsilon C := by
  classical
  obtain ⟨K, hK, houtside⟩ := initial_neck_alternative_outside_compact E
    ⟨htheta.le, hthetalt⟩ he hehalf
  let a (p : ℝ × StandardCapSpace) := radialArclength (E.flow.metric p.1) ‖p.2‖
  have ha : ContinuousOn a (Icc 0 theta ×ˢ K) :=
    (raw_radialArclength_continuousOn_slab E.flow.base htheta.le hthetalt).comp
      (continuousOn_fst.prodMk continuousOn_snd.norm)
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  obtain ⟨Y, hY⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn ha
  obtain ⟨C₀, hC₀, hcaps⟩ := exists_initial_radial_caps P E htheta hthetalt
    he hehalf (abs_nonneg Y)
  refine ⟨C₀, hC₀, ?_⟩
  intro C hC t ht x
  by_cases hx : x ∈ K
  · obtain ⟨N⟩ := hcaps C hC t ht x (by
      have h := hY (t, x) ⟨ht, hx⟩
      change |radialArclength (E.flow.metric t) ‖x‖| ≤ Y at h
      exact (le_abs_self _).trans (h.trans (le_abs_self Y)))
    exact StandardCanonicalAlternative.cap N
  · exact houtside x hx t ht C

end PoincareConjecture.M35.Uniqueness
