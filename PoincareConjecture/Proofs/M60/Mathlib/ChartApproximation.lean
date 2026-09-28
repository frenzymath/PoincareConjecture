import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension











set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M60




theorem exists_contDiff_approx_on_isClosed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Set E} (hK : IsClosed K) {f : E → F} (hf : ContinuousOn f K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ ∀ x ∈ K, dist (G x) (f x) < epsilon := by
  let : TietzeExtension F := TietzeExtension.of_homeo
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv.toHomeomorph
  let fK : C(K, F) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨a, ha⟩ := fK.exists_restrict_eq hK
  obtain ⟨G, hG, hclose, -⟩ := a.continuous.exists_contDiff_approx (⊤ : ℕ∞)
    continuous_const (fun _ => hepsilon)
  refine ⟨G, hG, ?_⟩
  intro x hx
  have heq : a x = f x := ContinuousMap.congr_fun ha ⟨x, hx⟩
  simpa only [heq] using hclose x




theorem exists_pos_inverse_chart_control
    {F N : Type*} [PseudoMetricSpace F] [PseudoMetricSpace N]
    (h : OpenPartialHomeomorph N F) {K : Set F}
    (hK : IsCompact K) (hKh : K ⊆ h.target) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ K, ∀ q : F, dist q p < delta →
      q ∈ h.target ∧ dist (h.symm q) (h.symm p) < epsilon := by
  obtain ⟨r, hr, hrange⟩ := hK.exists_thickening_subset_open h.open_target hKh
  have hu := hK.uniformContinuousAt_of_continuousAt h.symm
    (fun p hp => h.continuousAt_symm (hKh hp)) (Metric.dist_mem_uniformity hepsilon)
  obtain ⟨s, hs, hdist⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro p hp q hqp
  refine ⟨hrange ?_, ?_⟩
  · exact (mem_thickening_iff_exists_edist_lt K q).mpr
      ⟨p, hp, by
        rw [edist_dist]
        exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr (hqp.trans_le (min_le_left _ _))⟩
  · have hps : dist p q < s := by
      rw [dist_comm]
      exact hqp.trans_le (min_le_right _ _)
    have hd : dist (h.symm p) (h.symm q) < epsilon := hdist hps hp
    simpa only [dist_comm] using hd

end PoincareConjecture.M60
