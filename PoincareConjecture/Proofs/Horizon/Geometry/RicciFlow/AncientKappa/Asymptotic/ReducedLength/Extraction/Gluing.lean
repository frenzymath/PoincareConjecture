import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.CylinderCover
import Mathlib.Topology.MetricSpace.UniformConvergence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.FlowCarrier

attribute [local instance] topologicalSpace chartedSpace secondCountable

theorem exists_continuous_locallyUniform_limit_of_coordinateCylinder_limits
    {n : ℕ} (C : FlowCarrier n) {a b : ℝ}
    (d : ℕ → CoordinateCylinder C a b)
    (hcover : univ ×ˢ Ioo a b ⊆ ⋃ i, (d i).domain)
    (F : ℕ → C.carrier × ℝ → ℝ)
    (f : ∀ i, (d i).coordinateDomain → ℝ) (hf : ∀ i, Continuous (f i))
    (hlim : ∀ i, TendstoUniformly
      (fun k (z : (d i).coordinateDomain) => F k ((d i).param z.val)) (f i) atTop) :
    ∃ l : C.carrier × ℝ → ℝ,
      ContinuousOn l (univ ×ˢ Ioo a b) ∧
      TendstoLocallyUniformlyOn F l atTop (univ ×ˢ Ioo a b) := by
  let l : C.carrier × ℝ → ℝ := fun z => atTop.limUnder (fun k => F k z)
  have heq (i : ℕ) (z : (d i).coordinateDomain) : l ((d i).param z.val) = f i z :=
    ((hlim i).tendsto_at z).limUnder_eq
  have hdomain (i : ℕ) (z : (d i).domain) : l z.val = f i ((d i).toCoordinates z) := by
    rw [← heq, (d i).param_toCoordinates]
  have hcont (i : ℕ) : ContinuousOn l (d i).domain := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq' : (d i).domain.domRestrict l = f i ∘ (d i).toCoordinates := by
      funext z
      exact hdomain i z
    rw [heq']
    exact (hf i).comp (d i).continuous_toCoordinates
  have huni (i : ℕ) : TendstoUniformlyOn F l atTop (d i).domain := by
    intro u hu
    filter_upwards [hlim i u hu] with k hk z hz
    have h := hk ((d i).toCoordinates ⟨z, hz⟩)
    rw [(d i).param_toCoordinates, ← hdomain] at h
    exact h
  refine ⟨l, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
    exact ((hcont i z hi).continuousAt ((d i).domain_open.mem_nhds hi)).continuousWithinAt
  · intro u hu z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
    exact ⟨(d i).domain, mem_nhdsWithin_of_mem_nhds ((d i).domain_open.mem_nhds hi), huni i u hu⟩

end PoincareConjecture.FlowCarrier
