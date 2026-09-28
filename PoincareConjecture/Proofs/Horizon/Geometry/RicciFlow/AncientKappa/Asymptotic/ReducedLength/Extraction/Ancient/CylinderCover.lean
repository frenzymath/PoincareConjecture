import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Gluing


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.FlowCarrier

attribute [local instance] topologicalSpace chartedSpace secondCountable

theorem exists_positive_coordinateCylinder_cover {n : ℕ} (C : FlowCarrier n) :
    ∃ b : ℕ → ℝ, ∃ d : ∀ i, CoordinateCylinder C 0 (b i),
      univ ×ˢ Ioi (0 : ℝ) ⊆ ⋃ i, (d i).domain := by
  classical
  let X := C.carrier × Ioi (0 : ℝ)
  have hd (x : X) : ∃ d : CoordinateCylinder C 0 (x.2.val + 1),
      (x.1, x.2.val) ∈ d.domain :=
    C.exists_coordinateCylinder_at ⟨x.2.property, by linarith⟩
  choose d hd using hd
  let U (x : X) : Set X := (fun y : X => (y.1, y.2.val)) ⁻¹' (d x).domain
  have hU (x : X) : U x ∈ 𝓝 x :=
    ((d x).domain_open.preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mem_nhds (hd x)
  obtain ⟨A, hA, hcover⟩ := TopologicalSpace.countable_cover_nhds hU
  obtain ⟨p, _⟩ := C.connected.nonempty
  let x₀ : X := (p, ⟨1, by norm_num⟩)
  have hAne : A.Nonempty := by
    have hx : x₀ ∈ ⋃ x ∈ A, U x := hcover.symm ▸ mem_univ x₀
    obtain ⟨x, hx, _⟩ := mem_iUnion₂.mp hx
    exact ⟨x, hx⟩
  obtain ⟨s, hs⟩ := hA.exists_eq_range hAne
  refine ⟨fun i => (s i).2.val + 1, fun i => d (s i), ?_⟩
  intro y hy
  let x : X := (y.1, ⟨y.2, hy.2⟩)
  have hx : x ∈ ⋃ z ∈ A, U z := hcover.symm ▸ mem_univ x
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
  rw [hs] at hz
  obtain ⟨i, rfl⟩ := hz
  exact mem_iUnion.mpr ⟨i, hxz⟩

theorem exists_continuous_locallyUniform_limit_of_positive_coordinateCylinder_limits
    {n : ℕ} (C : FlowCarrier n) (b : ℕ → ℝ)
    (d : ∀ i, CoordinateCylinder C 0 (b i))
    (hcover : univ ×ˢ Ioi (0 : ℝ) ⊆ ⋃ i, (d i).domain)
    (F : ℕ → C.carrier × ℝ → ℝ)
    (f : ∀ i, (d i).coordinateDomain → ℝ) (hf : ∀ i, Continuous (f i))
    (hlim : ∀ i, TendstoUniformly
      (fun k (z : (d i).coordinateDomain) => F k ((d i).param z.val)) (f i) atTop) :
    ∃ l : C.carrier × ℝ → ℝ, ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)) ∧
      TendstoLocallyUniformlyOn F l atTop (univ ×ˢ Ioi (0 : ℝ)) := by
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
