import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.RadialChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.GraphTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.CompactConjugation








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1




theorem exists_supported_radial_graph_flattening_within
    (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target)
    (a : E2 → Real) {V : Set E2} (hV : IsOpen V) (hVm : V ⊆ m.source)
    (ha : ContDiffOn Real ∞ a V) (hapos : ∀ y ∈ V, -1 < a y)
    {K : Set E2} (hK : IsCompact K) (hKV : K ⊆ V)
    {W : Set E3} (hWsphere : W ⊆ sphere (0 : E3) 1)
    (hazero : ∀ y ∈ V, (m y : E3) ∈ W → a y = 0)
    {U : Set E3} (hU : IsOpen U)
    (hsweep : ∀ t ∈ Icc (0 : Real) 1, ∀ y ∈ K,
      (1 + (1 - t) * a y) • (m y : E3) ∈ U) :
    ∃ S : Set E3, IsCompact S ∧ S ⊆ U ∧
      S ⊆ (radialDiskChart m hm hmi) '' (V ×ˢ Ioi (-1)) ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ EqOn G id W ∧
        ∀ y ∈ K, G ((1 + a y) • (m y : E3)) = (m y : E3) := by
  let c := radialDiskChart m hm hmi
  have hVsource : V ×ˢ Ioi (-1) ⊆ c.source :=
    fun _ hz => ⟨hVm hz.1, hz.2⟩
  have hopen : IsOpen ((V ×ˢ Ioi (-1)) ∩ c ⁻¹' U) :=
    (c.toOpenPartialHomeomorph.continuousOn.mono hVsource).isOpen_inter_preimage
      (hV.prod isOpen_Ioi) hU
  have htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ y ∈ K,
      (y, (1 - t) * a y) ∈ V ×ˢ Ioi (-1) := by
    intro t ht y hy
    refine ⟨hKV hy, ?_⟩
    change -1 < (1 - t) * a y
    by_cases hay : 0 ≤ a y
    · have := mul_nonneg (sub_nonneg.mpr ht.2) hay
      linarith
    · have := mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge hay)
      nlinarith [hapos y (hKV hy)]
  obtain ⟨S₀, hS₀, hS₀V, F, hFfix, hFzero, hFmap⟩ :=
    exists_supported_local_graph_flattening a hV ha hK hKV
      hopen (fun t ht y hy => ⟨htrace t ht y hy, hsweep t ht y hy⟩)
  have hS₀c : S₀ ⊆ c.source := by
    intro z hz
    exact hVsource (hS₀V hz).1
  obtain ⟨G, hGS, hGfix, _, hGcoord, _⟩ :=
    exists_supported_partial_chart_transport c F hS₀ hS₀c hFfix
  refine ⟨c '' S₀, hGS, ?_, image_mono (hS₀V.trans inter_subset_left),
    G, hGfix, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hS₀V hz).2
  · intro z hzW
    by_cases hzS : z ∈ c '' S₀
    · obtain ⟨u, hu, rfl⟩ := hzS
      have huV := (hS₀V hu).1
      have hpos : 0 < 1 + u.2 := by
        have ht : -1 < u.2 := huV.2
        linarith
      have hnorm : ‖c u‖ = 1 + u.2 := by
        change ‖(1 + u.2) • (m u.1 : E3)‖ = 1 + u.2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
          norm_eq_of_mem_sphere (m u.1), mul_one]
      have htzero : u.2 = 0 := by
        have hunit := mem_sphere_zero_iff_norm.mp (hWsphere hzW)
        rw [hnorm] at hunit
        linarith
      have hmy : (m u.1 : E3) ∈ W := by
        simpa only [c, radialDiskChart_apply, htzero, add_zero, one_smul] using hzW
      change G (c u) = c u
      rw [hGcoord u (hS₀c hu), hFzero u.1 u.2 (hazero u.1 huV.1 hmy)]
    · exact hGfix z hzS
  · intro y hy
    have hsource : (y, a y) ∈ c.source := ⟨hVm (hKV hy), hapos y (hKV hy)⟩
    have h := hGcoord (y, a y) hsource
    rw [hFmap y hy] at h
    simpa only [c, radialDiskChart_apply, add_zero, one_smul] using h



theorem exists_supported_radial_graph_flattening
    (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target)
    (a : E2 → Real) {V : Set E2} (hV : IsOpen V) (hVm : V ⊆ m.source)
    (ha : ContDiffOn Real ∞ a V) (hapos : ∀ y ∈ V, -1 < a y)
    {K : Set E2} (hK : IsCompact K) (hKV : K ⊆ V)
    {W : Set E3} (hWsphere : W ⊆ sphere (0 : E3) 1)
    (hazero : ∀ y ∈ V, (m y : E3) ∈ W → a y = 0) :
    ∃ S : Set E3, IsCompact S ∧
      S ⊆ (radialDiskChart m hm hmi) '' (V ×ˢ Ioi (-1)) ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ EqOn G id W ∧
        ∀ y ∈ K, G ((1 + a y) • (m y : E3)) = (m y : E3) := by
  obtain ⟨S, hS, _, hSV, G, hfix, hGW, hmap⟩ :=
    exists_supported_radial_graph_flattening_within m hm hmi a hV hVm ha hapos hK hKV
      hWsphere hazero isOpen_univ (fun _ _ _ _ => mem_univ _)
  exact ⟨S, hS, hSV, G, hfix, hGW, hmap⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
