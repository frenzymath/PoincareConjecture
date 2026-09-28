import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Parametrization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

theorem locally_eventually_smooth_spacetime_parametrized_coefficients
    {J : Set ℝ} (hJ : IsOpen J) {g : ℕ → ℝ → RiemannianMetric n N}
    (hg : ∀ k, IsSmoothFamilyOn (g k) J) {f : ℕ → M → N}
    (hf : ∀ x : M, ∃ V, IsOpen V ∧ x ∈ V ∧
      ∀ᶠ k in atTop, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f k) V)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U) :
    ∀ z ∈ J ×ˢ U, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
          (g k y.1).pullbackCoefficients (f k ∘ e) y.2) W := by
  intro z hz
  obtain ⟨V, hV, hzV, hfV⟩ := hf (e z.2)
  let U' := U ∩ e ⁻¹' V
  have hU' : IsOpen U' := he.continuousOn.isOpen_inter_preimage hU hV
  refine ⟨J ×ˢ U', hJ.prod hU', ⟨hz.1, hz.2, hzV⟩, ?_⟩
  filter_upwards [hfV] with k hk p hp
  exact ((hg k).contDiffAt_spacetime_pullbackCoefficients hJ
    ((hk.contMDiffAt (hV.mem_nhds hp.2.2)).comp p.2
      (he.contMDiffAt (hU.mem_nhds hp.2.1))) hp.1).contDiffWithinAt

theorem tendstoUniformlyOn_parametrized_jets_of_chart_cover
    {ι : Type*} (q : ι → M) (hcover : ∀ x : M, ∃ i, x ∈ (extChartAt (𝓡 n) (q i)).source)
    {J : Set ℝ} (hJ : IsOpen J) {g : ℕ → ℝ → RiemannianMetric n N}
    {g₀ : ℝ → RiemannianMetric n M}
    (hg : ∀ k, IsSmoothFamilyOn (g k) J) (hg₀ : IsSmoothFamilyOn g₀ J)
    {f : ℕ → M → N}
    (hf : ∀ x : M, ∃ V, IsOpen V ∧ x ∈ V ∧
      ∀ᶠ k in atTop, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f k) V)
    (hjet : ∀ i r K, IsCompact K → K ⊆ J ×ˢ (extChartAt (𝓡 n) (q i)).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          (g k z.1).pullbackCoefficients (f k ∘ (extChartAt (𝓡 n) (q i)).symm) z.2))
        (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          (g₀ z.1).pullbackCoefficients (extChartAt (𝓡 n) (q i)).symm z.2)) atTop K)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (r : ℕ) {K : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKU : K ⊆ J ×ˢ U) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (g k z.1).pullbackCoefficients (f k ∘ e) z.2))
      (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (g₀ z.1).pullbackCoefficients e z.2)) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact (hJ.prod hU)).mp ?_ K hKU hK
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨i, hi⟩ := hcover (e z.2)
  obtain ⟨O, hO, hzO, hfO⟩ := hf (e z.2)
  let c := extChartAt (𝓡 n) (q i)
  let V := U ∩ e ⁻¹' (c.source ∩ O)
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage hU
    ((isOpen_extChartAt_source (I := 𝓡 n) (q i)).inter hO)
  have hzV : z.2 ∈ V := ⟨hz.2, hi, hzO⟩
  let α : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := c ∘ e
  have hα : ContDiffOn ℝ ∞ α V := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact (contMDiffOn_extChartAt (n := ∞) (x := q i)).comp (he.mono inter_subset_left)
      (fun _ hx => by simpa only [c, extChartAt_source, mem_preimage] using hx.2.1)
  have hαV : MapsTo α V c.target := fun x hx => c.map_source hx.2.1
  have hB₀ : ContDiffOn ℝ ∞ (fun y : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g₀ y.1).pullbackCoefficients c.symm y.2) (J ×ˢ c.target) := by
    intro y hy
    exact (hg₀.contDiffAt_spacetime_pullbackCoefficients hJ
      ((contMDiffOn_extChartAt_symm (n := ∞) (q i)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) (q i)).mem_nhds hy.2)) hy.1).contDiffWithinAt
  have htrans := smooth_convergence_fixed_spacetime_bilinear_pullback hJ hV
    (isOpen_extChartAt_target (I := 𝓡 n) (q i)) hα hαV hB₀
    (locally_eventually_smooth_spacetime_parametrized_coefficients hJ hg hf
      (isOpen_extChartAt_target (I := 𝓡 n) (q i)) (contMDiffOn_extChartAt_symm (n := ∞) (q i)))
    (hjet i)
  let W := J ×ˢ V
  have hW : IsOpen W := hJ.prod hV
  obtain ⟨A, ⟨hAn, hA⟩, hAW⟩ := (compact_basis_nhds z).mem_iff.mp (hW.mem_nhds ⟨hz.1, hzV⟩)
  refine ⟨A, nhdsWithin_le_nhds hAn, ((htrans r A hA hAW).congr ?_).congr_right ?_⟩
  · filter_upwards [hfO] with k hk y hy
    have heq : EqOn
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((g k p.1).pullbackCoefficients (f k ∘ c.symm) (α p.2)).bilinearComp
            (fderiv ℝ α p.2) (fderiv ℝ α p.2))
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (g k p.1).pullbackCoefficients (f k ∘ e) p.2) W := by
      intro p hp
      have hcs : c.symm (α p.2) = e p.2 := c.left_inv hp.2.2.1
      have hψ : MDifferentiableAt (𝓡 n) (𝓡 n) (f k ∘ c.symm) (α p.2) := by
        have hh := hk.contMDiffAt (hO.mem_nhds hp.2.2.2)
        rw [← hcs] at hh
        exact (hh.comp _ ((contMDiffOn_extChartAt_symm (n := ∞) (q i)).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 n) (q i)).mem_nhds (hαV hp.2)))).mdifferentiableAt
            (by simp)
      have hcompose : (f k ∘ c.symm) ∘ α =ᶠ[𝓝 p.2] f k ∘ e := by
        filter_upwards [hV.mem_nhds hp.2] with x hx
        dsimp only [α, Function.comp_apply]
        rw [c.left_inv hx.2.1]
      ext v w
      exact (g k p.1).pullbackCoefficients_comp_of_eventuallyEq hψ
        ((hα.contDiffAt (hV.mem_nhds hp.2)).differentiableAt (by simp)) hcompose v w
    exact (eqOn_iteratedFDeriv_of_isOpen hW heq r) (hAW hy)
  · intro y hy
    have heq : EqOn
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((g₀ p.1).pullbackCoefficients c.symm (α p.2)).bilinearComp
            (fderiv ℝ α p.2) (fderiv ℝ α p.2))
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g₀ p.1).pullbackCoefficients e p.2) W := by
      intro p hp
      have hcompose : c.symm ∘ α =ᶠ[𝓝 p.2] e := by
        filter_upwards [hV.mem_nhds hp.2] with x hx
        exact c.left_inv hx.2.1
      ext v w
      exact (g₀ p.1).pullbackCoefficients_comp_of_eventuallyEq
        (((contMDiffOn_extChartAt_symm (n := ∞) (q i)).contMDiffAt
          ((isOpen_extChartAt_target (I := 𝓡 n) (q i)).mem_nhds (hαV hp.2))).mdifferentiableAt
            (by simp))
        ((hα.contDiffAt (hV.mem_nhds hp.2)).differentiableAt (by simp)) hcompose v w
    exact (eqOn_iteratedFDeriv_of_isOpen hW heq r) (hAW hy)

end PoincareConjecture.RiemannianMetric
