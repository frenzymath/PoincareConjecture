import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Chart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Linearization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E A H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}

theorem exists_supported_chart_linearization
    (e d : OpenPartialHomeomorph E M)
    (he : ContMDiffOn 𝓘(Real, E) I ∞ e e.source)
    (hei : ContMDiffOn I 𝓘(Real, E) ∞ e.symm e.target)
    (hd : ContMDiffOn 𝓘(Real, E) I ∞ d d.source)
    (hdi : ContMDiffOn I 𝓘(Real, E) ∞ d.symm d.target)
    (he0 : (0 : E) ∈ e.source) (hd0 : (0 : E) ∈ d.source)
    (hcenter : e 0 = d 0) :
    ∃ r : Real, 0 < r ∧ ∃ L : E ≃L[Real] E,
      ∃ K : Set M, IsCompact K ∧ K ⊆ d.target ∧
      ∃ Phi : Real -> Diffeomorph I I M M ∞,
      (∀ x, Phi 0 x = x) ∧
      ContMDiff (𝓘(Real, Real).prod I) I ∞ (fun p : Real × M => Phi p.1 p.2) ∧
      (∀ t x, x ∉ K -> Phi t x = x) ∧
      MapsTo L (closedBall (0 : E) r) d.source ∧
      ∀ x ∈ closedBall (0 : E) r, Phi 1 (e x) = d (L x) := by
  let C := e.trans d.symm
  have hC0 : (0 : E) ∈ C.source := by
    refine ⟨he0, ?_⟩
    change e 0 ∈ d.target
    rw [hcenter]
    exact d.map_source hd0
  have hC : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ C C.source :=
    hdi.comp (he.mono inter_subset_left) inter_subset_right
  have hCi : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ C.symm C.target :=
    hei.comp (hd.mono inter_subset_left) inter_subset_right
  let D : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toPartialEquiv := C.toPartialEquiv
    open_source := C.open_source
    open_target := C.open_target
    contMDiffOn_toFun := hC
    contMDiffOn_invFun := hCi }
  have hlocal : IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞ C 0 :=
    ⟨D, hC0, fun _ _ => rfl⟩
  have hCb : Function.Bijective (fderiv Real C 0) := by
    have H := (hlocal.mfderivToContinuousLinearEquiv (by simp)).bijective
    change Function.Bijective (mfderiv 𝓘(Real, E) 𝓘(Real, E) C 0) at H
    simpa only [mfderiv_eq_fderiv, TangentSpace] using H
  obtain ⟨G, V, hG, hV, h0V, hVC, hGC⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact isCompact_singleton C.open_source
      (singleton_subset_iff.mpr hC0) C (by
        intro x hx
        exact (hC.contMDiffAt (C.open_source.mem_nhds hx)).contDiffAt.contDiffWithinAt)
  have hG0 : G 0 = 0 := by
    rw [hGC (h0V (mem_singleton 0))]
    change d.symm (e 0) = 0
    rw [hcenter, d.left_inv hd0]
  have hGb : Function.Bijective (fderiv Real G 0) := by
    have heq : G =ᶠ[𝓝 (0 : E)] C := by
      filter_upwards [hV.mem_nhds (h0V (mem_singleton 0))] with x hx
      exact hGC hx
    rw [heq.fderiv_eq]
    exact hCb
  obtain ⟨rho, hrho, S, hS, hSd, Q, hQ0, hQs, hQfix, hQmotion⟩ :=
    exists_supported_linearization_isotopy_within G hG hGb d.open_source hd0
  obtain ⟨delta, hdelta, hdeltaV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  let r := min rho delta
  have hr : 0 < r := lt_min hrho hdelta
  let L : E ≃L[Real] E := ContinuousLinearEquiv.ofBijective (fderiv Real G 0)
    (LinearMap.ker_eq_bot.mpr hGb.1) (LinearMap.range_eq_top.mpr hGb.2)
  obtain ⟨hK, hKd, Phi, hi, hs, hfix, hcoord⟩ :=
    exists_supported_chart_isotopy d hd hdi hS hSd Q hQ0 hQs hQfix
  have hxV (x : E) (hx : x ∈ closedBall (0 : E) r) : x ∈ V :=
    hdeltaV (closedBall_subset_closedBall (min_le_right _ _) hx)
  have hxC (x : E) (hx : x ∈ closedBall (0 : E) r) : x ∈ C.source := hVC (hxV x hx)
  have hGxd (x : E) (hx : x ∈ closedBall (0 : E) r) : G x ∈ d.source := by
    rw [hGC (hxV x hx)]
    exact d.map_target (hxC x hx).2
  have hmotion (x : E) (hx : x ∈ closedBall (0 : E) r) : Q 1 (G x) = L x := by
    have h := hQmotion 1 (show (1 : Real) ∈ Icc 0 1 by simp) x
      (closedBall_subset_closedBall (min_le_left _ _) hx)
    change Q 1 (G x) = fderiv Real G 0 x
    simpa only [hG0, sub_zero, sub_self, zero_smul, one_smul, zero_add] using h
  refine ⟨r, hr, L, d '' S, hK, hKd, Phi, hi, hs, hfix, ?_, ?_⟩
  · intro x hx
    by_contra hout
    have hnot : L x ∉ S := fun h => hout (hSd h)
    have hequal : L x = G x := (Q 1).injective ((hQfix 1 (L x) hnot).trans (hmotion x hx).symm)
    exact hout (hequal.symm ▸ hGxd x hx)
  intro x hx
  have heG : d (G x) = e x := by
    rw [hGC (hxV x hx)]
    exact d.right_inv (hxC x hx).2
  rw [← heG, hcoord 1 (G x) (hGxd x hx), hmotion x hx]

end Poincare.Manifold.Schoenflies
