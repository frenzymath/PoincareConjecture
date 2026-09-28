import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private theorem exists_global_extension_near_zero
    {g : E2 → E2} {U : Set E2} (hU : IsOpen U) (hg : ContDiffOn Real ∞ g U)
    (h0 : 0 ∈ U) (hbij : Bijective (fderiv Real g 0)) :
    ∃ r > 0, closedBall (0 : E2) r ⊆ U ∧
      ∃ G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ x ∈ closedBall (0 : E2) r, G x = g x := by
  let L := ContinuousLinearEquiv.ofBijective (fderiv Real g 0)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hg0 : ContDiffAt Real ∞ g 0 := hg.contDiffAt (hU.mem_nhds h0)
  have hd : HasFDerivAt g L.toContinuousLinearMap 0 :=
    (hg0.differentiableAt (by simp)).hasFDerivAt
  let Q := hg0.toOpenPartialHomeomorph g hd (by simp)
  let V := U ∩ (fderiv Real g) ⁻¹'
    range (fun B : E2 ≃L[Real] E2 => B.toContinuousLinearMap)
  have hV : IsOpen V :=
    (hg.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen
  have h0V : (0 : E2) ∈ V := ⟨h0, L, rfl⟩
  have hloc : IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ g V := by
    apply Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv hV
      (hg.mono inter_subset_left).contMDiffOn
    rintro x ⟨_, B, hB⟩
    rw [mfderiv_eq_fderiv, ← hB]
    exact B.bijective
  have h0Q : (0 : E2) ∈ Q.source := hg0.mem_toOpenPartialHomeomorph_source hd (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hV.inter Q.open_source).mem_nhds ⟨h0V, h0Q⟩)
  obtain ⟨G, hG⟩ := exists_global_extension_of_local_ball_embedding hr g
    (fun x hx y hy hxy => Q.injOn (hball hx).2 (hball hy).2 hxy)
    (fun x hx => hloc ⟨x, (hball hx).1⟩)
  exact ⟨r, hr, fun x hx => (hball hx).1.1, G, hG⟩

theorem exists_height_preserving_critical_graph_with_plane_action
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 → Real)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) + ∑ i : Fin 2, σ i * x i ^ 2) :
    ∃ J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ, ∃ r > 0,
      closedBall (0 : E2) r ⊆ e.source ∧
      ∃ A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
          (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : (Real ∙ v)ᗮ),
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        ∀ x ∈ closedBall (0 : E2) r,
          D (f (e x)) = (J x : E3) +
            (inner Real v (f p) + ∑ i : Fin 2, σ i * x i ^ 2) • v := by
  let J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr.symm
  let g : E2 → E2 := fun x => J.symm ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (e x)))
  have hg : ContDiffOn Real ∞ g e.source :=
    J.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      ((Real ∙ v)ᗮ.orthogonalProjectionOnto.contDiff.comp_contDiffOn
        (hf.contMDiff.comp_contMDiffOn he).contDiffOn)
  obtain ⟨r, hr, hrs, G, hG⟩ := exists_global_extension_near_zero e.open_source hg he0
    (bijective_fderiv_critical_planar_projection hf hv p hp e he0 hep he hei J)
  let H := J.toContinuousLinearEquiv.toDiffeomorph
  let A := (H.symm.trans G.symm).trans H
  let D := Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv 0 1 one_ne_zero A
  refine ⟨J, r, hr, hrs, A, D, ?_, ?_, ?_⟩
  · intro y
    simpa [D] using
      Poincare.Geometry.Euclidean.inner_liftPlaneDiffeomorph hv 0 1 one_ne_zero A y
  · intro t x
    change Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv 0 1 one_ne_zero A _ = _
    simp [Poincare.Geometry.Euclidean.liftPlaneDiffeomorph_apply,
      inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property]
  · intro x hx
    have hA : A ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (e x))) = J x := by
      change J (G.symm (g x)) = J x
      rw [← hG x hx, G.symm_apply_apply]
    rw [show D (f (e x)) = _ from
      Poincare.Geometry.Euclidean.liftPlaneDiffeomorph_apply hv 0 1 one_ne_zero A (f (e x)),
      hA, hform x (hrs hx)]
    simp only [one_mul, zero_add, add_comm]

theorem exists_height_preserving_critical_graph
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 → Real)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) + ∑ i : Fin 2, σ i * x i ^ 2) :
    ∃ J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ, ∃ r > 0,
      closedBall (0 : E2) r ⊆ e.source ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        ∀ x ∈ closedBall (0 : E2) r,
          D (f (e x)) = (J x : E3) +
            (inner Real v (f p) + ∑ i : Fin 2, σ i * x i ^ 2) • v := by
  obtain ⟨J, r, hr, hrs, _, D, hDheight, _, hD⟩ :=
    exists_height_preserving_critical_graph_with_plane_action hf hv p hp e he0 hep he hei σ hform
  exact ⟨J, r, hr, hrs, D, hDheight, hD⟩

end Poincare.Manifold.Schoenflies
