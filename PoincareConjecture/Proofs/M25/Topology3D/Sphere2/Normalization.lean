import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.ConeDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.LinearAction
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.LocalCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.GermCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.CompactChartTransport
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.OrthogonalPath

set_option autoImplicit false

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private instance sphereDimensionFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_sphere_pole_normalization (p : UnitTwoSphere)
    (f : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) :
    ∃ (A : E3 ≃ₗᵢ[ℝ] E3)
      (N : ℝ → UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
      (k : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
      (U : Set UnitTwoSphere),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × UnitTwoSphere => N q.1 q.2) ∧
      (∀ x, N 0 x = sphereMap A x) ∧
      (∀ x, N 1 (k x) = f x) ∧
      IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, k x = x := by
  let R := sphereConeExtension p f
  obtain ⟨L, hL, hLp⟩ := exists_sphereConeExtension_derivative_equiv p p f
  change (L : E3 →L[ℝ] E3) = fderiv ℝ R (p : E3) at hL
  let B := linearSphereDiffeomorph p L
  let g := f.trans B.symm
  let Q : E3 → E3 := fun x => L.symm (R x)
  have hR : DifferentiableAt ℝ R (p : E3) :=
    (contDiffAt_sphereConeExtension p f (ne_zero_of_mem_unit_sphere p)).differentiableAt
      (by simp)
  have hQ : DifferentiableAt ℝ Q (p : E3) :=
    (L.symm : E3 →L[ℝ] E3).differentiableAt.comp (p : E3) hR
  have hQp : Q (p : E3) = (p : E3) := by
    change L.symm (sphereConeExtension p f (p : E3)) = (p : E3)
    rw [sphereConeExtension_apply_sphere, ← hLp, L.symm_apply_apply]
  have hDQ : fderiv ℝ Q (p : E3) = ContinuousLinearMap.id ℝ E3 := by
    have hd := (L.symm : E3 →L[ℝ] E3).hasFDerivAt.comp (p : E3) hR.hasFDerivAt
    change HasFDerivAt Q
      ((L.symm : E3 →L[ℝ] E3).comp (fderiv ℝ R (p : E3))) (p : E3) at hd
    rw [← hL, ContinuousLinearEquiv.coe_symm_comp_coe] at hd
    exact hd.fderiv
  have hgQ (q : UnitTwoSphere) : g q = unitRadialProjection p (Q (q : E3)) := by
    change (linearSphereDiffeomorph p L).symm (f q) =
      unitRadialProjection p (L.symm (sphereConeExtension p f (q : E3)))
    rw [linearSphereDiffeomorph_symm_apply, sphereConeExtension_apply_sphere]
  have hgp : g p = p := by rw [hgQ, hQp, unitRadialProjection_apply_coe]
  obtain ⟨W, hW, hW0, hh, hh0, hdh0⟩ :=
    exists_local_sphere_identity_germ p g Q hQ hQp hDQ hgQ
  obtain ⟨r, hr, _, D, hD, hDI, hD0, hD1, hDfix, _⟩ :=
    exists_compact_germ_isotopy hW hW0 hh hh0 hdh0
  let T := spherePlaneChart (-p)
  have htarget (y : ℝ × ℝ) : y ∈ T.target :=
    spherePlaneChart_target (-p) ▸ mem_univ y
  obtain ⟨C, hC, _, hCs, _, _, hCfix⟩ :=
    exists_compact_chart_diffeomorph_family (𝓡 2) T
      (spherePlaneChart_target (-p)) (contMDiffOn_spherePlaneChart (-p))
      (contMDiff_spherePlaneChart_symm (-p)) D hD hDI
      (isCompact_closedBall (0 : ℝ × ℝ) (2 * r))
      (fun t x hx => (hDfix t x hx).1)
  have hC0 (x : UnitTwoSphere) : C 0 x = x := by
    by_cases hx : x ∈ T.source
    · rw [hC 0 x hx, hD0 0 le_rfl, T.left_inv hx]
    · apply (hCfix 0 x _).1
      rintro ⟨y, _, heq⟩
      exact hx (heq ▸ T.map_target (htarget y))
  have hps : p ∈ T.source := by
    simpa only [T, spherePlaneChart_source, mem_compl_iff, mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ p
  let U := (T.source ∩ T ⁻¹' ball (0 : ℝ × ℝ) r) ∩ g ⁻¹' T.source
  have hU : IsOpen U :=
    (T.continuousOn.isOpen_inter_preimage T.open_source isOpen_ball).inter
      (T.open_source.preimage g.continuous)
  have hpU : p ∈ U := by
    refine ⟨⟨hps, ?_⟩, ?_⟩
    · change T p ∈ ball (0 : ℝ × ℝ) r
      rw [spherePlaneChart_neg_apply]
      exact mem_ball_self hr
    · change g p ∈ T.source
      rw [hgp]
      exact hps
  have hC1 (x : UnitTwoSphere) (hx : x ∈ U) : C 1 x = g x := by
    rw [hC 1 x hx.1.1, hD1 1 le_rfl _ (ball_subset_closedBall hx.1.2)]
    change T.symm (T (g (T.symm (T x)))) = g x
    rw [T.left_inv hx.1.1, T.left_inv hx.2]
  let k := g.trans (C 1).symm
  have hk (x : UnitTwoSphere) (hx : x ∈ U) : k x = x := by
    change (C 1).symm (g x) = x
    rw [← hC1 x hx, (C 1).symm_apply_apply]
  obtain ⟨A, H, hH, _, hH0, hH1⟩ := exists_orthogonal_linear_path L
  let V (t : ℝ) := linearSphereDiffeomorph p (H (1 - t))
  have hrev : ContDiff ℝ ∞ (fun q : ℝ × E3 => H (1 - q.1) q.2) :=
    hH.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)
  have hVs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × UnitTwoSphere => V q.1 q.2) :=
    contMDiff_linearSphereDiffeomorph_family p (fun t => H (1 - t)) hrev
  have hV0 (x : UnitTwoSphere) : V 0 x = sphereMap A x := by
    change unitRadialProjection p (H (1 - 0) (x : E3)) = sphereMap A x
    rw [sub_zero, hH1 1 le_rfl]
    exact linearSphereDiffeomorph_isometry_apply p x A
  have hV1 (x : UnitTwoSphere) : V 1 x = B x := by
    change unitRadialProjection p (H (1 - 1) (x : E3)) =
      unitRadialProjection p (L (x : E3))
    rw [sub_self, hH0 0 le_rfl]
  let N (t : ℝ) := (C t).trans (V t)
  have hNs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × UnitTwoSphere => N q.1 q.2) :=
    hVs.comp (contMDiff_fst.prodMk hCs)
  refine ⟨A, N, k, U, hNs, ?_, ?_, hU, hpU, hk⟩
  · intro x
    change V 0 (C 0 x) = sphereMap A x
    rw [hC0, hV0]
  · intro x
    change V 1 (C 1 ((C 1).symm (g x))) = f x
    rw [(C 1).apply_symm_apply, hV1]
    exact B.apply_symm_apply (f x)

end PoincareConjecture.M25.Topology3D
