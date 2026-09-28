import PoincareConjecture.Proofs.M32.Claim11_35.WorldlineScalar
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M32

theorem normalizedCylinderScalar_monotoneOn_of_laplacian_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hI : Convex ℝ I)
    {x : C.carrier} (hx : x ∈ U)
    (hsmall : ∀ s (hs : s ∈ I),
      |(F.connection (origin + s / scale)).laplacian
        (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x)| ≤
      ((F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x)) ^ 2 / 6) :
    MonotoneOn (normalizedCylinderScalar e x) I := by
  classical
  let d : ℝ → ℝ := fun s => if hs : s ∈ I then
    let p := e.pointMap s hs x
    ((F.connection p.1).laplacian (F.connection p.1).scalarCurvature p.2 +
      2 * (F.connection p.1).ricciNormSq p.2) / scale ^ 2 else 0
  have hd (s : ℝ) (hs : s ∈ I) :
      HasDerivWithinAt (normalizedCylinderScalar e x) (d s) I s ∧
        (normalizedCylinderScalar e x s) ^ 2 / 2 ≤ d s := by
    simpa only [d, dif_pos hs] using
      normalizedCylinderScalar_derivative_ge_half_sq hM04 e hs hx (hsmall s hs)
  apply monotoneOn_of_hasDerivWithinAt_nonneg hI
    (fun s hs => (hd s hs).1.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).1.mono interior_subset)
  intro s hs
  exact (div_nonneg (sq_nonneg _) (by norm_num)).trans (hd s (interior_subset hs)).2

theorem exists_strongNeck_scalarComparison_along_cylinder
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
        {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier},
        ∀ (e : GeneralizedFlowCylinder F C origin scale I U) (_hI : Convex ℝ I)
          (x : C.carrier), x ∈ U →
          (∀ s (hs : s ∈ I), ∃ epsilon : ℝ, epsilon ≤ epsilon₀ ∧
            ∃ N : GeneralizedStrongNeck F (origin + s / scale) epsilon,
              N.center = e.forward s hs x) →
          ∀ s t (hs : s ∈ I) (ht : t ∈ I), s ≤ t →
            F.scalar (e.pointMap s hs x) ≤ F.scalar (e.pointMap t ht x) := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    exists_strongNeck_center_scalarLaplacian_bound.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F C origin scale I U e hI x hx hcenters
  have hbound := normalizedCylinderScalar_monotoneOn_of_laplacian_bound hM04 e hI hx
    (fun s hs => by
      obtain ⟨epsilon, hepsilon, N, hcenter⟩ := hcenters s hs
      simpa only [hcenter] using hcontrol N hepsilon)
  intro s t hs ht hst
  have h := hbound hs ht hst
  simp only [normalizedCylinderScalar, dif_pos hs, dif_pos ht] at h
  exact (div_le_div_iff_of_pos_right e.scale_pos).mp h

end PoincareConjecture.M32
