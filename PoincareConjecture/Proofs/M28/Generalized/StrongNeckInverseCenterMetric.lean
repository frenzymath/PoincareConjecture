import PoincareConjecture.Proofs.M28.Generalized.StrongNeckInverseCenterChart
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateGerms
import PoincareConjecture.Proofs.M13.Metric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u v

namespace PoincareConjecture.M28

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))

theorem strongNeck_half_pullbackCoefficients
    {Phi : E3 → strongNeckOpen S} {z : E3}
    (hPhi : MDifferentiableAt (𝓡 3) (𝓡 3) Phi z) :
    ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).pullbackCoefficients Phi z =
      (S.scale⁻¹ ^ 2) • (F.metric t).pullbackCoefficients
        ((Subtype.val : strongNeckOpen S → (F.slice t).carrier) ∘ Phi) z := by
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : strongNeckOpen S → (F.slice t).carrier) (Phi z) :=
    (contMDiff_subtype_val (I := 𝓡 3) (U := strongNeckOpen S) (n := 1)).mdifferentiable
      one_ne_zero (Phi z)
  ext v w
  change (H.rescaling.flow.metric 0).inner (Phi z)
      (mfderiv (𝓡 3) (𝓡 3) Phi z v) (mfderiv (𝓡 3) (𝓡 3) Phi z w) =
    (S.scale⁻¹ ^ 2) * (F.metric t).inner (Phi z).val
      (mfderiv (𝓡 3) (𝓡 3)
        ((Subtype.val : strongNeckOpen S → (F.slice t).carrier) ∘ Phi) z v)
      (mfderiv (𝓡 3) (𝓡 3)
        ((Subtype.val : strongNeckOpen S → (F.slice t).carrier) ∘ Phi) z w)
  rw [mfderiv_comp z hi hPhi]
  exact GeneralizedStrongNeck.rescaled_metric_at_zero S H (Phi z)
    (mfderiv (𝓡 3) (𝓡 3) Phi z v) (mfderiv (𝓡 3) (𝓡 3) Phi z w)

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

theorem inverseStrongNeckCenterChart_relative_metric
    (hepsilon : epsilon ≤ (1 / 200 : ℝ)) {R : ℝ} (hR : R < 1 / 8)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞)
    (hsource : Phi.source = Metric.ball 0 R)
    (htarget : Phi.target =
      ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        (strongNeckSourceCenter S) R)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞)
    (K : Set M)
    (hcore : ∀ y ∈ S.carrier,
      |(S.coordinate_inverse y).2| ≤ 2 * epsilon⁻¹ / 3 →
        y ∈ e.target ∧ e.symm y ∈ K)
    (gLimit : RiemannianMetric 3 M) (Q Ri delta : ℝ) (hRi : 0 < Ri)
    (hdelta : 0 < 1 + delta)
    (hrelative : ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      (1 + delta)⁻¹ * gLimit.inner x v v ≤
        Q * (F.metric t).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v) ∧
      Q * (F.metric t).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
        (1 + delta) * gLimit.inner x v v) :
    let Psi := inverseStrongNeckCenterChart S Phi e
    let a := Q * S.scale ^ 2
    ∀ z ∈ Metric.ball 0 R, ∀ v : E3,
      (Ri * a) / (1 + delta) *
          ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).pullbackCoefficients Phi z v v ≤
        RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric gLimit Ri hRi)
          Psi z v v ∧
      RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric gLimit Ri hRi)
          Psi z v v ≤
        (Ri * a) * (1 + delta) *
          ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).pullbackCoefficients
            Phi z v v := by
  let Psi := inverseStrongNeckCenterChart S Phi e
  obtain ⟨hPsi, hpoint, _, _, _, _⟩ :=
    inverseStrongNeckCenterChart_domain S H hepsilon hR Phi hsource htarget e K hcore
  dsimp only
  intro z hz v
  have hPhi : MDifferentiableAt (𝓡 3) (𝓡 3) Phi z :=
    Phi.mdifferentiableAt (by simp) (hsource.symm ▸ hz)
  have hPsiDiff : MDifferentiableAt (𝓡 3) (𝓡 3) Psi z :=
    Psi.mdifferentiableAt (by simp) (hPsi.symm ▸ hz)
  have hheight := strongNeck_center_chart_height S H hepsilon hR Phi hsource htarget hz
  have hcorez := hcore (Phi z).val (Phi z).property
    (hheight.trans (by have hi := inv_pos.mpr S.epsilon_pos; linarith))
  have heSource : Psi z ∈ e.source := e.symm.toPartialEquiv.map_source hcorez.1
  have heDiff : MDifferentiableAt (𝓡 3) (𝓡 3) e (Psi z) :=
    e.mdifferentiableAt (by simp) heSource
  have hcomposition : e ∘ Psi =ᶠ[𝓝 z]
      ((Subtype.val : strongNeckOpen S → (F.slice t).carrier) ∘ Phi) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact (hpoint y hy).2
  have hnorm := strongNeck_half_pullbackCoefficients S H hPhi
  have hraw : Q * (F.metric t).inner (e (Psi z))
        (mfderiv (𝓡 3) (𝓡 3) e (Psi z) (mfderiv (𝓡 3) (𝓡 3) Psi z v))
        (mfderiv (𝓡 3) (𝓡 3) e (Psi z) (mfderiv (𝓡 3) (𝓡 3) Psi z v)) =
      (Q * S.scale ^ 2) *
        ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).pullbackCoefficients
          Phi z v v := by
    calc
      _ = Q * (F.metric t).pullbackCoefficients (e ∘ Psi) z v v := by
        change _ = Q * (F.metric t).inner (e (Psi z))
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ Psi) z v)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ Psi) z v)
        rw [mfderiv_comp z heDiff hPsiDiff]
        rfl
      _ = Q * (F.metric t).pullbackCoefficients
          ((Subtype.val : strongNeckOpen S → (F.slice t).carrier) ∘ Phi) z v v := by
        rw [(F.metric t).pullbackCoefficients_eq_of_eventuallyEq hcomposition]
      _ = _ := by
        rw [hnorm]
        simp only [smul_apply, smul_eq_mul]
        field_simp [S.scale_pos.ne']
  let a := Q * S.scale ^ 2
  let h := ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).pullbackCoefficients Phi z v v
  let l := gLimit.pullbackCoefficients Psi z v v
  have hrel : (1 + delta)⁻¹ * l ≤ a * h ∧ a * h ≤ (1 + delta) * l := by
    have hh := hrelative (Psi z) (hpoint z hz).1 (mfderiv (𝓡 3) (𝓡 3) Psi z v)
    rw [hraw] at hh
    exact hh
  have hlower : a * h / (1 + delta) ≤ l := by
    apply (div_le_iff₀ hdelta).mpr
    nlinarith only [hrel.2]
  have hupper : l ≤ (1 + delta) * (a * h) := by
    have hh := mul_le_mul_of_nonneg_left hrel.1 hdelta.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hdelta.ne', one_mul] using hh
  change (Ri * a) / (1 + delta) * h ≤ Ri * l ∧
    Ri * l ≤ (Ri * a) * (1 + delta) * h
  constructor
  · calc
      (Ri * a) / (1 + delta) * h = Ri * (a * h / (1 + delta)) := by ring
      _ ≤ Ri * l := mul_le_mul_of_nonneg_left hlower hRi.le
  · calc
      Ri * l ≤ Ri * ((1 + delta) * (a * h)) :=
        mul_le_mul_of_nonneg_left hupper hRi.le
      _ = (Ri * a) * (1 + delta) * h := by ring

end PoincareConjecture.M28
