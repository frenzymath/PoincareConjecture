import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.QuantitativeWindowControl
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Estimates.Local

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
  {epsilon K : ℝ} {U : Set M}

theorem exists_uniform_normalized_neck_derivative_bound
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hK : 0 < K) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (x : M)
      (N : QuantitativeBackwardNeck g D epsilon K U x)
      (W : NormalizedBackwardWindow N),
      letI := N.model.carrier.topologicalSpace
      letI := N.model.carrier.chartedSpace
      letI := N.model.carrier.isManifold
      ∀ p : N.model.carrier.carrier,
        IsCompact (closure ((W.halfFlow.metric (-(1 / 2 : ℝ))).ball p r)) →
        (W.halfFlow.metric (-(1 / 2 : ℝ))).ball p r ⊆
          N.model.embedding ⁻¹' N.neck.carrier →
        ∀ t ∈ Icc (-(1 / 4 : ℝ)) 0,
        ∀ y ∈ (W.halfFlow.metric (-(1 / 2 : ℝ))).ball p (r / 2),
          (W.halfFlow.connection t).curvatureDerivativeNorm m y ≤ B := by
  obtain ⟨C, hC, hbound⟩ := hShi 3 m K K r hK hK hr
  refine ⟨C / (1 / 4 : ℝ) ^ ((m : ℝ) / 2), by positivity, ?_⟩
  intro x N W
  let := N.model.carrier.topologicalSpace
  let := N.model.carrier.chartedSpace
  let := N.model.carrier.isManifold
  let := N.model.carrier.t2Space
  let := N.model.carrier.secondCountable
  intro p hcompact hcapture t ht y hy
  have hshift : (fun s : ℝ => s + (-(1 / 2 : ℝ))) '' Icc 0 (1 / 2 : ℝ) ⊆
      Icc (-(1 / 2 : ℝ)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  let F := W.halfFlow.translate (-(1 / 2 : ℝ)) hshift ordConnected_Icc
    ⟨0, by norm_num, 1 / 2, by norm_num, by norm_num⟩
  have hmetric : F.metric 0 = W.halfFlow.metric (-(1 / 2 : ℝ)) := by
    change W.halfFlow.metric (0 + -(1 / 2 : ℝ)) = _
    rw [zero_add]
  have hcurv : ∀ s ∈ Icc (0 : ℝ) (1 / 2), ∀ z ∈ (F.metric 0).ball p r,
      (F.connection s).curvatureTensorNorm z ≤ K := by
    intro s hs z hz
    have hcapt : N.model.embedding z ∈ N.neck.carrier := hcapture (hmetric ▸ hz)
    exact normalized_backward_window_curvature_bound N W
      (hshift ⟨s, hs, rfl⟩) z hcapt
  have htime : t + 1 / 2 ∈ Ioc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [ht.1, ht.2]
  have hderiv := hbound N.model.carrier.carrier (1 / 2) (by norm_num)
    (by rw [div_self hK.ne']; norm_num) F p (hmetric.symm ▸ hcompact) hcurv
    (t + 1 / 2) htime y (hmetric.symm ▸ hy)
  change (W.halfFlow.connection (t + 1 / 2 + -(1 / 2 : ℝ))).curvatureDerivativeNorm
    m y ≤ C / (t + 1 / 2) ^ ((m : ℝ) / 2) at hderiv
  rw [show t + 1 / 2 + -(1 / 2 : ℝ) = t by ring] at hderiv
  refine hderiv.trans (div_le_div_of_nonneg_left hC.le (by positivity) ?_)
  exact Real.rpow_le_rpow (by norm_num) (by linarith [ht.1]) (by positivity)

end PoincareConjecture.M28
