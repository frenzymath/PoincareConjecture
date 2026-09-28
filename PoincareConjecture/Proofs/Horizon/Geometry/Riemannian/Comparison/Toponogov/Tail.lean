import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Shift
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Regular
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.SegmentRegular
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Inverse










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_smooth_radial_inverse_branch_of_shift
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (p x : M) (hpx : p ≠ x) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ (ε : ℝ) (γ : ℝ → M) (R : ℝ)
      (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (e : EuclideanSpace ℝ (Fin n) → M)
      (v : EuclideanSpace ℝ (Fin n))
      (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M),
      0 < ε ∧
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧
      γ 0 = p ∧ γ 1 = x ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p x) ∧
      0 < R ∧ (g.edist p x).toReal < R ∧
      (∀ a b, g.pullbackCoefficients (extChartAt (𝓡 n) (γ δ)).symm
        (extChartAt (𝓡 n) (γ δ) (γ δ)) (L a) (L b) = inner ℝ a b) ∧
      (∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧
      e 0 = γ δ ∧
      HasFDerivAt (fun w => extChartAt (𝓡 n) (γ δ) (e w))
        L.toContinuousLinearMap 0 ∧
      (∀ w ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • w))
          {t : ℝ | t • w ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (e (t • w))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • w)) t 1) = ‖w‖ ∧
          g.edist (γ δ) (e (t • w)) ≤
            ENNReal.ofReal ‖w‖ * ENNReal.ofReal t) ∧
      v ∈ Metric.ball 0 R ∧ v ≠ 0 ∧ e v = x ∧
      ‖v‖ = (1 - δ) * (g.edist p x).toReal ∧
      (g.edist p (γ δ)).toReal + ‖v‖ = (g.edist p x).toReal ∧
      (g.edist p (e 0)).toReal = δ * (g.edist p x).toReal ∧
      g.edist (e 0) (e v) = ENNReal.ofReal ‖v‖ ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        (mfderiv (𝓡 n) (𝓡 n) e (s • v)).IsInvertible) ∧
      v ∈ B.source ∧ B.source ⊆ Metric.ball 0 R ∧
      EqOn e B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target ∧
      (∀ y ∈ B.target, B.symm y ≠ 0) ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ‖B.symm y‖) B.target ∧
      (∀ y ∈ B.target,
        (g.edist p y).toReal ≤ δ * (g.edist p x).toReal + ‖B.symm y‖) := by
  have hdpos : 0 < g.edist p x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    exact edist_pos.mpr hpx
  have hdistpos : 0 < (g.edist p x).toReal :=
    ENNReal.toReal_pos hdpos.ne' (g.edist_ne_top p x)
  let R := (g.edist p x).toReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hcomplete p x
  obtain ⟨L, e, hL, he, he0, hed, hrad⟩ :=
    g.exists_orthonormal_radial_exponential_of_metricComplete hcomplete (γ δ) hR
  have hgeo := fun w hw => (hrad w hw).1
  have hspeed := fun w hw t ht => ((hrad w hw).2 t ht).1
  have hmetric := g.pullbackCoefficients_zero_of_orthonormal (γ δ)
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds
      (show (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 R by simpa using hR)))
    he0 hed hL
  obtain ⟨v, hv, hnorm, hx, hsplit, hmatch⟩ := exists_shifted_radial_vector_of_le_half
    g hε hγ hγ0 hγ1 hmin hδ hδhalf
    (by dsimp [R]; linarith) L e hL he0 hed hgeo
  have hδone : δ < 1 := by linarith
  have hden : 0 < 1 - δ := by linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; positivity)
  have heorigin := he.contMDiffAt (Metric.isOpen_ball.mem_nhds
    (show (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 R by simpa using hR))
  have hinit := isInvertible_mfderiv_zero_of_chart_derivative
    (heorigin.mdifferentiableAt (by simp)) he0 hed
  let β : ℝ := δ / (1 - δ)
  have hβ : 0 < β := by dsimp [β]; exact div_pos hδ hden
  have hβone : β ≤ 1 := by
    dsimp [β]
    exact (div_le_iff₀ hden).2 (by linarith [hδhalf])
  have hβmem : -β ∈ Icc (-δ / (1 - δ)) (1 : ℝ) := by
    dsimp [β]
    constructor
    · simp [div_eq_mul_inv]
    · have := div_nonneg hδ.le hden.le
      linarith
  have hback : e ((-β) • v) = p := by
    have h := (hmatch (-β) hβmem).self_of_nhds
    have harg : (1 - δ) * (-β) + δ = 0 := by
      dsimp [β]
      field_simp [ne_of_gt hden]
      ring
    change e ((-β) • v) = γ ((1 - δ) * (-β) + δ) at h
    rw [harg] at h
    exact h.trans hγ0
  have hminback : g.edist (e ((-β) • v)) (e v) =
      ENNReal.ofReal ((1 + β) * ‖v‖) := by
    have hcoef : (1 + β) * ((1 - δ) * (g.edist p x).toReal) =
        (g.edist p x).toReal := by
      dsimp [β]
      field_simp [ne_of_gt hden]
      ring
    rw [hback, hx, hnorm, hcoef,
      ENNReal.ofReal_toReal (g.edist_ne_top p x)]
  have hend := isInvertible_mfderiv_of_minimizing_backward_extension_of_le_one
    g D he hinit hgeo hspeed hv hv0 hβ hβone hminback
  have htailq : g.edist (γ δ) (e v) = ENNReal.ofReal ‖v‖ := by
    have h := hmin δ (by constructor <;> linarith [hδ, hδhalf]) 1 (by norm_num)
    rw [hx]
    rw [hγ1] at h
    rw [abs_of_nonpos (by linarith [hδhalf])] at h
    have hcoef : -(δ - 1) = 1 - δ := by ring
    rw [hcoef] at h
    rw [h, hnorm, ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - δ),
      ENNReal.ofReal_toReal (g.edist_ne_top p x)]
  have htailmin : g.edist (e 0) (e v) = ENNReal.ofReal ‖v‖ := by
    simpa only [he0] using htailq
  have hi := isInvertible_mfderiv_on_minimizing_segment g D
    he he0 hinit hgeo hspeed hv hv0 htailq hend
  have hi1 : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
    have h := hi 1 (by simp)
    rw [one_smul] at h
    exact h
  obtain ⟨B, hvB, hBU, heB, hB, hBi, hzero, hnormB⟩ :=
    exists_smooth_radial_inverse_branch Metric.isOpen_ball he hv hv0
      hi1
  have hbound : ∀ w ∈ Metric.ball 0 R,
      g.edist (γ δ) (e w) ≤ ENNReal.ofReal ‖w‖ := by
    intro w hw
    simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hrad w hw).2 1 (by simp)).2
  have hmajor := inverse_branch_distance_majorant g p (γ δ)
    hbound B hBU heB (left := δ * (g.edist p x).toReal)
  have hleftq : (g.edist p (γ δ)).toReal = δ * (g.edist p x).toReal := by
    have h := hmin 0 (by norm_num) δ (by constructor <;> linarith [hδ, hδhalf])
    rw [hγ0] at h
    have hreal := congrArg ENNReal.toReal h
    have habs : |(0 : ℝ) - δ| = δ := by
      have hnonpos : (0 : ℝ) - δ ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      ring
    rw [habs] at hreal
    simpa only [ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_mul] using hreal
  have hleft : (g.edist p (e 0)).toReal = δ * (g.edist p x).toReal := by
    simpa only [he0] using hleftq
  refine ⟨ε, γ, R, L, e, v, B, hε, hγ, hγ0, hγ1, hmin, hR,
    (by dsimp [R]; linarith), hL, hmetric, he, he0, hed, hrad, hv, hv0, hx, hnorm,
    hsplit, hleft, htailmin, hi, hvB, hBU, heB, hB, hBi, hzero, hnormB, ?_⟩
  intro y hy
  exact hmajor hleftq hy

end PoincareConjecture.RiemannianMetric
