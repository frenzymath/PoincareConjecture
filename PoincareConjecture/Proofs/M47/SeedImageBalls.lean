import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_AmbientBalls
import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeImage
import PoincareConjecture.Proofs.M01.NormalizationScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.Proofs.M47

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

private theorem inverse_metric_le_four
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞)
    (hlower : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 4 * h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v))
    {y : Y} (hy : y ∈ C.target) (v : TangentSpace (𝓡 3) y) :
    g.inner (C.symm y) (mfderiv (𝓡 3) (𝓡 3) C.symm y v)
      (mfderiv (𝓡 3) (𝓡 3) C.symm y v) ≤ 4 * h.inner y v v := by
  have he : C.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨C.mdifferentiableOn (by simp), C.symm.mdifferentiableOn (by simp)⟩
  have hd : (mfderiv (𝓡 3) (𝓡 3) C (C.symm y)).comp
      (mfderiv (𝓡 3) (𝓡 3) C.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) y) := he.comp_symm_deriv hy
  have hv : mfderiv (𝓡 3) (𝓡 3) C (C.symm y)
      (mfderiv (𝓡 3) (𝓡 3) C.symm y v) = v := congrArg (fun A => A v) hd
  have hm := hlower (C.symm y) (C.map_target hy)
    (mfderiv (𝓡 3) (𝓡 3) C.symm y v)
  rw [hv] at hm
  have hright : C.toPartialEquiv (C.symm.toPartialEquiv y) = y := C.right_inv hy
  exact hm.trans_eq (congrArg (fun q : Y => 4 * h.inner q v v) hright)

theorem seed_ball_subset_image [RegularSpace X] [T2Space Y]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞)
    (hlower : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 4 * h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v))
    (p : X) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball p r)))
    (hsource : closure (g.ball p r) ⊆ C.source) :
    h.ball (C p) (r / 2) ⊆ C '' g.ball p r := by
  have hopen : IsOpen (g.ball p r) :=
    isOpen_Iio.preimage ((M36.metric_edist_continuous g).comp
      (continuous_const.prodMk continuous_id))
  have hCs := C.toOpenPartialHomeomorph.isOpen_image_of_subset_source hopen
    (subset_closure.trans hsource)
  have hclosure := C.toOpenPartialHomeomorph.image_closure_of_compact_buffer hcompact hsource
  have hfrontier := C.toOpenPartialHomeomorph.image_frontier_of_compact_buffer
    hopen hcompact hsource
  change IsOpen (C '' g.ball p r) at hCs
  change C '' closure (g.ball p r) = closure (C '' g.ball p r) at hclosure
  change C '' frontier (g.ball p r) = frontier (C '' g.ball p r) at hfrontier
  have hp : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have htarget : closure (C '' g.ball p r) ⊆ C.target := by
    rw [← hclosure]
    rintro _ ⟨x, hx, rfl⟩
    exact C.map_source (hsource hx)
  let k := m01RescaledMetric g (1 / 4) (by norm_num)
  apply h.ball_subset_of_inverse_length_barrier k C.symm hCs (mem_image_of_mem C hp)
  · intro y hy
    exact C.symm.contMDiffOn.contMDiffAt (C.open_target.mem_nhds (htarget hy))
  · intro y hy v
    have hm := inverse_metric_le_four g h C hlower (htarget hy) v
    change (m01RescaledMetric g (1 / 4) _).inner _ _ _ ≤ _
    rw [m01RescaledMetric_inner]
    linarith
  · intro y hy
    rw [← hfrontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hpSource := hsource (subset_closure hp)
    have hxSource := hsource hx.1
    have hleftP : C.symm.toPartialEquiv (C.toPartialEquiv p) = p := C.left_inv hpSource
    have hleftX : C.symm.toPartialEquiv (C.toPartialEquiv x) = x := C.left_inv hxSource
    rw [hleftP, hleftX]
    have hnot : x ∉ g.ball p r := by simpa only [hopen.interior_eq] using hx.2
    have hdist : ENNReal.ofReal r ≤ g.edist p x := le_of_not_gt hnot
    change ENNReal.ofReal (r / 2) ≤ (m01RescaledMetric g (1 / 4) _).edist p x
    rw [m01RescaledMetric_edist]
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hscale : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [Real.sqrt_div (by norm_num), Real.sqrt_one, hfour]
    rw [hscale]
    calc
      ENNReal.ofReal (r / 2) = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_right hdist _

theorem seed_image_ball_subset
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞)
    (hupper : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v) ≤ 4 * g.inner x v v)
    (p : X) {r : ℝ} (hsource : g.ball p r ⊆ C.source) :
    C '' g.ball p r ⊆ h.ball (C p) (2 * r) := by
  apply g.image_ball_subset_ball_of_tangentNorm_le_on_open h C C.open_source
    (C.contMDiffOn.of_le (by simp)) (by norm_num : (0 : ℝ) < 2) ?_ hsource le_rfl
  intro x hx v
  unfold RiemannianMetric.tangentNorm
  calc
    Real.sqrt _ ≤ Real.sqrt (4 * g.inner x v v) := Real.sqrt_le_sqrt (hupper x hx v)
    _ = 2 * Real.sqrt (g.inner x v v) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have hfour : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hfour]

end PoincareConjecture.Proofs.M47
