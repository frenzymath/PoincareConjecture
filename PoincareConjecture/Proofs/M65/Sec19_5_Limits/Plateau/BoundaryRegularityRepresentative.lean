import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityContinuity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.AttainmentIdentities

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

theorem boundary_pullback_interior_ae {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) {f : LoopPlane → M}
    (hf : f =ᵐ[volume.restrict (ball (0 : LoopPlane) 1)] F.value)
    {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧
      (f ∘ diskBoundaryCoordinate p) =ᵐ[
        volume.restrict (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1})]
          (F.value ∘ diskBoundaryCoordinate p) := by
  obtain ⟨R, hR, _hleft, _hcap, _hreg, C, _hC, hdom⟩ :=
    exists_boundary_halfDisk_pullback hp
  have hclosed : f =ᵐ[volume.restrict loopDiskSet] F.value := by
    filter_upwards [m65Ae_mem_openLoopDisk,
      ae_restrict_of_ae (ae_imp_of_ae_restrict hf)] with z hz heq
    exact heq hz
  exact ⟨R, hR, ae_of_ae_map (contDiff_diskBoundaryCoordinate p).continuous.measurable.aemeasurable
    (ae_mono hdom (Measure.ae_smul_measure hclosed C))⟩

theorem weakDisk_boundary_representative_matches_interior
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g)
    {f : LoopPlane → M} (hf : M65InteriorDiskRepresentative connection F f)
    {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ (r β H : ℝ) (q : LoopPlane → M),
      0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < H ∧ ContinuousOn q (closedBall 0 r) ∧
      (q =ᵐ[volume.restrict (closedBall 0 r)] fun z =>
        if 0 ≤ z 1 then F.value (diskBoundaryCoordinate p z)
          else F.value (diskBoundaryCoordinate p (boundaryPlaneReflection z))) ∧
      (∀ x ∈ closedBall (0 : LoopPlane) r, ∀ y ∈ closedBall (0 : LoopPlane) r,
        ‖e (q y) - e (q x)‖ ≤ H * dist y x ^ β) ∧
      (∀ s ∈ Icc (-r) r, q (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        γ (F.parameter (boundaryCirclePoint hp s))) ∧
      EqOn q (f ∘ diskBoundaryCoordinate p)
        (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      ContMDiffOn (𝓡 2) (𝓡 3) ∞ q (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) := by
  obtain ⟨R, β, H, q, hR, hβ, hβ1, hH, hq, hqAE, hholder, htrace⟩ :=
    weakDisk_boundary_continuous_representative g he hinj hemb compact hγ hsmooth hregular
      F hmin hp
  obtain ⟨Q, hQ, hpull⟩ := boundary_pullback_interior_ae F hf.value_ae hp
  let r := min R Q
  have hr : 0 < r := lt_min hR hQ
  have hrR : r ≤ R := min_le_left _ _
  have hrQ : r ≤ Q := min_le_right _ _
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hUR : U ⊆ closedBall (0 : LoopPlane) R :=
    inter_subset_left.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR))
  have hUQ : U ⊆ closedBall (0 : LoopPlane) Q ∩ {z | 0 ≤ z 1} := by
    intro z hz
    have hzpos : 0 < z 1 := hz.2
    exact ⟨closedBall_subset_closedBall hrQ (ball_subset_closedBall hz.1), hzpos.le⟩
  have hcap : MapsTo (diskBoundaryCoordinate p) U (ball (0 : LoopPlane) 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_diskBoundaryCoordinate hp, Real.exp_lt_one_iff]
    exact neg_neg_of_pos hz.2
  have hfs : ContMDiffOn (𝓡 2) (𝓡 3) ∞ (f ∘ diskBoundaryCoordinate p) U :=
    hf.smooth.comp (contDiff_diskBoundaryCoordinate p).contMDiff.contMDiffOn hcap
  have hAE : (e ∘ q) =ᵐ[volume.restrict U] e ∘ f ∘ diskBoundaryCoordinate p := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUR hqAE,
      ae_restrict_of_ae_restrict_of_subset hUQ hpull,
      ae_restrict_mem hU.measurableSet] with z hqz hfz hz
    have hzpos : 0 ≤ z 1 := hz.2.le
    simp only [if_pos hzpos] at hqz
    exact congrArg e (hqz.trans hfz.symm)
  have heq : EqOn q (f ∘ diskBoundaryCoordinate p) U := by
    have hh := Measure.eqOn_open_of_ae_eq hAE hU
      (he.continuous.comp_continuousOn (hq.mono hUR))
      (he.continuous.comp_continuousOn hfs.continuousOn)
    exact fun z hz => hemb.injective (hh hz)
  refine ⟨r, β, H, q, hr, hβ, hβ1, hH,
    hq.mono (closedBall_subset_closedBall hrR),
    ae_restrict_of_ae_restrict_of_subset (closedBall_subset_closedBall hrR) hqAE, ?_, ?_,
    heq, hfs.congr heq⟩
  · intro x hx y hy
    exact hholder x (closedBall_subset_closedBall hrR hx) y
      (closedBall_subset_closedBall hrR hy)
  · intro s hs
    exact htrace s (Icc_subset_Icc (neg_le_neg hrR) hrR hs)

end PoincareConjecture.M65Boundary
