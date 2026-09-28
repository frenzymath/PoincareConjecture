import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BoundaryAngularTrace
import PoincareConjecture.Definitions.M60Area

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def diskColumn (f : LoopPlane → M) (z : LoopPlane) (i : Fin 2) :
    TangentSpace (𝓡 3) (f z) :=
  mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)

theorem diskColumn_continuousOn (f : LoopPlane → M)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet) (i : Fin 2) :
    ContinuousOn (fun z => (⟨f z, diskColumn f z i⟩ : TangentBundle (𝓡 3) M))
      loopDiskSet :=
  (hf.continuousOn_tangentMapWithin le_rfl m65LoopDisk_uniqueMDiffOn).comp
    (((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn) (fun _ hw => hw)

omit [IsManifold (𝓡 3) ∞ M] in

theorem diskColumn_eq_mfderiv (f : LoopPlane → M) {z : LoopPlane}
    (hz : z ∈ Metric.ball (0 : LoopPlane) 1) (i : Fin 2) :
    diskColumn f z i = mfderiv (𝓡 2) (𝓡 3) f z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  have hmem : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  exact congrArg (fun L : TangentSpace (𝓡 2) z →L[ℝ] TangentSpace (𝓡 3) (f z) =>
    L (EuclideanSpace.basisFun (Fin 2) ℝ i)) (mfderivWithin_of_mem_nhds hmem)

def diskConformalFactor (g : RiemannianMetric 3 M) (f : LoopPlane → M)
    (z : LoopPlane) : ℝ := g.inner (f z) (diskColumn f z 0) (diskColumn f z 0)

theorem diskConformalFactor_continuousOn (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet) :
    ContinuousOn (diskConformalFactor g f) loopDiskSet :=
  m65Metric_pairing_continuousOn g f (fun z => diskColumn f z 0)
    (fun z => diskColumn f z 0) (diskColumn_continuousOn f hf 0)
    (diskColumn_continuousOn f hf 0)

theorem diskColumn_inner (g : RiemannianMetric 3 M) (f : LoopPlane → M)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {z : LoopPlane} (hz : z ∈ loopDiskSet) (i j : Fin 2) :
    g.inner (f z) (diskColumn f z i) (diskColumn f z j) =
      if i = j then diskConformalFactor g f z else 0 := by
  have heq : EqOn
      (fun w => g.inner (f w) (diskColumn f w i) (diskColumn f w j))
      (fun w => if i = j then diskConformalFactor g f w else 0)
      (Metric.ball (0 : LoopPlane) 1) := by
    intro w hw
    obtain ⟨c, hc⟩ := hconf w hw
    have hp (k l : Fin 2) : g.inner (f w) (diskColumn f w k) (diskColumn f w l) =
        if k = l then c else 0 := by
      simpa only [diskColumn_eq_mfderiv f hw, m60AreaGram, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A k l) hc
    have hc0 : diskConformalFactor g f w = c := by
      simpa only [diskConformalFactor, ite_true] using hp 0 0
    dsimp only
    rw [hc0]
    exact hp i j
  have hleft := m65Metric_pairing_continuousOn g f
    (fun w => diskColumn f w i) (fun w => diskColumn f w j)
    (diskColumn_continuousOn f hf i) (diskColumn_continuousOn f hf j)
  have hright : ContinuousOn
      (fun w => if i = j then diskConformalFactor g f w else 0) loopDiskSet := by
    split_ifs
    · exact diskConformalFactor_continuousOn g f hf
    · exact continuousOn_const
  exact heq.of_subset_closure hleft hright Metric.ball_subset_closedBall (by
    rw [closure_ball (0 : LoopPlane) one_ne_zero]
    exact Subset.rfl) hz

theorem diskDifferential_inner_self (g : RiemannianMetric 3 M) (f : LoopPlane → M)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {z : LoopPlane} (hz : z ∈ loopDiskSet) (v : LoopPlane) :
    g.inner (f z) (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z v)
      (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z v) =
        diskConformalFactor g f z * ‖v‖ ^ 2 := by
  have hv : v = v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.single]
  have hd : mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z v =
      v 0 • diskColumn f z 0 + v 1 • diskColumn f z 1 := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, diskColumn]
  rw [hd]
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
    diskColumn_inner g f hf hconf hz]
  simp only [Fin.isValue, ite_true, zero_ne_one, one_ne_zero, ite_false, mul_zero,
    add_zero, zero_add, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring

theorem diskConformalFactor_eq_zero_iff (g : RiemannianMetric 3 M) (f : LoopPlane → M)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {z : LoopPlane} (hz : z ∈ loopDiskSet) :
    diskConformalFactor g f z = 0 ↔ mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0 := by
  constructor
  · intro hc
    ext v
    change mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z v = 0
    by_contra hv
    have hpos := g.pos (f z) (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z v) hv
    rw [diskDifferential_inner_self g f hf hconf hz, hc, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  · intro hd
    simp [diskConformalFactor, diskColumn, hd]

theorem diskDifferential_eq_zero_of_direction (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {z : LoopPlane} (hz : z ∈ loopDiskSet) {v : LoopPlane} (hv : v ≠ 0)
    (hd : mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z v = 0) :
    mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0 := by
  apply (diskConformalFactor_eq_zero_iff g f hf hconf hz).mp
  have hnorm := diskDifferential_inner_self g f hf hconf hz v
  rw [hd] at hnorm
  have hh : diskConformalFactor g f z * ‖v‖ ^ 2 = 0 := by simpa using hnorm.symm
  exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ (norm_ne_zero_iff.mpr hv))

end PoincareConjecture.M65StrictTrace
