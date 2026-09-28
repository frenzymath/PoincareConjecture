import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskTrace









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65MinimalDisk

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {γ : C1FreeLoopSpace (M := M)}



noncomputable def conformalFactor (S : M65MinimalDisk g connection γ)
    (z : LoopPlane) : ℝ :=
  g.inner (S.disk.map z) (S.boundaryColumn z 0) (S.boundaryColumn z 0)



theorem conformalFactor_continuousOn (S : M65MinimalDisk g connection γ) :
    ContinuousOn S.conformalFactor loopDiskSet :=
  m65Metric_pairing_continuousOn g S.disk.map (fun z => S.boundaryColumn z 0)
    (fun z => S.boundaryColumn z 0) (S.boundaryColumn_continuousOn 0)
    (S.boundaryColumn_continuousOn 0)



theorem boundaryColumn_inner (S : M65MinimalDisk g connection γ)
    {z : LoopPlane} (hz : z ∈ loopDiskSet) (i j : Fin 2) :
    g.inner (S.disk.map z) (S.boundaryColumn z i) (S.boundaryColumn z j) =
      if i = j then S.conformalFactor z else 0 := by
  have heq : EqOn
      (fun w => g.inner (S.disk.map w) (S.boundaryColumn w i) (S.boundaryColumn w j))
      (fun w => if i = j then S.conformalFactor w else 0)
      (Metric.ball (0 : LoopPlane) 1) := by
    intro w hw
    obtain ⟨c, hc⟩ := S.weakly_conformal w hw
    have hpair (k l : Fin 2) :
        g.inner (S.disk.map w) (S.boundaryColumn w k) (S.boundaryColumn w l) =
          if k = l then c else 0 := by
      simpa only [S.boundaryColumn_eq_mfderiv hw, m60AreaGram, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] using
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A k l) hc
    have hfactor : S.conformalFactor w = c := by
      simpa only [conformalFactor, ite_true] using hpair 0 0
    dsimp only
    rw [hfactor]
    exact hpair i j
  have hleft := m65Metric_pairing_continuousOn g S.disk.map
    (fun w => S.boundaryColumn w i) (fun w => S.boundaryColumn w j)
    (S.boundaryColumn_continuousOn i) (S.boundaryColumn_continuousOn j)
  have hright : ContinuousOn (fun w => if i = j then S.conformalFactor w else 0)
      loopDiskSet := by
    split_ifs
    · exact S.conformalFactor_continuousOn
    · exact continuousOn_const
  exact heq.of_subset_closure hleft hright Metric.ball_subset_closedBall (by
    rw [closure_ball (0 : LoopPlane) one_ne_zero]
    exact Subset.rfl) hz



theorem conformalFactor_nonneg (S : M65MinimalDisk g connection γ) (z : LoopPlane) :
    0 ≤ S.conformalFactor z := by
  by_cases h : S.boundaryColumn z 0 = 0
  · simp [conformalFactor, h]
  · exact (g.pos (S.disk.map z) (S.boundaryColumn z 0) h).le



theorem withinDifferential_inner_self (S : M65MinimalDisk g connection γ)
    {z : LoopPlane} (hz : z ∈ loopDiskSet) (v : LoopPlane) :
    g.inner (S.disk.map z)
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z v)
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z v) =
        S.conformalFactor z * ‖v‖ ^ 2 := by
  have hv : v = v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.single]
  have hd : mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z v =
      v 0 • S.boundaryColumn z 0 + v 1 • S.boundaryColumn z 1 := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, boundaryColumn]
  rw [hd]
  simp only [map_add, add_apply, map_smul,
    smul_apply, smul_eq_mul, S.boundaryColumn_inner hz]
  simp only [Fin.isValue, ite_true, zero_ne_one, one_ne_zero, ite_false, mul_zero,
    add_zero, zero_add, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring



theorem conformalFactor_eq_zero_iff (S : M65MinimalDisk g connection γ)
    {z : LoopPlane} (hz : z ∈ loopDiskSet) :
    S.conformalFactor z = 0 ↔
      mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z = 0 := by
  constructor
  · intro hc
    ext v
    change mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z v = 0
    by_contra hv
    have hpos := g.pos (S.disk.map z)
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z v) hv
    rw [S.withinDifferential_inner_self hz, hc, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  · intro hd
    simp [conformalFactor, boundaryColumn, hd]



theorem conformalFactor_finite_zeros (S : M65MinimalDisk g connection γ) :
    {z : LoopPlane | z ∈ loopDiskSet ∧ S.conformalFactor z = 0}.Finite := by
  convert S.finite_branches using 1
  ext z
  exact and_congr_right fun hz => S.conformalFactor_eq_zero_iff hz



theorem withinDifferential_injective (S : M65MinimalDisk g connection γ)
    {z : LoopPlane} (hz : z ∈ loopDiskSet) (hc : S.conformalFactor z ≠ 0) :
    Function.Injective (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z) := by
  intro v w hvw
  have hd : mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z (v - w) = 0 := by
    simp only [map_sub, hvw, sub_self]
  have hnorm := S.withinDifferential_inner_self hz (v - w)
  rw [hd] at hnorm
  have hzero : ‖v - w‖ ^ 2 = 0 :=
    (mul_eq_zero.mp (by simpa using hnorm.symm)).resolve_left hc
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

end PoincareConjecture.M65MinimalDisk
