import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.LocalInverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_inverse_branch
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ U)
    (hi : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible) :
    ∃ B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      v ∈ B.source ∧ B.source ⊆ U ∧ EqOn e B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target := by
  let c := extChartAt (𝓡 n) (e v)
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := c ∘ e
  have hev := he.contMDiffAt (hU.mem_nhds hv)
  have hc : e v ∈ c.source := mem_extChartAt_source _
  have hF : ContDiffAt ℝ ∞ F v := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hc)).comp v hev)
  have hchain := mfderiv_comp v
    (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hc))
    (hev.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  have hFi : (fderiv ℝ F v).IsInvertible := by
    change (fderiv ℝ ((extChartAt (𝓡 n) (e v)) ∘ e) v).IsInvertible
    rw [hchain]
    exact (isInvertible_mfderiv_extChartAt hc).comp hi
  obtain ⟨A, hA⟩ := hFi
  have hnear : {z | (fderiv ℝ F z).IsInvertible} ∈ 𝓝 v := by
    have h := A.nhds
    change Set.range (fun L : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) => (L : _ →L[ℝ] _)) ∈ 𝓝 A.toContinuousLinearMap at h
    rw [hA] at h
    exact (hF.fderiv_right (m := 0) (by simp)).continuousAt.preimage_mem_nhds h
  have hgood : U ∩ e ⁻¹' c.source ∩ {z | (fderiv ℝ F z).IsInvertible} ∈ 𝓝 v :=
    inter_mem (inter_mem (hU.mem_nhds hv)
      (hev.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds hc))) hnear
  obtain ⟨V, hsub, hV, hvV⟩ := mem_nhds_iff.mp hgood
  have hVi (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ V) :
      (mfderiv (𝓡 n) (𝓡 n) e z).IsInvertible := by
    have hzU := (hsub hz).1.1
    have hzc := (hsub hz).1.2
    change e z ∈ c.source at hzc
    have hzi := (hsub hz).2
    have hcz := isInvertible_mfderiv_extChartAt hzc
    have hd := mfderiv_comp z
      (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hzc))
      ((he.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    have heq : (mfderiv (𝓡 n) (𝓡 n) c (e z)).inverse.comp (fderiv ℝ F z) =
        mfderiv (𝓡 n) (𝓡 n) e z := by
      rw [hd, ← ContinuousLinearMap.comp_assoc, hcz.inverse_comp_self,
        ContinuousLinearMap.id_comp]
    exact heq ▸ hcz.inverse.comp hzi
  obtain ⟨B, hvB, heB⟩ := isLocalDiffeomorphOn_of_isInvertible_mfderiv hV
    (he.mono (fun _ hz => (hsub hz).1.1)) hVi ⟨v, hvV⟩
  let Q := B.toOpenPartialHomeomorph.restrOpen V hV
  have hQB : Q.source ⊆ B.source := fun _ hz => hz.1
  have hQU : Q.source ⊆ U := fun _ hz => (hsub hz.2).1.1
  refine ⟨Q, ⟨hvB, hvV⟩, hQU, (fun z hz => heB (hQB hz)), ?_, ?_⟩
  · exact B.contMDiffOn_toFun.mono hQB
  · exact B.contMDiffOn_invFun.mono (fun _ hz => hz.1)

omit [IsManifold (𝓡 n) ∞ M] in
theorem smooth_inverse_branch_radius
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hB : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {x : M} (hx : x ∈ B.target) (hx0 : B.symm x ≠ 0) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ‖B.symm y‖) x := by
  exact (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_norm ℝ hx0)).comp x
    (hB.contMDiffAt (B.open_target.mem_nhds hx))

theorem inverse_branch_distance_majorant [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (p q : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hbound : ∀ w ∈ Metric.ball 0 R, g.edist q (e w) ≤ ENNReal.ofReal ‖w‖)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hsource : B.source ⊆ Metric.ball 0 R) (heB : EqOn e B B.source)
    {left : ℝ} (hleft : (g.edist p q).toReal = left)
    {y : M} (hy : y ∈ B.target) :
    (g.edist p y).toReal ≤ left + ‖B.symm y‖ := by
  have hb := hbound (B.symm y) (hsource (B.map_target hy))
  rw [heB (B.map_target hy), B.right_inv hy] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  have htriangle := g.toReal_edist_triangle p q y
  rw [hleft] at htriangle
  linarith

theorem exists_smooth_radial_inverse_branch
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ U) (hv0 : v ≠ 0)
    (hi : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible) :
    ∃ B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      v ∈ B.source ∧ B.source ⊆ U ∧ EqOn e B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target ∧
      (∀ y ∈ B.target, B.symm y ≠ 0) ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ‖B.symm y‖) B.target := by
  obtain ⟨B, hvB, hsub, heB, hB, hBi⟩ := exists_smooth_inverse_branch
    (hU.sdiff isClosed_singleton) (he.mono sdiff_subset)
    (show v ∈ U \ {0} from ⟨hv, hv0⟩) hi
  have hne : ∀ y ∈ B.target, B.symm y ≠ 0 :=
    fun y hy => (hsub (B.map_target hy)).2
  exact ⟨B, hvB, hsub.trans sdiff_subset, heB, hB, hBi, hne,
    fun y hy => (smooth_inverse_branch_radius B hBi hy (hne y hy)).contMDiffWithinAt⟩

theorem inverse_branch_touches_distance [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) {p x : M}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (heB : EqOn e B B.source) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ B.source) (hx : e v = x) {left : ℝ}
    (hsplit : left + ‖v‖ = (g.edist p x).toReal) :
    left + ‖B.symm x‖ = (g.edist p x).toReal := by
  have hxB : B v = x := (heB hv).symm.trans hx
  rw [← hxB, B.left_inv hv]
  exact hxB ▸ hsplit

end PoincareConjecture.RiemannianMetric
