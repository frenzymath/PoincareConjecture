import PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeTangent
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic








set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

set_option maxHeartbeats 3000000 in

theorem exists_embedded_three_normal_chord_bound [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p)) :
    ∃ C : Real, 0 < C ∧ ∀ (p q : M) (v : EuclideanSpace Real (Fin N)),
      v ∈ (embeddedThreeTangent e p)ᗮ →
        |inner Real v (e q - e p)| ≤ C * ‖v‖ * ‖e q - e p‖ ^ 2 := by
  classical
  have hlocal : ∀ p0 : M, ∃ U : Set M, IsOpen U ∧ p0 ∈ U ∧
      ∃ C : Real, 0 < C ∧ ∀ p ∈ U, ∀ (q : M) (v : EuclideanSpace Real (Fin N)),
        v ∈ (embeddedThreeTangent e p)ᗮ →
          |inner Real v (e q - e p)| ≤ C * ‖v‖ * ‖e q - e p‖ ^ 2 := by
    intro p0
    let c := chartAt (EuclideanSpace Real (Fin 3)) p0
    let F : EuclideanSpace Real (Fin 3) → EuclideanSpace Real (Fin N) := e ∘ c.symm
    have hp0 : p0 ∈ c.source := mem_chart_source _ _
    have hx0 : c p0 ∈ c.target := c.map_source hp0
    have hF : ContDiffOn Real ∞ F c.target :=
      (hs.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 3) (x := p0))).contDiffOn
    have hc : c.MDifferentiable (𝓡 3) (𝓡 3) := mdifferentiable_chart p0
    have hderiv (x : EuclideanSpace Real (Fin 3)) (hx : x ∈ c.target) :
        fderiv Real F x =
          (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e (c.symm x)).comp
            (mfderiv (𝓡 3) (𝓡 3) c.symm x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x ((hs.mdifferentiable (by simp)).mdifferentiableAt)
        (hc.symm.mdifferentiableAt hx)
    have hFi : Function.Injective (fderiv Real F (c p0)) := by
      rw [hderiv _ hx0]
      exact (hi (c.symm (c p0))).comp (hc.symm.mfderiv_injective hx0)
    let L := fderiv Real F (c p0)
    let E : EuclideanSpace Real (Fin 3) ≃L[Real] L.range :=
      (LinearEquiv.ofInjective L.toLinearMap hFi).toContinuousLinearEquiv
    let B := ‖(E.symm : L.range →L[Real] EuclideanSpace Real (Fin 3))‖
    let m : Real := (B + 1)⁻¹
    have hB : 0 ≤ B := by
      simpa only [B] using
        (norm_nonneg (E.symm : L.range →L[Real] EuclideanSpace Real (Fin 3)))
    have hB1 : 0 < B + 1 := by linarith
    have hm : 0 < m := inv_pos.mpr hB1
    have hL (v : EuclideanSpace Real (Fin 3)) : m * ‖v‖ ≤ ‖L v‖ := by
      have h := (E.symm : L.range →L[Real] EuclideanSpace Real (Fin 3)).le_opNorm (E v)
      have hv : ‖v‖ ≤ B * ‖L v‖ := by
        have hE : ‖E v‖ = ‖L v‖ := rfl
        simpa only [ContinuousLinearEquiv.coe_coe, E.symm_apply_apply, hE] using h
      calc
        m * ‖v‖ = ‖v‖ / (B + 1) := by dsimp [m]; ring
        _ ≤ ‖L v‖ := (div_le_iff₀ hB1).mpr (by nlinarith [norm_nonneg (L v)])
    let a : NNReal := ⟨m / 2, (half_pos hm).le⟩
    have hFc := hF.contDiffAt (c.open_target.mem_nhds hx0)
    obtain ⟨A, hA, happrox⟩ :=
      (hFc.hasStrictFDerivAt (by simp)).approximates_deriv_on_nhds
        (c := a) (Or.inr (half_pos hm))
    have hDF : ContDiffAt Real 1 (fderiv Real F) (c p0) :=
      (hF.fderiv_of_isOpen (m := 1) c.open_target
        (by simpa only [one_add_one_eq_two, Nat.cast_ofNat] using
          ENat.natCast_le_of_coe_top_le_withTop (N := (∞ : WithTop ENat)) le_rfl 2)).contDiffAt
        (c.open_target.mem_nhds hx0)
    obtain ⟨K, D, hD, hLip⟩ := hDF.exists_lipschitzOnWith
    obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (Filter.inter_mem hA hD) (c.open_target.mem_nhds hx0))
    have htarget : Metric.ball (c p0) R ⊆ c.target := fun x hx => (hball hx).2
    have hcoord (x y : EuclideanSpace Real (Fin 3))
        (hx : x ∈ Metric.ball (c p0) R) (hy : y ∈ Metric.ball (c p0) R) :
        ‖x - y‖ ≤ (2 / m) * ‖F x - F y‖ := by
      have hrem : ‖F x - F y - L (x - y)‖ ≤ (m / 2) * ‖x - y‖ :=
        happrox x (hball hx).1.1 y (hball hy).1.1
      have hsum : ‖L (x - y)‖ ≤ ‖F x - F y‖ + ‖F x - F y - L (x - y)‖ := by
        calc
          ‖L (x - y)‖ = ‖(F x - F y) - (F x - F y - L (x - y))‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have hlow := hL (x - y)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hm).mpr
      nlinarith
    have hrem (x y : EuclideanSpace Real (Fin 3))
        (hx : x ∈ Metric.ball (c p0) R) (hy : y ∈ Metric.ball (c p0) R) :
        ‖F y - F x - fderiv Real F x (y - x)‖ ≤ (K : Real) * ‖y - x‖ ^ 2 := by
      let H : EuclideanSpace Real (Fin 3) → EuclideanSpace Real (Fin N) :=
        fun z => F z - F x - fderiv Real F x (z - x)
      have hseg : segment Real x y ⊆ Metric.ball (c p0) R :=
        (convex_ball _ _).segment_subset hx hy
      have hH (z : EuclideanSpace Real (Fin 3)) (hz : z ∈ segment Real x y) :
          HasFDerivWithinAt H (fderiv Real F z - fderiv Real F x) (segment Real x y) z := by
        have hz' := htarget (hseg hz)
        have hFz : DifferentiableAt Real F z :=
          (hF.contDiffAt (c.open_target.mem_nhds hz')).differentiableAt (by simp)
        convert! ((hFz.hasFDerivAt.sub_const (F x)).sub
          ((fderiv Real F x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))).hasFDerivWithinAt
          using 1
      have hbound (z : EuclideanSpace Real (Fin 3)) (hz : z ∈ segment Real x y) :
          ‖fderiv Real F z - fderiv Real F x‖ ≤ (K : Real) * ‖y - x‖ := by
        have hdz : ‖fderiv Real F z - fderiv Real F x‖ ≤ (K : Real) * ‖z - x‖ := by
          simpa only [dist_eq_norm] using
            hLip.dist_le_mul z (hball (hseg hz)).1.2 x (hball hx).1.2
        exact hdz.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
      have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hH hbound
        (left_mem_segment Real x y) (right_mem_segment Real x y)
      simpa only [H, sub_self, map_zero, sub_zero, pow_two, mul_assoc] using h
    let U := c.source ∩ c ⁻¹' Metric.ball (c p0) (R / 2)
    let V := c.source ∩ c ⁻¹' Metric.ball (c p0) R
    let Q := c.symm '' Metric.closedBall (c p0) (R / 2)
    have hU : IsOpen U := c.isOpen_inter_preimage Metric.isOpen_ball
    have hV : IsOpen V := c.isOpen_inter_preimage Metric.isOpen_ball
    have hcb : Metric.closedBall (c p0) (R / 2) ⊆ c.target := by
      intro x hx
      apply htarget
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
    have hQ : IsCompact Q := (isCompact_closedBall (c p0) (R / 2)).image_of_continuousOn
      (c.symm.continuousOn.mono hcb)
    have hQV : Q ⊆ V := by
      rintro p ⟨x, hx, rfl⟩
      refine ⟨c.symm.map_source (hcb hx), ?_⟩
      change c (c.symm x) ∈ Metric.ball (c p0) R
      rw [c.right_inv (hcb hx)]
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
    have hUQ : U ⊆ Q := by
      intro p hp
      exact ⟨c p, Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hp.2)), c.left_inv hp.1⟩
    have hsep : Disjoint (e '' Q) (e '' Vᶜ) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
      exact hq ((he.injective heq) ▸ hQV hp)
    obtain ⟨delta, hdelta, hdist⟩ := Metric.exists_pos_forall_lt_edist
      (hQ.image e.continuous) ((isClosed_compl_iff.mpr hV).isCompact.image
        e.continuous).isClosed hsep
    have hdeltaR : 0 < (delta : Real) := hdelta
    let C0 : Real := ((K : Real) + 1) * (2 / m) ^ 2
    have hC0 : 0 < C0 := by dsimp [C0]; positivity
    let C : Real := max C0 (delta : Real)⁻¹
    have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
    refine ⟨U, hU, ⟨hp0, by simpa using half_pos hR⟩, C, hC, ?_⟩
    intro p hp q v hv
    by_cases hq : q ∈ V
    · have hpc : c p ∈ Metric.ball (c p0) R :=
        Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hp.2) (by linarith))
      have hT : (fderiv Real F (c p)).range = embeddedThreeTangent e p := by
        rw [hderiv _ (c.map_source hp.1)]
        change LinearMap.range
          ((mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e (c.symm (c p))).toLinearMap.comp
            (mfderiv (𝓡 3) (𝓡 3) c.symm (c p)).toLinearMap) = _
        rw [LinearMap.range_comp_of_range_eq_top _
          (LinearMap.range_eq_top.mpr (hc.symm.mfderiv_surjective (c.map_source hp.1)))]
        rw [c.left_inv hp.1]
        rfl
      have hFp : F (c p) = e p := congrArg e (c.left_inv hp.1)
      have hFq : F (c q) = e q := congrArg e (c.left_inv hq.1)
      have hlin : inner Real v (fderiv Real F (c p) (c q - c p)) = 0 := by
        apply Submodule.inner_left_of_mem_orthogonal (K := embeddedThreeTangent e p) _ hv
        rw [← hT]
        exact ⟨c q - c p, rfl⟩
      have hrem' := hrem (c p) (c q) hpc hq.2
      rw [hFp, hFq] at hrem'
      have hc' := hcoord (c q) (c p) hq.2 hpc
      rw [hFp, hFq] at hc'
      have hsq : ‖c q - c p‖ ^ 2 ≤ (2 / m) ^ 2 * ‖e q - e p‖ ^ 2 := by
        calc
          ‖c q - c p‖ ^ 2 ≤ ((2 / m) * ‖e q - e p‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hc' 2
          _ = _ := mul_pow _ _ _
      have hrA : ‖e q - e p - fderiv Real F (c p) (c q - c p)‖ ≤ C0 * ‖e q - e p‖ ^ 2 := by
        calc
          _ ≤ (K : Real) * ‖c q - c p‖ ^ 2 := hrem'
          _ ≤ (K : Real) * ((2 / m) ^ 2 * ‖e q - e p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq K.coe_nonneg
          _ ≤ ((K : Real) + 1) * ((2 / m) ^ 2 * ‖e q - e p‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by dsimp [C0]; ring
      calc
        |inner Real v (e q - e p)| =
            |inner Real v (e q - e p - fderiv Real F (c p) (c q - c p))| := by
          congr 1
          rw [inner_sub_right v (e q - e p) (fderiv Real F (c p) (c q - c p)),
            hlin, sub_zero]
        _ ≤ ‖v‖ * ‖e q - e p - fderiv Real F (c p) (c q - c p)‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ ‖v‖ * (C0 * ‖e q - e p‖ ^ 2) := mul_le_mul_of_nonneg_left hrA (norm_nonneg _)
        _ = C0 * ‖v‖ * ‖e q - e p‖ ^ 2 := by ring
        _ ≤ C * ‖v‖ * ‖e q - e p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (sq_nonneg _)
    · have hdist' := hdist (e p) ⟨p, hUQ hp, rfl⟩ (e q) ⟨q, hq, rfl⟩
      have hfar : (delta : Real) < ‖e q - e p‖ := by
        simpa only [edist_dist, ← ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg delta.coe_nonneg,
          dist_comm (e p) (e q), dist_eq_norm] using hdist'
      have hquad : ‖e q - e p‖ ≤ (delta : Real)⁻¹ * ‖e q - e p‖ ^ 2 := by
        rw [inv_mul_eq_div]
        apply (le_div_iff₀ hdeltaR).mpr
        nlinarith [norm_nonneg (e q - e p)]
      calc
        |inner Real v (e q - e p)| ≤ ‖v‖ * ‖e q - e p‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖v‖ * ((delta : Real)⁻¹ * ‖e q - e p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (norm_nonneg _)
        _ = (delta : Real)⁻¹ * ‖v‖ * ‖e q - e p‖ ^ 2 := by ring
        _ ≤ C * ‖v‖ * ‖e q - e p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (sq_nonneg _)
  choose U hUo hUc C hC hbound using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun p _ => Set.mem_iUnion.mpr ⟨p, hUc p⟩)
  have hupper : ∃ D : Real, 0 < D ∧ ∀ i ∈ t, C i ≤ D := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i t hi ih =>
        obtain ⟨D, hD, hDt⟩ := ih
        refine ⟨max D (C i), lt_of_lt_of_le hD (le_max_left _ _), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_max_right _ _
        · exact (hDt j hj).trans (le_max_left _ _)
  obtain ⟨D, hD, hupper⟩ := hupper
  refine ⟨D, hD, ?_⟩
  intro p q v hv
  obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  exact (hbound i p hp q v hv).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hupper i hi) (norm_nonneg _)) (sq_nonneg _))

theorem embedded_three_nearest_normal
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (z : EuclideanSpace Real (Fin N)) (p : M)
    (hp : ∀ q : M, dist z (e p) ≤ dist z (e q)) :
    z - e p ∈ (embeddedThreeTangent e p)ᗮ := by
  let c := chartAt (EuclideanSpace Real (Fin 3)) p
  let F : EuclideanSpace Real (Fin 3) → EuclideanSpace Real (Fin N) := e ∘ c.symm
  have hpc : p ∈ c.source := mem_chart_source _ _
  have hcp : c p ∈ c.target := c.map_source hpc
  have hc : c.MDifferentiable (𝓡 3) (𝓡 3) := mdifferentiable_chart p
  have hFd : DifferentiableAt Real F (c p) :=
    ((hs.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 3) (x := p))).contDiffOn.contDiffAt
      (c.open_target.mem_nhds hcp)).differentiableAt (by simp)
  have hderiv : fderiv Real F (c p) =
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e (c.symm (c p))).comp
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c p)) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp _ ((hs.mdifferentiable (by simp)).mdifferentiableAt)
      (hc.symm.mdifferentiableAt hcp)
  have hT : (fderiv Real F (c p)).range = embeddedThreeTangent e p := by
    rw [hderiv]
    change LinearMap.range
      ((mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e (c.symm (c p))).toLinearMap.comp
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c p)).toLinearMap) = _
    rw [LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hc.symm.mfderiv_surjective hcp)), c.left_inv hpc]
    rfl
  have hFp : F (c p) = e p := congrArg e (c.left_inv hpc)
  have hmin : IsLocalMin (fun x => ‖z - F x‖ ^ 2) (c p) := by
    apply Filter.Eventually.of_forall
    intro x
    have h := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (hp (c.symm x))
    simpa only [F, Function.comp_apply, dist_eq_norm, c.left_inv hpc] using h
  have hzero := hmin.hasFDerivAt_eq_zero ((hasFDerivAt_const z (c p)).sub hFd.hasFDerivAt).norm_sq
  rw [← hT, Submodule.mem_orthogonal']
  rintro v ⟨w, rfl⟩
  have hw := DFunLike.congr_fun hzero w
  have hw' : 2 * inner Real (z - F (c p)) (-(fderiv Real F (c p) w)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, sub_apply,
      Pi.sub_apply, zero_apply, zero_sub, neg_apply, innerSL_apply_apply,
      nsmul_eq_mul, Nat.cast_ofNat] using hw
  rw [hFp, inner_neg_right] at hw'
  change inner Real (z - e p) (fderiv Real F (c p) w) = 0
  linarith only [hw']

end PoincareConjecture.Proofs.M02.Topology
