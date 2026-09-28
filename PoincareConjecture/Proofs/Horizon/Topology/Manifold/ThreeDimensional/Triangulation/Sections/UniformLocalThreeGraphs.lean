import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.ApproximateLinearGraph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open scoped NNReal ContDiff Topology

namespace Poincare.Topology

set_option maxHeartbeats 400000 in

theorem exists_uniform_local_three_graphs {N : Nat}
    (F : EuclideanSpace Real (Fin 3) → EuclideanSpace Real (Fin N))
    (s : Set (EuclideanSpace Real (Fin 3))) (hs : IsOpen s)
    (hF : ContDiffOn Real ∞ F s)
    (c : EuclideanSpace Real (Fin 3)) (hc : c ∈ s)
    (hi : Function.Injective (fderiv Real F c))
    (epsilon : NNReal) (hepsilon : 0 < epsilon) :
    ∃ R rho : Real, 0 < R ∧ 0 < rho ∧ Metric.ball c (4 * R) ⊆ s ∧
      ∀ p ∈ Metric.ball c R,
        ∃ g : OpenPartialHomeomorph (fderiv Real F p).range
            (EuclideanSpace Real (Fin 3)),
          g.source = Metric.ball 0 (2 * rho) ∧
          g 0 = p ∧
          g.target ⊆ Metric.ball c (4 * R) ∧
          (∀ v ∈ g.source,
            (fderiv Real F p).range.orthogonalProjectionOnto (F (g v) - F p) = v) ∧
          LipschitzOnWith epsilon
            (fun v : (fderiv Real F p).range =>
              F (g v) - F p - (v : EuclideanSpace Real (Fin N))) g.source ∧
          (∀ q ∈ Metric.ball c R, dist (F q) (F p) < rho → q ∈ g.target) := by
  classical
  let L0 := fderiv Real F c
  let E0 : EuclideanSpace Real (Fin 3) ≃L[Real] L0.range :=
    (LinearEquiv.ofInjective L0.toLinearMap hi).toContinuousLinearEquiv
  let B := ‖(E0.symm : L0.range →L[Real] EuclideanSpace Real (Fin 3))‖
  let m : Real := (B + 1)⁻¹
  have hB : 0 ≤ B :=
    norm_nonneg (E0.symm : L0.range →L[Real] EuclideanSpace Real (Fin 3))
  have hB1 : 0 < B + 1 := by linarith only [hB]
  have hm : 0 < m := inv_pos.mpr hB1
  have hL0 (v : EuclideanSpace Real (Fin 3)) : m * ‖v‖ ≤ ‖L0 v‖ := by
    have h := (E0.symm : L0.range →L[Real] EuclideanSpace Real (Fin 3)).le_opNorm (E0 v)
    have hv : ‖v‖ ≤ B * ‖L0 v‖ := by
      have he : ‖E0 v‖ = ‖L0 v‖ := rfl
      simpa only [ContinuousLinearEquiv.coe_coe, E0.symm_apply_apply, he] using h
    calc
      m * ‖v‖ = ‖v‖ / (B + 1) := by dsimp [m]; ring
      _ ≤ ‖L0 v‖ := (div_le_iff₀ hB1).mpr (by nlinarith only [hv, norm_nonneg (L0 v)])
  have heps : 0 < (epsilon : Real) := hepsilon
  have hmin : 0 < min (m / 8) ((epsilon : Real) * m / 8) :=
    lt_min (by positivity) (by positivity)
  let a : NNReal := ⟨min (m / 8) ((epsilon : Real) * m / 8), hmin.le⟩
  have ha : 0 < a := hmin
  have ham : (a : Real) ≤ m / 8 := min_le_left _ _
  have hae : (a : Real) ≤ (epsilon : Real) * m / 8 := min_le_right _ _
  have hac : 0 < (a : Real) := ha
  have hFc := hF.contDiffAt (hs.mem_nhds hc)
  obtain ⟨U, hU, happrox⟩ :=
    (hFc.hasStrictFDerivAt (by simp)).approximates_deriv_on_nhds
      (c := a / 2) (Or.inr (by positivity))
  have hDc : ContinuousAt (fun p => ‖fderiv Real F p - L0‖) c :=
    ((hFc.continuousAt_fderiv (by simp)).sub continuousAt_const).norm
  have hD : {p | ‖fderiv Real F p - L0‖ < (a : Real) / 2} ∈ 𝓝 c :=
    hDc (gt_mem_nhds (by simpa only [L0, sub_self, norm_zero] using half_pos hac))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Filter.inter_mem hU (hs.mem_nhds hc)) hD)
  let R : Real := r / 4
  let rho : Real := m * R / 16
  have hR : 0 < R := by dsimp [R]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hball : Metric.ball c (4 * R) ⊆
      (U ∩ s) ∩ {p | ‖fderiv Real F p - L0‖ < (a : Real) / 2} := by
    have hfour : 4 * R = r := by dsimp [R]; ring
    rw [hfour]
    exact hrsub
  have hsmall : Metric.ball c R ⊆ Metric.ball c (4 * R) :=
    Metric.ball_subset_ball (by linarith only [hR])
  refine ⟨R, rho, hR, hrho, fun z hz => (hball hz).1.2, ?_⟩
  intro p hp
  let Lp := fderiv Real F p
  have hdiff : ‖Lp - L0‖ ≤ (a : Real) / 2 := (hball (hsmall hp)).2.le
  have hlower (v : EuclideanSpace Real (Fin 3)) : (m / 2) * ‖v‖ ≤ ‖Lp v‖ := by
    have hrem : ‖(Lp - L0) v‖ ≤ ((a : Real) / 2) * ‖v‖ :=
      ((Lp - L0).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hdiff (norm_nonneg v))
    have hsum : ‖L0 v‖ ≤ ‖Lp v‖ + ‖(Lp - L0) v‖ := by
      calc
        ‖L0 v‖ = ‖Lp v - (Lp - L0) v‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    have hsm : ((a : Real) / 2) * ‖v‖ ≤ (m / 2) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (by linarith only [ham, hm]) (norm_nonneg v)
    nlinarith only [hL0 v, hrem, hsum, hsm]
  have hinj : Function.Injective Lp := by
    intro v w hvw
    have h := hlower (v - w)
    have hz : Lp (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    rw [hz, norm_zero] at h
    have heq : ‖v - w‖ = 0 := by nlinarith only [h, hm, norm_nonneg (v - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp heq)
  obtain ⟨E, hEval⟩ : ∃ E : EuclideanSpace Real (Fin 3) ≃L[Real] Lp.range,
      ∀ v, (E v : EuclideanSpace Real (Fin N)) = Lp v :=
    ⟨(LinearEquiv.ofInjective Lp.toLinearMap hinj).toContinuousLinearEquiv, fun _ => rfl⟩
  have hE (v : Lp.range) : Lp (E.symm v) = (v : EuclideanSpace Real (Fin N)) := by
    rw [← hEval, E.apply_symm_apply]
  have hEnorm : ‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖ ≤ 2 / m := by
    apply (E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3)).opNorm_le_bound
      (by positivity)
    intro v
    have h := hlower (E.symm v)
    rw [hE] at h
    change (m / 2) * ‖E.symm v‖ ≤ ‖v‖ at h
    calc
      ‖E.symm v‖ ≤ ‖v‖ / (m / 2) :=
        (le_div_iff₀ (half_pos hm)).mpr (by rw [mul_comm]; exact h)
      _ = (2 / m) * ‖v‖ := by ring
  have hEinv : m / 2 ≤ ‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ E.norm_symm_pos).mpr
    calc
      (m / 2) * ‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖ ≤
          (m / 2) * (2 / m) := mul_le_mul_of_nonneg_left hEnorm (by positivity)
      _ = 1 := by field_simp [ne_of_gt hm]
  have haE : a < ‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖₊⁻¹ := by
    change (a : Real) < ((‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖₊⁻¹ :
      NNReal) : Real)
    rw [NNReal.coe_inv, coe_nnnorm]
    linarith only [ham, hm, hEinv]
  let b : NNReal := ‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖₊⁻¹ - a
  have hbval : (b : Real) =
      ‖(E.symm : Lp.range →L[Real] EuclideanSpace Real (Fin 3))‖⁻¹ - (a : Real) := by
    simp only [b, NNReal.coe_sub haE.le, NNReal.coe_inv, coe_nnnorm]
  have hb : m / 4 ≤ (b : Real) := by rw [hbval]; linarith only [ham, hEinv, hm]
  have hbpos : 0 < (b : Real) := by linarith only [hb, hm]
  have hlip : a * b⁻¹ ≤ epsilon := by
    change ((a * b⁻¹ : NNReal) : Real) ≤ (epsilon : Real)
    rw [NNReal.coe_mul, NNReal.coe_inv, ← div_eq_mul_inv]
    apply (div_le_iff₀ hbpos).mpr
    have h := mul_le_mul_of_nonneg_left hb heps.le
    nlinarith only [hae, h, mul_pos heps hm]
  have hrhob : 2 * rho ≤ (b : Real) * R := by
    have h := mul_le_mul_of_nonneg_right hb hR.le
    dsimp [rho]
    nlinarith only [h, mul_pos hm hR]
  have hnear : Metric.ball p (2 * R) ⊆ Metric.ball c (4 * R) := by
    intro q hq
    have hp' := Metric.mem_ball.mp hp
    have hq' := Metric.mem_ball.mp hq
    exact lt_of_le_of_lt (dist_triangle q p c) (by linarith only [hp', hq', hR])
  have hap : ApproximatesLinearOn F
      (Lp.range.subtypeL.comp (E : EuclideanSpace Real (Fin 3) →L[Real] Lp.range))
      (Metric.ball p (2 * R)) a := by
    have hlin : Lp.range.subtypeL.comp
        (E : EuclideanSpace Real (Fin 3) →L[Real] Lp.range) = Lp := by
      apply ContinuousLinearMap.ext
      exact hEval
    rw [hlin]
    intro x hx y hy
    have hu := happrox x (hball (hnear hx)).1.1 y (hball (hnear hy)).1.1
    have herr : ‖(Lp - L0) (x - y)‖ ≤ ((a : Real) / 2) * ‖x - y‖ :=
      ((Lp - L0).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
    change ‖F x - F y - Lp (x - y)‖ ≤ (a : Real) * ‖x - y‖
    calc
      ‖F x - F y - Lp (x - y)‖ =
          ‖(F x - F y - L0 (x - y)) - (Lp - L0) (x - y)‖ := by
        congr 1
        simp only [sub_apply]
        abel
      _ ≤ ‖F x - F y - L0 (x - y)‖ + ‖(Lp - L0) (x - y)‖ := norm_sub_le _ _
      _ ≤ (a : Real) * ‖x - y‖ := by
        simp only [NNReal.coe_div, NNReal.coe_ofNat] at hu
        linarith only [hu, herr]
  obtain ⟨g0, hgsource, hgzero, hgtarget, hgproj, hglip, hgcover⟩ :=
    exists_approximate_linear_graph Lp.range F E p R hR a haE hap
  change g0.source = Metric.ball 0 ((b : Real) * R) at hgsource
  let V : Set Lp.range := Metric.ball 0 (2 * rho)
  have hV : V ⊆ g0.source := by
    rw [hgsource]
    exact Metric.ball_subset_ball hrhob
  let g : OpenPartialHomeomorph Lp.range (EuclideanSpace Real (Fin 3)) :=
    g0.restrOpen V Metric.isOpen_ball
  have hgsource' : g.source = V := by
    change g0.source ∩ V = V
    exact Set.inter_eq_right.mpr hV
  refine ⟨g, hgsource', hgzero, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hnear (hgtarget hq.1)
  · intro v hv
    exact hgproj v hv.1
  · have hsub : g.source ⊆ g0.source := fun _ hv => hv.1
    exact (hglip.mono hsub).weaken hlip
  · intro q hq hdist
    have hqp : q ∈ Metric.ball p (2 * R) := by
      have hp' : dist c p < R := by simpa only [dist_comm] using Metric.mem_ball.mp hp
      have hq' := Metric.mem_ball.mp hq
      exact lt_of_le_of_lt (dist_triangle q c p) (by linarith only [hp', hq'])
    have hnorm : ‖Lp.range.orthogonalProjectionOnto (F q - F p)‖ < rho :=
      (Lp.range.norm_orthogonalProjectionOnto_apply_le _).trans_lt
        (by simpa only [dist_eq_norm] using hdist)
    have hq0 : q ∈ g0.target := hgcover q hqp (by linarith only [hnorm, hrho, hrhob])
    have hproj := hgproj (g0.symm q) (g0.map_target hq0)
    rw [g0.right_inv hq0] at hproj
    change q ∈ g0.target ∧ g0.symm q ∈ V
    refine ⟨hq0, ?_⟩
    change dist (g0.symm q) 0 < 2 * rho
    rw [dist_zero_right, ← hproj]
    linarith only [hnorm, hrho]

end Poincare.Topology
