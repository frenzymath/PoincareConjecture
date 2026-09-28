import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring








set_option autoImplicit false

open scoped NNReal Topology

namespace PoincareConjecture.Proofs.M02.Topology


theorem exists_approximate_linear_graph {N : Nat}
    (T : Submodule Real (EuclideanSpace Real (Fin N)))
    (F : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin N))
    (L : EuclideanSpace Real (Fin 3) ≃L[Real] T)
    (c : EuclideanSpace Real (Fin 3)) (R : Real) (hR : 0 < R)
    (a : NNReal)
    (ha : a < ‖(L.symm : T →L[Real] EuclideanSpace Real (Fin 3))‖₊⁻¹)
    (hF : ApproximatesLinearOn F
      (T.subtypeL.comp (L : EuclideanSpace Real (Fin 3) →L[Real] T))
      (Metric.ball c (2 * R)) a) :
    let b : NNReal := ‖(L.symm : T →L[Real] EuclideanSpace Real (Fin 3))‖₊⁻¹ - a
    ∃ g : OpenPartialHomeomorph T (EuclideanSpace Real (Fin 3)),
      g.source = Metric.ball 0 ((b : Real) * R) ∧
      g 0 = c ∧
      g.target ⊆ Metric.ball c (2 * R) ∧
      (∀ v ∈ g.source, T.orthogonalProjectionOnto (F (g v) - F c) = v) ∧
      LipschitzOnWith (a * b⁻¹)
        (fun v : T => F (g v) - F c - (v : EuclideanSpace Real (Fin N))) g.source ∧
      (∀ q ∈ Metric.ball c (2 * R),
        ‖T.orthogonalProjectionOnto (F q - F c)‖ < (b : Real) * R → q ∈ g.target) := by
  classical
  let b : NNReal := ‖(L.symm : T →L[Real] EuclideanSpace Real (Fin 3))‖₊⁻¹ - a
  let Q : EuclideanSpace Real (Fin 3) -> T :=
    fun z => T.orthogonalProjectionOnto (F z - F c)
  have hQc : Q c = 0 := by simp [Q]
  have hQ : ApproximatesLinearOn Q
      (L : EuclideanSpace Real (Fin 3) →L[Real] T) (Metric.ball c (2 * R)) a := by
    intro z hz w hw
    have heq : Q z - Q w - L (z - w) =
        T.orthogonalProjectionOnto (F z - F w - (L (z - w) : EuclideanSpace Real (Fin N))) := by
      simp only [Q, map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
      abel
    change ‖Q z - Q w - L (z - w)‖ ≤ (a : Real) * ‖z - w‖
    rw [heq]
    exact (T.norm_orthogonalProjectionOnto_apply_le _).trans (hF z hz w hw)
  let e := hQ.toOpenPartialHomeomorph Q (Metric.ball c (2 * R)) (Or.inr ha)
    Metric.isOpen_ball
  let B : Set T := Metric.ball 0 ((b : Real) * R)
  have hc : c ∈ e.source := by
    change c ∈ Metric.ball c (2 * R)
    exact Metric.mem_ball_self (by linarith)
  have hB : B ⊆ e.target := by
    have hclosed : Metric.closedBall c R ⊆ Metric.ball c (2 * R) := by
      intro z hz
      change dist z c < 2 * R
      exact (Metric.mem_closedBall.mp hz).trans_lt (by linarith)
    have hin := hQ.closedBall_subset_target (Or.inr ha) Metric.isOpen_ball hR.le hclosed
    have hclosed' : Metric.closedBall (0 : T) ((b : Real) * R) ⊆ e.target := by
      simpa only [hQc, b, NNReal.coe_sub ha.le] using hin
    exact Set.Subset.trans Metric.ball_subset_closedBall hclosed'
  let g : OpenPartialHomeomorph T (EuclideanSpace Real (Fin 3)) :=
    e.symm.restrOpen B Metric.isOpen_ball
  have hsource : g.source = B := by
    change e.target ∩ B = B
    exact Set.inter_eq_right.mpr hB
  have htarget : g.target ⊆ Metric.ball c (2 * R) := by
    intro z hz
    exact hz.1
  have hproject (v : T) (hv : v ∈ g.source) : Q (g v) = v := by
    apply e.right_inv
    exact hv.1
  refine ⟨g, hsource, ?_, htarget, hproject, ?_, ?_⟩
  · change e.symm 0 = c
    rw [← hQc]
    exact e.left_inv hc
  · rw [lipschitzOnWith_iff_norm_sub_le]
    intro v hv w hw
    have hx := htarget (g.map_source hv)
    have hy := htarget (g.map_source hw)
    have hdist : ‖g v - g w‖ ≤ (b⁻¹ : NNReal) * ‖v - w‖ := by
      have h := (hQ.antilipschitz (Or.inr ha)).le_mul_dist ⟨g v, hx⟩ ⟨g w, hy⟩
      change dist (g v) (g w) ≤ (b⁻¹ : NNReal) * dist (Q (g v)) (Q (g w)) at h
      simpa only [hproject v hv, hproject w hw, dist_eq_norm] using h
    have hv' : T.starProjection (F (g v) - F c) = (v : EuclideanSpace Real (Fin N)) :=
      congrArg Subtype.val (hproject v hv)
    have hw' : T.starProjection (F (g w) - F c) = (w : EuclideanSpace Real (Fin N)) :=
      congrArg Subtype.val (hproject w hw)
    have hdiff : T.starProjection (F (g v) - F (g w)) =
        (v : EuclideanSpace Real (Fin N)) - (w : EuclideanSpace Real (Fin N)) := by
      calc
        T.starProjection (F (g v) - F (g w)) =
            T.starProjection ((F (g v) - F c) - (F (g w) - F c)) := by
          congr 1
          abel
        _ = _ := by rw [map_sub, hv', hw']
    have hL : Tᗮ.starProjection (L (g v - g w) : EuclideanSpace Real (Fin N)) = 0 :=
      Submodule.starProjection_orthogonal_apply_eq_zero (L (g v - g w)).property
    have herr :
        (F (g v) - F c - (v : EuclideanSpace Real (Fin N))) -
          (F (g w) - F c - (w : EuclideanSpace Real (Fin N))) =
        Tᗮ.starProjection
          (F (g v) - F (g w) - (L (g v - g w) : EuclideanSpace Real (Fin N))) := by
      rw [map_sub, hL, sub_zero, Submodule.starProjection_orthogonal_val, hdiff]
      abel
    calc
      ‖(F (g v) - F c - (v : EuclideanSpace Real (Fin N))) -
          (F (g w) - F c - (w : EuclideanSpace Real (Fin N)))‖ =
          ‖Tᗮ.starProjection
            (F (g v) - F (g w) - (L (g v - g w) : EuclideanSpace Real (Fin N)))‖ := by rw [herr]
      _ ≤ ‖F (g v) - F (g w) - (L (g v - g w) : EuclideanSpace Real (Fin N))‖ :=
        Tᗮ.norm_starProjection_apply_le _
      _ ≤ (a : Real) * ‖g v - g w‖ := hF (g v) hx (g w) hy
      _ ≤ (a : Real) * ((b⁻¹ : NNReal) * ‖v - w‖) :=
        mul_le_mul_of_nonneg_left hdist a.coe_nonneg
      _ = ((a * b⁻¹ : NNReal) : Real) * ‖v - w‖ := by
        simp only [NNReal.coe_mul, mul_assoc]
  · intro q hq hnorm
    change q ∈ Metric.ball c (2 * R) ∧ Q q ∈ B
    exact ⟨hq, by simpa only [B, Metric.mem_ball, dist_zero_right] using hnorm⟩

end PoincareConjecture.Proofs.M02.Topology
