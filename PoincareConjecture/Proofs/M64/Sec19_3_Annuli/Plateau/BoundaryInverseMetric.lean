import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNormalChart
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetMetric












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Topology ContDiff

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)





def m64BoundaryMetricInverse (G : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin G)





theorem m64BoundaryMetricInverse_smooth {U : Set E}
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ContDiffOn ℝ ∞ (fun x => m64BoundaryMetricInverse (G x)) U := by
  apply ReducedLengthMinimum.Variational.contDiffOn_inverse_operator
  · unfold InnerProductSpace.continuousLinearMapOfBilin
    exact contDiffOn_const.clm_comp hG
  · exact fun x hx => ReducedLengthMinimum.Variational.positive_form_operator_isUnit
      (G x) (hpos x hx)





theorem m64BoundaryMetricInverse_pairing
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < G v v)
    (hsym : ∀ v w : E, G v w = G w v) (v w : E) :
    G v (m64BoundaryMetricInverse G w) = inner ℝ v w := by
  let A := InnerProductSpace.continuousLinearMapOfBilin G
  have hu := ReducedLengthMinimum.Variational.positive_form_operator_isUnit G hpos
  have hinv : A (m64BoundaryMetricInverse G w) = w :=
    congrArg (fun L : E →L[ℝ] E => L w) (Ring.mul_inverse_cancel A hu)
  rw [hsym]
  calc
    _ = inner ℝ (A (m64BoundaryMetricInverse G w)) v :=
      (InnerProductSpace.continuousLinearMapOfBilin_apply G _ _).symm
    _ = inner ℝ w v := by rw [hinv]
    _ = inner ℝ v w := real_inner_comm _ _





theorem m64BoundaryMetricInverse_tangent_column
    (G : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin (n + 1)), v ≠ 0 → 0 < G v v)
    (haxis : ∀ z : EuclideanSpace ℝ (Fin (n + 1)),
      G (EuclideanSpace.single 0 1) z =
        G (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) * z 0) :
    m64BoundaryMetricInverse G (EuclideanSpace.single 0 1) =
      (G (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1))⁻¹ •
        EuclideanSpace.single 0 1 := by
  let e : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  let A := InnerProductSpace.continuousLinearMapOfBilin G
  have he : e ≠ 0 := by
    intro hh
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) hh
    simp [e] at h
  have hd := (hpos e he).ne'
  have hA : A e = G e e • e := by
    ext j
    have hh : A e j = G e (EuclideanSpace.single j 1) := by
      simpa only [A, EuclideanSpace.inner_single_right, starRingEnd_apply,
        star_trivial, one_mul] using InnerProductSpace.continuousLinearMapOfBilin_apply
          G e (EuclideanSpace.single j 1)
    rw [hh]
    change G (EuclideanSpace.single 0 1) _ = _
    rw [haxis]
    simp [e, eq_comm]
  have hu := ReducedLengthMinimum.Variational.positive_form_operator_isUnit G hpos
  have hi : m64BoundaryMetricInverse G (A e) = e :=
    ReducedLengthMinimum.Variational.inverse_operator_apply A hu e
  have hh : m64BoundaryMetricInverse G ((G e e)⁻¹ • A e) = (G e e)⁻¹ • e := by
    rw [map_smul, hi]
  simpa only [hA, smul_smul, inv_mul_cancel₀ hd, one_smul] using hh

end PoincareConjecture
