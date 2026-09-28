import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

open MeasureTheory Filter

namespace PoincareConjecture.M63

theorem exists_continuousL2_product
    {K E F G : Type*} [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [OpensMeasurableSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (mu : Measure K) (B : E →L[ℝ] F →L[ℝ] G) :
    ∃ M : C(K, E) →L[ℝ] Lp F 2 mu →L[ℝ] Lp G 2 mu,
      ‖M‖ ≤ ‖B‖ ∧ ∀ a v, ∀ᵐ x ∂mu, M a v x = B (a x) (v x) := by
  have hbound (a : C(K, E)) (v : Lp F 2 mu) (x : K) :
      ‖B (a x) (v x)‖ ≤ ‖B‖ * ‖a‖ * ‖v x‖ := by
    exact (B.le_opNorm₂ _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (a.norm_coe_le_norm x) (norm_nonneg B))
        (norm_nonneg (v x)))
  have hmem (a : C(K, E)) (v : Lp F 2 mu) :
      MemLp (fun x => B (a x) (v x)) 2 mu := by
    apply (Lp.memLp v).of_le_mul
      (B.aestronglyMeasurable_comp₂ a.continuous.aestronglyMeasurable
        (Lp.memLp v).aestronglyMeasurable)
    exact Eventually.of_forall (hbound a v)
  let p (a : C(K, E)) (v : Lp F 2 mu) : Lp G 2 mu :=
    (hmem a v).toLp (fun x => B (a x) (v x))
  have hae (a : C(K, E)) (v : Lp F 2 mu) :
      ∀ᵐ x ∂mu, p a v x = B (a x) (v x) := (hmem a v).coeFn_toLp
  have hnorm (a : C(K, E)) (v : Lp F 2 mu) :
      ‖p a v‖ ≤ ‖B‖ * ‖a‖ * ‖v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hae a v] with x hx
    rw [hx]
    exact hbound a v x
  have hadd₁ (a b : C(K, E)) (v : Lp F 2 mu) : p (a + b) v = p a v + p b v := by
    apply Lp.ext
    filter_upwards [hae (a + b) v, hae a v, hae b v, Lp.coeFn_add (p a v) (p b v)]
      with x hab ha hb hout
    simp only [hab, hout, Pi.add_apply, ha, hb, ContinuousMap.add_apply, map_add, add_apply]
  have hsmul₁ (c : ℝ) (a : C(K, E)) (v : Lp F 2 mu) : p (c • a) v = c • p a v := by
    apply Lp.ext
    filter_upwards [hae (c • a) v, hae a v, Lp.coeFn_smul c (p a v)] with x hca ha hout
    simp only [hca, hout, Pi.smul_apply, ha, ContinuousMap.smul_apply, map_smul, smul_apply]
  have hadd₂ (a : C(K, E)) (v w : Lp F 2 mu) : p a (v + w) = p a v + p a w := by
    apply Lp.ext
    filter_upwards [hae a (v + w), hae a v, hae a w, Lp.coeFn_add v w,
      Lp.coeFn_add (p a v) (p a w)] with x hvw hv hw hin hout
    simp only [hvw, hout, Pi.add_apply, hv, hw, hin, map_add]
  have hsmul₂ (c : ℝ) (a : C(K, E)) (v : Lp F 2 mu) : p a (c • v) = c • p a v := by
    apply Lp.ext
    filter_upwards [hae a (c • v), hae a v, Lp.coeFn_smul c v,
      Lp.coeFn_smul c (p a v)] with x hcv hv hin hout
    simp only [hcv, hout, Pi.smul_apply, hv, hin, map_smul]
  let m := LinearMap.mk₂ ℝ p hadd₁ hsmul₁ hadd₂ hsmul₂
  exact ⟨m.mkContinuous₂ ‖B‖ hnorm,
    m.mkContinuous₂_norm_le (norm_nonneg B) hnorm, hae⟩

end PoincareConjecture.M63
