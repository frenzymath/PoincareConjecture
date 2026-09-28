import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CovariantJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Charts
import Mathlib.Topology.MetricSpace.Algebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture

private theorem uniformlyOn_constant {X : Type*} (f : X → ℝ) (K : Set X) :
    TendstoUniformlyOn (fun _ : ℕ => f) f atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε

private theorem uniformlyOn_mul_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f g : ℕ → X → ℝ} {f₀ g₀ : X → ℝ}
    (hf : TendstoUniformlyOn f f₀ atTop K) (hg : TendstoUniformlyOn g g₀ atTop K)
    (hf₀ : ContinuousOn f₀ K) (hg₀ : ContinuousOn g₀ K) :
    TendstoUniformlyOn (fun i x => f i x * g i x) (fun x => f₀ x * g₀ x) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hf.tendstoLocallyUniformlyOn.mul₀ hg.tendstoLocallyUniformlyOn hf₀ hg₀)

private theorem uniformlyOn_finset_sum_zero {X ι : Type*} {K : Set X}
    (s : Finset ι) {f : ι → ℕ → X → ℝ}
    (hf : ∀ a ∈ s, TendstoUniformlyOn (f a) (fun _ => 0) atTop K) :
    TendstoUniformlyOn (fun i x => ∑ a ∈ s, f a i x) (fun _ => 0) atTop K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using uniformlyOn_constant (fun _ => 0) K
  | @insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).add
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
    change TendstoUniformlyOn (fun i x => f a i x + ∑ b ∈ s, f b i x)
      (fun _ => (0 : ℝ) + 0) atTop K at h
    simpa only [Finset.sum_insert ha, add_zero] using h

theorem tendstoUniformlyOn_roundCylinderTensorNormSquared
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) {r : ℕ}
    {T : ℕ → RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ}
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hT : ∀ a, TendstoUniformlyOn (fun i p => T i p a) (fun _ => 0) atTop K) :
    TendstoUniformlyOn
      (fun i p => roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p (T i p))
      (fun _ => 0) atTop K := by
  unfold roundCylinderTensorNormSquared
  apply uniformlyOn_finset_sum_zero Finset.univ
  intro a _
  apply uniformlyOn_finset_sum_zero Finset.univ
  intro b _
  let W := fun p => ∏ j : Fin r,
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ (a j) (b j)
  have hW : Continuous W := continuous_finsetProd Finset.univ fun j _ =>
    (contDiff_roundCylinderGram_inv hu q (a j) (b j)).continuous
  have hfirst : TendstoUniformlyOn (fun i p => W p * T i p a) (fun _ => 0) atTop K := by
    simpa only [mul_zero] using uniformlyOn_mul_compact hK
      (uniformlyOn_constant W K) (hT a) hW.continuousOn continuousOn_const
  simpa only [zero_mul] using uniformlyOn_mul_compact hK hfirst (hT b)
    continuousOn_const continuousOn_const

theorem tendstoUniformlyOn_roundCylinderIteratedDerivative_normSquared
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop, ContDiffOn ℝ ∞
        (fun z => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) z a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)) atTop K)
    (k : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun i p => roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) (B i) k p))
      (fun _ => 0) atTop K := by
  apply tendstoUniformlyOn_roundCylinderTensorNormSquared hu q hK
  intro a
  exact tendstoUniformlyOn_roundCylinderIteratedDerivative u
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) hU
    (fun a b d => (contDiff_roundCylinderChristoffel hu q a b d).contDiffOn)
    (fun a b => (contDiff_roundCylinderGram u q a b).contDiffOn)
    hlocal hjet k a hK hKU

theorem tendstoUniformlyOn_roundCylinder_fixedChart_jetSum
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop, ContDiffOn ℝ ∞
        (fun z => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) z a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)) atTop K)
    (order : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun i p => ∑ k ∈ Finset.range (order + 1), roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) (B i) k p))
      (fun _ => 0) atTop K := by
  apply uniformlyOn_finset_sum_zero
  intro k _
  exact tendstoUniformlyOn_roundCylinderIteratedDerivative_normSquared hu q hU
    hlocal hjet k hK hKU

theorem tendstoUniformlyOn_roundCylinder_changingChart_normSquared
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (qseq : ℕ → UnitTwoSphere)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop, ContDiffOn ℝ ∞
        (fun z => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) z a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)) atTop K)
    (k : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun i p => roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) (B i) k p))
      (fun _ => 0) atTop K := by
  simp_rw [roundCylinderTensorNormSquared_eq_chart_center u q]
  apply tendstoUniformlyOn_roundCylinderTensorNormSquared hu q hK
  intro a
  have h := (roundCylinderIteratedDerivative_smooth_convergence_of_changing_charts u
    (chartAt (EuclideanSpace ℝ (Fin 2)) q)
    (fun i => chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i))
    (fun i => roundCylinderGram_eq_chart_center u q (qseq i))
    (fun i => roundCylinderChristoffel_eq_chart_center u q (qseq i))
    hU
    (fun a b d => (contDiff_roundCylinderChristoffel hu q a b d).contDiffOn)
    (fun a b => (contDiff_roundCylinderGram u q a b).contDiffOn)
    hlocal hjet k a).2 0 K hK hKU
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply, zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → RoundCylinderCoordinates)).comp_tendstoUniformlyOn h

theorem tendstoUniformlyOn_roundCylinder_changingChart_jetSum
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (qseq : ℕ → UnitTwoSphere)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop, ContDiffOn ℝ ∞
        (fun z => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) z a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)) atTop K)
    (order : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun i p => ∑ k ∈ Finset.range (order + 1), roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) (B i) k p))
      (fun _ => 0) atTop K := by
  apply uniformlyOn_finset_sum_zero
  intro k _
  exact tendstoUniformlyOn_roundCylinder_changingChart_normSquared hu q qseq hU
    hlocal hjet k hK hKU

theorem tendstoUniformlyOn_roundCylinder_changingChart_error_jetSum
    {u : ℝ} (hu : u < 1) (q : UnitTwoSphere) (qseq : ℕ → UnitTwoSphere)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop, ContDiffOn ℝ ∞
        (fun z => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) z a b -
          roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) z a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient (B i)
          (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p a b -
          roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p a b))
        (fun _ => 0) atTop K)
    (order : ℕ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun i p => ∑ k ∈ Finset.range (order + 1), roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) p
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i)) (B i) k p))
      (fun _ => 0) atTop K := by
  apply uniformlyOn_finset_sum_zero
  intro k _
  simp_rw [roundCylinderTensorNormSquared_eq_chart_center u q]
  apply tendstoUniformlyOn_roundCylinderTensorNormSquared hu q hK
  intro a
  have h := (roundCylinderIteratedDerivative_smooth_zero_convergence_of_changing_charts u
    (chartAt (EuclideanSpace ℝ (Fin 2)) q)
    (fun i => chartAt (EuclideanSpace ℝ (Fin 2)) (qseq i))
    (fun i => roundCylinderChristoffel_eq_chart_center u q (qseq i))
    hU
    (fun a b d => (contDiff_roundCylinderChristoffel hu q a b d).contDiffOn)
    hlocal hjet k a).2 0 K hK hKU
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply, zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → RoundCylinderCoordinates)).comp_tendstoUniformlyOn h

end PoincareConjecture
