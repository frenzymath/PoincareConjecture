import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalEnergy
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.UniformSpace.Equiv











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)


def WeightedForm (K : Set V) : Type := dirichletForm K

instance (K : Set V) : AddCommGroup (WeightedForm K) :=
  inferInstanceAs (AddCommGroup (dirichletForm K))

instance (K : Set V) : Module ℝ (WeightedForm K) :=
  inferInstanceAs (Module ℝ (dirichletForm K))

instance (K : Set V) : TopologicalSpace (WeightedForm K) :=
  inferInstanceAs (TopologicalSpace (dirichletForm K))

instance (K : Set V) : IsTopologicalAddGroup (WeightedForm K) :=
  inferInstanceAs (IsTopologicalAddGroup (dirichletForm K))

instance (K : Set V) : ContinuousConstSMul ℝ (WeightedForm K) :=
  inferInstanceAs (ContinuousConstSMul ℝ (dirichletForm K))

@[instance_reducible] def weightedCore {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A i j x = A j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j) :
    InnerProductSpace.Core ℝ (WeightedForm K) where
  inner u v := principalFormPairing K A u v
  conj_inner_symm u v := by
    change principalFormPairing K A v u = principalFormPairing K A u v
    unfold principalFormPairing
    rw [real_inner_comm, principalEnergy_symmetric K A hA]
  re_inner_nonneg u := by
    let : NormedAddCommGroup (WeightedForm K) :=
      inferInstanceAs (NormedAddCommGroup (dirichletForm K))
    change 0 ≤ principalFormPairing K A u u
    exact (mul_nonneg (le_min zero_le_one hEll.le) (sq_nonneg ‖(u : dirichletForm K)‖)).trans
      (principalFormPairing_coercive hK A hell u)
  add_left u v w := by
    simp only [principalFormPairing, principalEnergy, map_add, inner_add_left,
      Finset.sum_add_distrib]
    ring
  smul_left u v r := by
    change principalFormPairing K A (r • u) v = r * principalFormPairing K A u v
    simp only [principalFormPairing, principalEnergy, map_smul, real_inner_smul_left,
      mul_add, Finset.mul_sum]
  definite u hu := by
    let : NormedAddCommGroup (WeightedForm K) :=
      inferInstanceAs (NormedAddCommGroup (dirichletForm K))
    have hc := principalFormPairing_coercive hK A hell u
    change principalFormPairing K A u u = 0 at hu
    rw [hu] at hc
    have hn : ‖(u : dirichletForm K)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(u : dirichletForm K)‖, lt_min zero_lt_one hEll]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem weightedCore_continuous {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A i j x = A j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j) :
    ContinuousAt (fun u => (weightedCore hK A hEll hA hell).inner u u) 0 :=
  ((principalFormPairing_continuous K A).comp (continuous_id.prodMk continuous_id)).continuousAt

theorem weightedCore_bounded {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A i j x = A j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j) :
    Bornology.IsVonNBounded ℝ {u : WeightedForm K |
      RCLike.re ((weightedCore hK A hEll hA hell).inner u u) < 1} := by
  let c := min 1 ell
  have hc : 0 < c := lt_min zero_lt_one hEll
  have hb : Bornology.IsBounded {u : dirichletForm K | principalFormPairing K A u u < 1} := by
    apply (Metric.isBounded_closedBall (x := (0 : dirichletForm K)) (r := c⁻¹ + 1)).subset
    intro u hu
    have he := principalFormPairing_coercive hK A hell u
    have hs : ‖u‖ ^ 2 < c⁻¹ := by
      rw [inv_eq_one_div]
      apply (lt_div_iff₀ hc).mpr
      simpa only [mul_comm] using he.trans_lt hu
    have hci := inv_pos.mpr hc
    have hn : ‖u‖ ≤ c⁻¹ + 1 := by nlinarith [sq_nonneg (‖u‖ - 1)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  exact NormedSpace.isVonNBounded_of_isBounded ℝ hb




theorem exists_principal_dirichlet_response {K : Set V} (hK : IsCompact K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A i j x = A j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    {T : ℝ} (hT : 0 ≤ T) {F : ℝ → dirichletValue K}
    (hF : MemLp F 2 (SpectralHeatNative.timeMeasure T)) :
    ∃ U D B : ℝ → dirichletValue K,
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (SpectralHeatNative.timeMeasure T) ∧
      MemLp B 2 (SpectralHeatNative.timeMeasure T) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, D t + B t = F t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
        ∃ v : dirichletForm K, dirichletInclusion K v = U t ∧
          ∀ w : dirichletForm K, principalFormPairing K A w v =
            inner ℝ (dirichletInclusion K w) (U t + B t)) := by
  let C := weightedCore hK.isClosed A hEll hA hell
  have hC := weightedCore_continuous hK.isClosed A hEll hA hell
  have hCb := weightedCore_bounded hK.isClosed A hEll hA hell
  let : NormedAddCommGroup (WeightedForm K) := C.toNormedAddCommGroupOfTopology hC hCb
  let : InnerProductSpace ℝ (WeightedForm K) := InnerProductSpace.ofCoreOfTopology C hC hCb
  let e : WeightedForm K ≃L[ℝ] dirichletForm K :=
    { LinearEquiv.refl ℝ (dirichletForm K) with
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let eu : WeightedForm K ≃ᵤ dirichletForm K :=
    { e.toEquiv with
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  let : CompleteSpace (WeightedForm K) := eu.completeSpace_iff.mpr inferInstance
  let J : WeightedForm K →L[ℝ] dirichletValue K :=
    (dirichletInclusion K).comp e.toContinuousLinearMap
  have hJc : IsCompactOperator J :=
    (isCompactOperator_dirichletInclusion hK).comp_clm e.toContinuousLinearMap
  have hJd : DenseRange J := dirichletInclusion_denseRange K
  have hJn : ‖J‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    have hE : 0 ≤ principalEnergy K A (e u) (e u) := by
      have hs : 0 ≤ ∑ i : Fin n, ‖dirichletPartial K i (e u)‖ ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      exact (mul_nonneg hEll.le hs).trans (principalEnergy_coercive hK.isClosed A hell (e u))
    have hs : ‖J u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq u]
      change ‖dirichletInclusion K (e u)‖ ^ 2 ≤ principalFormPairing K A (e u) (e u)
      simp only [principalFormPairing, real_inner_self_eq_norm_sq]
      linarith only [hE]
    simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  obtain ⟨U, D, B, hU0, hUcont, hD, hB, hd, heq, hgraph, _⟩ :=
    HilbertResolventNative.exists_response («V» := WeightedForm K)
      (H := dirichletValue K) (T := T) (F := F) J hJc hJd hJn hT hF
  refine ⟨U, D, B, hU0, hUcont, hD, hB, hd, heq, ?_⟩
  filter_upwards [hgraph] with t ht
  obtain ⟨v, hv, hp⟩ := (HilbertResolventNative.inGeneratorGraph_iff_variational J _ _).mp ht
  exact ⟨e v, hv, fun w => hp (e.symm w)⟩

end PoincareConjecture.M35.Uniqueness.Heat
