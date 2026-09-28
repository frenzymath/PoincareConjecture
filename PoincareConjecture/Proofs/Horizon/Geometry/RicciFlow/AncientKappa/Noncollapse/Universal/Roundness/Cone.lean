import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.RegionTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.OperatorReaction.Spectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped BigOperators

namespace PoincareConjecture.AncientKappaRoundness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def pinchingCone (c : ℝ) : Set (E →L[ℝ] E) :=
  {A | A.toLinearMap.IsSymmetric ∧
    (∀ v : E, ‖v‖ = 1 → 0 ≤ inner ℝ v (A v)) ∧
    ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 → inner ℝ v (A v) ≤ c * inner ℝ w (A w)}

omit [FiniteDimensional ℝ E] in
theorem zero_mem_pinchingCone (c : ℝ) : (0 : E →L[ℝ] E) ∈ pinchingCone c := by
  refine ⟨LinearMap.IsSymmetric.zero, ?_, ?_⟩ <;> simp

theorem pinchingCone_nonempty (c : ℝ) : (pinchingCone (E := E) c).Nonempty :=
  ⟨0, zero_mem_pinchingCone c⟩

omit [FiniteDimensional ℝ E] in
theorem isClosed_pinchingCone (c : ℝ) : IsClosed (pinchingCone (E := E) c) := by
  have heval (v : E) : Continuous (fun A : E →L[ℝ] E => inner ℝ v (A v)) :=
    continuous_const.inner (ContinuousLinearMap.apply ℝ E v).continuous
  simp only [pinchingCone, ofPred_and, ofPred_forall]
  exact Poincare.HamiltonIvey.isClosed_symmetric_continuousLinearMap.inter
    ((isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_le continuous_const (heval v)).inter
      (isClosed_iInter fun v => isClosed_iInter fun w => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_le (heval v) (continuous_const.mul (heval w))))

omit [FiniteDimensional ℝ E] in
theorem convex_pinchingCone (c : ℝ) : Convex ℝ (pinchingCone (E := E) c) := by
  intro A hA B hB a b ha hb _
  refine ⟨(hA.1.smul (by simp)).add (hB.1.smul (by simp)), ?_, ?_⟩
  · intro v hv
    simp only [add_apply, smul_apply, inner_add_right, inner_smul_right]
    exact add_nonneg (mul_nonneg ha (hA.2.1 v hv)) (mul_nonneg hb (hB.2.1 v hv))
  · intro v w hv hw
    have h := add_le_add (mul_le_mul_of_nonneg_left (hA.2.2 v w hv hw) ha)
      (mul_le_mul_of_nonneg_left (hB.2.2 v w hv hw) hb)
    simpa only [add_apply, smul_apply,
      inner_add_right, inner_smul_right, smul_eq_mul] using (show
        a * inner ℝ v (A v) + b * inner ℝ v (B v) ≤
          c * (a * inner ℝ w (A w) + b * inner ℝ w (B w)) by nlinarith [h])

theorem pinchingCone_conj_iff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃ₗᵢ[ℝ] F) (c : ℝ) (A : E →ₗ[ℝ] E) :
    LinearMap.toContinuousLinearMap (e.toLinearEquiv.conj A) ∈ pinchingCone c ↔
      A.toContinuousLinearMap ∈ pinchingCone c := by
  change (e.toLinearEquiv.conj A).IsSymmetric ∧ _ ↔ A.IsSymmetric ∧ _
  have hsymm : (e.toLinearEquiv.conj A).IsSymmetric ↔ A.IsSymmetric :=
    LinearMap.isSymmetric_linearIsometryEquiv_conj_iff A e
  rw [hsymm]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨hpos, hratio⟩
    constructor
    · intro v hv
      simpa [LinearEquiv.conj_apply] using hpos (e v) (by simpa using hv)
    · intro v w hv hw
      simpa [LinearEquiv.conj_apply] using hratio (e v) (e w)
        (by simpa using hv) (by simpa using hw)
  · rintro ⟨hpos, hratio⟩
    constructor
    · intro v hv
      simpa [LinearEquiv.conj_apply, LinearIsometryEquiv.inner_map_eq_flip] using
        hpos (e.symm v) (by simpa using hv)
    · intro v w hv hw
      simpa [LinearEquiv.conj_apply, LinearIsometryEquiv.inner_map_eq_flip] using
        hratio (e.symm v) (e.symm w) (by simpa using hv) (by simpa using hw)

omit [FiniteDimensional ℝ E] in
private theorem diagonal_rayleigh_le_greatest {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) (horder : Antitone d)
    {v : E} (hv : ‖v‖ = 1) : inner ℝ v (A v) ≤ d 0 := by
  have hsq : ∑ i, (inner ℝ (e i) v) ^ 2 = 1 := by
    simpa [hv] using e.sum_sq_inner_right v
  rw [Poincare.HamiltonIvey.diagonal_rayleigh_eq_sum hA e hd]
  calc
    _ ≤ ∑ i, d 0 * (inner ℝ (e i) v) ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (horder (by omega)) (sq_nonneg _)
    _ = d 0 := by rw [← Finset.mul_sum, hsq, mul_one]

theorem mem_pinchingCone_iff_diagonal {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (e : OrthonormalBasis (Fin 3) ℝ E) {d : Fin 3 → ℝ}
    (hd : ∀ i, A (e i) = d i • e i) (horder : Antitone d)
    {c : ℝ} (hc : 0 ≤ c) :
    A.toContinuousLinearMap ∈ pinchingCone c ↔ 0 ≤ d 2 ∧ d 0 ≤ c * d 2 := by
  constructor
  · intro h
    constructor
    · simpa [hd, inner_smul_right, e.orthonormal.1 2] using
        h.2.1 (e 2) (e.orthonormal.1 2)
    · simpa [hd, inner_smul_right, e.orthonormal.1 0, e.orthonormal.1 2] using
        h.2.2 (e 0) (e 2) (e.orthonormal.1 0) (e.orthonormal.1 2)
  · rintro ⟨hpos, hratio⟩
    refine ⟨hA, ?_, ?_⟩
    · intro v hv
      exact hpos.trans (Poincare.HamiltonIvey.diagonal_rayleigh_ge_least hA e hd horder hv)
    · intro v w hv hw
      exact (diagonal_rayleigh_le_greatest hA e hd horder hv).trans
        (hratio.trans (mul_le_mul_of_nonneg_left
          (Poincare.HamiltonIvey.diagonal_rayleigh_ge_least hA e hd horder hw) hc))

theorem mem_pinchingCone_iff_eigenvalues (hn : Module.finrank ℝ E = 3)
    {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) {c : ℝ} (hc : 0 ≤ c) :
    A.toContinuousLinearMap ∈ pinchingCone c ↔
      0 ≤ hA.eigenvalues hn 2 ∧ hA.eigenvalues hn 0 ≤ c * hA.eigenvalues hn 2 :=
  mem_pinchingCone_iff_diagonal hA (hA.eigenvectorBasis hn)
    (hA.apply_eigenvectorBasis hn) (hA.eigenvalues_antitone hn) hc

theorem eq_smul_id_of_mem_all_pinchingCones (hn : Module.finrank ℝ E = 3)
    {A : E →ₗ[ℝ] E}
    (hA : ∀ c : ℝ, 1 < c → A.toContinuousLinearMap ∈ pinchingCone c) :
    ∃ r : ℝ, 0 ≤ r ∧ A = r • LinearMap.id := by
  let hs : A.IsSymmetric := (hA 2 (by norm_num)).1
  have hpos : 0 ≤ hs.eigenvalues hn 2 :=
    ((mem_pinchingCone_iff_eigenvalues hn hs (by norm_num)).mp (hA 2 (by norm_num))).1
  have hle : hs.eigenvalues hn 0 ≤ hs.eigenvalues hn 2 := by
    apply (le_iff_forall_one_lt_le_mul₀ hpos).mpr
    intro c hc
    simpa [mul_comm] using
      ((mem_pinchingCone_iff_eigenvalues hn hs (show 0 ≤ c by linarith)).mp (hA c hc)).2
  have heig (i : Fin 3) : hs.eigenvalues hn i = hs.eigenvalues hn 2 :=
    le_antisymm ((hs.eigenvalues_antitone hn (by omega : (0 : Fin 3) ≤ i)).trans hle)
      (hs.eigenvalues_antitone hn (by omega : i ≤ (2 : Fin 3)))
  refine ⟨hs.eigenvalues hn 2, hpos, ?_⟩
  apply (hs.eigenvectorBasis hn).toBasis.ext
  intro i
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, OrthonormalBasis.coe_toBasis, heig,
    RCLike.ofReal_real_eq_id, id_eq] using
    hs.apply_eigenvectorBasis hn i

end PoincareConjecture.AncientKappaRoundness
