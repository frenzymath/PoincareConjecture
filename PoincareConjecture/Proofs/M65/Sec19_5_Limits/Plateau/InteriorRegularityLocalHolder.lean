import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityScalarHolder
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalDecay

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap InnerProductSpace

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior

theorem local_holder_of_energy_decay {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (hU : IsOpen U) (x0 : LoopPlane)
    {R β Λ : ℝ} (hR : 0 < R) (hRU : closedBall x0 R ⊆ U)
    (hβ : 0 < β) (hΛ : 0 ≤ Λ)
    (hE : ∀ x ∈ closedBall x0 (R / 2), ∀ r : ℝ, 0 < r → r ≤ R / 2 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2) ≤ Λ * r ^ (2 * β)) :
    ∃ (v : LoopPlane → EuclideanSpace ℝ (Fin N)) (H : ℝ), 0 < H ∧
      ContinuousOn v (closedBall x0 (R / 8)) ∧
      (v =ᵐ[volume.restrict (closedBall x0 (R / 8))] fun z => e (F.value z)) ∧
      ∀ x ∈ closedBall x0 (R / 8), ∀ y ∈ closedBall x0 (R / 8),
        ‖v y - v x‖ ≤ H * dist y x ^ β := by
  classical
  obtain ⟨θ, hθc, hθU, hθ⟩ := exists_disk_cutoff hU x0 hR.le hRU
  choose u d hu hd hw using fun j : Fin N => F.cutoff_global j θ hθc hθU
  have hcoord (j : Fin N) (x : LoopPlane) (hx : x ∈ closedBall x0 (R / 4))
      (r : ℝ) (hr : r ∈ Ioc 0 (R / 4)) :
      (∫ z in closedBall x r, ∑ i : Fin 2, (d j i z) ^ 2) ≤ Λ * r ^ (2 * β) := by
    have hsub : closedBall x r ⊆ closedBall x0 R :=
      closedBall_subset_closedBall' (by
        have hx' : dist x x0 ≤ R / 4 := hx
        linarith [hr.2])
    have hactual (i : Fin 2) : d j i =ᵐ[volume.restrict (closedBall x r)]
        fun z => F.derivative i z j := by
      filter_upwards [ae_restrict_of_ae (hd j i),
        ae_restrict_mem isClosed_closedBall.measurableSet] with z hz hzr
      rw [hz, (hθ z (hsub hzr)).2.1, (hθ z (hsub hzr)).2.2]
      simp only [one_mul, zero_apply, zero_mul, add_zero]
    have hEq : (∫ z in closedBall x r, ∑ i : Fin 2, (d j i z) ^ 2) =
        ∫ z in closedBall x r, ∑ i : Fin 2, (F.derivative i z j) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hactual] with z hz
      simp only [hz]
    have hdi (i : Fin 2) :=
      F.derivative_memLp i (closedBall x r) (isCompact_closedBall x r) (hsub.trans hRU)
    have hvec : IntegrableOn (fun z => ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2)
        (closedBall x r) := by
      apply integrable_finsetSum
      intro i _
      exact (hdi i).norm.integrable_sq
    have hscalar : IntegrableOn (fun z => ∑ i : Fin 2, (F.derivative i z j) ^ 2)
        (closedBall x r) := by
      apply integrable_finsetSum
      intro i _
      exact ((hdi i).eval_piLp j).integrable_sq
    rw [hEq]
    refine (integral_mono_ae hscalar hvec ?_).trans
      (hE x (closedBall_subset_closedBall (by linarith) hx) r hr.1 (by linarith [hr.2]))
    filter_upwards with z
    apply Finset.sum_le_sum
    intro i _
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (PiLp.norm_apply_le (F.derivative i z) j)
  have hscalar (j : Fin N) :
      ∃ (v : LoopPlane → ℝ) (H : ℝ), 0 < H ∧ ContinuousOn v (closedBall x0 (R / 8)) ∧
        (v =ᵐ[volume.restrict (closedBall x0 (R / 8))] u j) ∧
        ∀ x ∈ closedBall x0 (R / 8), ∀ y ∈ closedBall x0 (R / 8),
          |v y - v x| ≤ H * dist y x ^ β := by
    simpa only [show R / 4 / 2 = R / 8 by ring] using
      exists_scalar_holder_representative (u j) (d j) (hw j) x0 hΛ hβ
        (show 0 < R / 4 by positivity) (hcoord j)
  choose v H hH hv hvAE hholder using hscalar
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  let V : LoopPlane → EuclideanSpace ℝ (Fin N) := fun z => ∑ j, v j z • b j
  have hsum : 0 ≤ ∑ j, H j := Finset.sum_nonneg (fun j _ => (hH j).le)
  refine ⟨V, 1 + ∑ j, H j, by positivity, ?_, ?_, ?_⟩
  · exact continuousOn_finsetSum _ (fun j _ => (hv j).smul continuousOn_const)
  · have hcoordAE (j : Fin N) : v j =ᵐ[volume.restrict (closedBall x0 (R / 8))]
        fun z => e (F.value z) j := by
      filter_upwards [hvAE j, ae_restrict_of_ae (hu j),
        ae_restrict_mem isClosed_closedBall.measurableSet] with z hz hzu hzr
      rw [hz, hzu, (hθ z (closedBall_subset_closedBall (by linarith) hzr)).2.1, one_mul]
    filter_upwards [ae_all_iff.mpr hcoordAE] with z hz
    change (∑ j, v j z • b j) = e (F.value z)
    simp only [hz]
    exact b.sum_repr (e (F.value z))
  · intro x hx y hy
    have heq : V y - V x = ∑ j, (v j y - v j x) • b j := by
      simp only [V, sub_smul, Finset.sum_sub_distrib]
    rw [heq]
    calc
      ‖∑ j, (v j y - v j x) • b j‖ ≤ ∑ j, ‖(v j y - v j x) • b j‖ := norm_sum_le _ _
      _ = ∑ j, |v j y - v j x| := by
        simp only [norm_smul, Real.norm_eq_abs, b.norm_eq_one, mul_one]
      _ ≤ ∑ j, H j * dist y x ^ β :=
        Finset.sum_le_sum (fun j _ => hholder j x hx y hy)
      _ = (∑ j, H j) * dist y x ^ β := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + ∑ j, H j) * dist y x ^ β :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)

theorem local_holder_of_minimum
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hU : IsOpen U) (hmin : M65LocallyMinimizesEnergy g F)
    (x0 : LoopPlane) {R : ℝ} (hR : 0 < R) (hRU : closedBall x0 R ⊆ U) :
    ∃ (v : LoopPlane → EuclideanSpace ℝ (Fin N)) (β H : ℝ),
      0 < β ∧ β < 1 ∧ 0 < H ∧ ContinuousOn v (closedBall x0 (R / 8)) ∧
      (v =ᵐ[volume.restrict (closedBall x0 (R / 8))] fun z => e (F.value z)) ∧
      ∀ x ∈ closedBall x0 (R / 8), ∀ y ∈ closedBall x0 (R / 8),
        ‖v y - v x‖ ≤ H * dist y x ^ β := by
  obtain ⟨β, Λ, hβ, hβ1, hΛ, hdecay⟩ :=
    F.local_derivative_energy_decay g he hinj hemb compact hU hmin x0 hR hRU
  obtain ⟨v, H, hH, hv, hAE, hholder⟩ :=
    F.local_holder_of_energy_decay hU x0 hR hRU hβ hΛ.le hdecay
  exact ⟨v, β, H, hβ, hβ1, hH, hv, hAE, hholder⟩

end PoincareConjecture.M65LocalWeakMap
