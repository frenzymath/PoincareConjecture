import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ClassicalEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling









set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

theorem memLp_heatPowerContinuous (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    MemLp (heatPowerContinuous D S k t ht f : M → ℝ) 2
      (g.volumeMeasure.restrict Ω) :=
  (memLp_congr_ae (heatPowerContinuous_ae D S k t ht f)).mpr (Lp.memLp _)


theorem eLpNorm_heatPowerContinuous_le (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (eLpNorm (heatPowerContinuous D S k t ht f : M → ℝ) 2
      (g.volumeMeasure.restrict Ω)).toReal ≤
        ((k.factorial : ℝ) / t ^ k) * ‖f‖ := by
  rw [eLpNorm_congr_ae (heatPowerContinuous_ae D S k t ht f), ← Lp.norm_def]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right
      (norm_heatSpectralPower_le D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k ht) (norm_nonneg f))



theorem eLpNorm_heatPowerContinuous_restrict_le {V : Set M} (hV : V ⊆ Ω)
    (k : ℕ) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (eLpNorm (heatPowerContinuous D S k t (ha.trans_le hat) f : M → ℝ) 2
      (g.volumeMeasure.restrict V)).toReal ≤
        ((k.factorial : ℝ) / a ^ k) * ‖f‖ := by
  have ht := ha.trans_le hat
  have hmono := eLpNorm_mono_measure (p := 2) (μ := g.volumeMeasure.restrict Ω)
    (heatPowerContinuous D S k t ht f : M → ℝ) (Measure.restrict_mono hV le_rfl)
  apply (ENNReal.toReal_mono (memLp_heatPowerContinuous D S k t ht f).2.ne hmono).trans
  apply (eLpNorm_heatPowerContinuous_le D S k t ht f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos ha k)
    (pow_le_pow_left₀ ha.le hat k)



theorem iterate_laplacian_heatPowerContinuous (j k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    EqOn ((D.laplacian)^[j] (heatPowerContinuous D S k t ht f : M → ℝ))
      (fun x => (-1 : ℝ) ^ j * heatPowerContinuous D S (k + j) t ht f x) Ω := by
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      have heq := D.laplacian_eq_of_eventuallyEq
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, S.isOpen.mem_nhds hx, ih⟩)
      rw [heq, D.laplacian_const_mul,
        heatPowerContinuous_laplacian D S (k + j) t ht f x hx]
      simp only [pow_succ, Nat.add_assoc]
      ring



theorem eLpNorm_iterate_laplacian_heatPowerContinuous_restrict_le
    {V : Set M} (hVm : MeasurableSet V) (hV : V ⊆ Ω) (j k : ℕ)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (eLpNorm ((D.laplacian)^[j]
      (heatPowerContinuous D S k t (ha.trans_le hat) f : M → ℝ)) 2
        (g.volumeMeasure.restrict V)).toReal ≤
          (((k + j).factorial : ℝ) / a ^ (k + j)) * ‖f‖ := by
  have heq : eLpNorm ((D.laplacian)^[j]
      (heatPowerContinuous D S k t (ha.trans_le hat) f : M → ℝ)) 2
        (g.volumeMeasure.restrict V) =
      eLpNorm (heatPowerContinuous D S (k + j) t (ha.trans_le hat) f : M → ℝ) 2
        (g.volumeMeasure.restrict V) := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [ae_restrict_mem hVm] with x hx
    rw [iterate_laplacian_heatPowerContinuous D S j k t (ha.trans_le hat) f (hV hx)]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [heq]
  exact eLpNorm_heatPowerContinuous_restrict_le D S hV (k + j) ha hat f

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
