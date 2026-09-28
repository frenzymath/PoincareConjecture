import PoincareConjecture.Proofs.M35.Thm12_28.CurvatureMetricJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Norm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)

@[instance_reducible] private noncomputable def nullSectionalCovectorNormedGroup :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
attribute [local instance] nullSectionalCovectorNormedGroup

@[instance_reducible] private noncomputable def nullSectionalBilinearNormedGroup :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
attribute [local instance] nullSectionalBilinearNormedGroup

private theorem curvature_basis_expansion {g : RiemannianMetric 3 V}
    (D : LeviCivitaData g) (x : V) (v : Fin 4 → V) :
    D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) =
      ∑ i : Fin 4 → Fin 3, (∏ r, v r (i r)) *
        D.curvatureTensor x (EuclideanSpace.basisFun (Fin 3) ℝ (i 0))
          (EuclideanSpace.basisFun (Fin 3) ℝ (i 1))
          (EuclideanSpace.basisFun (Fin 3) ℝ (i 2))
          (EuclideanSpace.basisFun (Fin 3) ℝ (i 3)) := by
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor x
  rw [hA, multilinear_apply_basis_expansion A (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis, ← hA]



theorem curvatureTensor_tendsto_on_moving_vectors
    {gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → V) (p : V)
    (hjet : ∀ m ≤ 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p)))
    (vseq : ℕ → Fin 4 → V) (v : Fin 4 → V)
    (hv : ∀ i, Tendsto (fun k => vseq k i) atTop (𝓝 (v i))) :
    Tendsto (fun k => (Dseq k).curvatureTensor (pseq k)
      (vseq k 0) (vseq k 1) (vseq k 2) (vseq k 3)) atTop
      (𝓝 (D.curvatureTensor p (v 0) (v 1) (v 2) (v 3))) := by
  have hseq := funext (fun k => curvature_basis_expansion (Dseq k) (pseq k) (vseq k))
  rw [hseq, curvature_basis_expansion D p v]
  apply tendsto_finsetSum
  intro i _
  apply Tendsto.mul
  · apply tendsto_finsetProd
    intro r _
    exact ((EuclideanSpace.proj (i r) : V →L[ℝ] ℝ).continuous.tendsto _).comp (hv r)
  · have h := ((continuousMultilinearCurryFin0 ℝ V ℝ).continuous.tendsto _).comp
      (curvatureTensor_jets_tendsto_of_metric_jets Dseq D pseq p
        (EuclideanSpace.basisFun (Fin 3) ℝ (i 0))
        (EuclideanSpace.basisFun (Fin 3) ℝ (i 1))
        (EuclideanSpace.basisFun (Fin 3) ℝ (i 2))
        (EuclideanSpace.basisFun (Fin 3) ℝ (i 3)) 0
        (fun m hm => hjet m (by omega)))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h



theorem exists_null_sectional_plane_of_metric_jets
    {gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → V) (p : V)
    (hjet : ∀ m ≤ 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p)))
    (u v : ℕ → V)
    (hunit : ∀ᶠ k in atTop, (gseq k).inner (pseq k) (u k) (u k) = 1 ∧
      (gseq k).inner (pseq k) (v k) (v k) = 1 ∧
      (gseq k).inner (pseq k) (u k) (v k) = 0)
    (hcurv : Tendsto (fun k => (Dseq k).curvatureTensor (pseq k)
      (u k) (v k) (u k) (v k)) atTop (𝓝 0)) :
    ∃ a b : V, g.inner p a a = 1 ∧ g.inner p b b = 1 ∧
      g.inner p a b = 0 ∧ D.curvatureTensor p a b a b = 0 := by
  have hmetric : Tendsto (fun k => (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V (V →L[ℝ] V →L[ℝ] ℝ)).continuous.tendsto _).comp
      (hjet 0 (by omega))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  obtain ⟨c, hc, hlow⟩ := exists_uniform_bilinear_lower_bound
    (B := fun _ : V => g.euclideanCoefficients p) (K := {0}) isCompact_singleton
    continuousOn_const (fun _ _ w hw => g.pos p w hw)
  have hlower : ∀ᶠ k in atTop, ∀ w : V,
      (c / 2) * ‖w‖ ^ 2 ≤ (gseq k).inner (pseq k) w w := by
    filter_upwards [Metric.tendsto_nhds.mp hmetric (c / 2) (half_pos hc)] with k hk w
    have he := (g.euclideanCoefficients p - (gseq k).euclideanCoefficients (pseq k)).le_opNorm₂ w w
    change ‖g.inner p w w - (gseq k).inner (pseq k) w w‖ ≤
      ‖g.euclideanCoefficients p - (gseq k).euclideanCoefficients (pseq k)‖ * ‖w‖ * ‖w‖ at he
    have hnorm : ‖g.euclideanCoefficients p - (gseq k).euclideanCoefficients (pseq k)‖ ≤ c / 2 := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using hk.le
    have hdiff : g.inner p w w - (gseq k).inner (pseq k) w w ≤ (c / 2) * ‖w‖ ^ 2 := by
      calc
        _ ≤ |g.inner p w w - (gseq k).inner (pseq k) w w| := le_abs_self _
        _ ≤ ‖g.euclideanCoefficients p - (gseq k).euclideanCoefficients (pseq k)‖ * ‖w‖ ^ 2 := by
          simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using he
        _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖w‖)
    have h := hlow 0 (mem_singleton _) w
    change c * ‖w‖ ^ 2 ≤ g.inner p w w at h
    nlinarith only [h, hdiff]
  let R := max (2 / c) 0 + 1
  have hbound : ∀ᶠ k in atTop,
      (u k, v k) ∈ Metric.closedBall (0 : V) R ×ˢ Metric.closedBall (0 : V) R := by
    filter_upwards [hlower, hunit] with k hk hunitk
    have hb (w : V) (hw : (gseq k).inner (pseq k) w w = 1) :
        w ∈ Metric.closedBall (0 : V) R := by
      have h := hk w
      rw [hw] at h
      have hsquare : ‖w‖ ^ 2 ≤ 2 / c := (le_div_iff₀ hc).mpr (by linarith)
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp only [R]
      nlinarith only [hsquare, le_max_left (2 / c) 0, sq_nonneg (‖w‖ - 1 / 2)]
    exact ⟨hb (u k) hunitk.1, hb (v k) hunitk.2.1⟩
  obtain ⟨w, _hw, sigma, hsigma, hlim⟩ :=
    ((isCompact_closedBall (0 : V) R).prod (isCompact_closedBall (0 : V) R)).tendsto_subseq'
      hbound.frequently
  have hu : Tendsto (u ∘ sigma) atTop (𝓝 w.1) := hlim.fst_nhds
  have hv : Tendsto (v ∘ sigma) atTop (𝓝 w.2) := hlim.snd_nhds
  have hmetric' : Tendsto (fun k => (gseq (sigma k)).euclideanCoefficients (pseq (sigma k)))
      atTop (𝓝 (g.euclideanCoefficients p)) := hmetric.comp hsigma.tendsto_atTop
  have happ : Continuous (fun z : (V →L[ℝ] V →L[ℝ] ℝ) × V × V => z.1 z.2.1 z.2.2) := by
    fun_prop
  have heval {a b : ℕ → V} {a₀ b₀ : V}
      (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
      Tendsto (fun k => (gseq (sigma k)).inner (pseq (sigma k)) (a k) (b k)) atTop
        (𝓝 (g.inner p a₀ b₀)) :=
    (happ.tendsto (g.euclideanCoefficients p, a₀, b₀)).comp
      (hmetric'.prodMk_nhds (ha.prodMk_nhds hb))
  have hunit' := hsigma.tendsto_atTop.eventually hunit
  refine ⟨w.1, w.2, ?_, ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique (heval hu hu)
      (tendsto_const_nhds.congr' (hunit'.mono (fun _ hk => hk.1.symm)))
  · exact tendsto_nhds_unique (heval hv hv)
      (tendsto_const_nhds.congr' (hunit'.mono (fun _ hk => hk.2.1.symm)))
  · exact tendsto_nhds_unique (heval hu hv)
      (tendsto_const_nhds.congr' (hunit'.mono (fun _ hk => hk.2.2.symm)))
  · have h := curvatureTensor_tendsto_on_moving_vectors (fun k => Dseq (sigma k)) D
      (pseq ∘ sigma) p (fun m hm => (hjet m hm).comp hsigma.tendsto_atTop)
      (fun k => ![u (sigma k), v (sigma k), u (sigma k), v (sigma k)])
      ![w.1, w.2, w.1, w.2] (by intro i; fin_cases i <;> first | exact hu | exact hv)
    exact tendsto_nhds_unique h (hcurv.comp hsigma.tendsto_atTop)

end PoincareConjecture.M35
