import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.CurvatureReaction
import PoincareConjecture.Proofs.M04.CurvatureEnergyTime
import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients
import PoincareConjecture.Proofs.M04.TensorEvolution










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M45

open PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem hasDerivAt_curvatureEnergy
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    HasDerivAt (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2)
      (2 * tensorPairing (F.metric t) D.riemannEvaluation
          (D.tensorLaplacian D.riemannEvaluation) x +
        4 * (∑ a : Fin 4 → Fin d,
          D.riemannEvaluation x (fun i => b (a i)) *
            curvatureBfour D x (fun i => b (a i)))) t := by
  classical
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let P : (Fin 4 → TangentSpace (𝓡 n) x) → ℝ := fun v =>
    D.tensorLaplacian D.riemannEvaluation x v +
      D.curvatureReaction x (v 0) (v 1) (v 2) (v 3)
  have htime (v : Fin 4 → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => (F.connection s).riemannEvaluation x v) (P v) t := by
    have hvtuple : ![v 0, v 1, v 2, v 3] = v := by
      funext i
      fin_cases i <;> rfl
    have hv := (F.hasDerivWithinAt_curvatureTensor t (interior_subset ht) x
      (v 0) (v 1) (v 2) (v 3)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
    simpa only [LeviCivitaData.riemannEvaluation, P, D, hvtuple] using hv
  have hnorm := hasDerivAt_flow_tensorNorm_sq F
    (fun s => (F.connection s).riemannEvaluation)
    (fun s => isSmoothCovariantTensor_riemannEvaluation (F.connection s)) ht x P htime
  change HasDerivAt (fun s => ((F.connection s).curvatureDerivativeNorm 0 x) ^ 2)
    _ t at hnorm
  simp only [LeviCivitaData.curvatureDerivativeNorm_zero] at hnorm
  apply hnorm.congr_deriv
  change
    2 * (∑ a : Fin 4 → Fin d,
      D.riemannEvaluation x (fun i => b (a i)) *
        (D.tensorLaplacian D.riemannEvaluation x (fun i => b (a i)) +
          D.curvatureReaction x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3)))) +
      2 * (∑ j : Fin 4, ∑ a : Fin 4 → Fin d, ∑ l : Fin d,
        D.ricci x (b (a j)) (b l) *
          D.riemannEvaluation x (fun i => b (a i)) *
          D.riemannEvaluation x (fun i => b (Function.update a j l i))) = _
  have hupdate (a : Fin 4 → Fin d) (j : Fin 4) (l : Fin d) :
      Function.update (fun i => b (a i)) j (b l) =
        (fun i => b (Function.update a j l i)) := (Function.comp_update b a j l).symm
  have hreact (a : Fin 4 → Fin d) :
      D.curvatureReaction x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3)) =
        2 * curvatureBfour D x (fun i => b (a i)) -
          ∑ j : Fin 4, ∑ l : Fin d,
            D.ricci x (b (a j)) (b l) *
              D.riemannEvaluation x (fun i => b (Function.update a j l i)) := by
    have h := curvatureReaction_eq_Bfour_sub_slots D x (fun i => b (a i))
    change _ = 2 * curvatureBfour D x (fun i => b (a i)) -
      ∑ j : Fin 4, ∑ l : Fin d, D.ricci x (b (a j)) (b l) *
        D.riemannEvaluation x (Function.update (fun i => b (a i)) j (b l)) at h
    simpa only [hupdate] using h
  simp_rw [hreact]
  have hsum :
      (∑ a : Fin 4 → Fin d,
        D.riemannEvaluation x (fun i => b (a i)) *
          (∑ j : Fin 4, ∑ l : Fin d,
            D.ricci x (b (a j)) (b l) *
              D.riemannEvaluation x (fun i => b (Function.update a j l i)))) =
      ∑ j : Fin 4, ∑ a : Fin 4 → Fin d, ∑ l : Fin d,
        D.ricci x (b (a j)) (b l) *
          D.riemannEvaluation x (fun i => b (a i)) *
          D.riemannEvaluation x (fun i => b (Function.update a j l i)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsum]
  have hB :
      (∑ a : Fin 4 → Fin d,
        D.riemannEvaluation x (fun i => b (a i)) *
          (2 * curvatureBfour D x (fun i => b (a i)))) =
      2 * (∑ a : Fin 4 → Fin d,
        D.riemannEvaluation x (fun i => b (a i)) *
          curvatureBfour D x (fun i => b (a i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp only [tensorPairing]
  rw [hB]
  ring



theorem curvatureEnergy_heat_inequality_interior
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    derivWithin (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x +
        16 * ((F.connection t).curvatureTensorNorm x) ^ 3 := by
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hderiv := (hasDerivAt_curvatureEnergy F ht x).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_convex hconv hne t (interior_subset ht))
  have hbochner := laplacian_tensorNorm_sq (D := F.connection t)
    (isSmoothCovariantTensor_riemannEvaluation (F.connection t)) x
  change (F.connection t).laplacian
      (fun y => ((F.connection t).curvatureDerivativeNorm 0 y) ^ 2) x = _ at hbochner
  simp only [LeviCivitaData.curvatureDerivativeNorm_zero] at hbochner
  have hreaction := curvature_energy_reaction_le (F.connection t) x
  dsimp only at hderiv hreaction
  nlinarith [sq_nonneg ((F.metric t).tensorNorm
    ((F.connection t).covariantTensorDerivative (F.connection t).riemannEvaluation) x)]



theorem contDiffOn_curvatureEnergy_timeSlice (F : RicciFlow n M J) (x : M) :
    ContDiffOn ℝ ∞ (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun s : ℝ => (s, x)) := contMDiff_id.prodMk contMDiff_const
  have h := (contMDiffOn_flow_curvatureDerivativeEnergy F 0).comp hslice.contMDiffOn
    (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ univ) from
      fun _ hs => ⟨hs, mem_univ x⟩)
  simpa only [Function.comp_def, LeviCivitaData.curvatureDerivativeNorm_zero] using h.contDiffOn



theorem continuousOn_curvatureEnergy_heatRHS (F : RicciFlow n M J) (x : M) :
    ContinuousOn
      (fun t => (F.connection t).laplacian
          (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x +
        16 * ((F.connection t).curvatureTensorNorm x) ^ 3) J := by
  have hE : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ((F.connection p.1).curvatureTensorNorm p.2) ^ 2)
      (J ×ˢ univ) := by
    simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using
      contMDiffOn_flow_curvatureDerivativeEnergy F 0
  have hslice : ContinuousOn (fun t : ℝ => (t, x)) J :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hmaps : MapsTo (fun t : ℝ => (t, x)) J (J ×ˢ univ) :=
    fun _ ht => ⟨ht, mem_univ x⟩
  have hLap := (continuousOn_flow_timeDependentLaplacian F hE).comp hslice hmaps
  have hEtime := hE.continuousOn.comp hslice hmaps
  have hN : ContinuousOn (fun t => (F.connection t).curvatureTensorNorm x) J := by
    apply hEtime.sqrt.congr
    intro t _
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  exact hLap.add ((hN.pow 3).const_mul 16)



theorem curvatureEnergy_heat_inequality
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J) (x : M) :
    derivWithin (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J t ≤
      (F.connection t).laplacian
        (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x +
        16 * ((F.connection t).curvatureTensorNorm x) ^ 3 := by
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hderiv := (contDiffOn_curvatureEnergy_timeSlice F x).continuousOn_derivWithin
    (uniqueDiffOn_convex hconv hne) (by simp)
  exact ContinuousWithinAt.closure_le (hdense ht)
    ((hderiv t ht).mono interior_subset)
    (((continuousOn_curvatureEnergy_heatRHS F x) t ht).mono interior_subset)
    (fun s hs => curvatureEnergy_heat_inequality_interior F hs x)

end PoincareConjecture.M45
