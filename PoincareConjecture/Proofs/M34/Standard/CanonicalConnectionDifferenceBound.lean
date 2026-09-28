import PoincareConjecture.Proofs.M34.Standard.CanonicalCurvatureNorms
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceDensity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem canonicalDomain_connection_difference_norm_le
    {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U] :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
      (g' : RiemannianMetric n U) (D' : LeviCivitaData g') (p : U) (x : V n)
      {C : ℝ}, 0 ≤ C →
      ‖canonicalDomain_differenceEnergyBackground U hU g D p x‖ ≤ C →
      ‖canonicalDomain_differenceEnergyBackground U hU g' D' p x‖ ≤ C →
      norm (E := FA n) (CovariantDerivative.difference D.connection D'.connection
        ((extChartAt (𝓡 n) p).symm x)) ≤ (n : ℝ) ^ 3 * (2 * C) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x C hC hb0 hb1
  let r := (extChartAt (𝓡 n) p).symm
  let A : FA n := CovariantDerivative.difference D.connection D'.connection (r x)
  have hgamma {g0 : RiemannianMetric n U} (D0 : LeviCivitaData g0)
      (hb : ‖canonicalDomain_differenceEnergyBackground U hU g0 D0 p x‖ ≤ C)
      (i j l : Fin n) :
      |EuclideanSpace.proj l (D0.connection (fun _ : U => EuclideanSpace.single j 1)
        (r x) (EuclideanSpace.single i 1))| ≤ C := by
    have hg : ‖(canonicalDomain_differenceEnergyBackground U hU g0 D0 p x).1.2‖ ≤ C :=
      (norm_snd_le _).trans ((norm_fst_le _).trans hb)
    have hi := (pi_norm_le_iff_of_nonneg hC).mp hg i
    have hj := (pi_norm_le_iff_of_nonneg hC).mp hi j
    simpa only [Real.norm_eq_abs, canonicalDomain_differenceEnergyBackground, r] using
      (pi_norm_le_iff_of_nonneg hC).mp hj l
  have hag (i j l : Fin n) : |ag A i j l| ≤ 2 * C := by
    have hY := (constantChart_contMDiff_const_field (𝓡 n) (canonicalOpen_chart_eq hU)
      (EuclideanSpace.single j (1 : ℝ))).mdifferentiableAt (x := r x) (by simp)
    have hh := IsCovariantDerivativeOn.difference_apply
      D.connection.isCovariantDerivativeOnUniv D'.connection.isCovariantDerivativeOnUniv
      (mem_univ (r x)) hY
    have hv : A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) =
        D.connection (fun _ : U => EuclideanSpace.single j 1) (r x) (EuclideanSpace.single i 1) -
          D'.connection (fun _ : U => EuclideanSpace.single j 1) (r x)
            (EuclideanSpace.single i 1) :=
      congrArg (fun L => L (EuclideanSpace.single i 1)) hh
    dsimp only [ag]
    rw [hv, map_sub]
    have ht := norm_sub_le
      (EuclideanSpace.proj l (D.connection (fun _ : U => EuclideanSpace.single j 1)
        (r x) (EuclideanSpace.single i 1)))
      (EuclideanSpace.proj l (D'.connection (fun _ : U => EuclideanSpace.single j 1)
        (r x) (EuclideanSpace.single i 1)))
    simp only [Real.norm_eq_abs] at ht
    exact ht.trans (by linarith [hgamma D hb0 i j l, hgamma D' hb1 i j l])
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  have hv (j i : Fin n) : ‖A (e j) (e i)‖ ≤ n * (2 * C) := by
    simpa only [Fintype.card_fin] using
      PiLp.norm_le_card_mul_of_coordinates (A (e j) (e i)) (fun l => hag i j l)
  have h1 (j : Fin n) : ‖A (e j)‖ ≤ n * (n * (2 * C)) := by
    simpa only [Fintype.card_fin] using (A (e j)).opNorm_le_card_mul_of_coordinates (hv j)
  have h2 : ‖A‖ ≤ n * (n * (n * (2 * C))) := by
    simpa only [Fintype.card_fin] using A.opNorm_le_card_mul_of_coordinates h1
  convert h2 using 1
  ring

end PoincareConjecture.M34
