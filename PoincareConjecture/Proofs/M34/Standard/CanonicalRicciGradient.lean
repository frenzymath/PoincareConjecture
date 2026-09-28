import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceJetFluxParameters
import PoincareConjecture.Proofs.M03.MetricDifferenceEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem DifferenceEnergy.curvatureAction_trace {n : ℕ}
    (gamma : Gamma n) (R : Raw n) (i j k : Fin n) :
    (∑ l : Fin n, curvatureAction gamma i R l l j k) =
      -(∑ p : Fin n, gamma i j p * ∑ l : Fin n, R l l p k) -
        ∑ p : Fin n, gamma i k p * ∑ l : Fin n, R l l j p := by
  have hc : (∑ l : Fin n, ∑ p : Fin n, gamma i p l * R p l j k) =
      ∑ l : Fin n, ∑ p : Fin n, gamma i l p * R l p j k := Finset.sum_comm
  simp only [curvatureAction, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_sub_distrib, hc, sub_self, zero_sub, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun l p => gamma i j p * R l l p k),
    Finset.sum_comm (f := fun l p => gamma i k p * R l l j p)]

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

theorem canonicalDomain_ricci_trace :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x u v : V n),
      D.ricci ((extChartAt (𝓡 n) p).symm x) u v =
        ∑ l : Fin n, EuclideanSpace.proj l
          (D.curvature ((extChartAt (𝓡 n) p).symm x)
            (EuclideanSpace.single l 1) u v) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x u v
  rw [Proofs.M03.ricci_eq_sum_basis_of_curvature_pairing D
    ((extChartAt (𝓡 n) p).symm x) u v (PiLp.basisFun 2 ℝ (Fin n))]
  apply Finset.sum_congr rfl
  intro l _
  change (D.curvature _ ((PiLp.basisFun 2 ℝ (Fin n)) l) u v).ofLp l = _
  rw [PiLp.basisFun_apply]
  rfl

theorem canonicalDomain_ricci_expansion :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x u v : V n),
      D.ricci ((extChartAt (𝓡 n) p).symm x) u v =
        ∑ j : Fin n, ∑ k : Fin n,
          u j * v k * ∑ l : Fin n, canonicalDomain_curvatureArray U hU g D p x l l j k := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x u v
  let y := (extChartAt (𝓡 n) p).symm x
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let b := PiLp.basisFun 2 ℝ (Fin n)
  have hv (w : V n) : w = ∑ i : Fin n, w i • e i := by
    simpa [b, e, PiLp.basisFun_repr, PiLp.basisFun_apply] using (b.sum_repr w).symm
  obtain ⟨R, hR⟩ := Proofs.M03.exists_curvature_trilinearMap D y
  rw [canonicalDomain_ricci_trace U hU g D p x u v]
  have hcomponent (l : Fin n) :
      EuclideanSpace.proj l (D.curvature y (e l) u v) =
        ∑ j : Fin n, ∑ k : Fin n, u j * v k *
          canonicalDomain_curvatureArray U hU g D p x l l j k := by
    rw [← hR]
    conv_lhs => rw [hv u, hv v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hR]
    change v k * (u j * canonicalDomain_curvatureArray U hU g D p x l l j k) = _
    ring
  change (∑ l : Fin n, EuclideanSpace.proj l (D.curvature y (e l) u v)) = _
  simp_rw [hcomponent, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem canonicalDomain_covariantCurvatureArray_ricci_trace :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      ∀ i j k : Fin n,
        (∑ l : Fin n, canonicalDomain_covariantCurvatureArray U hU g D p x i l l j k) =
          fderiv ℝ (fun z => D.ricci ((extChartAt (𝓡 n) p).symm z)
            (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)) x
              (EuclideanSpace.single i 1) -
          D.ricci ((extChartAt (𝓡 n) p).symm x)
            (D.connection (fun _ : U => EuclideanSpace.single j 1)
              ((extChartAt (𝓡 n) p).symm x) (EuclideanSpace.single i 1))
            (EuclideanSpace.single k 1) -
          D.ricci ((extChartAt (𝓡 n) p).symm x)
            (EuclideanSpace.single j 1)
            (D.connection (fun _ : U => EuclideanSpace.single k 1)
              ((extChartAt (𝓡 n) p).symm x) (EuclideanSpace.single i 1)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx i j k
  let r := (extChartAt (𝓡 n) p).symm
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let R := canonicalDomain_curvatureArray U hU g D p
  let gamma := (canonicalDomain_differenceEnergyBackground U hU g D p x).1.2
  have htrace : (fun z => D.ricci (r z) (e j) (e k)) =
      fun z => ∑ l : Fin n, R z l l j k := by
    funext z
    exact canonicalDomain_ricci_trace U hU g D p z (e j) (e k)
  have hd := canonicalDomain_differentiableAt_curvatureArray U hU g D p x hx
  have hdr (l : Fin n) : DifferentiableAt ℝ (fun z => R z l l j k) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp
      (differentiableAt_pi.mp (differentiableAt_pi.mp hd l) l) j) k
  have hderiv : fderiv ℝ (fun z => D.ricci (r z) (e j) (e k)) x (e i) =
      ∑ l : Fin n, fderiv ℝ (fun z => R z l l j k) x (e i) := by
    rw [htrace, fderiv_fun_sum (fun l _ => hdr l)]
    simp only [sum_apply]
  have hleft : D.ricci (r x)
      (D.connection (fun _ : U => e j) (r x) (e i)) (e k) =
        ∑ q : Fin n, gamma i j q * ∑ l : Fin n, R x l l q k := by
    rw [canonicalDomain_ricci_expansion U hU g D p x]
    simp only [e, PiLp.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  have hright : D.ricci (r x) (e j)
      (D.connection (fun _ : U => e k) (r x) (e i)) =
        ∑ q : Fin n, gamma i k q * ∑ l : Fin n, R x l l j q := by
    rw [canonicalDomain_ricci_expansion U hU g D p x]
    rw [Finset.sum_comm]
    simp only [e, PiLp.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  change (∑ l : Fin n, (fderiv ℝ (fun z => R z l l j k) x (e i) +
    curvatureAction gamma i (R x) l l j k)) = _
  rw [Finset.sum_add_distrib, curvatureAction_trace]
  change _ = fderiv ℝ (fun z => D.ricci (r z) (e j) (e k)) x (e i) -
    D.ricci (r x) (D.connection (fun _ : U => e j) (r x) (e i)) (e k) -
    D.ricci (r x) (e j) (D.connection (fun _ : U => e k) (r x) (e i))
  rw [hderiv, hleft, hright]
  ring

end PoincareConjecture.M34
