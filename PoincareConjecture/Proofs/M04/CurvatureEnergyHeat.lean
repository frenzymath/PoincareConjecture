import PoincareConjecture.Definitions.Ch03.CurvatureReaction
import PoincareConjecture.Proofs.M04.CurvatureEnergyTime
import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients
import PoincareConjecture.Proofs.M04.TensorEvolution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private noncomputable def curvatureBfour {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (v : Fin 4 → TangentSpace (𝓡 n) x) : ℝ :=
  D.curvatureB x (v 0) (v 1) (v 2) (v 3) -
    D.curvatureB x (v 0) (v 1) (v 3) (v 2) -
    D.curvatureB x (v 0) (v 3) (v 1) (v 2) +
    D.curvatureB x (v 0) (v 2) (v 1) (v 3)

private theorem curvatureReaction_eq_Bfour_sub_slots
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (v : Fin 4 → TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    D.curvatureReaction x (v 0) (v 1) (v 2) (v 3) =
      2 * curvatureBfour D x v -
        ∑ j : Fin 4, ∑ l : Fin d,
          D.ricci x (v j) (b l) *
            D.riemannEvaluation x (Function.update v j (b l)) := by
  classical
  simp [LeviCivitaData.curvatureReaction, curvatureBfour,
    Fin.sum_univ_four, LeviCivitaData.riemannEvaluation,
    Finset.sum_add_distrib, Function.update]

set_option maxHeartbeats 1200000 in
private theorem abs_curvatureTensor_basis_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    let b := g.orthonormalBasis x
    |D.curvatureTensor x (b i) (b j) (b k) (b l)| ≤ D.curvatureTensorNorm x := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let R (i j k l : Fin d) := D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hN : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hNonneg1 (p q r : Fin d) : 0 ≤ ∑ s : Fin d, (R p q r s) ^ 2 :=
    Finset.sum_nonneg fun s _ => sq_nonneg (R p q r s)
  have hNonneg2 (p q : Fin d) :
      0 ≤ ∑ r : Fin d, ∑ s : Fin d, (R p q r s) ^ 2 :=
    Finset.sum_nonneg fun r _ => hNonneg1 p q r
  have hNonneg3 (p : Fin d) :
      0 ≤ ∑ q : Fin d, ∑ r : Fin d, ∑ s : Fin d, (R p q r s) ^ 2 :=
    Finset.sum_nonneg fun q _ => hNonneg2 p q
  have hNorm : (D.curvatureTensorNorm x) ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d, (R i j k l) ^ 2 := by
    change (Real.sqrt (∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d,
      ∑ l : Fin d, (R i j k l) ^ 2)) ^ 2 = _
    exact Real.sq_sqrt (Finset.sum_nonneg fun p _ => hNonneg3 p)
  have hTerm : (R i j k l) ^ 2 ≤
      ∑ p : Fin d, ∑ q : Fin d, ∑ r : Fin d, ∑ s : Fin d, (R p q r s) ^ 2 := by
    calc
      _ ≤ ∑ s : Fin d, (R i j k s) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun s : Fin d => (R i j k s) ^ 2)
          (fun s _ => sq_nonneg (R i j k s)) (Finset.mem_univ l)
      _ ≤ ∑ r : Fin d, ∑ s : Fin d, (R i j r s) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun r : Fin d => ∑ s : Fin d, (R i j r s) ^ 2)
          (fun r _ => hNonneg1 i j r) (Finset.mem_univ k)
      _ ≤ ∑ q : Fin d, ∑ r : Fin d, ∑ s : Fin d, (R i q r s) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun q : Fin d => ∑ r : Fin d, ∑ s : Fin d, (R i q r s) ^ 2)
          (fun q _ => hNonneg2 i q) (Finset.mem_univ j)
      _ ≤ ∑ p : Fin d, ∑ q : Fin d, ∑ r : Fin d, ∑ s : Fin d, (R p q r s) ^ 2 :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun p : Fin d => ∑ q : Fin d, ∑ r : Fin d, ∑ s : Fin d,
            (R p q r s) ^ 2)
          (fun p _ => hNonneg3 p)
          (Finset.mem_univ i)
  have hAbs : |R i j k l| ^ 2 ≤ (D.curvatureTensorNorm x) ^ 2 := by
    rw [sq_abs]
    exact hTerm.trans_eq hNorm.symm
  change |R i j k l| ≤ D.curvatureTensorNorm x
  nlinarith only [hAbs, abs_nonneg (R i j k l), hN]

private theorem abs_curvatureB_basis_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    let b := g.orthonormalBasis x
    |D.curvatureB x (b i) (b j) (b k) (b l)| ≤
      (n : ℝ) ^ 2 * (D.curvatureTensorNorm x) ^ 2 := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let N := D.curvatureTensorNorm x
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hdim : d = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hTerm (p q : Fin d) :
      |D.curvatureTensor x (b i) (b p) (b j) (b q) *
        D.curvatureTensor x (b k) (b p) (b l) (b q)| ≤ N ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (abs_curvatureTensor_basis_le D x i p j q)
      (abs_curvatureTensor_basis_le D x k p l q) (abs_nonneg _) hN
  change |D.curvatureB x (b i) (b j) (b k) (b l)| ≤ (n : ℝ) ^ 2 * N ^ 2
  calc
    _ = |∑ p : Fin d, ∑ q : Fin d,
        D.curvatureTensor x (b i) (b p) (b j) (b q) *
          D.curvatureTensor x (b k) (b p) (b l) (b q)| := rfl
    _ ≤ ∑ p : Fin d, |∑ q : Fin d,
        D.curvatureTensor x (b i) (b p) (b j) (b q) *
          D.curvatureTensor x (b k) (b p) (b l) (b q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin d, ∑ q : Fin d,
        |D.curvatureTensor x (b i) (b p) (b j) (b q) *
          D.curvatureTensor x (b k) (b p) (b l) (b q)| :=
      Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin d, ∑ _q : Fin d, N ^ 2 :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hTerm p q
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        hdim]
      ring

private theorem abs_curvatureBfour_basis_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (a : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    let b := g.orthonormalBasis x
    |curvatureBfour D x (fun i => b (a i))| ≤
      4 * (n : ℝ) ^ 2 * (D.curvatureTensorNorm x) ^ 2 := by
  let b := g.orthonormalBasis x
  obtain ⟨h1l, h1u⟩ := abs_le.mp (abs_curvatureB_basis_le D x (a 0) (a 1) (a 2) (a 3))
  obtain ⟨h2l, h2u⟩ := abs_le.mp (abs_curvatureB_basis_le D x (a 0) (a 1) (a 3) (a 2))
  obtain ⟨h3l, h3u⟩ := abs_le.mp (abs_curvatureB_basis_le D x (a 0) (a 3) (a 1) (a 2))
  obtain ⟨h4l, h4u⟩ := abs_le.mp (abs_curvatureB_basis_le D x (a 0) (a 2) (a 1) (a 3))
  change |D.curvatureB x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3)) -
      D.curvatureB x (b (a 0)) (b (a 1)) (b (a 3)) (b (a 2)) -
      D.curvatureB x (b (a 0)) (b (a 3)) (b (a 1)) (b (a 2)) +
      D.curvatureB x (b (a 0)) (b (a 2)) (b (a 1)) (b (a 3))| ≤ _
  apply abs_le.mpr
  constructor <;> nlinarith only [h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u]

private theorem curvature_energy_reaction_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    let b := g.orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    4 * (∑ a : Fin 4 → Fin d,
      D.riemannEvaluation x (fun i => b (a i)) *
        curvatureBfour D x (fun i => b (a i))) ≤
      16 * (n : ℝ) ^ 6 * (D.curvatureTensorNorm x) ^ 3 := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let N := D.curvatureTensorNorm x
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hdim : d = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hTerm (a : Fin 4 → Fin d) :
      D.riemannEvaluation x (fun i => b (a i)) *
        curvatureBfour D x (fun i => b (a i)) ≤
          N * (4 * (n : ℝ) ^ 2 * N ^ 2) := by
    calc
      _ ≤ |D.riemannEvaluation x (fun i => b (a i)) *
          curvatureBfour D x (fun i => b (a i))| := le_abs_self _
      _ = |D.riemannEvaluation x (fun i => b (a i))| *
          |curvatureBfour D x (fun i => b (a i))| := abs_mul _ _
      _ ≤ _ := mul_le_mul
        (abs_curvatureTensor_basis_le D x (a 0) (a 1) (a 2) (a 3))
        (abs_curvatureBfour_basis_le D x a) (abs_nonneg _) hN
  change 4 * (∑ a : Fin 4 → Fin d,
      D.riemannEvaluation x (fun i => b (a i)) *
        curvatureBfour D x (fun i => b (a i))) ≤ 16 * (n : ℝ) ^ 6 * N ^ 3
  calc
    _ ≤ 4 * (∑ _a : Fin 4 → Fin d, N * (4 * (n : ℝ) ^ 2 * N ^ 2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hTerm a) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, hdim, nsmul_eq_mul, Nat.cast_pow]
      ring

private theorem hasDerivAt_curvatureEnergy
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    HasDerivAt (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2)
      (2 * tensorPairing (F.metric t) D.riemannEvaluation
          (D.tensorLaplacian D.riemannEvaluation) x +
        4 * (∑ a : Fin 4 -> Fin d,
          D.riemannEvaluation x (fun i => b (a i)) *
            curvatureBfour D x (fun i => b (a i)))) t := by
  classical
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let P : (Fin 4 -> TangentSpace (𝓡 n) x) -> ℝ := fun v =>
    D.tensorLaplacian D.riemannEvaluation x v +
      D.curvatureReaction x (v 0) (v 1) (v 2) (v 3)
  have htime (v : Fin 4 -> TangentSpace (𝓡 n) x) :
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
  have hfun : (fun s => ((F.connection s).curvatureDerivativeNorm 0 x) ^ 2) =
      (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) := by
    funext s
    rw [(F.connection s).curvatureDerivativeNorm_zero x]
  rw [hfun] at hnorm
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
        (fun i => b (Function.update a j l i)) := by
    exact (Function.comp_update b a j l).symm
  have hreact0 (a : Fin 4 → Fin d) :
      D.curvatureReaction x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3)) =
        2 * curvatureBfour D x (fun i => b (a i)) -
          ∑ j : Fin 4, ∑ l : Fin d,
            D.ricci x (b (a j)) (b l) *
              D.riemannEvaluation x (Function.update (fun i => b (a i)) j (b l)) := by
    simpa only [b] using
      (curvatureReaction_eq_Bfour_sub_slots D x (fun i => b (a i)))
  have hreact (a : Fin 4 → Fin d) :
      D.curvatureReaction x (b (a 0)) (b (a 1)) (b (a 2)) (b (a 3)) =
        2 * curvatureBfour D x (fun i => b (a i)) -
          ∑ j : Fin 4, ∑ l : Fin d,
            D.ricci x (b (a j)) (b l) *
              D.riemannEvaluation x (fun i => b (Function.update a j l i)) := by
    rw [hreact0]
    simp only [hupdate]
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
    intro j hj
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
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
    intro a ha
    ring
  simp only [tensorPairing]
  rw [hB]
  ring

private theorem curvatureEnergy_heat_inequality_interior
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    derivWithin
      (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J t <=
      (F.connection t).laplacian
        (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 +
      16 * (n : ℝ) ^ 6 * ((F.connection t).curvatureTensorNorm x) ^ 3 := by
  classical
  let hconv : Convex ℝ J := F.interval.convex
  let hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  let hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconv hne
  have hderiv := (hasDerivAt_curvatureEnergy F ht x).hasDerivWithinAt.derivWithin
    (hJ t (interior_subset ht))
  have hbochner := laplacian_tensorNorm_sq
    (D := F.connection t)
    (isSmoothCovariantTensor_riemannEvaluation (F.connection t)) x
  change (F.connection t).laplacian
      (fun y => ((F.connection t).curvatureDerivativeNorm 0 y) ^ 2) x = _ at hbochner
  simp only [LeviCivitaData.curvatureDerivativeNorm_zero] at hbochner
  change (F.connection t).laplacian
      (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x =
      2 * tensorPairing (F.metric t) (F.connection t).riemannEvaluation
          ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation) x +
        2 * ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 at hbochner
  have hreaction := curvature_energy_reaction_le (F.connection t) x
  dsimp only at hderiv hreaction
  linarith

private theorem contDiffOn_curvatureEnergy_timeSlice
    (F : RicciFlow n M J) (x : M) :
    ContDiffOn ℝ ∞
      (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun s : ℝ => (s, x)) := contMDiff_id.prodMk contMDiff_const
  have h := (contMDiffOn_flow_curvatureDerivativeEnergy F 0).comp hslice.contMDiffOn
    (show Set.MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ Set.univ) from
      fun _ hs => ⟨hs, Set.mem_univ x⟩)
  simpa only [Function.comp_def, LeviCivitaData.curvatureDerivativeNorm_zero] using h.contDiffOn

private theorem continuousOn_curvatureEnergy_derivWithin
    (F : RicciFlow n M J) (x : M) :
    ContinuousOn
      (fun t => derivWithin
        (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J t) J := by
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  exact (contDiffOn_curvatureEnergy_timeSlice F x).continuousOn_derivWithin
    (uniqueDiffOn_convex hconv hne) (by simp)

set_option maxHeartbeats 800000 in
private theorem continuousOn_curvatureEnergy_heatRHS
    (F : RicciFlow n M J) (x : M) :
    ContinuousOn
      (fun t => (F.connection t).laplacian
          (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x -
        2 * ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 +
        16 * (n : ℝ) ^ 6 * ((F.connection t).curvatureTensorNorm x) ^ 3) J := by
  have hE0 := contMDiffOn_flow_curvatureDerivativeEnergy F 0
  have hE1 := contMDiffOn_flow_curvatureDerivativeEnergy F 1
  have hE0' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ((F.connection p.1).curvatureTensorNorm p.2) ^ 2)
      (J ×ˢ Set.univ) := by
    simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using hE0
  have hLap := continuousOn_flow_timeDependentLaplacian F (q :=
      fun p : ℝ × M => ((F.connection p.1).curvatureTensorNorm p.2) ^ 2) hE0'
  have hsliceMD : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ => (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hslice : ContinuousOn (fun t : ℝ => (t, x)) J :=
    hsliceMD.continuous.continuousOn
  have hLapx := hLap.comp hslice (fun _ ht => ⟨ht, Set.mem_univ x⟩)
  have hE1x : ContinuousOn
      (fun t : ℝ => ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2) J :=
    (hE1.comp hsliceMD.contMDiffOn (fun _ ht => ⟨ht, Set.mem_univ x⟩)).continuousOn
  have hE0x : ContinuousOn
      (fun t : ℝ => ((F.connection t).curvatureTensorNorm x) ^ 2) J :=
    (hE0'.comp hsliceMD.contMDiffOn (fun _ ht => ⟨ht, Set.mem_univ x⟩)).continuousOn
  have hNx : ContinuousOn
      (fun t : ℝ => (F.connection t).curvatureTensorNorm x) J := by
    have hsqrt := hE0x.sqrt
    apply hsqrt.congr
    intro t ht
    change (F.connection t).curvatureTensorNorm x =
      Real.sqrt (((F.connection t).curvatureTensorNorm x) ^ 2)
    rw [Real.sqrt_sq_eq_abs]
    exact (abs_of_nonneg (show 0 ≤ (F.connection t).curvatureTensorNorm x
      from Real.sqrt_nonneg _)).symm
  have hNcube : ContinuousOn
      (fun t : ℝ => ((F.connection t).curvatureTensorNorm x) ^ 3) J := by
    have hprod := hNx.mul hE0x
    apply hprod.congr
    intro t ht
    change (F.connection t).curvatureTensorNorm x ^ 3 =
      (F.connection t).curvatureTensorNorm x *
        (F.connection t).curvatureTensorNorm x ^ 2
    ring
  have htwo : ContinuousOn (fun _ : ℝ => (2 : ℝ)) J := continuousOn_const
  have hcoef : ContinuousOn (fun _ : ℝ => 16 * (n : ℝ) ^ 6) J := continuousOn_const
  exact (hLapx.sub (htwo.mul hE1x)).add (hcoef.mul hNcube)

theorem curvatureEnergy_heat_inequality
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J) (x : M) :
    derivWithin
      (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J t <=
      (F.connection t).laplacian
        (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 +
      16 * (n : ℝ) ^ 6 * ((F.connection t).curvatureTensorNorm x) ^ 3 := by
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hderivcont : ContinuousWithinAt
      (fun t => derivWithin
        (fun s => ((F.connection s).curvatureTensorNorm x) ^ 2) J t)
      (interior J) t :=
    ((continuousOn_curvatureEnergy_derivWithin F x) t ht).mono
      (interior_subset : interior J ⊆ J)
  have hRHScont : ContinuousWithinAt
      (fun t => (F.connection t).laplacian
          (fun y => ((F.connection t).curvatureTensorNorm y) ^ 2) x -
        2 * ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 +
        16 * (n : ℝ) ^ 6 * ((F.connection t).curvatureTensorNorm x) ^ 3)
      (interior J) t :=
    ((continuousOn_curvatureEnergy_heatRHS F x) t ht).mono
      (interior_subset : interior J ⊆ J)
  exact ContinuousWithinAt.closure_le (hdense ht) hderivcont hRHScont
    (fun s hs => curvatureEnergy_heat_inequality_interior F hs x)

end PoincareConjecture.M04
