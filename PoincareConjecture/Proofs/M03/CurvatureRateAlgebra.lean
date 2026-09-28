import PoincareConjecture.Proofs.M03.ScalarEnergyComparison
import PoincareConjecture.Proofs.M03.CurvatureTrilinear
import PoincareConjecture.Proofs.M03.MetricInverse
import PoincareConjecture.Proofs.M03.MetricDifferenceEvolution
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.FamilyBundleCoordinates










set_option autoImplicit false
set_option maxHeartbeats 2400000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem sub_mul_mul_telescope
    (a a' b b' c c' : ℝ) :
    a * b * c - a' * b' * c' =
      (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by
  ring

theorem abs_sub_mul_mul_le
    (a a' b b' c c' : ℝ) :
    |a * b * c - a' * b' * c'| ≤
      |a - a'| * |b| * |c| +
        |a'| * |b - b'| * |c| +
        |a'| * |b'| * |c - c'| := by
  rw [sub_mul_mul_telescope]
  calc
    |(a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c')| ≤
        |(a - a') * b * c + a' * (b - b') * c| +
          |a' * b' * (c - c')| := abs_add_le _ _
    _ ≤ (|(a - a') * b * c| + |a' * (b - b') * c|) +
          |a' * b' * (c - c')| := by
      exact add_le_add_left
        (abs_add_le ((a - a') * b * c) (a' * (b - b') * c)) _
    _ = |a - a'| * |b| * |c| +
          |a'| * |b - b'| * |c| +
          |a'| * |b'| * |c - c'| := by
      simp only [abs_mul]


theorem curvature_reaction_eq_inverse_frame_sum
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (u v w : TangentSpace (𝓡 n) x) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let b := g.orthonormalBasis x
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let R := D.curvature x
    let P := fun z : TangentSpace (𝓡 n) x => ∑ r, D.ricci x z (b r) • b r
    let L := fun r s : TangentSpace (𝓡 n) x =>
      R (R u v r) s w - (2 : ℝ) • R v r (R s u w) +
        (2 : ℝ) • R r u (R v s w) + D.ricci x (R u v w) r • s -
        D.ricci x u r • R s v w - D.ricci x v r • R u s w -
        D.ricci x w r • R u v s
    (∑ r, (R (R u v (b r)) (b r) w -
        (2 : ℝ) • R v (b r) (R (b r) u w) +
        (2 : ℝ) • R (b r) u (R v (b r) w))) +
      P (R u v w) - R (P u) v w - R u (P v) w - R u v (P w) =
        ∑ i : Fin n, ∑ j : Fin n, a i j • L (E i x) (E j x) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let b := g.orthonormalBasis x
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  let Rc (z : TangentSpace (𝓡 n) x) : TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    ∑ r, g.inner x (T z (b r) (b r))
  have hRc (z q : TangentSpace (𝓡 n) x) : Rc z q = D.ricci x z q := by
    simp only [Rc, sum_apply, hT,
      LeviCivitaData.ricci, LeviCivitaData.curvatureTensor, b]
  let L0 := fun r s : TangentSpace (𝓡 n) x =>
    T (T u v r) s w - (2 : ℝ) • T v r (T s u w) +
      (2 : ℝ) • T r u (T v s w) + Rc (T u v w) r • s -
      Rc u r • T s v w - Rc v r • T u s w - Rc w r • T u v s
  let L : TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    LinearMap.mk₂ ℝ L0
      (by
        intro r r' s
        simp only [L0, map_add, LinearMap.add_apply, add_smul]
        module)
      (by
        intro c r s
        simp only [L0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
          smul_smul]
        module)
      (by
        intro r s s'
        simp only [L0, map_add, LinearMap.add_apply, smul_add]
        module)
      (by
        intro c r s
        simp only [L0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
          smul_smul]
        module)
  have hL (r s : TangentSpace (𝓡 n) x) : L r s = L0 r s := rfl
  have hrec (z : TangentSpace (𝓡 n) x) :
      z = ∑ i : Fin n, theta i x z • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V z) hx
  have hbilin (r s : TangentSpace (𝓡 n) x) :
      L r s = ∑ i : Fin n, ∑ j : Fin n,
        (theta i x r * theta j x s) • L (E i x) (E j x) := by
    nth_rw 1 [hrec r]
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, LinearMap.smul_apply]
    nth_rw 1 [hrec s]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_smul]
  have htrace (i j : Fin n) : a i j =
      ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hcontract : (∑ r, L (b r) (b r)) =
      ∑ i : Fin n, ∑ j : Fin n, a i j • L (E i x) (E j x) := by
    calc
      _ = ∑ r, ∑ i : Fin n, ∑ j : Fin n,
          (theta i x (b r) * theta j x (b r)) • L (E i x) (E j x) :=
        Finset.sum_congr rfl (fun r _ => hbilin (b r) (b r))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, ← htrace]
  let P := fun z : TangentSpace (𝓡 n) x => ∑ r, D.ricci x z (b r) • b r
  have hreaction :
      (∑ r, (T (T u v (b r)) (b r) w -
          (2 : ℝ) • T v (b r) (T (b r) u w) +
          (2 : ℝ) • T (b r) u (T v (b r) w))) +
        P (T u v w) - T (P u) v w - T u (P v) w - T u v (P w) =
          ∑ r, L (b r) (b r) := by
    simp only [P, hL, L0, hRc, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  dsimp only
  simpa only [hL, L0, hRc, hT, P, a, G, b, E, cb, e, V] using
    hreaction.trans hcontract

set_option maxHeartbeats 4000000 in

theorem norm_model_curvature_reaction_difference_le
    {n : ℕ}
    (G G' : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hG : G.IsInvertible) (hG' : G'.IsInvertible)
    (R R' : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u v w : EuclideanSpace ℝ (Fin n)) :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
    let ric := fun
      (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) p q =>
      ∑ k, (T (e k) p q) k
    let Q := fun
      (A : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =>
      ∑ i : Fin n, ∑ j : Fin n, (A (EuclideanSpace.proj j)) i •
        (T (T u v (e i)) (e j) w - (2 : ℝ) • T v (e i) (T (e j) u w) +
          (2 : ℝ) • T (e i) u (T v (e j) w) +
          ric T (T u v w) (e i) • e j - ric T u (e i) • T (e j) v w -
          ric T v (e i) • T u (e j) w - ric T w (e i) • T u v (e j))
    ‖Q G.inverse R - Q G'.inverse R'‖ ≤
      (n : ℝ) ^ 2 * (5 + 4 * n) *
        (‖G.inverse‖ * ‖G - G'‖ * ‖G'.inverse‖ * ‖R‖ ^ 2 +
          ‖G'.inverse‖ * (‖R‖ + ‖R'‖) * ‖R - R'‖) * ‖u‖ * ‖v‖ * ‖w‖ := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  dsimp only
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let rc (T : FS) (p q : V) : ℝ := ∑ k, (EuclideanSpace.proj k) (T (e k) p q)
  let L (T U : FS) (i j : Fin n) : V :=
    T (U u v (e i)) (e j) w - (2 : ℝ) • T v (e i) (U (e j) u w) +
      (2 : ℝ) • T (e i) u (U v (e j) w) + rc U (T u v w) (e i) • e j -
      rc U u (e i) • T (e j) v w - rc U v (e i) • T u (e j) w -
      rc U w (e i) • T u v (e j)
  let B (A : (V →L[ℝ] ℝ) →L[ℝ] V) (T U : FS) : V :=
    ∑ i : Fin n, ∑ j : Fin n, (A (EuclideanSpace.proj j)) i • L T U i j
  change ‖B G.inverse R R - B G'.inverse R' R'‖ ≤ _
  have he (i : Fin n) : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
  have hproj (j : Fin n) : ‖(EuclideanSpace.proj j : V →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖z j‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using (PiLp.norm_apply_le z j)
  have hentry (A : (V →L[ℝ] ℝ) →L[ℝ] V) (i j : Fin n) :
      ‖(A (EuclideanSpace.proj j)) i‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖A (EuclideanSpace.proj j)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖A‖ * ‖(EuclideanSpace.proj j : V →L[ℝ] ℝ)‖ := A.le_opNorm _
      _ ≤ ‖A‖ := by nlinarith [hproj j, norm_nonneg A]
  have hT (T : FS) (p q r : V) :
      ‖T p q r‖ ≤ ‖T‖ * ‖p‖ * ‖q‖ * ‖r‖ := by
    calc
      _ ≤ ‖T p‖ * ‖q‖ * ‖r‖ := (T p).le_opNorm₂ q r
      _ ≤ (‖T‖ * ‖p‖) * ‖q‖ * ‖r‖ := by
        gcongr
        exact T.le_opNorm p
  have hrc (T : FS) (p q : V) :
      ‖rc T p q‖ ≤ (n : ℝ) * ‖T‖ * ‖p‖ * ‖q‖ := by
    calc
      _ ≤ ∑ k : Fin n, ‖(EuclideanSpace.proj k) (T (e k) p q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, ‖T‖ * ‖p‖ * ‖q‖ := by
        apply Finset.sum_le_sum
        intro k _
        change ‖(T (e k) p q) k‖ ≤ _
        exact (PiLp.norm_apply_le (T (e k) p q) k).trans
          (by simpa only [he, mul_one] using hT T (e k) p q)
      _ = _ := by simp; ring
  have hL (T U : FS) (i j : Fin n) :
      ‖L T U i j‖ ≤ (5 + 4 * (n : ℝ)) *
        (‖T‖ * ‖U‖ * ‖u‖ * ‖v‖ * ‖w‖) := by
    let Z := ‖T‖ * ‖U‖ * ‖u‖ * ‖v‖ * ‖w‖
    have h1 : ‖T (U u v (e i)) (e j) w‖ ≤ Z := by
      calc
        _ ≤ ‖T‖ * ‖U u v (e i)‖ * ‖e j‖ * ‖w‖ := hT _ _ _ _
        _ ≤ ‖T‖ * (‖U‖ * ‖u‖ * ‖v‖ * ‖e i‖) * ‖e j‖ * ‖w‖ := by
          gcongr
          exact hT _ _ _ _
        _ = Z := by simp only [he]; dsimp [Z]; ring
    have h2a : ‖T v (e i) (U (e j) u w)‖ ≤ Z := by
      calc
        _ ≤ ‖T‖ * ‖v‖ * ‖e i‖ * ‖U (e j) u w‖ := hT _ _ _ _
        _ ≤ ‖T‖ * ‖v‖ * ‖e i‖ * (‖U‖ * ‖e j‖ * ‖u‖ * ‖w‖) := by
          gcongr
          exact hT _ _ _ _
        _ = Z := by simp only [he]; dsimp [Z]; ring
    have h2 : ‖(2 : ℝ) • T v (e i) (U (e j) u w)‖ ≤ 2 * Z := by
      simpa only [norm_smul, Real.norm_ofNat] using
        mul_le_mul_of_nonneg_left h2a (by norm_num : (0 : ℝ) ≤ 2)
    have h3a : ‖T (e i) u (U v (e j) w)‖ ≤ Z := by
      calc
        _ ≤ ‖T‖ * ‖e i‖ * ‖u‖ * ‖U v (e j) w‖ := hT _ _ _ _
        _ ≤ ‖T‖ * ‖e i‖ * ‖u‖ * (‖U‖ * ‖v‖ * ‖e j‖ * ‖w‖) := by
          gcongr
          exact hT _ _ _ _
        _ = Z := by simp only [he]; dsimp [Z]; ring
    have h3 : ‖(2 : ℝ) • T (e i) u (U v (e j) w)‖ ≤ 2 * Z := by
      simpa only [norm_smul, Real.norm_ofNat] using
        mul_le_mul_of_nonneg_left h3a (by norm_num : (0 : ℝ) ≤ 2)
    have h4 : ‖rc U (T u v w) (e i) • e j‖ ≤ (n : ℝ) * Z := by
      rw [norm_smul]
      calc
        _ ≤ ((n : ℝ) * ‖U‖ * ‖T u v w‖ * ‖e i‖) * ‖e j‖ := by
          gcongr
          exact hrc _ _ _
        _ ≤ ((n : ℝ) * ‖U‖ * (‖T‖ * ‖u‖ * ‖v‖ * ‖w‖) * ‖e i‖) * ‖e j‖ := by
          gcongr
          exact hT _ _ _ _
        _ = (n : ℝ) * Z := by simp only [he]; dsimp [Z]; ring
    have h5 : ‖rc U u (e i) • T (e j) v w‖ ≤ (n : ℝ) * Z := by
      rw [norm_smul]
      calc
        _ ≤ ((n : ℝ) * ‖U‖ * ‖u‖ * ‖e i‖) *
            (‖T‖ * ‖e j‖ * ‖v‖ * ‖w‖) := by
          exact mul_le_mul (hrc _ _ _) (hT _ _ _ _) (norm_nonneg _) (by positivity)
        _ = (n : ℝ) * Z := by simp only [he]; dsimp [Z]; ring
    have h6 : ‖rc U v (e i) • T u (e j) w‖ ≤ (n : ℝ) * Z := by
      rw [norm_smul]
      calc
        _ ≤ ((n : ℝ) * ‖U‖ * ‖v‖ * ‖e i‖) *
            (‖T‖ * ‖u‖ * ‖e j‖ * ‖w‖) := by
          exact mul_le_mul (hrc _ _ _) (hT _ _ _ _) (norm_nonneg _) (by positivity)
        _ = (n : ℝ) * Z := by simp only [he]; dsimp [Z]; ring
    have h7 : ‖rc U w (e i) • T u v (e j)‖ ≤ (n : ℝ) * Z := by
      rw [norm_smul]
      calc
        _ ≤ ((n : ℝ) * ‖U‖ * ‖w‖ * ‖e i‖) *
            (‖T‖ * ‖u‖ * ‖v‖ * ‖e j‖) := by
          exact mul_le_mul (hrc _ _ _) (hT _ _ _ _) (norm_nonneg _) (by positivity)
        _ = (n : ℝ) * Z := by simp only [he]; dsimp [Z]; ring
    have hsub {x y : V} {a b : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
        ‖x - y‖ ≤ a + b := (norm_sub_le x y).trans (add_le_add hx hy)
    exact (hsub (hsub (hsub (norm_add_le_of_le
      (norm_add_le_of_le (hsub h1 h2) h3) h4) h5) h6) h7).trans_eq (by dsimp [Z]; ring)
  have hB (A : (V →L[ℝ] ℝ) →L[ℝ] V) (T U : FS) :
      ‖B A T U‖ ≤ (n : ℝ) ^ 2 * (5 + 4 * n) * ‖A‖ *
        ‖T‖ * ‖U‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖(A (EuclideanSpace.proj j)) i • L T U i j‖ :=
        (norm_sum_le _ _).trans
          (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n,
          ‖A‖ * ((5 + 4 * (n : ℝ)) * (‖T‖ * ‖U‖ * ‖u‖ * ‖v‖ * ‖w‖)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul (hentry A i j) (hL T U i j) (norm_nonneg _) (norm_nonneg A)
      _ = _ := by simp; ring
  have hBA (A A' : (V →L[ℝ] ℝ) →L[ℝ] V) (T U : FS) :
      B (A - A') T U = B A T U - B A' T U := by
    change (∑ i : Fin n, ∑ j : Fin n,
      ((A (EuclideanSpace.proj j)) i - (A' (EuclideanSpace.proj j)) i) •
        L T U i j) = _
    simp only [B, sub_smul, Finset.sum_sub_distrib]
  have hLT (T T' U : FS) (i j : Fin n) :
      L (T - T') U i j = L T U i j - L T' U i j := by
    simp only [L, rc, ContinuousLinearMap.sub_apply, map_sub,
      Finset.sum_sub_distrib, sub_smul, smul_sub]
    module
  have hLU (T U U' : FS) (i j : Fin n) :
      L T (U - U') i j = L T U i j - L T U' i j := by
    simp only [L, rc, ContinuousLinearMap.sub_apply, map_sub,
      Finset.sum_sub_distrib, sub_smul, smul_sub]
    module
  have hBT (A : (V →L[ℝ] ℝ) →L[ℝ] V) (T T' U : FS) :
      B A (T - T') U = B A T U - B A T' U := by
    simp only [B, hLT, smul_sub, Finset.sum_sub_distrib]
  have hBU (A : (V →L[ℝ] ℝ) →L[ℝ] V) (T U U' : FS) :
      B A T (U - U') = B A T U - B A T U' := by
    simp only [B, hLU, smul_sub, Finset.sum_sub_distrib]
  have htel : B G.inverse R R - B G'.inverse R' R' =
      B (G.inverse - G'.inverse) R R + B G'.inverse (R - R') R +
        B G'.inverse R' (R - R') := by
    rw [hBA, hBT, hBU]
    abel
  have hinv : G.inverse - G'.inverse =
      G.inverse.comp ((G' - G).comp G'.inverse) := by
    ext l
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      map_sub, hG'.self_apply_inverse, hG.inverse_apply_self]
  have hInvNorm : ‖G.inverse - G'.inverse‖ ≤
      ‖G.inverse‖ * ‖G - G'‖ * ‖G'.inverse‖ := by
    rw [hinv]
    calc
      _ ≤ ‖G.inverse‖ * ‖(G' - G).comp G'.inverse‖ :=
        G.inverse.opNorm_comp_le _
      _ ≤ ‖G.inverse‖ * (‖G' - G‖ * ‖G'.inverse‖) := by
        gcongr
        exact (G' - G).opNorm_comp_le _
      _ = _ := by rw [norm_sub_rev]; ring
  rw [htel]
  calc
    _ ≤ ((n : ℝ) ^ 2 * (5 + 4 * n) * ‖G.inverse - G'.inverse‖ *
        ‖R‖ * ‖R‖ * ‖u‖ * ‖v‖ * ‖w‖ +
      (n : ℝ) ^ 2 * (5 + 4 * n) * ‖G'.inverse‖ *
        ‖R - R'‖ * ‖R‖ * ‖u‖ * ‖v‖ * ‖w‖) +
      (n : ℝ) ^ 2 * (5 + 4 * n) * ‖G'.inverse‖ *
        ‖R'‖ * ‖R - R'‖ * ‖u‖ * ‖v‖ * ‖w‖ :=
      norm_add_le_of_le (norm_add_le_of_le (hB _ _ _) (hB _ _ _)) (hB _ _ _)
    _ ≤ ((n : ℝ) ^ 2 * (5 + 4 * n) *
        (‖G.inverse‖ * ‖G - G'‖ * ‖G'.inverse‖) *
        ‖R‖ * ‖R‖ * ‖u‖ * ‖v‖ * ‖w‖ +
      (n : ℝ) ^ 2 * (5 + 4 * n) * ‖G'.inverse‖ *
        ‖R - R'‖ * ‖R‖ * ‖u‖ * ‖v‖ * ‖w‖) +
      (n : ℝ) ^ 2 * (5 + 4 * n) * ‖G'.inverse‖ *
        ‖R'‖ * ‖R - R'‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
      gcongr
    _ = _ := by ring

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_curvature_reaction_coordinate_energy_bound
    {n dH dS : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let FH := V →L[ℝ] V →L[ℝ] ℝ
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x
    ∀ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (s : Finset M) (Q : M → Set V),
      (∀ a ∈ s, IsCompact (Q a) ∧ Q a ⊆ (chartAt V a).target) →
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J')
        (R R' : (t : ℝ) → (x : M) → BS x),
        (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
        (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
        ∀ (K : Set ℝ), IsCompact K → K ⊆ J ∩ J' →
          let c := chartAt V
          let eH := trivializationAt FH BH
          let eS := trivializationAt FS BS
          let G := fun a (p : ℝ × V) =>
            ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
              ((F.metric p.1).inner ((c a).symm p.2)))).2
          let G' := fun a (p : ℝ × V) =>
            ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
              ((F'.metric p.1).inner ((c a).symm p.2)))).2
          let Rbar := fun a (p : ℝ × V) =>
            ((eS a) (TotalSpace.mk' FS ((c a).symm p.2) (R p.1 ((c a).symm p.2)))).2
          let Rbar' := fun a (p : ℝ × V) =>
            ((eS a) (TotalSpace.mk' FS ((c a).symm p.2) (R' p.1 ((c a).symm p.2)))).2
          let H := fun t x => (F.metric t).inner x - (F'.metric t).inner x
          let S := fun t x => R t x - R' t x
          let fH := fun a i (p : ℝ × V) => qH
            ((eH a) (TotalSpace.mk' FH ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2 i
          let fS := fun a i (p : ℝ × V) => qS
            ((eS a) (TotalSpace.mk' FS ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2 i
          let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
          let ric := fun (T : FS) p q => ∑ k, (T (e k) p q) k
          let reaction := fun (A : FH) (T : FS) u v w =>
            ∑ i : Fin n, ∑ j : Fin n, (A.inverse (EuclideanSpace.proj j)) i •
              (T (T u v (e i)) (e j) w - (2 : ℝ) • T v (e i) (T (e j) u w) +
                (2 : ℝ) • T (e i) u (T v (e j) w) + ric T (T u v w) (e i) • e j -
                ric T u (e i) • T (e j) v w - ric T v (e i) • T u (e j) w -
                ric T w (e i) • T u v (e j))
          let B := fun l j k m : Fin n => (EuclideanSpace.proj j).smulRight
            ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight (e l)))
          let qQ := fun a α p => ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α *
            ((reaction (G a p) (Rbar a p) (e j) (e k) (e m) -
              reaction (G' a p) (Rbar' a p) (e j) (e k) (e m)) l)
          ∃ CQ : ℝ, 0 ≤ CQ ∧ ∀ a ∈ s, ∀ t ∈ K, ∀ z ∈ Q a,
            (∑ α : Fin dS, 2 * fS a α (t, z) * qQ a α (t, z)) ≤
              CQ * ((∑ i : Fin dH, (fH a i (t, z)) ^ 2) +
                (∑ α : Fin dS, (fS a α (t, z)) ^ 2)) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let FH := V →L[ℝ] V →L[ℝ] ℝ
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let : NormedAddCommGroup FH := inferInstance
  let : NormedSpace ℝ FH := inferInstance
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : NormedAddCommGroup ((V →L[ℝ] ℝ) →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ ((V →L[ℝ] ℝ) →L[ℝ] V) := inferInstance
  let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] ℝ
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let : ∀ x, AddCommGroup (BH x) := inferInstance
  let : ∀ x, Module ℝ (BH x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  dsimp only
  intro qH qS s Q hQ J J' F F' R R' hR hR' K hK hKJ
  let c := chartAt V (M := M)
  let eH := trivializationAt FH BH
  let eS := trivializationAt FS BS
  let G := fun a (p : ℝ × V) => ((eH a) (TotalSpace.mk' FH
    ((c a).symm p.2) ((F.metric p.1).inner ((c a).symm p.2)))).2
  let G' := fun a (p : ℝ × V) => ((eH a) (TotalSpace.mk' FH
    ((c a).symm p.2) ((F'.metric p.1).inner ((c a).symm p.2)))).2
  have hGcoord (a : M) (p : ℝ × V) : G a p =
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        a ((c a).symm p.2) a ((c a).symm p.2)
        ((F.metric p.1).inner ((c a).symm p.2)) := rfl
  have hG'coord (a : M) (p : ℝ × V) : G' a p =
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        a ((c a).symm p.2) a ((c a).symm p.2)
        ((F'.metric p.1).inner ((c a).symm p.2)) := rfl
  let Rbar := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS
    ((c a).symm p.2) (R p.1 ((c a).symm p.2)))).2
  let Rbar' := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS
    ((c a).symm p.2) (R' p.1 ((c a).symm p.2)))).2
  let H := fun t x => (F.metric t).inner x - (F'.metric t).inner x
  let S := fun t x => R t x - R' t x
  let hv := fun a (p : ℝ × V) => qH ((eH a) (TotalSpace.mk' FH
    ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2
  let sv := fun a (p : ℝ × V) => qS ((eS a) (TotalSpace.mk' FS
    ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let ric := fun (T : FS) p q => ∑ k, (T (e k) p q) k
  let reaction := fun (A : FH) (T : FS) u v w =>
    ∑ i : Fin n, ∑ j : Fin n, (A.inverse (EuclideanSpace.proj j)) i •
      (T (T u v (e i)) (e j) w - (2 : ℝ) • T v (e i) (T (e j) u w) +
        (2 : ℝ) • T (e i) u (T v (e j) w) + ric T (T u v w) (e i) • e j -
        ric T u (e i) • T (e j) v w - ric T v (e i) • T u (e j) w -
        ric T w (e i) • T u v (e j))
  let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m => (EuclideanSpace.proj j).smulRight
    ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight (e l)))
  let qQ := fun a α p => ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α *
    ((reaction (G a p) (Rbar a p) (e j) (e k) (e m) -
      reaction (G' a p) (Rbar' a p) (e j) (e k) (e m)) l)
  let coeff := fun a p => (n : ℝ) ^ 2 * (5 + 4 * n) *
    (‖(G a p).inverse‖ * ‖(G' a p).inverse‖ * ‖Rbar a p‖ ^ 2 *
      ‖qH.symm.toContinuousLinearMap‖ +
      ‖(G' a p).inverse‖ * (‖Rbar a p‖ + ‖Rbar' a p‖) *
        ‖qS.symm.toContinuousLinearMap‖)
  have hcoeff0 (a : M) (p : ℝ × V) : 0 ≤ coeff a p := by dsimp [coeff]; positivity
  have hbaseH (a : M) : (c a).source ⊆ (eH a).baseSet := by
    simp only [c, eH, V, FH, BH, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, mem_univ x⟩
  have hbaseS (a : M) : (c a).source ⊆ (eS a).baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx, hx⟩
  obtain ⟨R0, hR0, hRsm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  obtain ⟨R1, hR1, hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  have hReq : R0 = R := by
    funext t x
    ext u v w
    exact (hR0 t x u v w).trans (hR t x u v w).symm
  have hR'eq : R1 = R' := by
    funext t x
    ext u v w
    exact (hR1 t x u v w).trans (hR' t x u v w).symm
  rw [hReq] at hRsm
  rw [hR'eq] at hR'sm
  have hlocal : ∀ a : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ K ×ˢ Q a, a ∈ s → coeff a p ≤ C := by
    intro a
    by_cases ha : a ∈ s
    · have hbase (z : V) (hz : z ∈ Q a) : (c a).symm z ∈
          (trivializationAt V (TangentSpace (𝓡 n)) a).baseSet := by
        simpa only [TangentBundle.trivializationAt_baseSet] using
          (c a).map_target ((hQ a ha).2 hz)
      have hi : ContinuousOn (fun p => (G a p).inverse) (K ×ˢ Q a) := by
        simp_rw [hGcoord]
        exact
          (contMDiffOn_family_metric_frame_inverse F.smooth a).2.2.continuousOn.comp
            (continuousOn_fst.prodMk (((c a).continuousOn_symm.mono (hQ a ha).2).comp
              continuousOn_snd (fun p hp => hp.2)))
            (fun p hp => ⟨(hKJ hp.1).1, hbase p.2 hp.2⟩)
      have hi' : ContinuousOn (fun p => (G' a p).inverse) (K ×ˢ Q a) := by
        simp_rw [hG'coord]
        exact
          (contMDiffOn_family_metric_frame_inverse F'.smooth a).2.2.continuousOn.comp
            (continuousOn_fst.prodMk (((c a).continuousOn_symm.mono (hQ a ha).2).comp
              continuousOn_snd (fun p hp => hp.2)))
            (fun p hp => ⟨(hKJ hp.1).2, hbase p.2 hp.2⟩)
      have hr : ContinuousOn (Rbar a) (K ×ˢ Q a) := by
        have hh := (contDiffOn_family_bundle_coordinates (E := BS)
          qS R hRsm a (hbaseS a)).continuousOn.mono
            (Set.prod_mono (fun t ht => (hKJ ht).1) (hQ a ha).2)
        simpa only [Function.comp_def, Rbar, ContinuousLinearEquiv.symm_apply_apply]
          using qS.symm.continuous.comp_continuousOn hh
      have hr' : ContinuousOn (Rbar' a) (K ×ˢ Q a) := by
        have hh := (contDiffOn_family_bundle_coordinates (E := BS)
          qS R' hR'sm a (hbaseS a)).continuousOn.mono
            (Set.prod_mono (fun t ht => (hKJ ht).2) (hQ a ha).2)
        simpa only [Function.comp_def, Rbar', ContinuousLinearEquiv.symm_apply_apply]
          using qS.symm.continuous.comp_continuousOn hh
      have hc : ContinuousOn (coeff a) (K ×ˢ Q a) :=
        continuousOn_const.mul
          ((((hi.norm.mul hi'.norm).mul (hr.norm.pow 2)).mul continuousOn_const).add
            ((hi'.norm.mul (hr.norm.add hr'.norm)).mul continuousOn_const))
      obtain ⟨b, hb⟩ := (hK.prod (hQ a ha).1).bddAbove_image hc
      refine ⟨max b 0, le_max_right _ _, ?_⟩
      intro p hp _
      exact (hb (Set.mem_image_of_mem (coeff a) hp)).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun _ _ hs => (ha hs).elim⟩
  choose C hC0 hC using hlocal
  let C0 := ∑ a ∈ s, C a
  have hC00 : 0 ≤ C0 := Finset.sum_nonneg (fun a _ => hC0 a)
  have hbound (a : M) (ha : a ∈ s) (p : ℝ × V) (hp : p ∈ K ×ˢ Q a) :
      coeff a p ≤ C0 := (hC a p hp ha).trans
        (Finset.single_le_sum (fun b _ => hC0 b) ha)
  let theta := fun α : Fin dS => ∑ l, ∑ j, ∑ k, ∑ m, |qS (B l j k m) α|
  let T := ∑ α, theta α
  have htheta0 (α : Fin dS) : 0 ≤ theta α := by dsimp [theta]; positivity
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun α _ => htheta0 α)
  refine ⟨3 * T * C0, by positivity, ?_⟩
  intro a ha t ht z hz
  let p : ℝ × V := (t, z)
  have hp : p ∈ K ×ˢ Q a := ⟨ht, hz⟩
  have hzt : z ∈ (c a).target := (hQ a ha).2 hz
  have hx : (c a).symm z ∈
      (trivializationAt V (TangentSpace (𝓡 n)) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using (c a).map_target hzt
  have hGi : (G a p).IsInvertible := by
    rw [hGcoord]
    exact
      (contMDiffOn_family_metric_frame_inverse F.smooth a).1 (t, (c a).symm z) hx
  have hG'i : (G' a p).IsInvertible := by
    rw [hG'coord]
    exact
      (contMDiffOn_family_metric_frame_inverse F'.smooth a).1 (t, (c a).symm z) hx
  have hh : qH (G a p - G' a p) = hv a p := by
    dsimp only [hv, H]
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eH a) _
      (hbaseH a ((c a).map_target hzt)), map_sub]
    simp only [map_sub]
    rfl
  have hs : qS (Rbar a p - Rbar' a p) = sv a p := by
    dsimp only [sv, S]
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eS a) _
      (hbaseS a ((c a).map_target hzt)), map_sub]
    simp only [map_sub]
    rfl
  have hhnorm : ‖G a p - G' a p‖ ≤
      ‖qH.symm.toContinuousLinearMap‖ * ‖hv a p‖ := by
    have h := qH.symm.toContinuousLinearMap.le_opNorm (hv a p)
    simpa only [← hh, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using h
  have hsnorm : ‖Rbar a p - Rbar' a p‖ ≤
      ‖qS.symm.toContinuousLinearMap‖ * ‖sv a p‖ := by
    have h := qS.symm.toContinuousLinearMap.le_opNorm (sv a p)
    simpa only [← hs, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using h
  have he (i : Fin n) : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
  have hraw (l j k m : Fin n) :
      |(reaction (G a p) (Rbar a p) (e j) (e k) (e m) -
        reaction (G' a p) (Rbar' a p) (e j) (e k) (e m)) l| ≤
        C0 * (‖hv a p‖ + ‖sv a p‖) := by
    have h := norm_model_curvature_reaction_difference_le
      (G a p) (G' a p) hGi hG'i (Rbar a p) (Rbar' a p) (e j) (e k) (e m)
    change ‖reaction (G a p) (Rbar a p) (e j) (e k) (e m) -
      reaction (G' a p) (Rbar' a p) (e j) (e k) (e m)‖ ≤ _ at h
    simp only [he, mul_one] at h
    have hcoord := PiLp.norm_apply_le
      (reaction (G a p) (Rbar a p) (e j) (e k) (e m) -
        reaction (G' a p) (Rbar' a p) (e j) (e k) (e m)) l
    rw [Real.norm_eq_abs] at hcoord
    refine (hcoord.trans h).trans ?_
    calc
      _ ≤ (n : ℝ) ^ 2 * (5 + 4 * n) *
          (‖(G a p).inverse‖ * (‖qH.symm.toContinuousLinearMap‖ * ‖hv a p‖) *
              ‖(G' a p).inverse‖ * ‖Rbar a p‖ ^ 2 +
            ‖(G' a p).inverse‖ * (‖Rbar a p‖ + ‖Rbar' a p‖) *
              (‖qS.symm.toContinuousLinearMap‖ * ‖sv a p‖)) := by gcongr
      _ ≤ coeff a p * (‖hv a p‖ + ‖sv a p‖) := by
        dsimp only [coeff]
        nlinarith [mul_nonneg
          (show 0 ≤ (n : ℝ)^2 * (5 + 4*n) * ‖(G a p).inverse‖ *
            ‖(G' a p).inverse‖ * ‖Rbar a p‖^2 * ‖qH.symm.toContinuousLinearMap‖
            by positivity) (norm_nonneg (sv a p)),
          mul_nonneg (show 0 ≤ (n : ℝ)^2 * (5 + 4*n) * ‖(G' a p).inverse‖ *
            (‖Rbar a p‖ + ‖Rbar' a p‖) * ‖qS.symm.toContinuousLinearMap‖
            by positivity) (norm_nonneg (hv a p))]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound a ha p hp) (by positivity)
  have hq (α : Fin dS) : |qQ a α p| ≤
      theta α * (C0 * (‖hv a p‖ + ‖sv a p‖)) := by
    dsimp only [qQ, theta]
    simp only [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro m _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hraw l j k m) (abs_nonneg _)
  have hpoint (α : Fin dS) : 2 * sv a p α * qQ a α p ≤
      2 * ‖sv a p‖ * (theta α * (C0 * (‖hv a p‖ + ‖sv a p‖))) := by
    have hscoord : |sv a p α| ≤ ‖sv a p‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (sv a p) α
    calc
      _ ≤ |2 * sv a p α * qQ a α p| := le_abs_self _
      _ = 2 * |sv a p α| * |qQ a α p| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ _ := by gcongr; exact hq α
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun α _ => hpoint α)
  have hright : (∑ α : Fin dS,
      2 * ‖sv a p‖ * (theta α * (C0 * (‖hv a p‖ + ‖sv a p‖)))) =
      T * C0 * (2 * ‖sv a p‖ * (‖hv a p‖ + ‖sv a p‖)) := by
    dsimp only [T]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [hright] at hsum
  have hyoung : 2 * ‖sv a p‖ * (‖hv a p‖ + ‖sv a p‖) ≤
      3 * (‖hv a p‖ ^ 2 + ‖sv a p‖ ^ 2) := by
    nlinarith [sq_nonneg (‖hv a p‖ - ‖sv a p‖), sq_nonneg ‖hv a p‖]
  have hfinal := hsum.trans
    (mul_le_mul_of_nonneg_left hyoung (mul_nonneg hT0 hC00))
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hfinal
  change (∑ α : Fin dS, 2 * sv a p α * qQ a α p) ≤
    3 * T * C0 * ((∑ i : Fin dH, (hv a p i) ^ 2) +
      (∑ α : Fin dS, (sv a p α) ^ 2))
  nlinarith only [hfinal]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_reaction_frame_coordinates_eq_model
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (R0 : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
    (hR : ∀ u v w, R0 u v w = D.curvature x u v w)
    (u v w : TangentSpace (𝓡 n) x) :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let A := e.linearEquivAt ℝ x hx
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BS := fun y : M => TangentSpace (𝓡 n) y →L[ℝ]
      TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y
    let T := ((trivializationAt FS BS x0) (TotalSpace.mk' FS x R0)).2
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let R := D.curvature x
    let L := fun r s : TangentSpace (𝓡 n) x =>
      R (R u v r) s w - (2 : ℝ) • R v r (R s u w) +
        (2 : ℝ) • R r u (R v s w) + D.ricci x (R u v w) r • s -
        D.ricci x u r • R s v w - D.ricci x v r • R u s w -
        D.ricci x w r • R u v s
    let e0 := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
    let ric := fun p q : V => ∑ k, (T (e0 k) p q) k
    A (∑ i : Fin n, ∑ j : Fin n, a i j • L (E i x) (E j x)) =
      ∑ i : Fin n, ∑ j : Fin n, a i j •
        (T (T (A u) (A v) (e0 i)) (e0 j) (A w) -
          (2 : ℝ) • T (A v) (e0 i) (T (e0 j) (A u) (A w)) +
          (2 : ℝ) • T (e0 i) (A u) (T (A v) (e0 j) (A w)) +
          ric (T (A u) (A v) (A w)) (e0 i) • e0 j -
          ric (A u) (e0 i) • T (e0 j) (A v) (A w) -
          ric (A v) (e0 i) • T (A u) (e0 j) (A w) -
          ric (A w) (e0 i) • T (A u) (A v) (e0 j)) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let A := e.linearEquivAt ℝ x hx
  let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b0
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BS := fun y : M => TangentSpace (𝓡 n) y →L[ℝ]
    TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y
  let eS := trivializationAt FS BS x0
  let T : FS := (eS (TotalSpace.mk' FS x R0)).2
  let e0 := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  have hmodel (p q r : V) : T p q r = A (R0 (A.symm p) (A.symm q) (A.symm r)) := by
    have hxhom : x ∈ (trivializationAt (V →L[ℝ] V)
        (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) x0).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, hx⟩
    dsimp only [T, eS]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
      hx hx hxhom]
    rw [Trivialization.linearMapAt_apply, if_pos hxhom, hom_trivializationAt_apply]
    change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
      (TangentSpace (𝓡 n)) x0 x x0 x (R0 (e.symm x p) (e.symm x q)) r = _
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_apply]
    rw [Trivialization.symmL_apply (R := ℝ) e hx r, e.linearMapAt_def_of_mem hx]
    rfl
  have hcurv (p q r : TangentSpace (𝓡 n) x) :
      A (D.curvature x p q r) = T (A p) (A q) (A r) := by
    rw [hmodel]
    simp only [LinearEquiv.symm_apply_apply, hR]
  have hframe (i : Fin n) : A (E i x) = e0 i := by
    change A (e.localFrame b0 i x) = e0 i
    rw [e.localFrame_apply_of_mem_baseSet b0 (i := i) hx]
    simp only [Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply, b0,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    exact A.apply_symm_apply (e0 i)
  have hRic (p q : TangentSpace (𝓡 n) x) :
      D.ricci x p q = ∑ k : Fin n, (T (e0 k) (A p) (A q)) k := by
    let b := (PiLp.basisFun 2 ℝ (Fin n)).map A.symm
    have hrepr (z : TangentSpace (𝓡 n) x) (k : Fin n) : b.repr z k = (A z) k := by
      simp [b, Module.Basis.map_repr, PiLp.basisFun_repr]
    have hb (k : Fin n) : A (b k) = e0 k := by
      simp only [b, Module.Basis.map_apply, PiLp.basisFun_apply,
        LinearEquiv.apply_symm_apply, e0]
    rw [ricci_eq_sum_basis_of_curvature_pairing D x p q b]
    simp only [hrepr, hcurv, hb]
  dsimp only
  change A (∑ i : Fin n, ∑ j : Fin n, _ • _) = _
  dsimp only [E, b0, e0, e, V] at hframe
  simp only [map_sum, map_smul, map_sub, map_add, hcurv, hRic, hframe]
  rfl

set_option maxHeartbeats 3600000 in

theorem curvatureOnFields_reaction_covariant_derivative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P A B C X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) :
    let N := fun (V W : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection W y (V y)
    let R := fun (V W Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields V W Z y
    let K := fun (V W Z L : (y : M) → TangentSpace (𝓡 n) y) y =>
      N V (R W Z L) y - R (N V W) Z L y -
        R W (N V Z) L y - R W Z (N V L) y
    let Z := fun (A B C X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
      R (R A B X) Y C y - (2 : ℝ) • R B X (R Y A C) y +
        (2 : ℝ) • R X A (R B Y C) y + R (R A B C) X Y y -
        R (R A X Y) B C y - R A (R B X Y) C y - R A B (R C X Y) y
    N P (Z A B C X Y) x - Z (N P A) B C X Y x -
      Z A (N P B) C X Y x - Z A B (N P C) X Y x -
      Z A B C (N P X) Y x - Z A B C X (N P Y) x =
        K P (R A B X) Y C x + R (K P A B X) Y C x -
        (2 : ℝ) • K P B X (R Y A C) x -
        (2 : ℝ) • R B X (K P Y A C) x +
        (2 : ℝ) • K P X A (R B Y C) x +
        (2 : ℝ) • R X A (K P B Y C) x +
        K P (R A B C) X Y x + R (K P A B C) X Y x -
        K P (R A X Y) B C x - R (K P A X Y) B C x -
        K P A (R B X Y) C x - R A (K P B X Y) C x -
        K P A B (R C X Y) x - R A B (K P C X Y) x := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (V W : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection W y (V y)
  let R := fun (V W Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields V W Z y
  let K := fun (V W Z L : (y : M) → TangentSpace (𝓡 n) y) y =>
    N V (R W Z L) y - R (N V W) Z L y -
      R W (N V Z) L y - R W Z (N V L) y
  let Z := fun (A B C X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    R (R A B X) Y C y - (2 : ℝ) • R B X (R Y A C) y +
      (2 : ℝ) • R X A (R B Y C) y + R (R A B C) X Y y -
      R (R A X Y) B C y - R A (R B X Y) C y - R A B (R C X Y) y
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% W) x :=
    (hW.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hN (V W : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) : S (N V W) :=
    D.contMDiffOn_connection_apply hU V W hV hW
  have hR (V W Z : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) (hZ : S Z) : S (R V W Z) := by
    have hb : S (VectorField.mlieBracket (𝓡 n) V W) := by
      intro y hy
      exact ((hV.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
        (hW.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN V _ hV (hN W Z hW hZ)).sub_section
      (hN W _ hW (hN V Z hV hZ))).sub_section (hN _ Z hb hZ)
  have hK (V W Z L : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) (hZ : S Z) (hL : S L) : S (K V W Z L) :=
    (((hN V _ hV (hR W Z L hW hZ hL)).sub_section
      (hR _ Z L (hN V W hV hW) hZ hL)).sub_section
      (hR W _ L hW (hN V Z hV hZ) hL)).sub_section
      (hR W Z _ hW hZ (hN V L hV hL))
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hadd (V W : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) : N P (V + W) x = N P V x + N P W x :=
    congrArg (fun f => f (P x)) (hc.add (hmd V hV) (hmd W hW))
  have hsub (V W : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) : N P (V - W) x = N P V x - N P W x := by
    have heq := congrArg (fun f => f (P x))
      (hc.add (hmd _ (hV.sub_section hW)) (hmd W hW))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  have hsmul (V : (y : M) → TangentSpace (𝓡 n) y) (hV : S V) :
      N P ((2 : ℝ) • V) x = (2 : ℝ) • N P V x :=
    congrArg (fun f => f (P x)) (hc.smul_const (2 : ℝ) (hmd V hV))
  have h0 := hR _ Y C (hR A B X hA hB hX) hY hC
  have h1 := hR B X _ hB hX (hR Y A C hY hA hC)
  have h2 := hR X A _ hX hA (hR B Y C hB hY hC)
  have h3 := hR _ X Y (hR A B C hA hB hC) hX hY
  have h4 := hR _ B C (hR A X Y hA hX hY) hB hC
  have h5 := hR A _ C hA (hR B X Y hB hX hY) hC
  have h6 := hR A B _ hA hB (hR C X Y hC hX hY)
  have hs1 : S ((2 : ℝ) • R B X (R Y A C)) := by
    simpa only [two_smul] using h1.add_section h1
  have hs2 : S ((2 : ℝ) • R X A (R B Y C)) := by
    simpa only [two_smul] using h2.add_section h2
  have houter : N P (Z A B C X Y) x =
      N P (R (R A B X) Y C) x - (2 : ℝ) • N P (R B X (R Y A C)) x +
        (2 : ℝ) • N P (R X A (R B Y C)) x + N P (R (R A B C) X Y) x -
        N P (R (R A X Y) B C) x - N P (R A (R B X Y) C) x -
        N P (R A B (R C X Y)) x := by
    change N P ((((((R (R A B X) Y C - (2 : ℝ) • R B X (R Y A C)) +
      (2 : ℝ) • R X A (R B Y C)) + R (R A B C) X Y) -
      R (R A X Y) B C) - R A (R B X Y) C) - R A B (R C X Y)) x = _
    rw [hsub _ _ (((((h0.sub_section hs1).add_section hs2).add_section h3).sub_section
        h4).sub_section h5) h6,
      hsub _ _ ((((h0.sub_section hs1).add_section hs2).add_section h3).sub_section h4) h5,
      hsub _ _ (((h0.sub_section hs1).add_section hs2).add_section h3) h4,
      hadd _ _ ((h0.sub_section hs1).add_section hs2) h3,
      hadd _ _ (h0.sub_section hs1) hs2, hsub _ _ h0 hs1,
      hsmul _ h1, hsmul _ h2]
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  have heval (V W L : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) (hL : S L) :
      R V W L x = T (V x) (W x) (L x) :=
    ((hT (V x) (W x) (L x)).trans
      (curvature_eq_curvatureOnFields D hU V W L hV hW hL hx)).symm
  change N P (Z A B C X Y) x - Z (N P A) B C X Y x -
    Z A (N P B) C X Y x - Z A B (N P C) X Y x -
    Z A B C (N P X) Y x - Z A B C X (N P Y) x =
      K P (R A B X) Y C x + R (K P A B X) Y C x -
      (2 : ℝ) • K P B X (R Y A C) x -
      (2 : ℝ) • R B X (K P Y A C) x +
      (2 : ℝ) • K P X A (R B Y C) x +
      (2 : ℝ) • R X A (K P B Y C) x +
      K P (R A B C) X Y x + R (K P A B C) X Y x -
      K P (R A X Y) B C x - R (K P A X Y) B C x -
      K P A (R B X Y) C x - R A (K P B X Y) C x -
      K P A B (R C X Y) x - R A B (K P C X Y) x
  rw [houter,
    heval (K P A B X) Y C (hK P A B X hP hA hB hX) hY hC,
    heval B X (K P Y A C) hB hX (hK P Y A C hP hY hA hC),
    heval X A (K P B Y C) hX hA (hK P B Y C hP hB hY hC),
    heval (K P A B C) X Y (hK P A B C hP hA hB hC) hX hY,
    heval (K P A X Y) B C (hK P A X Y hP hA hX hY) hB hC,
    heval A (K P B X Y) C hA (hK P B X Y hP hB hX hY) hC,
    heval A B (K P C X Y) hA hB (hK P C X Y hP hC hX hY)]
  dsimp only [Z, K]
  simp (disch := solve_by_elim (maxDepth := 16) only
      [hP, hA, hB, hC, hX, hY, hN, hR]) only
    [heval, map_sub, LinearMap.sub_apply]
  module

end PoincareConjecture.Proofs.M03
