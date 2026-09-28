import Mathlib.Algebra.BigOperators.Module
import PoincareConjecture.Proofs.M03.CurvatureConnectionDifference
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.CurvatureVectorTime
import PoincareConjecture.Proofs.M03.ScalarMixedDerivative











set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03


theorem smul_sub_smul_decompose
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (a a' : R) (v v' : V) :
    a • v - a' • v' = (a - a') • v + a' • (v - v') := by
  calc
    a • v - a' • v' = (a • v - a' • v) + (a' • v - a' • v') := by
      abel
    _ = (a - a') • v + a' • (v - v') := by
      rw [sub_smul, smul_sub]

theorem sum_sub_sum_eq_sum_sub
    {ι A : Type*} [DecidableEq ι] [AddCommGroup A]
    (s : Finset ι) (f g : ι → A) :
    s.sum f - s.sum g = s.sum (fun i => f i - g i) := by
  rw [← Finset.sum_sub_distrib]

theorem sum_smul_sub_sum_smul_decompose
    {ι R V : Type*} [DecidableEq ι] [Ring R]
    [AddCommGroup V] [Module R V]
    (s : Finset ι) (a a' : ι → R) (v v' : ι → V) :
      s.sum (fun i => a i • v i) - s.sum (fun i => a' i • v' i) =
      s.sum (fun i => (a i - a' i) • v i + a' i • (v i - v' i)) := by
  calc
    s.sum (fun i => a i • v i) - s.sum (fun i => a' i • v' i) =
        s.sum (fun i => a i • v i - a' i • v' i) :=
      (Finset.sum_sub_distrib _ _).symm
    _ = s.sum (fun i => (a i - a' i) • v i + a' i • (v i - v' i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact smul_sub_smul_decompose (a i) (a' i) (v i) (v' i)

end PoincareConjecture.Proofs.M03


open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

section ResidualEstimates

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000


theorem abs_ricciFlow_iteratedCurvature_lowered_residual_le
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    ∀ (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y),
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      (∀ j, g.tangentNorm x (X j x) ≤ 1) →
      let b := g.orthonormalBasis x
      let ext := fun i => FiberBundle.extend V (b i)
      let ell := fun r =>
        Real.sqrt (∑ γ : Fin (r + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          g.inner x (K t r (fun j => ext (γ j)) x) (K t r (fun j => ext (γ j)) x))
      |g.inner x (deriv (fun s => K s k (Fin.init X) x) t -
        ∑ i, ∑ j, a x i j • K t (k + 2)
          (Fin.cons (E i) (Fin.cons (E j) (Fin.init X))) x)
          (X (Fin.last (k + 3)) x)| ≤
        ((CurvatureResidualPattern.residualPatterns k).map (fun r =>
          |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1)).sum := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let g := F.metric t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  intro X hX x hx hunit
  let b := g.orthonormalBasis x
  let ext := fun i => FiberBundle.extend V (b i)
  let ell := fun r =>
    Real.sqrt (∑ γ : Fin (r + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      g.inner x (K t r (fun j => ext (γ j)) x) (K t r (fun j => ext (γ j)) x))
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) =>
    g.inner x (K t r (Fin.init Z) x) (Z (Fin.last (r + 3)) x)
  let ev := fun r : CurvatureResidualPattern k =>
    CurvatureResidualPattern.evaluate r (a x) low E X
  let bound := fun r : CurvatureResidualPattern k =>
    |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1
  have hterm (r : CurvatureResidualPattern k) : |ev r| ≤ bound r := by
    have hh := abs_curvature_two_factor_contraction_le_orthonormal_energy
      (F.connection t) r.1 r.2.1 r.2.2.2 x0 X hX hx hunit
    change |∑ γ : Fin 4 → Fin n,
        (a x (γ 0) (γ 1) * a x (γ 2) (γ 3)) *
          (low r.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inl j))) *
            low r.2.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inr j))))| ≤
      (n : ℝ) ^ 2 * ell r.1 * ell r.2.1 at hh
    dsimp only [ev, CurvatureResidualPattern.evaluate]
    rw [abs_mul]
    calc
      _ ≤ |(r.2.2.1 : ℝ)| * ((n : ℝ) ^ 2 * ell r.1 * ell r.2.1) :=
        mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = bound r := by dsimp only [bound]; ring
  have hlist (ps : List (CurvatureResidualPattern k)) :
      |(ps.map ev).sum| ≤ (ps.map bound).sum := by
    induction ps with
    | nil => simp only [List.map_nil, List.sum_nil, abs_zero, le_refl]
    | cons r ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (hterm r) ih)
  have heq := ricciFlow_iteratedCurvature_lowered_residual_patterns F ht x0 k X hX hx
  change g.inner x (deriv (fun s => K s k (Fin.init X) x) t -
      ∑ i, ∑ j, a x i j • K t (k + 2)
        (Fin.cons (E i) (Fin.cons (E j) (Fin.init X))) x)
        (X (Fin.last (k + 3)) x) =
      ((CurvatureResidualPattern.residualPatterns k).map ev).sum at heq
  change |g.inner x (deriv (fun s => K s k (Fin.init X) x) t -
      ∑ i, ∑ j, a x i j • K t (k + 2)
        (Fin.cons (E i) (Fin.cons (E j) (Fin.init X))) x)
        (X (Fin.last (k + 3)) x)| ≤
      ((CurvatureResidualPattern.residualPatterns k).map bound).sum
  rw [heq]
  exact hlist _


theorem abs_ricciFlow_iteratedCurvature_residual_pairing_le
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (k : ℕ) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => G.inverse (EuclideanSpace.proj j) i
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    let err := fun Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y =>
      deriv (fun s => K s k Y x) t -
        ∑ i, ∑ j, a i j • K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) Y)) x
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend V (b i)
    let ell := fun r =>
      Real.sqrt (∑ γ : Fin (r + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        g.inner x (K t r (fun j => ext (γ j)) x) (K t r (fun j => ext (γ j)) x))
    |∑ α : Fin (k + 3) → Fin n, ∑ β : Fin (k + 3) → Fin n,
      (∏ j, a (α j) (β j)) * g.inner x (err (fun j => E (α j)))
        (K t k (fun j => E (β j)) x)| ≤
      (n : ℝ) ^ (k + 3) * ell k *
        ((CurvatureResidualPattern.residualPatterns k).map (fun r =>
          |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1)).sum := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let g := F.metric t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => G.inverse (EuclideanSpace.proj j) i
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let err := fun Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y =>
    deriv (fun s => K s k Y x) t -
      ∑ i, ∑ j, a i j • K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) Y)) x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let ext := fun i : ι => FiberBundle.extend V (b i)
  let ell := fun r => Real.sqrt (∑ γ : Fin (r + 3) → ι,
    g.inner x (K t r (fun j => ext (γ j)) x) (K t r (fun j => ext (γ j)) x))
  let S := ((CurvatureResidualPattern.residualPatterns k).map (fun r =>
    |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1)).sum
  let c := fun (p : ι) (i : Fin n) => theta i x (b p)
  let B := fun (p : ι) (y : M) => ∑ i : Fin n, c p i • E i y
  let coeff := fun (γ : Fin (k + 3) → ι) (α : Fin (k + 3) → Fin n) =>
    ∏ j, c (γ j) (α j)
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hB (p : ι) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (B p)) e.baseSet :=
    ContMDiffOn.sum_section (fun i _ => (hE i).const_smul_section)
  have hBx (p : ι) : B p x = b p := by
    simpa only [B, c, FiberBundle.extend_apply_self] using
      (e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V (b p)) hx).symm
  have hBnorm (p : ι) : g.tangentNorm x (B p x) = 1 := by
    rw [hBx]
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [RiemannianMetric.tangentNorm,
      show g.inner x (b p) (b p) = 1 from b.inner_eq_one p, Real.sqrt_one]
  have expand (L : MultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x))
      (γ : Fin (k + 3) → ι) :
      L (fun j => B (γ j) x) = ∑ α : Fin (k + 3) → Fin n,
        coeff γ α • L (fun j => E (α j) x) := by
    simpa only [B, coeff, MultilinearMap.map_smul_univ] using
      L.map_sum (fun j i => c (γ j) i • E i x)
  have hK (s : ℝ) (γ : Fin (k + 3) → ι) :
      K s k (fun j => B (γ j)) x = ∑ α : Fin (k + 3) → Fin n,
        coeff γ α • K s k (fun j => E (α j)) x := by
    obtain ⟨L, hL⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap
      (F.connection s) k x
    have hEL (α : Fin (k + 3) → Fin n) :
        L (fun j => E (α j) x) = K s k (fun j => E (α j)) x :=
      hL e.open_baseSet _ (fun j => hE _) hx
    have hBL : L (fun j => B (γ j) x) = K s k (fun j => B (γ j)) x :=
      hL e.open_baseSet _ (fun j => hB (γ j)) hx
    rw [← hBL, expand]
    simp only [hEL]
  have hK2 (i j : Fin n) (γ : Fin (k + 3) → ι) :
      K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => B (γ r)))) x =
        ∑ α : Fin (k + 3) → Fin n, coeff γ α •
          K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r)))) x := by
    obtain ⟨L, hL⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap
      (F.connection t) (k + 2) x
    let L' : MultilinearMap ℝ (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x)
        (TangentSpace (𝓡 n) x) := (L.curryLeft (E i x)).curryLeft (E j x)
    have hL' (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
        (hY : ∀ r, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
          (T% (Y r)) e.baseSet) :
        L' (fun r => Y r x) =
          K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) Y)) x := by
      have hh := hL e.open_baseSet (Fin.cons (E i) (Fin.cons (E j) Y))
        (by intro r; refine Fin.cases (hE i) ?_ r
            intro r; exact Fin.cases (hE j) hY r) hx
      convert hh using 1
      change L (Fin.cons (E i x) (Fin.cons (E j x) (fun r => Y r x))) = _
      congr 1
      funext r
      refine Fin.cases rfl ?_ r
      intro r
      exact Fin.cases rfl (fun _ => rfl) r
    rw [← hL' _ (fun r => hB (γ r)), expand]
    exact Finset.sum_congr rfl fun α _ => congrArg (fun v => coeff γ α • v)
      (hL' _ (fun r => hE (α r)))
  have hKd (α : Fin (k + 3) → Fin n) :
      HasDerivAt (fun s => K s k (fun j => E (α j)) x)
        (deriv (fun s => K s k (fun j => E (α j)) x) t) t := by
    have hh := contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection e.open_baseSet k (fun j _ => E (α j))
      (fun j => (hE (α j)).comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
        (fun _ hp => hp.2))
    exact (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s => K s k (fun j => E (α j))) hh ht).1 x hx
  have hdot (γ : Fin (k + 3) → ι) :
      deriv (fun s => K s k (fun j => B (γ j)) x) t =
        ∑ α : Fin (k + 3) → Fin n,
          coeff γ α • deriv (fun s => K s k (fun j => E (α j)) x) t := by
    have hd : HasDerivAt
        (fun s => ∑ α : Fin (k + 3) → Fin n, coeff γ α • K s k (fun j => E (α j)) x)
        (∑ α : Fin (k + 3) → Fin n,
          coeff γ α • deriv (fun s => K s k (fun j => E (α j)) x) t) t :=
      HasDerivAt.fun_sum (fun α _ => (hKd α).const_smul (coeff γ α))
    exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hK s γ)).deriv
  have hdiff (γ : Fin (k + 3) → ι) :
      (∑ i, ∑ j, a i j •
        K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => B (γ r)))) x) =
      ∑ α : Fin (k + 3) → Fin n, coeff γ α •
        ∑ i, ∑ j, a i j •
          K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r)))) x := by
    simp only [hK2, Finset.smul_sum, smul_smul]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have herr (γ : Fin (k + 3) → ι) :
      (∑ α : Fin (k + 3) → Fin n, coeff γ α • err (fun j => E (α j))) =
        err (fun j => B (γ j)) := by
    dsimp only [err]
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← hdot, ← hdiff]
  have htrace (i j : Fin n) : a i j = ∑ p : ι, c p i * c p j :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hpair : (∑ α : Fin (k + 3) → Fin n, ∑ β : Fin (k + 3) → Fin n,
      (∏ j, a (α j) (β j)) * g.inner x (err (fun j => E (α j)))
        (K t k (fun j => E (β j)) x)) =
      ∑ γ : Fin (k + 3) → ι,
        g.inner x (err (fun j => B (γ j))) (K t k (fun j => B (γ j)) x) := by
    rw [curvature_all_rank_gram_contraction (g.inner x) a c htrace]
    change (∑ γ : Fin (k + 3) → ι,
      g.inner x (∑ α, coeff γ α • err (fun j => E (α j)))
        (∑ β, coeff γ β • K t k (fun j => E (β j)) x)) = _
    simp only [herr, ← hK]
  have hell : 0 ≤ ell k := Real.sqrt_nonneg _
  have hnormsmul (c : ℝ) (v : TangentSpace (𝓡 n) x) :
      g.tangentNorm x (c • v) = |c| * g.tangentNorm x v := by
    have hh : g.inner x (c • v) (c • v) = c ^ 2 * g.inner x v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [RiemannianMetric.tangentNorm, hh, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
    rfl
  have hnormzero (v : TangentSpace (𝓡 n) x) (hv : g.tangentNorm x v = 0) : v = 0 := by
    by_contra hne
    exact (ne_of_gt (Real.sqrt_pos.mpr (g.pos x v hne))) hv
  have hterm (γ : Fin (k + 3) → ι) :
      |g.inner x (err (fun j => B (γ j))) (K t k (fun j => B (γ j)) x)| ≤ ell k * S := by
    have hv := curvature_iterated_tangentNorm_le_orthonormal_energy (F.connection t) k
      e.open_baseSet (fun j => B (γ j)) (fun j => hB _) hx
    change g.tangentNorm x (K t k (fun j => B (γ j)) x) ≤
      ell k * ∏ j, g.tangentNorm x (B (γ j) x) at hv
    simp only [hBnorm, Finset.prod_const_one, mul_one] at hv
    by_cases hz : ell k = 0
    · have hv0 := hnormzero (K t k (fun j => B (γ j)) x)
        (le_antisymm (hv.trans_eq hz) (Real.sqrt_nonneg _))
      rw [hv0, map_zero, abs_zero, hz, zero_mul]
    have hpos : 0 < ell k := lt_of_le_of_ne hell (Ne.symm hz)
    let Z := fun y => (ell k)⁻¹ • K t k (fun j => B (γ j)) y
    have hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Z) e.baseSet :=
      (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative (F.connection t)
        e.open_baseSet k (fun j => B (γ j)) (fun j => hB _)).const_smul_section
    have hZunit : g.tangentNorm x (Z x) ≤ 1 := by
      rw [show Z x = (ell k)⁻¹ • K t k (fun j => B (γ j)) x from rfl, hnormsmul,
        abs_of_pos (inv_pos.mpr hpos)]
      calc
        _ ≤ (ell k)⁻¹ * ell k := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hell)
        _ = 1 := inv_mul_cancel₀ hz
    have hb := abs_ricciFlow_iteratedCurvature_lowered_residual_le F ht x0 k
      (Fin.snoc (fun j => B (γ j)) Z)
      (by
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.snoc_last] using hZ
        · simpa only [Fin.snoc_castSucc] using hB (γ i)) hx
      (by
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.snoc_last] using hZunit
        · simpa only [Fin.snoc_castSucc] using (hBnorm (γ i)).le)
    dsimp only at hb
    simp only [Fin.init_snoc, Fin.snoc_last] at hb
    change |g.inner x (err (fun j => B (γ j)))
      ((ell k)⁻¹ • K t k (fun j => B (γ j)) x)| ≤ S at hb
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hpos)] at hb
    have hm := mul_le_mul_of_nonneg_left hb hell
    simpa only [← mul_assoc, mul_inv_cancel₀ hz, one_mul] using hm
  have hdim : Fintype.card ι = n := by
    dsimp only [ι]
    rw [Fintype.card_fin, VectorBundle.finrank_eq ℝ V (TangentSpace (𝓡 n)) x,
      finrank_euclideanSpace_fin]
  change |∑ α : Fin (k + 3) → Fin n, ∑ β : Fin (k + 3) → Fin n,
    (∏ j, a (α j) (β j)) * g.inner x (err (fun j => E (α j)))
      (K t k (fun j => E (β j)) x)| ≤ (n : ℝ) ^ (k + 3) * ell k * S
  rw [hpair]
  calc
    _ ≤ ∑ γ : Fin (k + 3) → ι,
        |g.inner x (err (fun j => B (γ j))) (K t k (fun j => B (γ j)) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _γ : Fin (k + 3) → ι, ell k * S := Finset.sum_le_sum fun γ _ => hterm γ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        hdim, nsmul_eq_mul, Nat.cast_pow]
      ring


theorem ricciFlow_iteratedCurvature_energy_max_deriv_le
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (k : ℕ) (hk : 0 < k) (H : ℝ) (hH : 1 ≤ H) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let Q := fun (r : ℕ) (s : ℝ) (y : M) =>
      let b := (F.metric s).orthonormalBasis y
      let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
      let K := curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
      ∑ γ : Fin (r + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)),
        (F.metric s).inner y (K (fun j => ext (γ j)) y) (K (fun j => ext (γ j)) y)
    let cc := ((CurvatureResidualPattern.residualPatterns k).map
      (fun r => |(r.2.2.1 : ℝ)|)).sum
    let Dk := (n : ℝ) ^ (k + 3) * (n : ℝ) ^ 2 * cc
    let mk := 2 * (n : ℝ) + 2 * ((k + 3 : ℕ) : ℝ) * (n : ℝ) ^ 2
    let L := mk * H + 2 * Dk * (H + H ^ 2)
    (∀ j, j < k → Real.sqrt (Q j t x) ≤ H) →
    IsLocalMax (Q k t) x →
    deriv (fun s => Q k s x) t ≤ L * (Q k t x + 1) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let Q := fun (r : ℕ) (s : ℝ) (y : M) =>
    let b := (F.metric s).orthonormalBasis y
    let ext := fun i => FiberBundle.extend V (b i)
    let K := curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
    ∑ γ : Fin (r + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)),
      (F.metric s).inner y (K (fun j => ext (γ j)) y) (K (fun j => ext (γ j)) y)
  let ell := fun r => Real.sqrt (Q r t x)
  let ps := CurvatureResidualPattern.residualPatterns k
  let cc := (ps.map (fun r => |(r.2.2.1 : ℝ)|)).sum
  let Dk := (n : ℝ) ^ (k + 3) * (n : ℝ) ^ 2 * cc
  let mk := 2 * (n : ℝ) + 2 * ((k + 3 : ℕ) : ℝ) * (n : ℝ) ^ 2
  let L := mk * H + 2 * Dk * (H + H ^ 2)
  change (∀ j, j < k → ell j ≤ H) → IsLocalMax (Q k t) x →
    deriv (fun s => Q k s x) t ≤ L * (Q k t x + 1)
  intro hlow hmax
  have hH0 : 0 ≤ H := (by norm_num : (0 : ℝ) ≤ 1).trans hH
  have hell (r : ℕ) : 0 ≤ ell r := Real.sqrt_nonneg _
  have hQ := curvature_iterated_orthonormal_energy_nonneg_and_eq_sq_sqrt
    (F.connection t) k x
  change 0 ≤ Q k t x ∧ Q k t x = ell k ^ 2 at hQ
  have hc : 0 ≤ cc := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hz
    exact abs_nonneg _
  have hD : 0 ≤ Dk := by dsimp only [Dk]; positivity
  have hm : 0 ≤ mk := by dsimp only [mk]; positivity
  have hproduct (r : CurvatureResidualPattern k) :
      ell r.1 * ell r.2.1 ≤ H * ell k + H ^ 2 := by
    have hord := r.orders
    by_cases hp : r.1 = k
    · have hq : r.2.1 = 0 := by omega
      simp only [hp, hq]
      have hh := mul_le_mul_of_nonneg_left (hlow 0 hk) (hell k)
      nlinarith only [hh, sq_nonneg H]
    by_cases hq : r.2.1 = k
    · have hp0 : r.1 = 0 := by omega
      simp only [hp0, hq]
      have hh := mul_le_mul_of_nonneg_right (hlow 0 hk) (hell k)
      nlinarith only [hh, sq_nonneg H]
    have hp' : r.1 < k := by omega
    have hq' : r.2.1 < k := by omega
    have hh := mul_le_mul (hlow r.1 hp') (hlow r.2.1 hq') (hell r.2.1) hH0
    have he := mul_nonneg hH0 (hell k)
    nlinarith only [hh, he]
  have hsum (rs : List (CurvatureResidualPattern k)) :
      (rs.map (fun r => |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1)).sum ≤
      (n : ℝ) ^ 2 * (rs.map (fun r => |(r.2.2.1 : ℝ)|)).sum *
        (H * ell k + H ^ 2) := by
    induction rs with
    | nil => simp only [List.map_nil, List.sum_nil, mul_zero, zero_mul, le_refl]
    | cons r rs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hh := mul_le_mul_of_nonneg_left (hproduct r)
        (mul_nonneg (abs_nonneg (r.2.2.1 : ℝ)) (sq_nonneg (n : ℝ)))
      calc
        _ = (|(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2) * (ell r.1 * ell r.2.1) +
            (rs.map (fun r => |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1)).sum := by ring
        _ ≤ (|(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2) * (H * ell k + H ^ 2) +
            (n : ℝ) ^ 2 * (rs.map (fun r => |(r.2.2.1 : ℝ)|)).sum *
              (H * ell k + H ^ 2) := add_le_add hh ih
        _ = _ := by ring
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x y x y ((F.metric s).inner y)
  let a := fun (s : ℝ) (y : M) (i j : Fin n) => (G s y).inverse (EuclideanSpace.proj j) i
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let kf := fun s (α : Fin (k + 3) → Fin n) => K s k (fun r => E (α r))
  let W := fun s y (α β : Fin (k + 3) → Fin n) => ∏ r, a s y (α r) (β r)
  let pair := fun s (y : M)
      (v w : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) y) =>
    ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
  let q := fun s y => pair s y (fun α => kf s α y) (fun α => kf s α y)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hqQ (s : ℝ) {y : M} (hy : y ∈ e.baseSet) : q s y = Q k s y :=
    curvature_iterated_squared_norm_frame_eq_orthonormal (F.connection s) k x hy
  have hQslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (Q k t) := by
    intro y
    exact (contMDiffAt_ricciFlow_iteratedCurvature_orthonormal_energy F k ht y).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hqs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) e.baseSet :=
    hQslice.contMDiffOn.congr (fun y hy => hqQ t hy)
  have heq : q t =ᶠ[𝓝 x] Q k t := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact hqQ t hy
  have hqmax : IsLocalMax (q t) x := heq.isLocalMax_iff.mpr hmax
  let N := fun (P A : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection t).connection A y (P y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let lap := ∑ i, ∑ j, a t x i j *
    (d (E i) (d (E j) (q t)) x - d (N (E i) (E j)) (q t) x)
  have hlap : lap ≤ 0 :=
    scalar_frame_laplacian_nonpos_of_isLocalMax (F.connection t) x hx (q t) hqs hqmax
  let next := ∑ i, ∑ j, a t x i j * pair t x
    (fun α => K t (k + 1) (Fin.cons (E i) (fun r => E (α r))) x)
    (fun α => K t (k + 1) (Fin.cons (E j) (fun r => E (α r))) x)
  have hnext : 0 ≤ next :=
    (curvature_iterated_bochner_next_energy (F.connection t) k x hx).2
  let P := pair t x
    (fun α => deriv (fun s => kf s α x) t - ∑ i, ∑ j, a t x i j •
      K t (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r)))) x)
    (fun α => kf t α x)
  let S := (ps.map (fun r => |(r.2.2.1 : ℝ)| * (n : ℝ) ^ 2 * ell r.1 * ell r.2.1)).sum
  have hpair := abs_ricciFlow_iteratedCurvature_residual_pairing_le F ht x k hx
  change |P| ≤ (n : ℝ) ^ (k + 3) * ell k * S at hpair
  have hP : P ≤ Dk * ell k * (H * ell k + H ^ 2) := by
    calc
      P ≤ |P| := le_abs_self _
      _ ≤ (n : ℝ) ^ (k + 3) * ell k * S := hpair
      _ ≤ (n : ℝ) ^ (k + 3) * ell k *
          ((n : ℝ) ^ 2 * cc * (H * ell k + H ^ 2)) :=
        mul_le_mul_of_nonneg_left (hsum ps) (by positivity)
      _ = _ := by dsimp only [Dk]; ring
  have hlinear : 2 * ell k ≤ Q k t x + 1 := by
    nlinarith only [hQ.2, sq_nonneg (ell k - 1)]
  have hP2 : 2 * P ≤ Dk * (2 * H + H ^ 2) * Q k t x + Dk * H ^ 2 := by
    calc
      2 * P ≤ 2 * (Dk * ell k * (H * ell k + H ^ 2)) := by linarith only [hP]
      _ = 2 * Dk * H * ell k ^ 2 + (Dk * H ^ 2) * (2 * ell k) := by ring
      _ ≤ 2 * Dk * H * Q k t x + (Dk * H ^ 2) * (Q k t x + 1) := by
        rw [← hQ.2]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hlinear
          (mul_nonneg hD (sq_nonneg H)))
      _ = _ := by ring
  let raised := fun i => e.symmL ℝ x ((G t x).inverse (EuclideanSpace.proj i))
  let outputRate := ∑ α, ∑ β, W t x α β *
    (F.connection t).ricci x (kf t α x) (kf t β x)
  let inputRate := ∑ α, ∑ β, ∑ r : Fin (k + 3),
    2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
      (∏ s ∈ Finset.univ.erase r, a t x (α s) (β s)) *
        (F.metric t).inner x (kf t α x) (kf t β x)
  have hmetric := curvature_all_rank_metric_rate_le (F.connection t) (k + 3) x hx
    (fun α => kf t α x)
  change -2 * outputRate + inputRate ≤
    mk * (F.connection t).curvatureTensorNorm x * q t x at hmetric
  have hcurv : (F.connection t).curvatureTensorNorm x ≤ H := by
    rw [← curvature_iterated_zero_orthonormal_energy_sqrt (F.connection t) x]
    exact hlow 0 hk
  have hmetric' : -2 * outputRate + inputRate ≤ mk * H * Q k t x := by
    rw [hqQ t hx] at hmetric
    exact hmetric.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcurv hm) hQ.1)
  have hheat := ricciFlow_iteratedCurvature_scalar_heat_identity F ht k x hx
  change deriv (fun s => q s x) t - lap =
    -2 * next + 2 * P - 2 * outputRate + inputRate at hheat
  have htime : (fun s => q s x) = (fun s => Q k s x) := funext (fun s => hqQ s hx)
  rw [htime] at hheat
  have hupper : deriv (fun s => Q k s x) t ≤
      (mk * H + Dk * (2 * H + H ^ 2)) * Q k t x + Dk * H ^ 2 := by
    nlinarith only [hheat, hlap, hnext, hP2, hmetric']
  have hcoef : mk * H + Dk * (2 * H + H ^ 2) ≤ L := by
    dsimp only [L]
    nlinarith only [mul_nonneg hD (sq_nonneg H)]
  have hconst : Dk * H ^ 2 ≤ L := by
    dsimp only [L]
    nlinarith only [mul_nonneg hm hH0, mul_nonneg hD hH0,
      mul_nonneg hD (sq_nonneg H)]
  calc
    deriv (fun s => Q k s x) t ≤
        (mk * H + Dk * (2 * H + H ^ 2)) * Q k t x + Dk * H ^ 2 := hupper
    _ ≤ L * Q k t x + L := add_le_add (mul_le_mul_of_nonneg_right hcoef hQ.1) hconst
    _ = L * (Q k t x + 1) := by ring


theorem ricciFlow_iteratedCurvature_terminal_bound
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (_hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hC : ∀ s ∈ Ico 0 T, ∀ x : M, (F.connection s).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let ell := fun (k : ℕ) (s : ℝ) (x : M) =>
      let b := (F.metric s).orthonormalBasis x
      let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
      let K := curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
      Real.sqrt (∑ γ : Fin (k + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (F.metric s).inner x (K (fun j => ext (γ j)) x) (K (fun j => ext (γ j)) x))
    ∀ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ Ico a T, ∀ x : M, ell k s x ≤ A := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let Q := fun (k : ℕ) (s : ℝ) (x : M) =>
    let b := (F.metric s).orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let K := curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
    ∑ γ : Fin (k + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      (F.metric s).inner x (K (fun j => ext (γ j)) x) (K (fun j => ext (γ j)) x)
  let ell := fun k s x => Real.sqrt (Q k s x)
  change ∀ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ Ico a T, ∀ x : M, ell k s x ≤ A
  have hQ0 (k : ℕ) (s : ℝ) (x : M) : 0 ≤ Q k s x :=
    (curvature_iterated_orthonormal_energy_nonneg_and_eq_sq_sqrt (F.connection s) k x).1
  have hsm (k : ℕ) (s : ℝ) (hs : s ∈ Ioo 0 T) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Q k p.1 p.2) (s, x) :=
    contMDiffAt_ricciFlow_iteratedCurvature_orthonormal_energy F k
      (by simpa only [interior_Ico] using hs) x
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro s hs x
      have heq : ell 0 s x = (F.connection s).curvatureTensorNorm x :=
        curvature_iterated_zero_orthonormal_energy_sqrt (F.connection s) x
      rw [heq]
      exact (hC s ⟨ha.le.trans hs.1, hs.2⟩ x).trans (le_max_left _ _)
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    choose A hA0 hAb using (fun j : Fin k => ih j j.isLt)
    let H := 1 + ∑ j : Fin k, A j
    have hH : 1 ≤ H := by
      have hh : 0 ≤ ∑ j : Fin k, A j := Finset.sum_nonneg (fun j _ => hA0 j)
      dsimp only [H]
      linarith only [hh]
    have hH0 : 0 ≤ H := (by norm_num : (0 : ℝ) ≤ 1).trans hH
    have hlow (s : ℝ) (hs : s ∈ Ico a T) (x : M) (j : ℕ) (hj : j < k) :
        ell j s x ≤ H := by
      have hh : A ⟨j, hj⟩ ≤ ∑ i : Fin k, A i :=
        Finset.single_le_sum (fun i _ => hA0 i) (Finset.mem_univ (⟨j, hj⟩ : Fin k))
      have hb := hAb ⟨j, hj⟩ s hs x
      change ell j s x ≤ A ⟨j, hj⟩ at hb
      dsimp only [H]
      linarith only [hb, hh]
    let cc := ((CurvatureResidualPattern.residualPatterns k).map
      (fun r => |(r.2.2.1 : ℝ)|)).sum
    let Dk := (n : ℝ) ^ (k + 3) * (n : ℝ) ^ 2 * cc
    let mk := 2 * (n : ℝ) + 2 * ((k + 3 : ℕ) : ℝ) * (n : ℝ) ^ 2
    let L := mk * H + 2 * Dk * (H + H ^ 2)
    have hc : 0 ≤ cc := by
      apply List.sum_nonneg
      intro z hz
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hz
      exact abs_nonneg _
    have hL : 0 ≤ L := by dsimp only [L, Dk, mk]; positivity
    cases isEmpty_or_nonempty M with
    | inl hM =>
      let : IsEmpty M := hM
      exact ⟨0, le_rfl, fun _ _ x => isEmptyElim x⟩
    | inr hM =>
      let : Nonempty M := hM
      have hslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (Q k a) := by
        intro x
        exact (hsm k a ⟨ha, haT⟩ x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
      obtain ⟨xa, _, hma⟩ := isCompact_univ.exists_isMaxOn
        (univ_nonempty : (univ : Set M).Nonempty) hslice.continuous.continuousOn
      let A0 := Q k a xa
      have hA00 : 0 ≤ A0 := hQ0 k a xa
      have hinit (x : M) : Q k a x ≤ A0 := isMaxOn_iff.mp hma x (mem_univ x)
      let B := (A0 + 1) * Real.exp (L * (T - a))
      refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
      intro b hb x
      have hcont : ContinuousOn (fun p : ℝ × M => Q k p.1 p.2) (Icc a b ×ˢ univ) := by
        intro p hp
        exact (hsm k p.1 ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb.2⟩ p.2).continuousAt.continuousWithinAt
      have hdiff (s : ℝ) (hs : s ∈ Ioc a b) (y : M) :
          DifferentiableAt ℝ (fun r => Q k r y) s := by
        have hs' : s ∈ Ioo 0 T := ⟨ha.trans hs.1, hs.2.trans_lt hb.2⟩
        exact ((hsm k s hs' y).comp s
          (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt (by simp)
      have hrate (s : ℝ) (hs : s ∈ Ioc a b) (y : M)
          (hmax : IsLocalMax (Q k s) y) :
          deriv (fun r => Q k r y) s ≤ L * (Q k s y + 1) := by
        have hst : s ∈ interior (Ico 0 T) := by
          rw [interior_Ico]
          exact ⟨ha.trans hs.1, hs.2.trans_lt hb.2⟩
        exact ricciFlow_iteratedCurvature_energy_max_deriv_le F hst k hkpos H hH y
          (hlow s ⟨hs.1.le, hs.2.trans_lt hb.2⟩ y) hmax
      have hgrowth := scalar_shifted_exp_bound_of_max_deriv (Q k) hb.1 hcont hdiff hrate hinit x
      have hexp : Real.exp (L * (b - a)) ≤ Real.exp (L * (T - a)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hb.2.le a) hL
      have hB : Q k b x ≤ B := by
        have hh := hgrowth.trans (mul_le_mul_of_nonneg_left hexp (by linarith only [hA00]))
        change Q k b x + 1 ≤ B at hh
        linarith only [hh]
      exact Real.sqrt_le_sqrt hB


theorem ricciFlow_connection_frame_terminal_control
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ s ∈ Ico 0 T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) (x0 : M)
    {Q : Set M} (hQ : IsCompact Q)
    (hQframe : Q ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let theta := e.localFrameCoeff (𝓡 n)
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let Gamma := fun (s : ℝ) (x : M) (i j l : Fin n) =>
      theta l x ((F.connection s).connection (E j) x (E i x))
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
      (∀ s ∈ Ico a T, ∀ x ∈ Q, ∀ i j l : Fin n,
        |Gamma s x i j l| ≤ B) ∧
      (∀ s ∈ Ico a T, ∀ x ∈ Q, ∀ i j l : Fin n,
        |deriv (fun r => Gamma r x i j l) s| ≤ L) ∧
      (∀ s ∈ Ico a T, ∀ t ∈ Ico a T,
        ∀ x ∈ Q, ∀ i j l : Fin n,
          |Gamma t x i j l - Gamma s x i j l| ≤ L * |t - s|) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let N := fun s (P A : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection A y (P y)
  let Gamma := fun (s : ℝ) (x : M) (i j l : Fin n) => theta l x (N s (E i) (E j) x)
  let dotN := fun (s : ℝ) (x : M) (i j : Fin n) => deriv (fun r => N r (E i) (E j) x) s
  change ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
    (∀ s ∈ Ico a T, ∀ x ∈ Q, ∀ i j l : Fin n, |Gamma s x i j l| ≤ B) ∧
    (∀ s ∈ Ico a T, ∀ x ∈ Q, ∀ i j l : Fin n,
      |deriv (fun r => Gamma r x i j l) s| ≤ L) ∧
    (∀ s ∈ Ico a T, ∀ t ∈ Ico a T, ∀ x ∈ Q, ∀ i j l : Fin n,
      |Gamma t x i j l - Gamma s x i j l| ≤ L * |t - s|)
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have haI : a ∈ Ico a T := ⟨le_rfl, haT⟩
  have htime {s : ℝ} (hs : s ∈ Ico a T) : s ∈ Ico 0 T :=
    ⟨ha.le.trans hs.1, hs.2⟩
  have hinterior {s : ℝ} (hs : s ∈ Ico a T) : s ∈ interior (Ico 0 T) := by
    rw [interior_Ico]
    exact ⟨ha.trans_le hs.1, hs.2⟩
  have hE (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (E i)) e.baseSet := e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hEvalue {x : M} (hx : x ∈ e.baseSet) (i : Fin n) :
      E i x = e.symmL ℝ x (cb i) := by
    dsimp only [E]
    rw [e.localFrame_apply_of_mem_baseSet cb hx]
    simp only [Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply]
    exact (Trivialization.symmL_apply (R := ℝ) e hx (cb i)).symm
  have htheta {x : M} (hx : x ∈ e.baseSet) (l : Fin n) (v : TangentSpace (𝓡 n) x) :
      theta l x v = (e.continuousLinearMapAt ℝ x v) l := by
    have hh := e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) cb hx
      (FiberBundle.extend V v) l
    rw [FiberBundle.extend_apply_self] at hh
    change theta l x v = _ at hh
    rw [hh]
    simp only [Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, cb, OrthonormalBasis.coe_toBasis_repr_apply,
      Trivialization.linearEquivAt_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
    rfl
  obtain ⟨c0, C0, hc0, hC0, hframe0⟩ := exists_pos_uniform_metric_frame_bounds
    (F.smooth.mono (Set.prod_mono (singleton_subset_iff.mpr h0) subset_rfl))
    (isCompact_singleton : IsCompact ({0} : Set ℝ))
    x0 hQ hQframe
  let lam := 2 * (n : ℝ) * max C 0
  let d := Real.exp (-(lam * T)) * c0
  let D := Real.exp (lam * T) * C0
  have hd : 0 < d := mul_pos (Real.exp_pos _) hc0
  have hD : 0 < D := mul_pos (Real.exp_pos _) hC0
  let U := Real.sqrt D
  let Rc := (Real.sqrt d)⁻¹
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hRc : 0 ≤ Rc := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hdsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hcomparison := (metric_endpoint_control_of_curvature_bound hT F hRm).1
  have hframe {s : ℝ} (hs : s ∈ Ico 0 T) {x : M} (hx : x ∈ Q) (v : V) :
      d * ‖v‖ ^ 2 ≤ (F.metric s).inner x (e.symmL ℝ x v) (e.symmL ℝ x v) ∧
      (F.metric s).inner x (e.symmL ℝ x v) (e.symmL ℝ x v) ≤ D * ‖v‖ ^ 2 := by
    have hzero := hframe0 0 (mem_singleton 0) x hx v
    have hsmetric := hcomparison s hs x (e.symmL ℝ x v)
    constructor
    · calc
        _ = Real.exp (-(lam * T)) * (c0 * ‖v‖ ^ 2) := by dsimp only [d]; ring
        _ ≤ Real.exp (-(lam * T)) * (F.metric 0).inner x
            (e.symmL ℝ x v) (e.symmL ℝ x v) :=
          mul_le_mul_of_nonneg_left hzero.1 (Real.exp_pos _).le
        _ ≤ _ := hsmetric.1
    · calc
        _ ≤ Real.exp (lam * T) * (F.metric 0).inner x
            (e.symmL ℝ x v) (e.symmL ℝ x v) := hsmetric.2
        _ ≤ Real.exp (lam * T) * (C0 * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hzero.2 (Real.exp_pos _).le
        _ = D * ‖v‖ ^ 2 := by dsimp only [D]; ring
  have hframeNorm {s : ℝ} (hs : s ∈ Ico 0 T) {x : M} (hx : x ∈ Q) (i : Fin n) :
      (F.metric s).tangentNorm x (E i x) ≤ U := by
    have hh := (hframe hs hx (cb i)).2
    have hcb : ‖cb i‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
    rw [hcb, one_pow, mul_one] at hh
    rw [hEvalue (hQframe hx), RiemannianMetric.tangentNorm]
    exact Real.sqrt_le_sqrt hh
  have hcovector {s : ℝ} (hs : s ∈ Ico 0 T) {x : M} (hx : x ∈ Q)
      (l : Fin n) (v : TangentSpace (𝓡 n) x) :
      |theta l x v| ≤ Rc * (F.metric s).tangentNorm x v := by
    let w := e.continuousLinearMapAt ℝ x v
    have hh := (hframe hs hx w).1
    rw [e.symmL_continuousLinearMapAt (hQframe hx)] at hh
    have hsqrt := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_mul hd.le, Real.sqrt_sq (norm_nonneg w)] at hsqrt
    change Real.sqrt d * ‖w‖ ≤ (F.metric s).tangentNorm x v at hsqrt
    calc
      |theta l x v| = |w l| := congrArg abs (htheta (hQframe hx) l v)
      _ ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w l
      _ = Rc * (Real.sqrt d * ‖w‖) := by
        dsimp only [Rc]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hdsqrt), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hRc
  let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s P (R s A B C) y - R s (N s P A) B C y -
      R s A (N s P B) C y - R s A B (N s P C) y
  let energy := fun s x =>
    let b := (F.metric s).orthonormalBasis x
    let ext := fun i => FiberBundle.extend V (b i)
    let kb := fun γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K s (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) x
    ∑ γ, (F.metric s).inner x (kb γ) (kb γ)
  let L1 := 96 * ((n : ℝ) + 1) ^ 3 * max C 0
  obtain ⟨Qa, hQa, _, _, henergy⟩ :=
    ricciFlow_curvature_derivative_energy_terminal_bound hT F hRm ha haT
  change ∀ s ∈ Ico a T, ∀ x : M, energy s x ≤ Qa * Real.exp (L1 * (T - a)) at henergy
  let H1 := Real.sqrt (Qa * Real.exp (L1 * (T - a)))
  have hH1 : 0 ≤ H1 := Real.sqrt_nonneg _
  let L := Rc * (3 * (n : ℝ) * H1 * U * U)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hNfamily (i j : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (fun p : ℝ × M => TotalSpace.mk' V p.2 (N p.1 (E i) (E j) p.2))
      (Ico 0 T ×ˢ e.baseSet) :=
    contMDiffOn_connection_family_apply F.smooth F.connection e.open_baseSet
      (E j) (E i) (hE j) (hE i)
  have hderiv {s : ℝ} (hs : s ∈ Ico a T) {x : M} (hx : x ∈ e.baseSet)
      (i j l : Fin n) : HasDerivAt (fun r => Gamma r x i j l)
        (theta l x (dotN s x i j)) s := by
    have hn := (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun r => N r (E i) (E j)) (hNfamily i j) (hinterior hs)).1 x hx
    let cov := (EuclideanSpace.proj l).comp (e.continuousLinearMapAt ℝ x)
    have hd := cov.hasFDerivAt.comp_hasDerivAt s hn
    have hcv (v : TangentSpace (𝓡 n) x) : cov v = theta l x v := (htheta hx l v).symm
    simpa only [Function.comp_def, hcv, Gamma, dotN] using hd
  have hrate {s : ℝ} (hs : s ∈ Ico a T) {x : M} (hx : x ∈ Q) (i j l : Fin n) :
      |deriv (fun r => Gamma r x i j l) s| ≤ L := by
    have hv := ricciFlow_connection_variation_tangentNorm_le_curvature_derivative_energy
      F (hinterior hs) e.open_baseSet (E i) (E j) (hE i) (hE j) (hQframe hx)
    change (F.metric s).tangentNorm x (dotN s x i j) ≤
      3 * (n : ℝ) * Real.sqrt (energy s x) *
        (F.metric s).tangentNorm x (E i x) * (F.metric s).tangentNorm x (E j x) at hv
    have henergyNorm : Real.sqrt (energy s x) ≤ H1 := Real.sqrt_le_sqrt (henergy s hs x)
    have hscale : (F.metric s).tangentNorm x (dotN s x i j) ≤ 3 * (n : ℝ) * H1 * U * U := by
      apply hv.trans
      apply mul_le_mul _ (hframeNorm (htime hs) hx j) (Real.sqrt_nonneg _) (by positivity)
      apply mul_le_mul _ (hframeNorm (htime hs) hx i) (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left henergyNorm (by positivity)
    rw [(hderiv hs (hQframe hx) i j l).deriv]
    exact (hcovector (htime hs) hx l _).trans (mul_le_mul_of_nonneg_left hscale hRc)
  have hlip {s t : ℝ} (hs : s ∈ Ico a T) (ht : t ∈ Ico a T)
      {x : M} (hx : x ∈ Q) (i j l : Fin n) :
      |Gamma t x i j l - Gamma s x i j l| ≤ L * |t - s| := by
    have hh := (convex_Ico a T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => Gamma r x i j l)
      (f' := fun r => deriv (fun q => Gamma q x i j l) r)
      (fun r hr => (hderiv hr (hQframe hx) i j l).differentiableAt.hasDerivAt.hasDerivWithinAt)
      (fun r hr => by simpa only [Real.norm_eq_abs] using hrate hr hx i j l) hs ht
    simpa only [Real.norm_eq_abs] using hh
  have hinitial (i j l : Fin n) : ∃ B0 : ℝ, 0 ≤ B0 ∧
      ∀ x ∈ Q, |Gamma a x i j l| ≤ B0 := by
    have hn := (F.connection a).contMDiffOn_connection_apply e.open_baseSet
      (E i) (E j) (hE i) (hE j)
    have hg : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => Gamma a x i j l) e.baseSet :=
      contMDiffOn_localFrameCoeff cb e.open_baseSet subset_rfl hn l
    obtain ⟨B0, hB0⟩ := hQ.bddAbove_image ((hg.continuousOn.abs).mono hQframe)
    refine ⟨max B0 0, le_max_right _ _, ?_⟩
    intro x hx
    exact (hB0 (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  choose b hb hbound using hinitial
  let B0 := ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, b i j l
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hb i j l
  have hbB0 (i j l : Fin n) : b i j l ≤ B0 := by
    calc
      _ ≤ ∑ l : Fin n, b i j l := Finset.single_le_sum (fun l _ => hb i j l) (Finset.mem_univ l)
      _ ≤ ∑ j : Fin n, ∑ l : Fin n, b i j l :=
        Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun l _ => hb i j l) (Finset.mem_univ j)
      _ ≤ B0 := Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hb i j l)
        (Finset.mem_univ i)
  refine ⟨B0 + L * (T - a), L, add_nonneg hB0 (mul_nonneg hL (sub_nonneg.mpr haT.le)),
    hL, ?_, (fun s hs x hx i j l => hrate hs hx i j l),
    (fun s hs t ht x hx i j l => hlip hs ht hx i j l)⟩
  intro s hs x hx i j l
  have hdiff := hlip haI hs hx i j l
  rw [abs_of_nonneg (sub_nonneg.mpr hs.1)] at hdiff
  have hbase := (hbound i j l x hx).trans (hbB0 i j l)
  calc
    |Gamma s x i j l| = |Gamma a x i j l + (Gamma s x i j l - Gamma a x i j l)| := by
      congr 1
      ring
    _ ≤ |Gamma a x i j l| + |Gamma s x i j l - Gamma a x i j l| := abs_add_le _ _
    _ ≤ B0 + L * (s - a) := add_le_add hbase hdiff
    _ ≤ B0 + L * (T - a) := add_le_add (le_refl B0) (mul_le_mul_of_nonneg_left
      (sub_le_sub_right hs.2.le a) hL)

end ResidualEstimates

end PoincareConjecture.Proofs.M03
