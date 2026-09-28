import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.JacobiCoefficientJets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff Topology BigOperators Manifold

namespace PoincareConjecture.CoordinateExponential

open Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem norm_iteratedFDeriv_radialCoframeCoeff_le_of_operator
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (m : ℕ) {A : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hA : ‖iteratedFDeriv ℝ m (fun y => (T y).inverse) x‖ ≤ A)
    (a : Fin n) (u : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ m (fun y => radialCoframeCoeff b T a y u) x‖ ≤ A * ‖u‖ := by
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    (innerSL ℝ (b a)).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) u)
  have hL : ‖L‖ ≤ ‖u‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro F
    have h := norm_inner_le_norm (𝕜 := ℝ) (b a) (F u)
    rw [b.norm_eq_one, one_mul] at h
    exact h.trans ((F.le_opNorm u).trans_eq (mul_comm _ _))
  have hInv : ContDiff ℝ ∞ (fun y => (T y).inverse) := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => (hTi y).contDiffAt_map_inverse.comp y hT.contDiffAt
  have h := L.norm_iteratedFDeriv_comp_left (x := x) hInv.contDiffAt
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  have hh := (h.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hA (norm_nonneg u))
  simpa only [L, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply, radialCoframeCoeff,
    OrthonormalBasis.repr_apply_apply, mul_comm] using hh

def coframeOrderBound (n m : ℕ) (r : ℝ) (C : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1), Real.exp ((2 : ℝ) ^ q *
    max 1 (∑ j ∈ Finset.range (q + 1), radialJacobiCoefficientJetBound n j r C))

theorem coframeOrderBound_nonneg (n m : ℕ) (r : ℝ) (C : ℕ → ℝ) :
    0 ≤ coframeOrderBound n m r C := by unfold coframeOrderBound; positivity

theorem radialCoframeCoeff_jets_le
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (hgeo : ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
      christoffelBilinear g.euclideanCoefficients (t • x) x x = 0)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (C : ℕ → ℝ) {r : ℝ}
    (hC : ∀ q ≤ m, ∀ J : Fin 4 → Fin n, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖iteratedFDeriv ℝ q (radialCurvatureComponent D 0 (fun i => b (J i))) x‖ ≤ C q)
    (q : ℕ) (hq : q ≤ m) (a : Fin n) (u : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 r) :
    ‖iteratedFDeriv ℝ q (fun y => radialCoframeCoeff b T a y u) x‖ ≤
      coframeOrderBound n m r C * ‖u‖ := by
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  have hsymm (x v w : EuclideanSpace ℝ (Fin n)) : Γ x v w = Γ x w v :=
    christoffelBilinear_symm ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp))
      (Filter.Eventually.of_forall fun y v w => g.symm y v w) v w
  let K := ∑ j ∈ Finset.range (q + 1), radialJacobiCoefficientJetBound n j r C
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => radialJacobiCoefficientJetBound_nonneg ..)
  have hb (j : ℕ) (hj : j ≤ q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball 0 r) :
      ‖iteratedFDeriv ℝ j (fun z => radialJacobiCoefficient Γ T (t, z)) y‖ ≤ K :=
    (norm_iteratedFDeriv_radialJacobiCoefficient_le D b h0 hgeo hT hTi hTv j C
      (fun k hk => hC k (hk.trans (hj.trans hq))) ht hy).trans
      (Finset.single_le_sum (fun k _ => radialJacobiCoefficientJetBound_nonneg n k r C)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have h := norm_iteratedFDeriv_radial_coframe_le hΓ hsymm hgeo hT hTi hTv
    isOpen_ball q hK hb hx
  apply norm_iteratedFDeriv_radialCoframeCoeff_le_of_operator b hT hTi q
    (h.trans ?_) a u
  exact Finset.single_le_sum (fun j _ => Real.exp_nonneg ((2 : ℝ) ^ j *
    max 1 (∑ k ∈ Finset.range (j + 1), radialJacobiCoefficientJetBound n k r C)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))

def connectionOrderBound (n m : ℕ) (r A : ℝ) (C : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1), connectionComponentJetBound n q r (fun _ => A) C

theorem connectionOrderBound_nonneg (n m : ℕ) (r A : ℝ) (C : ℕ → ℝ) :
    0 ≤ connectionOrderBound n m r A C :=
  Finset.sum_nonneg (fun q _ => connectionComponentJetBound_nonneg ..)

theorem radialConnectionCoeff_jets_le
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (hgeo : ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
      christoffelBilinear g.euclideanCoefficients (t • x) x x = 0)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (C : ℕ → ℝ) {r : ℝ}
    (hC : ∀ q ≤ m, ∀ J : Fin 4 → Fin n, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖iteratedFDeriv ℝ q (radialCurvatureComponent D 0 (fun i => b (J i))) x‖ ≤ C q)
    (q : ℕ) (hq : q ≤ m) (j a : Fin n) (u : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 r) :
    ‖iteratedFDeriv ℝ q (fun y => radialConnectionCoeff b
      (christoffelBilinear g.euclideanCoefficients) T j a y u) x‖ ≤
      connectionOrderBound n m r (coframeOrderBound n m r C) C * ‖u‖ := by
  have h := norm_iteratedFDeriv_radialConnectionCoeff_le D b h0 hgeo hT hTi hTv q
    (fun _ => coframeOrderBound n m r C) C
    (fun k hk a u y hy => radialCoframeCoeff_jets_le D b h0 hgeo hT hTi hTv m C hC
      k (hk.trans hq) a u hy) (fun k hk => hC k (hk.trans hq)) j a u hx
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  exact Finset.single_le_sum
    (fun k _ => connectionComponentJetBound_nonneg n k r (fun _ => coframeOrderBound n m r C) C)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))

theorem exists_uniform_radial_frame_jet_bounds
    (n : ℕ) (r : ℝ) (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) (m : ℕ) :
    ∃ A B : ℝ, ∃ K : ℕ → ℝ, 0 ≤ A ∧ 0 ≤ B ∧ (∀ l, 0 ≤ K l) ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
        (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
      (∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w) →
      (∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
        christoffelBilinear g.euclideanCoefficients (t • x) x x = 0) →
      ∀ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ∞ T → (∀ x, (T x).IsInvertible) →
      (∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x) →
      (∀ l, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r, D.curvatureDerivativeNorm l x ≤ C l) →
      (∀ q ≤ m, ∀ l, ∀ J : Fin (4 + l) → Fin n, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ‖iteratedFDeriv ℝ q (radialCurvatureComponent D l (fun i => b (J i))) x‖ ≤ K l) ∧
      (∀ q ≤ m, ∀ a u, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ‖iteratedFDeriv ℝ q (fun y => radialCoframeCoeff b T a y u) x‖ ≤ A * ‖u‖) ∧
      (∀ q ≤ m, ∀ j a u, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ‖iteratedFDeriv ℝ q (fun y => radialConnectionCoeff b
          (christoffelBilinear g.euclideanCoefficients) T j a y u) x‖ ≤ B * ‖u‖) := by
  induction m with
  | zero =>
    let A := coframeOrderBound n 0 r (fun _ => C 0)
    let B := connectionOrderBound n 0 r A (fun _ => C 0)
    refine ⟨A, B, C, coframeOrderBound_nonneg .., connectionOrderBound_nonneg .., hC, ?_⟩
    intro g D b h0 hgeo T hT hTi hTv hcurv
    have hK (q : ℕ) (hq : q ≤ 0) (l : ℕ) (J : Fin (4 + l) → Fin n)
        (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 r) :
        ‖iteratedFDeriv ℝ q (radialCurvatureComponent D l (fun i => b (J i))) x‖ ≤ C l := by
      have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
      subst q
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hh := abs_radialCurvatureComponent_le_of_curvatureDerivativeNorm_le
        D l (fun i => b (J i)) x (hcurv l x hx)
      simpa only [tangentNorm_zero_eq_norm_of_normalized h0, b.norm_eq_one,
        Finset.prod_const_one, mul_one] using hh
    exact ⟨hK,
      fun q hq a u x hx => radialCoframeCoeff_jets_le D b h0 hgeo hT hTi hTv 0
        (fun _ => C 0) (fun k hk => hK k hk 0) q hq a u hx,
      fun q hq j a u x hx => radialConnectionCoeff_jets_le D b h0 hgeo hT hTi hTv 0
        (fun _ => C 0) (fun k hk => hK k hk 0) q hq j a u hx⟩
  | succ m ih =>
    obtain ⟨A, B, K, hA, hB, hK, hprev⟩ := ih
    let K' : ℕ → ℝ := fun l => max (K l)
      (curvatureComponentSuccJetBound n l m (fun _ => A) (fun _ => B)
        (fun _ => K l) (fun _ => K (l + 1)))
    let A' := coframeOrderBound n (m + 1) r (fun _ => K' 0)
    let B' := connectionOrderBound n (m + 1) r A' (fun _ => K' 0)
    refine ⟨A', B', K', coframeOrderBound_nonneg .., connectionOrderBound_nonneg ..,
      (fun l => (hK l).trans (le_max_left ..)), ?_⟩
    intro g D b h0 hgeo T hT hTi hTv hcurv
    obtain ⟨hcurvprev, hframeprev, hconnprev⟩ := hprev g D b h0 hgeo T hT hTi hTv hcurv
    have hnext (q : ℕ) (hq : q ≤ m + 1) (l : ℕ) (J : Fin (4 + l) → Fin n)
        (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 r) :
        ‖iteratedFDeriv ℝ q (radialCurvatureComponent D l (fun i => b (J i))) x‖ ≤ K' l := by
      by_cases hqm : q ≤ m
      · exact (hcurvprev q hqm l J x hx).trans (le_max_left ..)
      · have hqeq : q = m + 1 := by omega
        subst q
        exact (norm_iteratedFDeriv_radialCurvatureComponent_succ_le D b hT hTi hTv l m
          (fun _ => A) (fun _ => B) (fun _ => K l) (fun _ => K (l + 1)) x
          (fun k hk a u => hframeprev k hk a u x hx)
          (fun k hk j a u => hconnprev k hk j a u x hx)
          (fun k hk J => hcurvprev k hk l J x hx)
          (fun k hk J => hcurvprev k hk (l + 1) J x hx) J).trans (le_max_right ..)
    exact ⟨hnext,
      fun q hq a u x hx => radialCoframeCoeff_jets_le D b h0 hgeo hT hTi hTv (m + 1)
        (fun _ => K' 0) (fun k hk => hnext k hk 0) q hq a u hx,
      fun q hq j a u x hx => radialConnectionCoeff_jets_le D b h0 hgeo hT hTi hTv (m + 1)
        (fun _ => K' 0) (fun k hk => hnext k hk 0) q hq j a u hx⟩

end PoincareConjecture.CoordinateExponential
