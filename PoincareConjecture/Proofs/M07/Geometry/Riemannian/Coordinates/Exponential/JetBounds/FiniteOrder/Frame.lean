import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FrameInduction









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric Poincare.Riemannian.RadialTransport
open scoped ContDiff Topology BigOperators Manifold

namespace PoincareConjecture.CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem exists_uniform_radial_frame_jet_bounds_through
    (n : ℕ) (r : ℝ) (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l)
    (m N : ℕ) (hm : m ≤ N) :
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
      (∀ l ≤ N, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        D.curvatureDerivativeNorm l x ≤ C l) →
      (∀ q ≤ m, ∀ l, l + m ≤ N → ∀ J : Fin (4 + l) → Fin n,
        ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
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
    have hK (q : ℕ) (hq : q ≤ 0) (l : ℕ) (hl : l + 0 ≤ N)
        (J : Fin (4 + l) → Fin n) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 r) :
        ‖iteratedFDeriv ℝ q (radialCurvatureComponent D l (fun i => b (J i))) x‖ ≤ C l := by
      have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
      subst q
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hh := abs_radialCurvatureComponent_le_of_curvatureDerivativeNorm_le
        D l (fun i => b (J i)) x (hcurv l hl x hx)
      simpa only [tangentNorm_zero_eq_norm_of_normalized h0, b.norm_eq_one,
        Finset.prod_const_one, mul_one] using hh
    exact ⟨hK,
      fun q hq a u x hx => radialCoframeCoeff_jets_le D b h0 hgeo hT hTi hTv 0
        (fun _ => C 0) (fun k hk => hK k hk 0 (by omega)) q hq a u hx,
      fun q hq j a u x hx => radialConnectionCoeff_jets_le D b h0 hgeo hT hTi hTv 0
        (fun _ => C 0) (fun k hk => hK k hk 0 (by omega)) q hq j a u hx⟩
  | succ m ih =>
    obtain ⟨A, B, K, hA, hB, hK, hprev⟩ := ih (by omega)
    let K' : ℕ → ℝ := fun l => max (K l)
      (curvatureComponentSuccJetBound n l m (fun _ => A) (fun _ => B)
        (fun _ => K l) (fun _ => K (l + 1)))
    let A' := coframeOrderBound n (m + 1) r (fun _ => K' 0)
    let B' := connectionOrderBound n (m + 1) r A' (fun _ => K' 0)
    refine ⟨A', B', K', coframeOrderBound_nonneg .., connectionOrderBound_nonneg ..,
      (fun l => (hK l).trans (le_max_left ..)), ?_⟩
    intro g D b h0 hgeo T hT hTi hTv hcurv
    obtain ⟨hcurvprev, hframeprev, hconnprev⟩ := hprev g D b h0 hgeo T hT hTi hTv hcurv
    have hnext (q : ℕ) (hq : q ≤ m + 1) (l : ℕ) (hl : l + (m + 1) ≤ N)
        (J : Fin (4 + l) → Fin n) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 r) :
        ‖iteratedFDeriv ℝ q (radialCurvatureComponent D l (fun i => b (J i))) x‖ ≤ K' l := by
      by_cases hqm : q ≤ m
      · exact (hcurvprev q hqm l (by omega) J x hx).trans (le_max_left ..)
      · have hqeq : q = m + 1 := by omega
        subst q
        exact (norm_iteratedFDeriv_radialCurvatureComponent_succ_le D b hT hTi hTv l m
          (fun _ => A) (fun _ => B) (fun _ => K l) (fun _ => K (l + 1)) x
          (fun k hk a u => hframeprev k hk a u x hx)
          (fun k hk j a u => hconnprev k hk j a u x hx)
          (fun k hk J => hcurvprev k hk l (by omega) J x hx)
          (fun k hk J => hcurvprev k hk (l + 1) (by omega) J x hx) J).trans (le_max_right ..)
    exact ⟨hnext,
      fun q hq a u x hx => radialCoframeCoeff_jets_le D b h0 hgeo hT hTi hTv (m + 1)
        (fun _ => K' 0) (fun k hk => hnext k hk 0 (by omega)) q hq a u hx,
      fun q hq j a u x hx => radialConnectionCoeff_jets_le D b h0 hgeo hT hTi hTv (m + 1)
        (fun _ => K' 0) (fun k hk => hnext k hk 0 (by omega)) q hq j a u hx⟩

end PoincareConjecture.CoordinateExponential
