import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferedEstimates
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CoordinateBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44





theorem exists_buffered_coordinate_modulus (P : M44CapPersistencePredecessors.{u})
    (n m : ℕ) {K H r a b Z : ℝ} (hK : 0 < K) (hH : 0 < H) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 ≤ b) (hZ : 1 ≤ Z) :
    ∃ B L : ℝ, 1 ≤ B ∧ 0 ≤ L ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ {T : ℝ}, 0 < T → T ≤ H → ∀ (F : RicciFlow n M (Icc 0 T)),
      (∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ j ≤ m, ∀ x : M, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
      ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
      ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
      (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
      (∀ x ∈ U, IsCompact (closure ((F.metric 0).ball (e x) r))) →
      (∀ x ∈ U, ∀ v, a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e x v v) →
      (∀ x ∈ U, ∀ v, (F.metric 0).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
      (∀ x ∈ U, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) x‖ ≤ Z) →
      ∀ j ≤ m, ∀ x ∈ U,
        (∀ t ∈ Icc 0 T,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B) ∧
        (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ L * |t - s|) := by
  obtain ⟨D, hD, hderiv⟩ := exists_buffered_initial_derivative_bound P n m hK hH hr
  have ha' : 0 < a * Real.exp (-2 * (n : ℝ) * K * H) := mul_pos ha (Real.exp_pos _)
  have hb' : 0 ≤ b * Real.exp (2 * (n : ℝ) * K * H) := mul_nonneg hb (Real.exp_pos _).le
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_closed_coordinate_jet_estimates n m
    (fun _ => D) (fun _ => hD.le) ha' hb' hZ hH.le
  refine ⟨B, L, hB, hL, ?_⟩
  intro M _ _ _ _ _ T hT hTH F hcurv hinitial U hU e he hi hcompact hlower hupper hjets
  apply hbound hT F (by simpa only [sub_zero] using hTH) hU he hi
  · intro t ht x hx v
    exact (buffered_pullback_ellipticity P hTH hK.le ha F hcurv e
      (hlower x hx) (hupper x hx) ht v).1
  · intro t ht x hx v
    exact (buffered_pullback_ellipticity P hTH hK.le ha F hcurv e
      (hlower x hx) (hupper x hx) ht v).2
  · intro t ht x hx j hj
    exact hderiv M hT hTH F hcurv hinitial (e x) (hcompact x hx) j hj t ht
  · exact hjets

end PoincareConjecture.M44
