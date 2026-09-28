import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteChainReorientation
import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalNegativeReturnCircle










set_option autoImplicit false
open Set
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture




theorem NeckOnlyCover.exists_circle_certificate_of_local_positive_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ (C : BalancedNeckChain g H.epsilon),
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          ((C.neck (i + 1)).center ∈
                closure ((C.neck i).region 0 H.epsilon⁻¹) ∧
              (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
            ((C.neck i).center ∈
                closure ((C.neck (i + 1)).region (-H.epsilon⁻¹) 0) ∧
              (C.neck i).center ∉ (C.neck (i + 1)).carrier)) →
        let L := H.epsilon⁻¹
        let A := C.neck a
        let B := C.neck b
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∀ (R : EpsilonNeck g), R.epsilon = H.epsilon →
          R.center ∈ closure (A.region (-L) 0) → R.center ∉ U →
          (∀ t ∈ Ioo (0 : ℝ) L,
            ¬ Disjoint R.carrier (B.region t L)) →
          ∀ (P : EpsilonNeck g), P ∈ H.necks →
            P.center ∈ H.X ∩ B.region (4 * L / 5) L →
            ∃ (Q : EpsilonNeck g) (F : SphereBundleCircleCertificate g H.X),
              (Q = P ∨ Q = P.reverse) ∧ F.epsilon = H.epsilon ∧
                F.carrier = (U ∪ R.carrier) ∪ Q.carrier := by
  obtain ⟨er, hrpos, hrcap, reflect⟩ :=
    BalancedNeckChain.exists_reflected_finite_chain_of_frontier_incidence.{u}
  obtain ⟨ec, hcpos, _, circle⟩ :=
    NeckOnlyCover.exists_circle_certificate_of_local_negative_return.{u}
  refine ⟨min er ec, lt_min hrpos hcpos, (min_le_left _ _).trans hrcap, ?_⟩
  intro M _ _ _ _ _ _ g H he C a b hshape hinc
  rcases le_min_iff.mp he with ⟨her, hec⟩
  let L : ℝ := H.epsilon⁻¹
  let A := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro R heR hy hout hreturn P hP hz
  obtain ⟨D, hDshape, _hsource, hneck, hunion⟩ := reflect C hshape her hinc
  have hDa : D.neck a = B.reverse := by
    have hindex : a + b - a = b := by omega
    simpa only [hindex] using congrFun hneck a
  have hDb : D.neck b = A.reverse := by
    have hindex : a + b - b = a := by omega
    simpa only [hindex] using congrFun hneck b
  have hyD : R.center ∈ closure ((D.neck b).region 0 L) := by
    simpa only [hDb, EpsilonNeck.reverse_region, neg_zero] using hy
  have houtD : R.center ∉ ⋃ i ∈ D.shape.active, (D.neck i).carrier := by
    rw [hunion]
    exact hout
  have hreturnD : ∀ t ∈ Ioo (-L) 0,
      ¬ Disjoint R.carrier ((D.neck a).region (-L) t) := by
    intro t ht
    have hneg : -t ∈ Ioo (0 : ℝ) L := by
      constructor <;> linarith only [ht.1, ht.2]
    simpa only [hDa, EpsilonNeck.reverse_region, neg_neg] using hreturn (-t) hneg
  have hzD : P.center ∈ H.X ∩ (D.neck a).region (-L) (-(4 * L / 5)) := by
    simpa only [hDa, EpsilonNeck.reverse_region, neg_neg] using hz
  obtain ⟨Q, F, hQ, heF, hcarrier⟩ :=
    circle H hec D a b hDshape R heR hyD houtD hreturnD P hP hzD
  refine ⟨Q, F, hQ, heF, ?_⟩
  rw [hunion] at hcarrier
  exact hcarrier

end PoincareConjecture
