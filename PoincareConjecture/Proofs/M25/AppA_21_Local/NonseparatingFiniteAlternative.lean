import PoincareConjecture.Proofs.M25.AppA_21_Local.TwoEndedFiniteStop
import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalNegativeReturnCircle
import PoincareConjecture.Proofs.M25.AppA_21_Local.ProtectedRestartCompletion
import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalPositiveReturnCircle









set_option autoImplicit false
open Set
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture



theorem N1_nonseparating_neckOnly_finite_tube_or_fibration :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∀ N ∈ H.necks, N.IsNonseparating) →
      (∃ (C : BalancedNeckChain g H.epsilon) (a b : ℤ),
          C.shape = ChainShape.finite a b ∧
          H.X ⊆ ⋃ i ∈ C.shape.active, (C.neck i).carrier) ∨
      (∃ F : SphereBundleCircleCertificate g H.X,
          F.epsilon = H.epsilon ∧ H.X ⊆ F.carrier) := by
  obtain ⟨es, hsp, hscap, stop⟩ :=
    NeckOnlyCover.exists_two_ended_finite_chain_or_deep_return.{u}
  obtain ⟨en, hnp, _, negativeCircle⟩ :=
    NeckOnlyCover.exists_circle_certificate_of_local_negative_return.{u}
  obtain ⟨ep, hpp, _, positiveCircle⟩ :=
    NeckOnlyCover.exists_circle_certificate_of_local_positive_return.{u}
  obtain ⟨er, hrp, _, restart⟩ :=
    NeckOnlyCover.exists_finite_chain_or_circle_of_negative_end_avoidance.{u}
  refine ⟨min es (min en (min ep er)), by positivity,
    (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g H he hnon
  classical
  rcases le_min_iff.mp he with ⟨hes, he⟩
  rcases le_min_iff.mp he with ⟨hen, he⟩
  rcases le_min_iff.mp he with ⟨hep, her⟩
  let L : ℝ := H.epsilon⁻¹
  obtain ⟨x, hx⟩ := H.connected_X.nonempty
  obtain ⟨N, hN, hNx⟩ := H.pointwise_center_cover x hx
  have hNX : N.center ∈ H.X := by rwa [hNx]
  obtain ⟨C, a, b, hshape, _hsource, ha0, hb0, _hstart,
    hcenters, _hquarters, hinc, hfinal⟩ := stop H hes hnon N hN hNX
  rcases hfinal with hcov | ⟨R, _hR, heR, _hRX, hout, hreturn⟩
  · exact Or.inl ⟨C, a, b, hshape, hcov⟩
  have ha : a ∈ C.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, ha0.trans hb0⟩
  have hb : b ∈ C.shape.active := by
    rw [hshape]
    exact ⟨ha0.trans hb0, le_rfl⟩
  have avoid (A : EpsilonNeck g) (heA : A.epsilon = H.epsilon)
      (hAX : A.center ∈ H.X) (havoid : Disjoint H.X (A.region (-L) (-(4 * L / 5)))) :
      (∃ (D : BalancedNeckChain g H.epsilon) (a b : ℤ),
          D.shape = ChainShape.finite a b ∧
            H.X ⊆ ⋃ i ∈ D.shape.active, (D.neck i).carrier) ∨
        (∃ F : SphereBundleCircleCertificate g H.X,
          F.epsilon = H.epsilon ∧ H.X ⊆ F.carrier) := by
    rcases restart H her hnon A heA hAX havoid with hfinite | ⟨F, heF⟩
    · exact Or.inl hfinite
    · exact Or.inr ⟨F, heF, F.contains_X⟩
  rcases hreturn with ⟨hfront, hdeep⟩ | ⟨hfront, hdeep⟩
  · by_cases hcontact : ∃ P ∈ H.necks,
        P.center ∈ H.X ∩ (C.neck a).region (-L) (-(4 * L / 5))
    · obtain ⟨P, hP, hPX⟩ := hcontact
      obtain ⟨_Q, F, _hQ, heF, _hcarrier⟩ :=
        negativeCircle H hen C a b hshape R heR hfront hout hdeep P hP hPX
      exact Or.inr ⟨F, heF, F.contains_X⟩
    · apply avoid (C.neck a) (C.epsilon_eq a ha) (hcenters a ha)
      apply Set.disjoint_left.mpr
      intro y hy hregion
      obtain ⟨P, hP, hPy⟩ := H.pointwise_center_cover y hy
      exact hcontact ⟨P, hP, by simpa only [hPy, mem_inter_iff] using And.intro hy hregion⟩
  · by_cases hcontact : ∃ P ∈ H.necks,
        P.center ∈ H.X ∩ (C.neck b).region (4 * L / 5) L
    · obtain ⟨P, hP, hPX⟩ := hcontact
      obtain ⟨_Q, F, _hQ, heF, _hcarrier⟩ :=
        positiveCircle H hep C a b hshape hinc R heR hfront hout hdeep P hP hPX
      exact Or.inr ⟨F, heF, F.contains_X⟩
    · have havoid : Disjoint H.X ((C.neck b).region (4 * L / 5) L) := by
        apply Set.disjoint_left.mpr
        intro y hy hregion
        obtain ⟨P, hP, hPy⟩ := H.pointwise_center_cover y hy
        exact hcontact ⟨P, hP, by simpa only [hPy, mem_inter_iff] using And.intro hy hregion⟩
      apply avoid (C.neck b).reverse (C.epsilon_eq b hb) (hcenters b hb)
      simpa only [EpsilonNeck.reverse_region, neg_neg] using havoid

end PoincareConjecture
