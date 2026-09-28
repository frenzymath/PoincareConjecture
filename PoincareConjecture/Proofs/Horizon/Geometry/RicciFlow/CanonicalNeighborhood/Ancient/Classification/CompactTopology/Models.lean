import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.ProjectiveDouble
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.SphereBundle
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Global
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem GlobalNeckCapConclusion.sphere_or_projective_of_compact_positive_sectional
    [CompactSpace M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} {epsilon C : ℝ}
    (H : GlobalNeckCapConclusion g epsilon C) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x v w, g.inner x v v = 1 → g.inner x w w = 1 →
      g.inner x v w = 0 → 0 < D.sectionalCurvature x v w) :
    Nonempty (ClosedComponentCertificate .threeSphere (univ : Set M)) ∨
      Nonempty (ClosedComponentCertificate .realProjectiveThree (univ : Set M)) := by
  rcases H.closed_or_fibration_of_isCompact isCompact_univ with
    ⟨kind, ⟨A⟩, _⟩ | ⟨B, _, hB⟩
  · cases kind with
    | threeSphere => exact Or.inl ⟨A⟩
    | realProjectiveThree => exact Or.inr ⟨A⟩
    | realProjectiveThreeConnectedSum =>
        exact (A.not_univ_of_projectiveDouble_of_compact_positive_sectional g D hc hsec rfl).elim
  · exact (B.not_whole_of_compact_positive_sectional D hc hsec hB).elim

variable [SecondCountableTopology M] [ConnectedSpace M]

theorem AncientKappaNormalization.isRoundMetricSlice_of_constant_positive
    {K : AncientKappaSolution 3 M} {p : M} {b : ℝ}
    (A : AncientKappaNormalization K p b)
    (hround : ConstantPositiveSectionalCurvature (A.target.flow.metric 0)
      (A.target.flow.connection 0)) :
    IsRoundMetricSlice (K.flow.connection b) := by
  obtain ⟨c, hc, hsec⟩ := hround
  have hmetric : MetricHomothety (K.flow.metric b) (A.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) A.scale := by
    intro x v w
    simpa [Diffeomorph.coe_refl, mfderiv_id] using A.metric_eq 0 x v w
  have hinner (x : M) (v w : TangentSpace (𝓡 3) x) :
      (A.target.flow.metric 0).inner x v w = A.scale * (K.flow.metric b).inner x v w := by
    simpa using A.metric_eq 0 x v w
  refine ⟨c * A.scale, mul_pos hc A.scale_pos, fun x v w => ?_⟩
  have hcurv := Homothety.homothety_curvatureTensor_eq
    (K.flow.metric b) (A.target.flow.metric 0) (Diffeomorph.refl (𝓡 3) M ∞)
    A.scale hmetric (K.flow.connection b) (A.target.flow.connection 0) x v w v w
  simp only [Diffeomorph.coe_refl, mfderiv_id] at hcurv
  apply mul_left_cancel₀ A.scale_pos.ne'
  calc
    A.scale * (K.flow.connection b).curvatureTensor x v w v w =
        (A.target.flow.connection 0).curvatureTensor x v w v w := hcurv.symm
    _ = c * ((A.target.flow.metric 0).inner x v v *
          (A.target.flow.metric 0).inner x w w -
          (A.target.flow.metric 0).inner x v w ^ 2) :=
      (A.target.flow.connection 0).curvatureTensor_diagonal_of_constant_sectional x c
        ((A.target.flow.connection 0).sectionalCurvature_eq_of_orthonormal x c (hsec x)) v w
    _ = A.scale * (c * A.scale * ((K.flow.metric b).inner x v v *
          (K.flow.metric b).inner x w w - (K.flow.metric b).inner x v w ^ 2)) := by
      rw [hinner, hinner, hinner]
      ring

theorem M27KappaAlternativePredecessors.compact_nonround_normalized_alternatives
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            IsCompact (univ : Set M) → ¬ IsRoundAncientKappaSolution K →
            (Nonempty (ClosedComponentCertificate .threeSphere (univ : Set M)) ∨
              Nonempty (ClosedComponentCertificate .realProjectiveThree (univ : Set M))) ∨
            ∃ (p : M) (b : ℝ), b ≤ 0 ∧
              ∃ A : AncientKappaNormalization K p b,
                ¬ ConstantPositiveSectionalCurvature (A.target.flow.metric 0)
                  (A.target.flow.connection 0) ∧
                Nonempty (M26StrongDoubleCappedTube A.target 0 epsilon C) := by
  classical
  obtain ⟨epsilon₀, he₀, hcompact⟩ := P.compact_alternatives
  refine ⟨epsilon₀, he₀, fun epsilon he he₀' => ?_⟩
  obtain ⟨C, hC, halternative⟩ := hcompact epsilon he he₀'
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hc hnonround
  obtain ⟨b, hb, hbad⟩ : ∃ b : ℝ, b ≤ 0 ∧ ¬ IsRoundMetricSlice (K.flow.connection b) := by
    by_contra h
    apply hnonround
    intro b hb
    by_contra hbad
    exact h ⟨b, hb, hbad⟩
  let p : M := Classical.choice inferInstance
  obtain ⟨A⟩ := P.normalization M K p b hb
  have hn : ¬ ConstantPositiveSectionalCurvature (A.target.flow.metric 0)
      (A.target.flow.connection 0) := fun h =>
    hbad (A.isRoundMetricSlice_of_constant_positive h)
  obtain ⟨H⟩ := halternative A.target hc
  obtain ⟨H⟩ := H.compact_alternatives
  cases H with
  | round h _ => exact (hn h).elim
  | compactSmall S => exact Or.inl S.component
  | doubleCapped T => exact Or.inr ⟨p, b, hb, A, hn, ⟨T⟩⟩

end PoincareConjecture
