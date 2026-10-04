import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Alternatives
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap
import PoincareLib.Geometry.Riemannian.Soul.Point

/-!
# Exact alternatives from cap-preserving attachments

An actual static attachment preserves its cap core when made strong. Strong
neck coverage outside that core therefore gives the pointwise coverage in
the M27 capped branches. Positive noncompact curvature supplies the global
Euclidean diffeomorphism independently through the point-soul theorem.

Reference: Morgan--Tian, Corollary 9.88, pp. 239--240, and
Theorem 9.93(4), p. 242.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Strongification retains the actual static cap core and its exterior
coverage, with the original epsilon and quantitative constant. -/
theorem NoncompactKappa.strongCappedTube_of_covered_attachment
    (K : AncientKappaSolution 3 M) {t epsilon C : ℝ} (ht : t ≤ 0)
    (A : CappedTubeCertificate (K.flow.metric t))
    (hcap : A.cap.epsilon = epsilon) (htube : A.tube.epsilon = epsilon)
    (hconstant : A.cap.cap_constant ≤ C) (hwhole : A.carrier = univ)
    (hdisjoint : Disjoint A.cap.closed_core A.tube.carrier)
    (hstrong : ∀ x : M, x ∉ A.cap.core →
      ∃ N : StrongEvolvingNeck K t epsilon, N.center = x) :
    ∃ T : M26StrongCappedTube K t epsilon C,
      T.cap.cap.core = A.cap.core ∧
        ∀ x : M, x ∈ T.cap.cap.core ∨
          ∃ N : StrongEvolvingNeck K t epsilon, N.center = x := by
  classical
  let T := strongCappedTubeOfCappedTube K ht A hcap htube hconstant
    (fun x hx => hstrong x (fun hcore =>
      disjoint_left.mp hdisjoint (A.cap.core_subset_closed_core hcore) hx)) hwhole
  refine ⟨T, rfl, ?_⟩
  intro x
  by_cases hx : x ∈ A.cap.core
  · exact Or.inl hx
  · exact Or.inr (hstrong x hx)

/-- A covered cap attachment on a positive noncompact solution yields the
full Euclidean alternative, including its actual global diffeomorphism. -/
theorem m27CappedEuclidean_of_covered_attachment
    (K : AncientKappaSolution 3 M)
    (hnoncompact : ¬ IsCompact (univ : Set M))
    (hpositive : M27PositiveSectionalCurvature K 0)
    {epsilon C : ℝ} (A : CappedTubeCertificate (K.flow.metric 0))
    (hcap : A.cap.epsilon = epsilon) (htube : A.tube.epsilon = epsilon)
    (hconstant : A.cap.cap_constant ≤ C) (hwhole : A.carrier = univ)
    (hdisjoint : Disjoint A.cap.closed_core A.tube.carrier)
    (hstrong : ∀ x : M, x ∉ A.cap.core →
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) :
    M27KappaNine93Conclusion K epsilon C := by
  let : NoncompactSpace M := ⟨hnoncompact⟩
  obtain ⟨S⟩ := RiemannianMetric.exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    (K.flow.metric 0) (K.flow.connection 0) (K.complete 0 le_rfl) hpositive
  obtain ⟨T, _, hcoverage⟩ := NoncompactKappa.strongCappedTube_of_covered_attachment
    K le_rfl A hcap htube hconstant hwhole hdisjoint hstrong
  exact .cappedEuclidean T hpositive S.euclidean hcoverage

end PoincareMT
