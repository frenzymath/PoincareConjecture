import PoincareLib.Geometry.Riemannian.Soul.Point
import PoincareLib.Geometry.Riemannian.Soul.Separation.Radial
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.EscapeCarrier

/-!
# Point-soul data for separating necks

The point-soul producer supplies both the Euclidean topology needed by an
actual neck separator and the radial parametrization used to identify its
compact inner side. Keeping those outputs in one theorem prevents consumers
from choosing unrelated soul points or radial charts.

Reference: Morgan--Tian, Theorem 2.7 and the discussion after Corollary 2.10,
pp. 25--27; Proposition 2.19 and Lemma 2.20, pp. 31--32.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M]
  {g : RiemannianMetric 3 M}

/- The region output is deliberately kept in the neck module's native form;
   this adapter only supplies the common point-soul and Euclidean witnesses. -/
theorem exists_neck_regions_of_pointSoulData
    (P : PointSoulData g) (N : EpsilonNeck g) :
    ∃ A B : Set M,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = N.central_sphereᶜ ∧
      frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
      N.region (-N.epsilon⁻¹) 0 ⊆ A ∧
      N.region 0 N.epsilon⁻¹ ⊆ B ∧
      ((IsCompact (closure A) ∧ ¬Bornology.IsBounded
          (P.euclidean.symm.toHomeomorph '' B)) ∨
        (IsCompact (closure B) ∧ ¬Bornology.IsBounded
          (P.euclidean.symm.toHomeomorph '' A))) ∧
      (∀ r : ℝ, 0 < r →
        IsConnected (distanceSphere g P.center r) ∧
        IsCompact (distanceSphere g P.center r)) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        IsConnected (distanceAnnulus g P.center a b) ∧
        IsCompact (distanceAnnulus g P.center a b)) := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos,
      hbounded⟩ := N.exists_ambient_complementary_regions
    P.euclidean.symm.toHomeomorph
  have hside :
      (IsCompact (closure A) ∧ ¬Bornology.IsBounded
          (P.euclidean.symm.toHomeomorph '' B)) ∨
        (IsCompact (closure B) ∧ ¬Bornology.IsBounded
          (P.euclidean.symm.toHomeomorph '' A)) := by
    rcases hbounded with ⟨hAb, hBu⟩ | ⟨hBb, hAu⟩
    · exact Or.inl ⟨EpsilonNeck.compact_closure_of_bounded_image
        P.euclidean.symm.toHomeomorph hAb, hBu⟩
    · exact Or.inr ⟨EpsilonNeck.compact_closure_of_bounded_image
        P.euclidean.symm.toHomeomorph hBb, hAu⟩
  refine ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos,
    hside, ?_, ?_⟩
  · intro r hr
    exact ⟨P.radial.isConnected_distanceSphere hr,
      P.radial.isCompact_distanceSphere hr⟩
  · intro a b ha hab
    exact ⟨P.radial.isConnected_distanceAnnulus ha hab,
      P.radial.isCompact_distanceAnnulus ha⟩

/-- The neck region package follows directly from the original positive-
curvature hypotheses, with no chosen soul or separation premise added. -/
theorem exists_neck_regions_of_strictlyPositiveSectionalCurvature
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature)
    (N : EpsilonNeck g) :
    ∃ P : PointSoulData g, ∃ A B : Set M,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = N.central_sphereᶜ ∧
      frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
      N.region (-N.epsilon⁻¹) 0 ⊆ A ∧
      N.region 0 N.epsilon⁻¹ ⊆ B ∧
      ((IsCompact (closure A) ∧ ¬Bornology.IsBounded
          (P.euclidean.symm.toHomeomorph '' B)) ∨
        (IsCompact (closure B) ∧ ¬Bornology.IsBounded
          (P.euclidean.symm.toHomeomorph '' A))) ∧
      (∀ r : ℝ, 0 < r →
        IsConnected (distanceSphere g P.center r) ∧
        IsCompact (distanceSphere g P.center r)) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        IsConnected (distanceAnnulus g P.center a b) ∧
        IsCompact (distanceAnnulus g P.center a b)) := by
  obtain ⟨P⟩ := exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    g D hcomplete hpos
  obtain ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos',
      hside, hspheres, hannuli⟩ := exists_neck_regions_of_pointSoulData P N
  exact ⟨P, A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos',
    hside, hspheres, hannuli⟩

/-- The checked point-soul producer can be fixed before choosing a shrinking
neck sequence.  This is the common package consumed by the noncompact
small-neck argument: every neck has ambient sides and radial sphere/annulus
data for the same soul, while the entire carriers escape compact sets. -/
theorem exists_escaping_neck_regions_of_no_scale_lower_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature) (ε : ℝ)
    (hsmall : ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ N : EpsilonNeck g, N.epsilon = ε → ρ ≤ N.scale) :
    ∃ (P : PointSoulData g) (N : ℕ → EpsilonNeck g),
      (∀ i, (N i).epsilon = ε) ∧
      Tendsto (fun i => (N i).scale) atTop (𝓝 0) ∧
      (∀ K : Set M, IsCompact K →
        ∀ᶠ i in atTop, Disjoint (N i).carrier K) ∧
      ∀ i, ∃ A B : Set M,
        IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = (N i).central_sphereᶜ ∧
        frontier A = (N i).central_sphere ∧
        frontier B = (N i).central_sphere ∧
        (N i).region (-(N i).epsilon⁻¹) 0 ⊆ A ∧
        (N i).region 0 (N i).epsilon⁻¹ ⊆ B ∧
        ((IsCompact (closure A) ∧ ¬Bornology.IsBounded
            (P.euclidean.symm.toHomeomorph '' B)) ∨
          (IsCompact (closure B) ∧ ¬Bornology.IsBounded
            (P.euclidean.symm.toHomeomorph '' A))) ∧
        (∀ r : ℝ, 0 < r →
          IsConnected (distanceSphere g P.center r) ∧
          IsCompact (distanceSphere g P.center r)) ∧
        (∀ a b : ℝ, 0 < a → a ≤ b →
          IsConnected (distanceAnnulus g P.center a b) ∧
          IsCompact (distanceAnnulus g P.center a b)) := by
  obtain ⟨P⟩ := exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    g D hcomplete hpos
  obtain ⟨N, hε, hscale, _⟩ :=
    EpsilonNeck.exists_escaping_neck_sequence_of_no_scale_lower_bound
      D ε hsmall
  refine ⟨P, N, hε, hscale, fun K hK =>
    EpsilonNeck.eventually_disjoint_carrier_compact_of_scale_tendsto_zero
      D N hε hscale hK, ?_⟩
  intro i
  exact exists_neck_regions_of_pointSoulData P (N i)

end PoincareMT.RiemannianMetric
