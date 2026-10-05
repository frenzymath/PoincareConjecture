import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ZeroChargeLinkDegree
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderBaseLinkSection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.CompactConnectedHeightSign

/-!
# Actual extrema at isolated zero-section points

Empty local-link zero section and link connectedness force one
strict height sign on the entire star off its center. The finite
carrier neighborhood gives a strict local extremum without any
generic vertex-height premise. See Alexander 1924, pp. 6--8 and
M76 derivation 268.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- An isolated zero section and connected actual link force
one uniform signed link gap and a strict sign at every other
star point. See Alexander pp. 6--8 and M76 derivation 268. -/
theorem exists_signed_link_gap_of_isolated_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (L : E →ₗ[ℝ] ℝ)
    (hconn : (K.link 0).vertexAbstractComplex.edgeGraph.Connected)
    (hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {y | L y = 0} → x = 0) :
    ∃ η : ℝ, 0 < η ∧
      (((∀ y ∈ (K.link 0).space, η ≤ L y) ∧
        ∀ x ∈ (K.closedStar 0).space, x ≠ 0 → 0 < L x) ∨
       ((∀ y ∈ (K.link 0).space, L y ≤ -η) ∧
        ∀ x ∈ (K.closedStar 0).space, x ≠ 0 → L x < 0)) := by
  have hempty := K.link_zero_eq_empty_of_isolated_section L hlocal
  have hnonzero (y : E) (hy : y ∈ (K.link 0).space) : L y ≠ 0 :=
    fun hyL => (hempty.subset ⟨hy, hyL⟩).elim
  have hcompact := (K.link 0).isCompact_space_of_finite (finite_link_faces hK 0)
  have hconnected := ((K.link 0).isPathConnected_space_of_connected_edgeGraph hconn).isConnected
  obtain ⟨η, hη, hpositive | hnegative⟩ := hcompact.exists_uniform_height_sign hconnected
    L.continuous_of_finiteDimensional.continuousOn hnonzero
  · refine ⟨η, hη, Or.inl ⟨hpositive, ?_⟩⟩
    intro x hx hx0
    obtain ⟨y, hy, r, hr, hxy⟩ := exists_linkPoint_smul hx hx0
    rw [hxy, map_smul, smul_eq_mul]
    exact mul_pos hr.1 (hη.trans_le (hpositive y hy))
  · refine ⟨η, hη, Or.inr ⟨hnegative, ?_⟩⟩
    intro x hx hx0
    obtain ⟨y, hy, r, hr, hxy⟩ := exists_linkPoint_smul hx hx0
    rw [hxy, map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hr.1 ((hnegative y hy).trans_lt (neg_neg_of_pos hη))

/-- The actual carrier has a strict local minimum or maximum
at an isolated zero-section vertex with connected link.
This does not assert a global sphere filling. See Alexander
pp. 6--8 and M76 derivation 268. -/
theorem exists_ball_strict_extremum_of_isolated_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (hconn : (K.link 0).vertexAbstractComplex.edgeGraph.Connected)
    (hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {y | L y = 0} → x = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ((∀ x ∈ K.space ∩ Metric.ball 0 ε, x ≠ 0 → 0 < L x) ∨
       (∀ x ∈ K.space ∩ Metric.ball 0 ε, x ≠ 0 → L x < 0)) := by
  obtain ⟨ε, hε, hnear⟩ := K.exists_ball_inter_space_subset_closedStar hK hzero
  obtain ⟨_, _, ⟨_, hpos⟩ | ⟨_, hneg⟩⟩ :=
    K.exists_signed_link_gap_of_isolated_section hK L hconn hlocal
  · exact ⟨ε, hε, Or.inl (fun x hx hx0 => hpos x (hnear hx) hx0)⟩
  · exact ⟨ε, hε, Or.inr (fun x hx hx0 => hneg x (hnear hx) hx0)⟩

end Geometry.SimplicialComplex
