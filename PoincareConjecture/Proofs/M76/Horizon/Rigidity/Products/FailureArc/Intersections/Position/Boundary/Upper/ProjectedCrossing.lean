import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.PeriodicCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.exists_original_projected_crossing_patch
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S C₀ C₁ : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (A : P2 ≃ᴬ[ℝ] P2) {U : Set P2} (hU : IsOpen U) (hAU : A 0 ∈ U)
    (haxis₀ : ∀ z, ∀ _ : A z ∈ U,
      (h (((A z).1 : AddCircle p), ((A z).2 : AddCircle p)) : X) ∈ C₀ ↔ z.2 = 0)
    (haxis₁ : ∀ z, ∀ _ : A z ∈ U,
      (h (((A z).1 : AddCircle p), ((A z).2 : AddCircle p)) : X) ∈ C₁ ↔ z.1 = 0) :
    ∃ d : ℝ, 0 < d ∧ ∃ u : P2 → X,
      PolyhedralPLInCharts e u (Icc (-d) d ×ˢ Icc (-d) d) ∧
      InjOn u (Icc (-d) d ×ˢ Icc (-d) d) ∧
      MapsTo u (Icc (-d) d ×ˢ Icc (-d) d) S ∧
      u 0 = (h (((A 0).1 : AddCircle p), ((A 0).2 : AddCircle p)) : X) ∧
      (∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d, u z ∈ C₀ ↔ z.2 = 0) ∧
      ∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d, u z ∈ C₁ ↔ z.1 = 0 := by
  have hp : 0 < p := Fact.out
  let Q := (AddCircle.openPartialHomeomorphCoe p ((A 0).1 - p / 2)).prod
    (AddCircle.openPartialHomeomorphCoe p ((A 0).2 - p / 2))
  have hAQ : A 0 ∈ Q.source := by
    change ((A 0).1 ∈ Ioo ((A 0).1 - p / 2) ((A 0).1 - p / 2 + p)) ∧
      ((A 0).2 ∈ Ioo ((A 0).2 - p / 2) ((A 0).2 - p / 2 + p))
    constructor <;> constructor <;> linarith
  have hopen : IsOpen (A ⁻¹' (U ∩ Q.source)) :=
    (hU.inter Q.open_source).preimage A.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨hAU, hAQ⟩
  let d := ε / 2
  have hd : 0 < d := half_pos hε
  have hbox (z : P2) (hz : z ∈ Icc (-d) d ×ˢ Icc (-d) d) : A z ∈ U ∩ Q.source := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, max_lt_iff]
    exact ⟨(abs_le.mpr hz.1).trans_lt (half_lt_self hε),
      (abs_le.mpr hz.2).trans_lt (half_lt_self hε)⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show -d < d by linarith)).prod
      (isFinitePLBallPair_Icc (show -d < d by linarith))
  let u (z : P2) : X := h (((A z).1 : AddCircle p), ((A z).2 : AddCircle p))
  have hu : PolyhedralPLInCharts e u (Icc (-d) d ×ˢ Icc (-d) d) := by
    rw [← hJs]
    exact M.polyhedralPL_periodic_comp H F hF hFval h hvalue J hJ
      ((J.affineOnFaces_affine A.toContinuousAffineMap).finitePiecewiseAffineOn hJ)
  refine ⟨d, hd, u, hu, ?_, fun _ _ => (h _).property, rfl, ?_, ?_⟩
  · intro z hz w hw heq
    apply A.injective
    apply Q.injOn (hbox z hz).2 (hbox w hw).2
    exact h.injective (Subtype.ext heq)
  · intro z hz
    exact haxis₀ z (hbox z hz).1
  · intro z hz
    exact haxis₁ z (hbox z hz).1

end PoincareConjecture.M76.PeriodicSquare
