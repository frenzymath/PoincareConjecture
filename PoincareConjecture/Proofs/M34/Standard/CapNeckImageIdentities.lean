import PoincareConjecture.Proofs.M34.Standard.CapNeckImage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X} (N : EpsilonNeck g)
  (e : OpenPartialHomeomorph M X)
  (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  {epsilon c r : ℝ} (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1 / 2)
  (hdom : Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆
    Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
  (hsource : N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆ e.source)
  (D : LeviCivitaData h) (q₀ : UnitTwoSphere) (hr : 0 < r)
  (hscalar : 0 < D.scalarCurvature (e (N.coordinate_map (q₀, c))))
  (hscale : r = D.scalarCurvature (e (N.coordinate_map (q₀, c))) ^ (-1 / 2 : ℝ))
  (hclose : RoundCylinderClose epsilon 0 (fun z v w => r⁻¹ ^ 2 *
    roundCylinderPullback h (fun z => e (N.coordinate_map (z.1, z.2 + c))) z v w))

local notation "Nimage" =>
  N.imageShift e hf hi hepsilon hepsilon' hdom hsource D q₀ hr hscalar hscale hclose

theorem imageShift_data :
    (Nimage).epsilon = epsilon ∧ (Nimage).scale = r ∧
      (Nimage).center = e (N.coordinate_map (q₀, c)) ∧ (Nimage).connection = D ∧
      (Nimage).carrier = e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ∧
      (Nimage).central_sphere = e '' (N.coordinate_map '' (univ ×ˢ ({c} : Set ℝ))) ∧
      (Nimage).coordinate_map = fun z => e (N.coordinate_map (z.1, z.2 + c)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem imageShift_region (a b : ℝ) (ha : -epsilon⁻¹ ≤ a) (hb : b ≤ epsilon⁻¹) :
    (Nimage).region a b = e '' N.region (a + c) (b + c) := by
  ext x
  change (x ∈ e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ∧
    a < (N.coordinate_inverse (e.symm x)).2 - c ∧
      (N.coordinate_inverse (e.symm x)).2 - c < b) ↔ _
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hlo, hhi⟩
    rw [e.left_inv (hsource hy)] at hlo hhi
    refine ⟨y, ⟨hy.1, ?_, ?_⟩, rfl⟩ <;> linarith
  · rintro ⟨y, hy, rfl⟩
    have hwindow : y ∈ N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) := by
      refine ⟨hy.1, ?_, ?_⟩ <;> linarith [hy.2.1, hy.2.2]
    refine ⟨⟨y, hwindow, rfl⟩, ?_⟩
    rw [e.left_inv (hsource hwindow)]
    constructor <;> linarith [hy.2.1, hy.2.2]

theorem imageShift_carrier_leftAnchored (hc : c = epsilon⁻¹ - N.epsilon⁻¹) :
    (Nimage).carrier = e '' N.region (-N.epsilon⁻¹) (2 / epsilon - N.epsilon⁻¹) := by
  change e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) = _
  rw [hc]
  congr 2
  all_goals
    try simp only [div_eq_mul_inv]
    ring

theorem imageShift_negative_leftAnchored (hc : c = epsilon⁻¹ - N.epsilon⁻¹) :
    (Nimage).region (-epsilon⁻¹) (-epsilon⁻¹ / 2) =
      e '' N.region (-N.epsilon⁻¹) (1 / (2 * epsilon) - N.epsilon⁻¹) := by
  have hregion := N.imageShift_region e hf hi hepsilon hepsilon' hdom hsource
    D q₀ hr hscalar hscale hclose (-epsilon⁻¹) (-epsilon⁻¹ / 2) le_rfl
    (by linarith [inv_pos.mpr hepsilon])
  rw [hregion, hc]
  congr 2
  all_goals
    try simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem imageShift_zero_sets (hc : c = 0) (he : epsilon = N.epsilon) :
    (Nimage).carrier = e '' N.carrier ∧
      (Nimage).central_sphere = e '' N.central_sphere := by
  change e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) = e '' N.carrier ∧
    e '' (N.coordinate_map '' (univ ×ˢ ({c} : Set ℝ))) = e '' N.central_sphere
  rw [hc, he]
  simp only [add_zero]
  constructor
  · congr 1
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (N.coordinate_inverse_mem x hx).2⟩⟩
  · rw [N.central_sphere_eq]

end PoincareConjecture.EpsilonNeck
