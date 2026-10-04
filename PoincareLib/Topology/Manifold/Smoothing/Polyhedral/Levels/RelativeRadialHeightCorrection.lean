import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.RadialHeightCorrection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.ConicalPlaneExtension

/-!
# Actual patches retained by radial correction and coning

The explicit correction ratio is one where the two heights
already agree. Affine uniqueness fixes complete supplied
subcomplexes, including zero-height faces. Cone homogeneity
then retains a supplied linear germ on its entire actual
cone. See Cairns 1940, pp. 801--802, Hudson 1969, pp. 15--19,
Alexander 1924, pp. 6--8 and M76 derivation 286e.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Positive radial height correction fixes every point of
a supplied subcomplex on whose vertices both heights already
agree. The explicit scale-one zero branch controls the whole
zero-height part as well. See Cairns pp. 801--802 and
M76 derivation 286e. -/
theorem exists_radial_height_correction_fixed_subcomplex
    (K L : SimplicialComplex ℝ E) (hLK : L ≤ K) (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hrad : InjOn (NormedSpace.normalize : E → E) K.space)
    (φ : E → ℝ) (hφ : K.AffineOnFaces φ) (B C : E →ₗ[ℝ] ℝ)
    (hC : K.RespectsAffineHyperplane C.toAffineMap)
    (hneg : ∀ x ∈ K.vertices, φ x < 0 ↔ B x < 0)
    (hpos : ∀ x ∈ K.vertices, 0 < φ x ↔ 0 < B x)
    (hφL : EqOn φ B L.vertices) :
    ∃ (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) (f : E → E)
      (e : K.space ≃ₜ (K.radialRescale hlin hrad r hr).space),
      K.AffineOnFaces f ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      EqOn f (fun x => r x • x) K.vertices ∧ e.IsFinitePL ∧
      (∀ x : K.space, B (e x) = φ x) ∧
      (∀ x : K.space, C (e x) = 0 ↔ C x = 0) ∧
      EqOn f id L.space := by
  obtain ⟨r, hr, f, e, hf, hef, hfv, he, hheight, hplane, hratio⟩ :=
    K.exists_radial_height_correction_with_ratio hK hlin hrad φ hφ B C hC hneg hpos
  have hfL : L.AffineOnFaces f := fun s hs => hf s (hLK hs)
  refine ⟨r, hr, f, e, hf, hef, hfv, he, hheight, hplane, ?_⟩
  apply hfL.eqOn_of_eqOn_vertices (L.affineOnFaces_affine (ContinuousAffineMap.id ℝ E))
  intro x hx
  rw [hfv (hLK hx)]
  change r x • x = x
  rw [hratio x]
  change (if B x = 0 then 1 else φ x / B x) • x = x
  by_cases hBx : B x = 0
  · rw [if_pos hBx, one_smul]
  · rw [if_neg hBx, hφL hx, div_self hBx, one_smul]

omit [FiniteDimensional ℝ E] in
/-- A cone-face affine map fixing zero retains any supplied
linear base germ throughout its complete actual cone.
No subcomplex condition or nonempty base is needed for this
pointwise conclusion. See Hudson pp. 15--19 and
M76 derivation 286e. -/
theorem AffineOnFaces.eqOn_linear_on_convexJoin_of_eqOn_base
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : SimplicialComplex ℝ E}
    {hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E)}
    {hrad : InjOn (NormedSpace.normalize : E → E) K.space}
    {g : E → F} (hg : (K.coneAtZero hlin hrad).AffineOnFaces g) (hg0 : g 0 = 0)
    (T : E →ₗ[ℝ] F) {P : Set E} (hPK : P ⊆ K.space) (hbase : EqOn g T P) :
    EqOn g T (convexJoin ℝ {0} P) := by
  intro x hx
  obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff P x).mp hx
  rw [hxy, hg.smul_on_cone hg0 y (hPK hy) r hr, hbase hy, map_smul]

end Geometry.SimplicialComplex
