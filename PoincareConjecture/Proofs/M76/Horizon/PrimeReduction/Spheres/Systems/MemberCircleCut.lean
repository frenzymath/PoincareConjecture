import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereParameter
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSpherePolygonCut
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)





theorem ChartwisePLSphere.exists_parameter_circle_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    (hLP : L.boundary ℝ ⊆ P.space)
    (B : OpenPartialHomeomorph V3 P3) {w : V3}
    (hw : w ∈ B.source) (hBw : B w = 0)
    (hBS : ∀ x ∈ B.source, x ∈ P.space ↔ (B x).2 = 0)
    (hBL : ∀ x ∈ L.boundary ℝ ∩ B.source, (B x).1.1 = 0) :
    ∃ (g : V3 → V3) (m : ℕ) (R : Polygon V3 (m + 3)) (d₀ d₁ : Set V3),
      FinitePiecewiseAffineOn g P.space ∧ InjOn g P.space ∧
      MapsTo g P.space (sphere (0 : V3) 1) ∧
      Function.Injective R ∧ R.HasSimplicialEdges ∧
      R.boundary ℝ = g '' L.boundary ℝ ∧
      IsFinitePLBallPair (ℝ × ℝ) d₀ (R.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (R.boundary ℝ) ∧
      d₀ ∪ d₁ = sphere (0 : V3) 1 ∧ d₀ ∩ d₁ = R.boundary ℝ ∧
      PolyhedralPLInCharts e s.map d₀ ∧ PolyhedralPLInCharts e s.map d₁ ∧
      InjOn s.map (sphere (0 : V3) 1) ∧
      (s.map '' d₀) ∪ (s.map '' d₁) = S ∧
      (s.map '' d₀) ∩ (s.map '' d₁) = Q.symm '' L.boundary ℝ ∧
      (∀ x ∈ L.boundary ℝ, s.map (g x) = Q.symm x) := by
  classical
  obtain ⟨g, hg, hgS, hgi, hright, _, _⟩ :=
    s.exists_finite_clipped_parameter Q hQ J P hJ hJQ hP hPs
  obtain ⟨m, R, hRi, hR, hRb⟩ :=
    L.exists_polygon_finitePL_image hL hLi hg hLP (hgi.mono hLP)
  have hzero : (0 : P3) ∈ B.target := hBw ▸ B.map_source hw
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp B.open_target 0 hzero
  let z : P3 := ((ε / 2, 0), 0)
  have hz : z ∈ B.target := by
    apply hball
    change dist z 0 < ε
    simpa [z, dist_eq_norm, Prod.norm_def, abs_of_pos hε] using
      (show ε / 2 < ε ∧ 0 < ε from ⟨half_lt_self hε, hε⟩)
  have hxB : B.symm z ∈ B.source := B.map_target hz
  have hxP : B.symm z ∈ P.space := (hBS _ hxB).mpr (by rw [B.right_inv hz])
  have hxL : B.symm z ∉ L.boundary ℝ := by
    intro hx
    have hh := hBL _ ⟨hx, hxB⟩
    rw [B.right_inv hz] at hh
    exact (half_pos hε).ne' hh
  have hgr : g (B.symm z) ∉ R.boundary ℝ := by
    rw [hRb]
    rintro ⟨y, hy, heq⟩
    exact hxL ((hgi (hLP hy) hxP heq) ▸ hy)
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsphere : sphere (0 : V3) 1 = frontier (closedBall (0 : V3) 1) := by
    rw [frontier_closedBall _ one_ne_zero]
  have hRS : R.boundary ℝ ⊆ sphere (0 : V3) 1 := by
    rw [hRb]
    rintro _ ⟨x, hx, rfl⟩
    exact hgS (hLP hx)
  obtain ⟨d₀, d₁, hd₀, hd₁, hunion, hinter, _⟩ :=
    K.exists_convex_sphere_polygon_cut hK (isCompact_closedBall (0 : V3) 1)
      (convex_closedBall (0 : V3) 1)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hKs.trans hsphere) (by simp) R hR hRi (hRS.trans hsphere.subset)
      ⟨g (B.symm z), hsphere.subset (hgS hxP)⟩ hgr
  rw [← hsphere] at hunion
  have hd₀S : d₀ ⊆ sphere (0 : V3) 1 := subset_union_left.trans hunion.subset
  have hd₁S : d₁ ⊆ sphere (0 : V3) 1 := subset_union_right.trans hunion.subset
  have hphysical : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨y, hy⟩ := s.parametrization.surjective ⟨x, hx⟩
      exact ⟨y, y.property, (s.map_eq y).trans (congrArg Subtype.val hy)⟩
  have hsi : InjOn s.map (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x, hx⟩, s.map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hmaprim : s.map '' R.boundary ℝ = Q.symm '' L.boundary ℝ := by
    rw [hRb, image_image]
    exact image_congr (fun x hx => hright x (hLP hx))
  have hPL {d : Set V3} (hd : IsFinitePLBallPair (ℝ × ℝ) d (R.boundary ℝ))
      (hdS : d ⊆ sphere (0 : V3) 1) : PolyhedralPLInCharts e s.map d := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨D, hD, hDs, _⟩, _⟩, _⟩ := hd
    rw [← hDs]
    exact s.piecewiseAffine.restrict_finite D hD (hDs.subset.trans hdS)
  refine ⟨g, m, R, d₀, d₁, hg, hgi, hgS, hRi, hR, hRb, hd₀, hd₁,
    hunion, hinter, hPL hd₀ hd₀S, hPL hd₁ hd₁S, hsi, ?_, ?_,
    fun x hx => hright x (hLP hx)⟩
  · rw [← image_union, hunion, hphysical]
  · rw [← hsi.image_inter hd₀S hd₁S, hinter, hmaprim]

end PoincareConjecture.M76
