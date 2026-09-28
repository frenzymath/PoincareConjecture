import PoincareConjecture.Proofs.M25.Topology3D.Plane.Tube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubePolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PolygonGraph
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_curve_inscribed_normal_graph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun x : ℝ × sphere (0 : E) 1 => c x.1 x.2))
    {a b : ℝ} (hab : a ≤ b) (hi : ∀ z ∈ Icc a b, Injective (c z))
    (hm : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z) q)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℝ, 0 < m ∧ ∃ w : ℝ, 0 < w ∧ w < 1 ∧
      ∃ T : OpenPartialHomeomorph (ℝ × E) (ℝ × E),
        T.source = Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w} ∧
        (∀ x : ℝ × E, T x = (x.1, curveAnnularExtension o q0 c x)) ∧
        ContDiffOn ℝ ∞ T T.source ∧ ContDiffOn ℝ ∞ T.symm T.target ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ s : Fin (n + 1) → ℝ,
          StrictMono s ∧ s 0 = 0 ∧ s (Fin.last n) = 2 * Real.pi ∧
          (∀ i : Fin n, s i.succ - s i.castSucc < ε) ∧
          ∃ h : Icc (a - m / 2) (b + m / 2) × sphere (0 : E) 1 → ℝ,
            Continuous h ∧ ∀ z : Icc (a - m / 2) (b + m / 2),
              IsSimplePolygon (inscribedPolygon (fun t => c z (sphereCircleParameter e t)) s) ∧
              (∀ q, |h (z, q)| < w) ∧
              (inscribedPolygon (fun t => c z (sphereCircleParameter e t)) s).boundary ℝ =
                range (fun q => c z q + h (z, q) •
                  curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) ∧
              ∀ q,
                let y := c z q + h (z, q) •
                  curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))
                curveTubeProjection q0 T (z, y) = q ∧
                  curveTubeHeight T (z, y) = h (z, q) := by
  obtain ⟨m, hm0, w, hw0, hw1, T, hs, hT, hfwd, hInv⟩ :=
    exists_curveAnnularTube o q0 c hc hab hi hm
  let K := Icc (a - m / 2) (b + m / 2)
  have hK : IsCompact K := isCompact_Icc
  have htime : ∀ z ∈ K, z ∈ Ioo (a - m) (b + m) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzero : ∀ z ∈ K, ∀ q : sphere (0 : E) 1,
      (z, c z q) ∈ T.target ∧ curveTubeProjection q0 T (z, c z q) = q := by
    intro z hz q
    have h := curveAnnularTube_coordinates_apply o q0 c T hw1 hs hT z (htime z hz) q
      (r := 0) (by simpa only [abs_zero] using hw0)
    simp only [zero_smul, add_zero] at h
    exact ⟨h.1, h.2.1⟩
  have hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0 :=
    fun y hy => (curveAnnularTube_coordinates o q0 c T hw1 hs hT hy).1
  let Γ : ℝ × ℝ → E := fun x => c x.1 (sphereCircleParameter e x.2)
  have hΓ : ContDiff ℝ ∞ Γ := contDiff_curveFamily_circleParameter e c hc
  let d : ℝ → ℝ → E := fun z t => fderiv ℝ Γ (z, t) (0, 1)
  have hdcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2) :=
    ((hΓ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hd : ∀ z t, HasDerivAt (fun t => Γ (z, t)) (d z t) t := by
    intro z t
    exact (hΓ.differentiable (by simp) (z, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  have hproj : ∀ z ∈ K, ∀ t : ℝ,
      curveTubeProjection q0 T (z, Γ (z, t)) = sphereCircleParameter e t :=
    fun z hz t => (hzero z hz (sphereCircleParameter e t)).2
  have hloop : ∀ z ∈ K, Γ (z, 2 * Real.pi) = Γ (z, 0) := by
    intro z _
    exact congrArg (c z) (periodic_sphereCircleParameter e).eq
  obtain ⟨n, hn, s, hsm, hs0, hsN, hmesh, hpoly⟩ :=
    exists_uniform_inscribed_tube_polygons e q0 T hInv hx hK hΓ.continuous.continuousOn
      (fun z _ t _ => hd z t) hdcont.continuousOn
      (fun z hz t _ => (hzero z hz (sphereCircleParameter e t)).1) hproj hloop hε
  let p : ℝ → Polygon E n := fun z => inscribedPolygon (fun t => Γ (z, t)) s
  have hp : ∀ i : Fin n, ContinuousOn (fun z => p z i) K := by
    intro i
    exact (hΓ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨h, hh, hgraph⟩ := exists_continuous_polygon_family_normal_graph o q0 c T hw1 hs hT
    hInv hK p hp (fun z hz y hy => (hpoly z hz).2.1 hy) (fun z hz => (hpoly z hz).2.2)
  refine ⟨m, hm0, w, hw0, hw1, T, hs, hT, hfwd, hInv, n, hn, s, hsm,
    hs0, hsN, hmesh, h, hh, ?_⟩
  intro z
  exact ⟨(hpoly z z.2).1, hgraph z⟩

end PoincareConjecture.M25.Topology3D
