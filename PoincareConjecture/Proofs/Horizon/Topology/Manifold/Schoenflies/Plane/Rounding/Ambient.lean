import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Graph.Realization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.UniformRoundedSamples
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Tube.Tube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]



theorem exists_ambient_rounded_polygon_of_smooth_circle
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    (c : sphere (0 : E) 1 → E)
    (hc : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ c) :
    ∃ n : ℕ, ∃ p : Polygon E (n + 3), IsSimplePolygon p ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) →
        (∀ s, |deriv ρ s| ≤ 1) →
        ∃ F : E ≃ₘ[ℝ] E,
          (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
          F '' range c = range (roundedPolygonParameter ρ p) := by
  let q0 := sphereCircleParameter e 0
  have hfamily : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.2) := hc.contMDiff.comp contMDiff_snd
  have hmi (q : sphere (0 : E) 1) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) c q) :=
    (hc.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp)
  obtain ⟨m, hm, w, hw, hw1, T, hs, he, hfwd, hInv⟩ :=
    exists_curveAnnularTube o q0 (fun _ => c) hfamily (a := 0) (b := 0) le_rfl
      (fun _ _ => hc.isEmbedding.injective) (fun _ _ q => hmi q)
  have hs' : T.source = Ioo (-m) m ×ˢ {x : E | |‖x‖ - 1| < w} := by simpa using hs
  have hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0 :=
    fun y hy => (curveAnnularTube_coordinates o q0 (fun _ => c) T hw1 hs' he hy).1
  let γ : ℝ → E := fun s => c (sphereCircleParameter e s)
  have hγ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.2) :=
    contDiff_curveFamily_circleParameter e (fun _ => c) hfamily
  have hper : Periodic γ (2 * Real.pi) := by
    intro s
    exact congrArg c (periodic_sphereCircleParameter e s)
  have hcoord (q : sphere (0 : E) 1) :
      (0, c q) ∈ T.target ∧ curveTubeProjection q0 T (0, c q) = q ∧
        curveTubeHeight T (0, c q) = 0 := by
    simpa only [zero_smul, add_zero] using
      curveAnnularTube_coordinates_apply o q0 (fun _ => c) T hw1 hs' he 0
        ⟨neg_neg_of_pos hm, hm⟩ q (r := 0) (by simpa using hw)
  obtain ⟨N, hN, hstep, _, hsimple, hround⟩ :=
    exists_uniform_rounded_tube_samples e q0 T hInv hx (K := {0}) isCompact_singleton
      (fun _ => γ) hγ (fun _ => hper)
      (fun z hz s _ => by
        have hz0 : z = 0 := hz
        subst z
        exact (hcoord _).1)
      (fun z hz s => by
        have hz0 : z = 0 := hz
        subst z
        exact (hcoord _).2.1)
      (fun z hz s _ => by
        have hz0 : z = 0 := hz
        subst z
        exact (hcoord _).2.2)
      (A := w / 2) (ε := 1) (by positivity) zero_lt_one
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  let h : ℝ := 2 * Real.pi / (n + 3 : ℕ)
  let p := inscribedPolygon γ (fun i : Fin (n + 3 + 1) => h * (i.val : ℝ))
  refine ⟨n, p, hsimple 0 (by simp), ?_⟩
  intro δ hδ hδhalf ρ hρ htail hbound hder
  obtain ⟨hG, hGper, hGgood⟩ := hround δ hδ hδhalf ρ hρ htail hbound hder
  let G : ℝ → E := fun s => roundedVertexPath ρ (fun j : ℤ => γ (h * (j : ℝ))) (s / h)
  have hG' : ContDiff ℝ ∞ G := hG.comp
    (f := fun s : ℝ => ((0 : ℝ), s)) (contDiff_const.prodMk contDiff_id)
  have hGper' : Periodic G (2 * Real.pi) := hGper 0
  obtain ⟨F, hK, hF⟩ := exists_ambient_diffeomorph_of_positive_tube_projection
    e o q0 c T hw1 hs' he hfwd hInv (neg_neg_of_pos hm) hm
      (show w / 2 < w by linarith) G hG' hGper'
      (fun s hs => (hGgood 0 (by simp) s hs).1)
      (fun s hs => (hGgood 0 (by simp) s hs).2.1)
      (fun s hs => (hGgood 0 (by simp) s hs).2.2)
  refine ⟨F, hK, hF.trans ?_⟩
  have hperiod : h * ((n + 3 : ℕ) : ℝ) = 2 * Real.pi :=
    div_mul_cancel₀ _ (by positivity)
  have hparam := roundedPolygonParameter_inscribed_uniform ρ γ h (hperiod.symm ▸ hper)
  change range G = range (roundedPolygonParameter ρ p)
  rw [show roundedPolygonParameter ρ p =
    roundedVertexPath ρ (fun j : ℤ => γ (h * (j : ℝ))) from hparam]
  apply Subset.antisymm
  · rintro y ⟨s, rfl⟩
    exact ⟨s / h, rfl⟩
  · rintro y ⟨s, rfl⟩
    refine ⟨s * h, ?_⟩
    change roundedVertexPath ρ (fun j : ℤ => γ (h * (j : ℝ))) (s * h / h) = _
    rw [mul_div_cancel_right₀ s hstep.ne']

end Poincare.Manifold.Schoenflies.Plane
