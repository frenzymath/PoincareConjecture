import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicCircle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicTubeAngle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicFiber
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Graph.GraphTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

theorem exists_smooth_normal_graph_of_positive_tube_projection
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    (q0 : sphere (0 : E) 1) (c : sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L U w A : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L U ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E,
      T p = (p.1, curveAnnularExtension o q0 (fun _ => c) p))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (γ : ℝ → E) (hγ : ContDiff ℝ ∞ γ) (hper : Periodic γ (2 * Real.pi))
    (hdom : ∀ s ∈ Icc 0 (2 * Real.pi),
      ((0, s), γ s) ∈ curveTubeAngularDomain e q0 T)
    (hpos : ∀ s ∈ Icc 0 (2 * Real.pi), 0 < fderiv ℝ
      (fun y : E => curveTubeAngle e q0 T ((0, s), y)) (γ s) (deriv γ s))
    (hbound : ∀ s ∈ Icc 0 (2 * Real.pi), |curveTubeHeight T (0, γ s)| < A) :
    ∃ g : sphere (0 : E) 1 → ℝ,
      ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ g ∧ (∀ q, |g q| < A) ∧
      range γ = range (fun q => c q + g q •
        curveFamilyNormal o (radialFamilyExtension q0 (fun _ => c)) (0, (q : E))) := by
  have hτ : 0 < 2 * Real.pi := by positivity
  have hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0 :=
    fun y hy => (curveAnnularTube_coordinates o q0 (fun _ => c) T hw hs he hy).1
  have hreduce (s : ℝ) : ∃ m : ℤ,
      s - (m : ℝ) * (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := by
    let m : ℤ := ⌊s / (2 * Real.pi)⌋
    have hlo : (m : ℝ) * (2 * Real.pi) ≤ s := (le_div_iff₀ hτ).mp (Int.floor_le _)
    have hhi : s < ((m : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one _)
    exact ⟨m, ⟨by linarith, by nlinarith⟩⟩
  have hdomAll (s : ℝ) : ((0, s), γ s) ∈ curveTubeAngularDomain e q0 T := by
    obtain ⟨m, hm⟩ := hreduce s
    have hphase : Circle.exp (-(s - (m : ℝ) * (2 * Real.pi))) = Circle.exp (-s) := by
      rw [show -(s - (m : ℝ) * (2 * Real.pi)) = -s + (m : ℝ) * (2 * Real.pi) by ring]
      exact Circle.periodic_exp.int_mul m (-s)
    have h := hdom (s - (m : ℝ) * (2 * Real.pi)) hm
    simpa only [curveTubeAngularDomain, mem_ofPred_eq, hper.sub_int_mul_eq m, hphase] using h
  have hboundAll (s : ℝ) : |curveTubeHeight T (0, γ s)| < A := by
    obtain ⟨m, hm⟩ := hreduce s
    simpa only [hper.sub_int_mul_eq m] using hbound _ hm
  have hprops := curveTubeAngle_lift_properties e q0 T hInv hx
    (K := {0}) (fun _ => γ) (hγ.comp contDiff_snd) (fun _ => hper)
    (fun z hz s hs => by
      have hz0 : z = 0 := hz
      subst z
      exact hdom s hs)
    (fun z hz s hs => by
      have hz0 : z = 0 := hz
      subst z
      exact hpos s hs)
  let α : ℝ → ℝ := fun s => curveTubeAngle e q0 T ((0, s), γ s)
  obtain ⟨hV, hangle⟩ := curveTubeAngle_regular e q0 T hInv hx
  have hα : ContDiff ℝ ∞ α := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact (hangle.contDiffAt (hV.mem_nhds (hdomAll s))).comp s
      (f := fun t => ((0, t), γ t))
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk hγ.contDiffAt)
  have hαper (s : ℝ) : α (s + 2 * Real.pi) = α s + 2 * Real.pi := by
    change circleAngularCoordinate e
      (s + 2 * Real.pi, (curveTubeProjection q0 T (0, γ (s + 2 * Real.pi)) : E)) = _
    rw [hper s]
    simpa only [Int.cast_one, one_mul, α, curveTubeAngle] using
      circleAngularCoordinate_add_int_period e s
        (curveTubeProjection q0 T (0, γ s) : E) 1
  have hαpos (s : ℝ) : 0 < deriv α s := by
    exact hprops.2.2 0 (by simp) s
  obtain ⟨B, hB, hBi⟩ := exists_smooth_inverse_of_add_period
    (V := ℝ) hτ (hα.comp contDiff_snd) (fun _ s => hαper s) (fun _ s => hαpos s)
  let β : ℝ → ℝ := fun s => B (0, s)
  have hβ : ContDiff ℝ ∞ β := hB.comp (contDiff_const.prodMk contDiff_id)
  have hαβ (s : ℝ) : α (β s) = s := (hBi 0 s).1
  have hβα (s : ℝ) : β (α s) = s := (hBi 0 s).2.1
  have hβper (s : ℝ) : β (s + 2 * Real.pi) = β s + 2 * Real.pi := (hBi 0 s).2.2
  let H : ℝ → ℝ := fun s => curveTubeHeight T (0, γ (β s))
  have hH : ContDiff ℝ ∞ H := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact ((contDiffOn_curveTubeHeight T hInv hx).contDiffAt
      (T.open_target.mem_nhds (hdomAll (β s)).1)).comp s
        (contDiffAt_const.prodMk (hγ.comp hβ).contDiffAt)
  have hHper : Periodic H (2 * Real.pi) := by
    intro s
    change curveTubeHeight T (0, γ (β (s + 2 * Real.pi))) = _
    rw [hβper, hper (β s)]
  let g : sphere (0 : E) 1 → ℝ := periodicCircleCurve (2 * Real.pi) e H
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ g := by
    have h := contMDiff_periodicCircleCurve_family (V := ℝ) hτ e
      (fun _ => H) (hH.comp contDiff_snd) (fun _ => hHper)
    have hj : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
        (fun q : sphere (0 : E) 1 => ((0 : ℝ), q)) :=
      contMDiff_const.prodMk contMDiff_id
    exact h.comp (f := fun q : sphere (0 : E) 1 => ((0 : ℝ), q)) hj
  have hgbound (q : sphere (0 : E) 1) : |g q| < A := hboundAll _
  have hgparam (s : ℝ) : g (sphereCircleParameter e s) = H s := by
    simpa only [div_self hτ.ne', one_mul] using
      periodicCircleCurve_sphereCircleParameter hτ e hHper s
  have hproj (s : ℝ) : curveTubeProjection q0 T (0, γ (β s)) =
      sphereCircleParameter e s := by
    rw [← sphereCircleParameter_curveTubeAngle e q0 T ((0, β s), γ (β s))]
    change sphereCircleParameter e (α (β s)) = sphereCircleParameter e s
    rw [hαβ]
  have hformula (s : ℝ) : γ (β s) = c (sphereCircleParameter e s) +
      g (sphereCircleParameter e s) •
        curveFamilyNormal o (radialFamilyExtension q0 (fun _ => c))
          (0, (sphereCircleParameter e s : E)) := by
    have h := (curveAnnularTube_coordinates o q0 (fun _ => c) T hw hs he
      (hdomAll (β s)).1).2.2.2.2
    simpa only [hproj, hgparam, H] using h
  refine ⟨g, hg, hgbound, Subset.antisymm ?_ ?_⟩
  · rintro y ⟨s, rfl⟩
    exact ⟨sphereCircleParameter e (α s),
      (hformula (α s)).symm.trans (congrArg γ (hβα s))⟩
  · rintro y ⟨q, rfl⟩
    obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
    exact ⟨β s, hformula s⟩

theorem exists_ambient_diffeomorph_of_positive_tube_projection
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2))
    (q0 : sphere (0 : E) 1) (c : sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L U w A : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L U ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E,
      T p = (p.1, curveAnnularExtension o q0 (fun _ => c) p))
    (hfwd : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hL : L < 0) (hU : 0 < U) (hAw : A < w)
    (γ : ℝ → E) (hγ : ContDiff ℝ ∞ γ) (hper : Periodic γ (2 * Real.pi))
    (hdom : ∀ s ∈ Icc 0 (2 * Real.pi),
      ((0, s), γ s) ∈ curveTubeAngularDomain e q0 T)
    (hpos : ∀ s ∈ Icc 0 (2 * Real.pi), 0 < fderiv ℝ
      (fun y : E => curveTubeAngle e q0 T ((0, s), y)) (γ s) (deriv γ s))
    (hbound : ∀ s ∈ Icc 0 (2 * Real.pi), |curveTubeHeight T (0, γ s)| < A) :
    ∃ F : E ≃ₘ[ℝ] E,
      (∃ K : Set E, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      F '' range c = range γ := by
  obtain ⟨g, hg, hgbound, heq⟩ :=
    exists_smooth_normal_graph_of_positive_tube_projection e o q0 c T hw hs he hInv
      γ hγ hper hdom hpos hbound
  obtain ⟨F, _, _, ⟨K, hK, hfix⟩, _, hF⟩ :=
    exists_curveAnnularTube_graph_transport o q0 (fun _ => c) T hw hs he hfwd hInv
      (a := 0) (b := 0) hL hU hAw (fun p => g p.2) (hg.comp contMDiff_snd)
      (fun p => hgbound p.2)
  refine ⟨F 0, ⟨K, hK, fun x hx => (hfix 0 x hx).1⟩, ?_⟩
  rw [← range_comp, heq]
  congr 1
  funext q
  exact hF 0 (by simp) q

end Poincare.Manifold.Schoenflies.Plane
