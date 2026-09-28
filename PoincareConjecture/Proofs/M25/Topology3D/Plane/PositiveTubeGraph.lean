import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicTubeAngle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.LocalPeriodicInverse
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicCircle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.GraphTransport










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_smooth_normal_graph_of_positive_tube_projection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L0 U0 L U w a b A : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L0 U0 ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E, T p = (p.1, curveAnnularExtension o q0 c p))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (_hL : L0 ≤ L) (_hU : U ≤ U0) (ha : L < a) (hb : b < U) (hA : 0 < A)
    (γ : ℝ → ℝ → E) (hγ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.1 p.2))
    (hper : ∀ z, Periodic (γ z) (2 * Real.pi))
    (hdom : ∀ z ∈ Ioo L U, ∀ s ∈ Icc 0 (2 * Real.pi),
      ((z, s), γ z s) ∈ curveTubeAngularDomain e q0 T)
    (hpos : ∀ z ∈ Ioo L U, ∀ s ∈ Icc 0 (2 * Real.pi),
      0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y))
        (γ z s) (deriv (γ z) s))
    (hheight : ∀ z ∈ Ioo L U, ∀ s ∈ Icc 0 (2 * Real.pi),
      |curveTubeHeight T (z, γ z s)| < A) :
    ∃ g : ℝ × sphere (0 : E) 1 → ℝ,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ p, |g p| < A) ∧ ∀ z ∈ Icc a b,
        range (fun q : sphere (0 : E) 1 => c z q + g (z, q) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) = range (γ z) := by
  have hP : 0 < 2 * Real.pi := by positivity
  have hx (y : ℝ × E) (hy : y ∈ T.target) : (T.symm y).2 ≠ 0 :=
    (curveAnnularTube_coordinates o q0 c T hw hs he hy).1
  have hfull (z : ℝ) (hz : z ∈ Ioo L U) (t : ℝ) :
      (z, γ z t) ∈ T.target ∧ |curveTubeHeight T (z, γ z t)| < A := by
    let m : ℤ := ⌊t / (2 * Real.pi)⌋
    have hlo : (m : ℝ) * (2 * Real.pi) ≤ t := (le_div_iff₀ hP).mp (Int.floor_le _)
    have hhi : t < ((m : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hP).mp (Int.lt_floor_add_one _)
    have hr : t - (m : ℝ) * (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) :=
      ⟨by linarith, by nlinarith⟩
    have htarget := (hdom z hz _ hr).1
    have hbound := hheight z hz _ hr
    rw [(hper z).sub_int_mul_eq m] at htarget hbound
    exact ⟨htarget, hbound⟩
  let B : ℝ × ℝ → ℝ := fun p => curveTubeAngle e q0 T (p, γ p.1 p.2)
  obtain ⟨hB, hBper, hBpos⟩ := curveTubeAngle_lift_properties e q0 T hInv hx γ hγ hper hdom hpos
  obtain ⟨G, hG, hGper, hGinv⟩ := exists_smooth_local_inverse_of_add_period ha hb hP hB
    (fun z _ t => hBper z t) hBpos
  let H : ℝ × ℝ → ℝ × E := fun p => (p.1, γ p.1 (G p))
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk (hγ.comp (contDiff_fst.prodMk hG))
  let k : ℝ × ℝ → ℝ := fun p => curveTubeHeight T (H p)
  have hk : ContDiffOn ℝ ∞ k (Ioo L U ×ˢ univ) := by
    intro p hp
    exact (((contDiffOn_curveTubeHeight T hInv hx).contDiffAt
      (T.open_target.mem_nhds (hfull p.1 hp.1 (G p)).1)).comp p hH.contDiffAt).contDiffWithinAt
  have hkbound (p : ℝ × ℝ) (hp : p.1 ∈ Ioo L U) : |k p| < A :=
    (hfull p.1 hp (G p)).2
  have hkper (z t : ℝ) : k (z, t + 2 * Real.pi) = k (z, t) := by
    dsimp only [k, H]
    rw [hGper, hper z]
  let ε := min (a - L) (U - b) / 2
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)
  let l := a - ε
  let u := b + ε
  have hl : L < l := by
    dsimp [l, ε]
    linarith [min_le_left (a - L) (U - b)]
  have hu : u < U := by
    dsimp [u, ε]
    linarith [min_le_right (a - L) (U - b)]
  have hKJ : Icc l u ⊆ Ioo L U := fun z hz =>
    ⟨hl.trans_le hz.1, hz.2.trans_lt hu⟩
  obtain ⟨σ, hσ, hσrange, hσone, hσtail⟩ := exists_smooth_interval_cutoff a b hε
  have hσzero (z : ℝ) (hz : z ∉ Icc l u) : σ z = 0 := by
    apply hσtail
    by_cases hlz : l ≤ z
    · exact Or.inr (lt_of_not_ge (fun h => hz ⟨hlz, h⟩)).le
    · exact Or.inl (lt_of_not_ge hlz).le
  let f : ℝ → ℝ → ℝ := fun z t => σ z * k (z, t)
  have hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) :=
    contDiff_timeCutoff isClosed_Icc isOpen_Ioo hKJ hσ hσzero hk
  have hfbound (z t : ℝ) : |f z t| < A := by
    by_cases hz : z ∈ Ioo L U
    · change |σ z * k (z, t)| < A
      rw [abs_mul, abs_of_nonneg (hσrange z).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hσrange z).2).trans_lt (hkbound (z, t) hz)
    · simpa only [f, hσzero z (fun h => hz (hKJ h)), zero_mul, abs_zero] using hA
  have hfper (z : ℝ) : Periodic (f z) (2 * Real.pi) := by
    intro t
    dsimp only [f]
    rw [hkper]
  let g : ℝ × sphere (0 : E) 1 → ℝ := fun p =>
    periodicCircleCurve (2 * Real.pi) e (f p.1) p.2
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_periodicCircleCurve_family hP e f hf hfper
  have hgrep (z s : ℝ) : g (z, sphereCircleParameter e s) = f z s := by
    simpa only [g, div_self hP.ne', one_mul] using
      periodicCircleCurve_sphereCircleParameter hP e (hfper z) s
  refine ⟨g, hg, fun p => hfbound p.1 _, ?_⟩
  intro z hz
  have hzJ : z ∈ Ioo L U := ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
  have hformula (s : ℝ) : γ z (G (z, s)) =
      c z (sphereCircleParameter e s) + g (z, sphereCircleParameter e s) •
        curveFamilyNormal o (radialFamilyExtension q0 c) (z, (sphereCircleParameter e s : E)) := by
    have hproj : curveTubeProjection q0 T (z, γ z (G (z, s))) = sphereCircleParameter e s := by
      have h := sphereCircleParameter_curveTubeAngle e q0 T ((z, G (z, s)), γ z (G (z, s)))
      rw [(hGinv z hz s).1] at h
      exact h.symm
    have hcoord := (curveAnnularTube_coordinates o q0 c T hw hs he
      (hfull z hzJ (G (z, s))).1).2.2.2.2
    rw [hproj] at hcoord
    rw [hgrep]
    simpa only [f, hσone z hz, one_mul, k, H] using hcoord
  apply Subset.antisymm
  · rintro y ⟨q, rfl⟩
    obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
    exact ⟨G (z, s), hformula s⟩
  · rintro y ⟨t, rfl⟩
    refine ⟨sphereCircleParameter e (B (z, t)), ?_⟩
    have h := hformula (B (z, t))
    rw [(hGinv z hz t).2] at h
    exact h.symm




theorem exists_positive_tube_curve_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L0 U0 L U w a b A : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L0 U0 ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E, T p = (p.1, curveAnnularExtension o q0 c p))
    (hfwd : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hL : L0 ≤ L) (hU : U ≤ U0) (ha : L < a) (hb : b < U) (hA : 0 < A) (hAw : A < w)
    (γ : ℝ → ℝ → E) (hγ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.1 p.2))
    (hper : ∀ z, Periodic (γ z) (2 * Real.pi))
    (hdom : ∀ z ∈ Ioo L U, ∀ s ∈ Icc 0 (2 * Real.pi),
      ((z, s), γ z s) ∈ curveTubeAngularDomain e q0 T)
    (hpos : ∀ z ∈ Ioo L U, ∀ s ∈ Icc 0 (2 * Real.pi),
      0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y))
        (γ z s) (deriv (γ z) s))
    (hheight : ∀ z ∈ Ioo L U, ∀ s ∈ Icc 0 (2 * Real.pi),
      |curveTubeHeight T (z, γ z s)| < A) :
    ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      (∃ K : Set E, IsCompact K ∧
        ∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x)) ∧
      ∀ z ∈ Icc a b, range (fun q : sphere (0 : E) 1 => F z (c z q)) = range (γ z) := by
  obtain ⟨g, hg, hbound, hrange⟩ := exists_smooth_normal_graph_of_positive_tube_projection
    e o q0 c T hw hs he hInv hL hU ha hb hA γ hγ hper hdom hpos hheight
  obtain ⟨F, hF, hFinv, hK, hcompact, hgraph⟩ := exists_curveAnnularTube_graph_transport
    o q0 c T hw hs he hfwd hInv (hL.trans_lt ha) (hb.trans_le hU) hAw g hg hbound
  refine ⟨F, hF, hFinv, hK, hcompact, ?_⟩
  intro z hz
  rw [show (fun q : sphere (0 : E) 1 => F z (c z q)) =
    (fun q => c z q + g (z, q) •
      curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) from funext (hgraph z hz)]
  exact hrange z hz

end PoincareConjecture.M25.Topology3D
