import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Endpoint

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

universe u

namespace PoincareConjecture.M63

theorem exists_joint_coordinate_geodesic_endpoint
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ v w, B y v w = B y w v)
    {x : E} (hx : x ∈ U) :
    ∃ epsilon r : ℝ,
      0 < epsilon ∧ 0 < r ∧ ball x epsilon ⊆ U ∧
      ∃ Gamma : (E × E) × ℝ → E × E,
        ContDiffOn ℝ ∞ Gamma
          ((ball x epsilon ×ˢ ball 0 r) ×ˢ Ioo (-2 : ℝ) 2) ∧
        (∀ y ∈ ball x epsilon, ∀ v ∈ ball 0 r,
          Gamma ((y, v), 0) = (y, v) ∧
          ∀ t ∈ Ioo (-2 : ℝ) 2,
            (Gamma ((y, v), t)).1 ∈ U ∧
            HasDerivAt (fun s => Gamma ((y, v), s))
              (coordinateGeodesicField B (Gamma ((y, v), t))) t) ∧
        (∀ y ∈ ball x epsilon, ∀ t ∈ Ioo (-2 : ℝ) 2,
          Gamma ((y, 0), t) = (y, 0)) ∧
        (∀ y ∈ ball x epsilon,
          HasFDerivAt (fun v => (Gamma ((y, v), 1)).1)
            (ContinuousLinearMap.id ℝ E) 0) := by
  have hfield := contDiffAt_coordinateGeodesicField
    (z := (x, (0 : E))) (hB.contDiffAt (hU.mem_nhds hx)) (hinv x hx)
  obtain ⟨K, Q, hQ, hK⟩ :=
    (hfield.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  have hQU : Q ∩ (U ×ˢ univ) ∈ 𝓝 (x, (0 : E)) :=
    inter_mem hQ ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
  obtain ⟨R, hR, hRQ⟩ := Metric.mem_nhds_iff.mp hQU
  obtain ⟨V, delta, Phi, hV, hxV, hVU, hdelta, hPhi, hinit, hspec⟩ :=
    exists_smooth_coordinate_geodesic_flow hU hB hinv hsymm hx (0 : E)
  let W := (V ×ˢ Ioo (-delta) delta) ∩ Phi ⁻¹' ball (x, 0) (R / 4)
  have hWopen : IsOpen W := hPhi.continuousOn.isOpen_inter_preimage
    (hV.prod isOpen_Ioo) isOpen_ball
  have hWmem : ((x, (0 : E)), 0) ∈ W := by
    refine ⟨⟨hxV, ⟨by linarith, hdelta⟩⟩, ?_⟩
    change Phi ((x, 0), 0) ∈ ball (x, 0) (R / 4)
    rw [hinit (x, 0) hxV]
    exact mem_ball_self (by linarith)
  obtain ⟨e, he, heW⟩ := Metric.isOpen_iff.mp hWopen _ hWmem
  let d := min e (R / 4)
  have hd : 0 < d := lt_min he (by linarith)
  have hde : d ≤ e := min_le_left _ _
  have hdR : d ≤ R / 4 := min_le_right _ _
  have hsub (y : E) (hy : y ∈ ball x d) (v : E) (hv : v ∈ ball 0 d)
      (t : ℝ) (ht : t ∈ Ioo (-d) d) : ((y, v), t) ∈ W := by
    apply heW
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(mem_ball.mp hy).trans_le hde, (mem_ball.mp hv).trans_le hde⟩
    · rw [Real.dist_eq, sub_zero]
      exact (abs_lt.mpr ht).trans_le hde
  have hball : ball x d ⊆ U := by
    intro y hy
    exact (hVU (hsub y hy 0 (mem_ball_self hd) 0 ⟨by linarith, hd⟩).1.1).1
  have hcenter (y : E) (hy : y ∈ ball x d) :
      dist (y, (0 : E)) (x, 0) < R / 4 := by
    rw [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)]
    exact (mem_ball.mp hy).trans_le hdR
  have hfieldSub (y : E) (hy : y ∈ ball x d) :
      ball (y, (0 : E)) (R / 2) ⊆ ball (x, 0) R := by
    intro z hz
    have hy0 := hcenter y hy
    have hz0 := dist_triangle z (y, (0 : E)) (x, 0)
    rw [mem_ball] at hz ⊢
    linarith
  have hstay (y : E) (hy : y ∈ ball x d) (v : E) (hv : v ∈ ball 0 d)
      (t : ℝ) (ht : t ∈ Ioo (-d) d) :
      Phi ((y, v), t) ∈ ball (y, 0) (R / 2) := by
    have hz : dist (Phi ((y, v), t)) (x, 0) < R / 4 :=
      mem_ball.mp (hsub y hy v hv t ht).2
    have hy0 : dist (x, (0 : E)) (y, 0) < R / 4 := by
      rw [dist_comm]
      exact hcenter y hy
    have htri := dist_triangle (Phi ((y, v), t)) (x, (0 : E)) (y, 0)
    rw [mem_ball]
    linarith

  let D (y : E) (hy : y ∈ ball x d) :
      CoordinateExponential.LocalFlowData B U y :=
    { radius := d
      radius_pos := hd
      fieldRadius := R / 2
      fieldRadius_pos := by linarith
      field_ball_subset := fun z hz => (hRQ (hfieldSub y hy hz)).2
      constant := K
      lipschitz := hK.mono (fun z hz => (hRQ (hfieldSub y hy hz)).1)
      flow := fun p => Phi ((y, p.1), p.2)
      smooth := hPhi.comp
        ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
        (fun p hp => (hsub y hy p.1 hp.1 p.2 hp.2).1)
      initial := fun v hv =>
        hinit (y, v) (hsub y hy v hv 0 ⟨by linarith, hd⟩).1.1
      hasDerivAt := fun v hv t ht =>
        (hspec (y, v) (hsub y hy v hv t ht).1.1 t (hsub y hy v hv t ht).1.2).2.1
      stays := hstay y hy }
  let tau := d / 2
  have htau : 0 < tau := half_pos hd
  let r := tau * d
  have hr : 0 < r := mul_pos htau hd
  have hvelocity (v : E) (hv : v ∈ ball 0 r) : tau⁻¹ • v ∈ ball 0 d := by
    have hvn : ‖v‖ < tau * d := by simpa only [mem_ball, dist_zero_right, r] using hv
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr htau)]
    calc
      tau⁻¹ * ‖v‖ < tau⁻¹ * (tau * d) :=
        mul_lt_mul_of_pos_left hvn (inv_pos.mpr htau)
      _ = d := by rw [← mul_assoc, inv_mul_cancel₀ htau.ne', one_mul]
  let Gamma : (E × E) × ℝ → E × E := fun z =>
    CoordinateExponential.velocityScale tau
      (Phi ((z.1.1, tau⁻¹ • z.1.2), tau * z.2))
  have hinput : ContDiff ℝ ∞ (fun z : (E × E) × ℝ =>
      ((z.1.1, tau⁻¹ • z.1.2), tau * z.2)) := by fun_prop
  have hmaps : MapsTo (fun z : (E × E) × ℝ =>
      ((z.1.1, tau⁻¹ • z.1.2), tau * z.2))
      ((ball x d ×ˢ ball 0 r) ×ˢ Ioo (-2 : ℝ) 2) (V ×ˢ Ioo (-delta) delta) := by
    intro z hz
    have htime : tau * z.2 ∈ Ioo (-d) d :=
      (D z.1.1 hz.1.1).normalized_time_mem hz.2
    exact (hsub z.1.1 hz.1.1 (tau⁻¹ • z.1.2)
      (hvelocity z.1.2 hz.1.2) (tau * z.2) htime).1
  have hGamma : ContDiffOn ℝ ∞ Gamma
      ((ball x d ×ˢ ball 0 r) ×ˢ Ioo (-2 : ℝ) 2) :=
    (CoordinateExponential.velocityScale (E := E) tau).contDiff.contDiffOn.comp
      (hPhi.comp hinput.contDiffOn hmaps) (fun _ _ => mem_univ _)
  refine ⟨d, r, hd, hr, hball, Gamma, hGamma, ?_, ?_, ?_⟩
  · intro y hy v hv
    have hvD : v ∈ (D y hy).domain := hvelocity v hv
    refine ⟨(D y hy).trajectory_initial hvD, ?_⟩
    intro t ht
    exact ⟨(D y hy).trajectory_mem hvD ht, (D y hy).trajectory_hasDerivAt hvD ht⟩
  · intro y hy t ht
    dsimp only [Gamma]
    rw [smul_zero]
    have hz : Phi ((y, 0), tau * t) = (y, 0) :=
      (D y hy).zero ((D y hy).normalized_time_mem ht)
    rw [hz]
    ext <;> simp only [CoordinateExponential.velocityScale_fst,
      CoordinateExponential.velocityScale_snd, smul_zero]
  · intro y hy
    have heq : (fun v => (Gamma ((y, v), 1)).1) = (D y hy).exponential := by
      funext v
      exact (D y hy).trajectory_endpoint v
    rw [heq]
    exact (D y hy).hasFDerivAt_exponential_zero

end PoincareConjecture.M63
