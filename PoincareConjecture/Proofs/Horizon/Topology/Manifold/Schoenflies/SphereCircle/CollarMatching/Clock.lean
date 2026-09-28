import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open CircleCollar
private abbrev Circle := CircleCollar.Circle
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private def capClock (s ρ : Real) : Real := s * ((1 - ρ ^ 2) / (2 * ρ))

private theorem capClock_one (s : Real) : capClock s 1 = 0 := by simp [capClock]

private theorem hasDerivAt_capClock_one (s : Real) :
    HasDerivAt (capClock s) (-s) 1 := by
  have h := (((hasDerivAt_const (1 : Real) (1 : Real)).sub ((hasDerivAt_id 1).pow 2)).div
    ((hasDerivAt_const (1 : Real) (2 : Real)).mul (hasDerivAt_id 1)) (by norm_num)).const_mul s
  convert! h using 1
  norm_num [capClock]



theorem exists_disk_preserving_cap_clock {s : Real} (hs : s < 0) :
    ∃ G : Diffeomorph (𝓡 2) (𝓡 2) Plane Plane ∞,
      G '' closedBall 0 1 = closedBall 0 1 ∧
      G '' ball 0 1 = ball 0 1 ∧
      (∀ p : Circle, G p = p) ∧
      ∃ ζ : Real, 0 < ζ ∧ ζ < 1 ∧
        ∀ p : Circle, ∀ ρ : Real, |ρ - 1| < ζ ->
          G (ρ • (p : Plane)) = (1 + s * ((1 - ρ ^ 2) / (2 * ρ))) • (p : Plane) := by
  let k : Plane -> Plane := fun x => ((1 + capClock s ‖x‖) / ‖x‖) • x
  have hk : ContDiffOn Real ∞ k ({0}ᶜ : Set Plane) := by
    intro x hx
    have hn : ContDiffAt Real ∞ (fun x : Plane => ‖x‖) x := contDiffAt_norm Real hx
    have hd : (2 : Real) * ‖x‖ ≠ 0 := mul_ne_zero (by norm_num) (norm_ne_zero_iff.mpr hx)
    exact (((contDiffAt_const.add
      (contDiffAt_const.mul ((contDiffAt_const.sub (hn.pow 2)).div
        (contDiffAt_const.mul hn) hd))).div hn (norm_ne_zero_iff.mpr hx)).smul
          contDiffAt_id).contDiffWithinAt
  have hkformula (p : Circle) {ρ : Real} (hρ : 0 < ρ) :
      k (ρ • (p : Plane)) = (1 + capClock s ρ) • (p : Plane) := by
    simp only [k, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      norm_eq_of_mem_sphere p, mul_one, smul_smul]
    rw [div_mul_cancel₀ _ hρ.ne']
  have hkfix (p : Circle) : k p = p := by
    simpa only [capClock_one, add_zero, one_smul] using hkformula p zero_lt_one
  obtain ⟨g, hg, _, hggerm⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_sphere (0 : Plane) 1) isClosed_singleton.isOpen_compl
    (fun p hp => ne_zero_of_mem_unit_sphere ⟨p, hp⟩) hk
  have hgfix (p : Circle) : g p = p := (hggerm p p.property).eq_of_nhds.trans (hkfix p)
  have hgnormal (p : Circle) : 0 < inner Real (p : Plane) (fderiv Real g p p) := by
    have hcurve : HasDerivAt (fun ρ : Real => g (ρ • (p : Plane)))
        (fderiv Real g p p) 1 := by
      have hgp : HasFDerivAt g (fderiv Real g p) ((1 : Real) • (p : Plane)) := by
        simpa only [one_smul] using (hg.differentiable (by simp) p).hasFDerivAt
      have hh := hgp.comp_hasDerivAt (1 : Real) ((hasDerivAt_id (1 : Real)).smul_const (p : Plane))
      convert! hh using 1
      simp
    have hclock : HasDerivAt (fun ρ : Real => (1 + capClock s ρ) • (p : Plane))
        ((-s) • (p : Plane)) 1 := by
      simpa using ((hasDerivAt_const (1 : Real) (1 : Real)).add
        (hasDerivAt_capClock_one s)).smul_const (p : Plane)
    have heq : (fun ρ : Real => g (ρ • (p : Plane))) =ᶠ[𝓝 1]
        (fun ρ : Real => (1 + capClock s ρ) • (p : Plane)) := by
      have hc : Tendsto (fun ρ : Real => ρ • (p : Plane)) (𝓝 1) (𝓝 (p : Plane)) := by
        simpa using (show ContinuousAt (fun ρ : Real => ρ • (p : Plane)) 1 by fun_prop).tendsto
      filter_upwards [(hggerm p p.property).comp_tendsto hc,
        Ioi_mem_nhds zero_lt_one] with ρ hρ hρpos
      exact hρ.trans (hkformula p hρpos)
    have hd : fderiv Real g p p = (-s) • (p : Plane) :=
      hcurve.unique (hclock.congr_of_eventuallyEq heq)
    rw [hd, inner_smul_right]
    simpa using neg_pos.mpr hs
  obtain ⟨ε, hε, hε1, _, _, _, G, _, hGg, hGfix, hGclosed, hGball⟩ :=
    exists_ambient_circle_collar_extension hg hgfix hgnormal isOpen_univ (subset_univ _)
  have hcircleU : sphere (0 : Plane) 1 ⊆ interior {x | g x = k x} := by
    intro p hp
    exact mem_interior_iff_mem_nhds.mpr (hggerm p hp)
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere (0 : Plane) 1).exists_cthickening_subset_open
    isOpen_interior hcircleU
  let ζ := min ε δ
  have hζ : 0 < ζ := lt_min hε hδ
  have hζ1 : ζ < 1 := (min_le_left _ _).trans_lt hε1
  refine ⟨G, hGclosed, hGball, hGfix, ζ, hζ, hζ1, ?_⟩
  intro p ρ hρ
  have hρpos : 0 < ρ := by
    have := (abs_lt.mp (hρ.trans hζ1)).1
    linarith
  have hdist : dist (ρ • (p : Plane)) (p : Plane) = |ρ - 1| := by
    rw [dist_eq_norm, show ρ • (p : Plane) - (p : Plane) =
      (ρ - 1) • (p : Plane) by rw [sub_smul, one_smul], norm_smul]
    simp [Real.norm_eq_abs]
  have hxthick : ρ • (p : Plane) ∈ cthickening δ (sphere (0 : Plane) 1) :=
    mem_cthickening_of_dist_le (ρ • (p : Plane)) (p : Plane) δ
      (sphere (0 : Plane) 1) p.property (by
        rw [hdist]
        exact hρ.le.trans (min_le_right _ _))
  have hxg : g (ρ • (p : Plane)) = k (ρ • (p : Plane)) :=
    show ρ • (p : Plane) ∈ {x | g x = k x} from interior_subset (hδU hxthick)
  rw [hGg _ (by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos] using
      hρ.trans_le (min_le_left ε δ)), hxg, hkformula p hρpos]
  rfl



theorem exists_disk_chart_matching_cap_clock
    (e : OpenPartialHomeomorph Plane S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hsource : closedBall 0 1 ⊆ e.source)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (Circle × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hTsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (hcenter : range (fun p : Circle => T (p, 0)) = e '' sphere (0 : Plane) 1)
    (hinward : ∀ p : Circle, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1)
    {s : Real} (hs : s < 0) :
    ∃ d : OpenPartialHomeomorph Plane S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      d '' closedBall 0 1 = e '' closedBall 0 1 ∧
      d '' ball 0 1 = e '' ball 0 1 ∧
      (∀ p : Circle, d p = e p) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞,
        ∃ η : Real, 0 < η ∧ η < 1 ∧
          ∀ p : Circle, ∀ ρ : Real, |ρ - 1| < η ->
            ρ • (p : Plane) ∈ d.source ∧
            |s * ((1 - ρ ^ 2) / (2 * ρ))| < ε ∧
            d (ρ • (p : Plane)) = T (q p, s * ((1 - ρ ^ 2) / (2 * ρ))) := by
  obtain ⟨d, hd, hdi, hdsource, hdclosed, hdball, hdfix, q, a, ha, halim, hmatch⟩ :=
    exists_disk_chart_matching_collar e he hei hsource hε T hT hTi hTsource hcenter hinward
  obtain ⟨G, hGclosed, hGball, hGfix, ζ, hζ, hζ1, hGclock⟩ :=
    exists_disk_preserving_cap_clock hs
  obtain ⟨δ, hδ, hδclock⟩ := Metric.continuousAt_iff.mp
    (hasDerivAt_capClock_one s).continuousAt a ha
  let η := min ζ δ
  have hη : 0 < η := lt_min hζ hδ
  have hη1 : η < 1 := (min_le_left _ _).trans_lt hζ1
  let D : PartialDiffeomorph (𝓡 2) (𝓡 2) Plane S2 ∞ :=
    { d with contMDiffOn_toFun := hd, contMDiffOn_invFun := hdi }
  let DG := G.toPartialDiffeomorph.trans D
  let d' := DG.toOpenPartialHomeomorph
  have hd'source : closedBall (0 : Plane) 1 ⊆ d'.source := by
    intro x hx
    change x ∈ univ ∧ G x ∈ d.source
    exact ⟨mem_univ _, hdsource (hGclosed ▸ mem_image_of_mem G hx)⟩
  have hd'apply (x : Plane) : d' x = d (G x) := rfl
  refine ⟨d', DG.contMDiffOn, DG.symm.contMDiffOn, hd'source, ?_, ?_, ?_, q, η,
    hη, hη1, ?_⟩
  · change (d ∘ G) '' closedBall 0 1 = _
    rw [image_comp, hGclosed, hdclosed]
  · change (d ∘ G) '' ball 0 1 = _
    rw [image_comp, hGball, hdball]
  · intro p
    rw [hd'apply, hGfix, hdfix]
  · intro p ρ hρ
    have hclock : |capClock s ρ| < a := by
      have hh := hδclock (show dist ρ 1 < δ by
        simpa only [Real.dist_eq] using hρ.trans_le (min_le_right ζ δ))
      simpa only [capClock_one, dist_zero_right, Real.norm_eq_abs] using hh
    have hrad : |1 + capClock s ρ - 1| < a := by simpa using hclock
    obtain ⟨hinsource, hvalue⟩ := hmatch p (1 + capClock s ρ) hrad
    have hGvalue := hGclock p ρ (hρ.trans_le (min_le_left ζ δ))
    refine ⟨?_, hclock.trans (halim.trans_le (min_le_left _ _)), ?_⟩
    · change ρ • (p : Plane) ∈ univ ∧ G (ρ • (p : Plane)) ∈ d.source
      exact ⟨mem_univ _, hGvalue.symm ▸ hinsource⟩
    · rw [hd'apply, hGvalue]
      convert! hvalue using 1
      simp only [add_sub_cancel_left, capClock]

end Poincare.Manifold.Schoenflies
