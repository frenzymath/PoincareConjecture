import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Normal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open CircleCollar
private abbrev Circle := CircleCollar.Circle
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem exists_disk_chart_matching_collar
    (e : OpenPartialHomeomorph Plane S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hsource : closedBall 0 1 ⊆ e.source)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (Circle × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hTsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (hcenter : range (fun p : Circle => T (p, 0)) = e '' sphere (0 : Plane) 1)
    (hinward : ∀ p : Circle, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1) :
    ∃ d : OpenPartialHomeomorph Plane S2,
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      closedBall 0 1 ⊆ d.source ∧
      d '' closedBall 0 1 = e '' closedBall 0 1 ∧
      d '' ball 0 1 = e '' ball 0 1 ∧
      (∀ p : Circle, d p = e p) ∧
      ∃ q : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞,
        ∃ η : Real, 0 < η ∧ η < min ε 1 ∧
          ∀ p : Circle, ∀ ρ : Real, |ρ - 1| < η ->
            ρ • (p : Plane) ∈ d.source ∧ d (ρ • (p : Plane)) = T (q p, ρ - 1) := by
  obtain ⟨q, hq⟩ := exists_boundary_reparametrization e he hei hsource hε T hT hTi
    hTsource hcenter
  let E : PartialDiffeomorph (𝓡 2) (𝓡 2) Plane S2 ∞ :=
    { e with contMDiffOn_toFun := he, contMDiffOn_invFun := hei }
  let TT : PartialDiffeomorph Iprod (𝓡 2) (Circle × Real) S2 ∞ :=
    { T with contMDiffOn_toFun := hT, contMDiffOn_invFun := hTi }
  let Q := q.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real (n := ∞))
  let P := ((radial.trans Q.toPartialDiffeomorph).trans TT).trans E.symm
  have hPformula (p : Circle) {ρ : Real} (hρ : 0 < ρ) :
      P (ρ • (p : Plane)) = e.symm (T (q p, ρ - 1)) := by
    change e.symm (T (Q (radial (ρ • (p : Plane))))) = _
    rw [radial_smul p hρ]
    rfl
  have hpE (p : Circle) : (p : Plane) ∈ e.source :=
    hsource (sphere_subset_closedBall p.property)
  have hpP (p : Circle) : (p : Plane) ∈ P.source := by
    change (((p : Plane) ∈ radial.source ∧ radial p ∈ Q.toPartialDiffeomorph.source) ∧
      Q (radial p) ∈ T.source) ∧ T (Q (radial p)) ∈ e.target
    rw [radial_circle]
    refine ⟨⟨⟨ne_zero_of_mem_unit_sphere p, mem_univ _⟩, ?_⟩, ?_⟩
    · change (q p, (0 : Real)) ∈ T.source
      rw [hTsource]
      exact ⟨mem_univ _, by constructor <;> linarith⟩
    · change T (q p, 0) ∈ e.target
      rw [hq]
      exact e.map_source (hpE p)
  have hPfix (p : Circle) : P p = (p : Plane) := by
    simpa only [one_smul, sub_self, hq p, e.left_inv (hpE p)] using hPformula p zero_lt_one
  obtain ⟨k, hk, _, hkP⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_sphere (0 : Plane) 1) P.open_source (fun p hp => hpP ⟨p, hp⟩)
    P.contMDiffOn.contDiffOn
  have hkfix (p : Circle) : k p = p := (hkP p p.property).eq_of_nhds.trans (hPfix p)
  have hkinj (p : Circle) : Injective (fderiv Real k p) := by
    rw [(hkP p p.property).fderiv_eq]
    have hl := P.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hpP p)
    have hh : Injective (mfderiv (𝓡 2) (𝓡 2) P p) :=
      (hl.mfderivToContinuousLinearEquiv (by simp)).injective
    rw [mfderiv_eq_fderiv] at hh
    convert! hh using 1
  have hkinward (p : Circle) :
      ∀ᶠ t in 𝓝[<] (0 : Real), ‖k ((1 + t) • (p : Plane))‖ < 1 := by
    have hc : ContinuousAt (fun t : Real => (1 + t) • (p : Plane)) 0 := by fun_prop
    have heq : ∀ᶠ t in 𝓝 (0 : Real), k ((1 + t) • (p : Plane)) =
        P ((1 + t) • (p : Plane)) := by
      have hh := (hkP p p.property).comp_tendsto (show
        Tendsto (fun t : Real => (1 + t) • (p : Plane)) (𝓝 0) (𝓝 (p : Plane)) by
          simpa using hc.tendsto)
      exact hh
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsLT (show -ε < 0 by linarith),
      Ioo_mem_nhdsLT (show (-1 : Real) < 0 by norm_num)] with t ht htε ht1
    rw [ht, hPformula p (by linarith [ht1.1])]
    have hin := hinward (q p) t htε
    obtain ⟨x, hx, hxe⟩ := hin
    rw [show 1 + t - 1 = t by ring, ← hxe,
      e.left_inv (hsource (ball_subset_closedBall hx))]
    exact mem_ball_zero_iff.mp hx
  have hnormal (p : Circle) : 0 < inner Real (p : Plane) (fderiv Real k p p) :=
    normal_derivative_pos_of_inward hk hkfix hkinj hkinward p
  obtain ⟨ζ, hζ, hζ1, S, _, _, G, _, hGk, hGfix, hGclosed, hGball⟩ :=
    exists_ambient_circle_collar_extension hk hkfix hnormal e.open_source
      (fun p hp => hpE ⟨p, hp⟩)
  let U : Set Plane := P.source ∩ interior {x | k x = P x}
  have hU : IsOpen U := P.open_source.inter isOpen_interior
  have hcircleU : sphere (0 : Plane) 1 ⊆ U := by
    intro p hp
    exact ⟨hpP ⟨p, hp⟩, mem_interior_iff_mem_nhds.mpr (hkP p hp)⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere (0 : Plane) 1).exists_cthickening_subset_open hU hcircleU
  let η := min (min ζ δ) (min ε 1 / 2)
  have hη : 0 < η := lt_min (lt_min hζ hδ) (div_pos (lt_min hε zero_lt_one) (by norm_num))
  have hηlim : η < min ε 1 := (min_le_right _ _).trans_lt (by
    have := lt_min hε zero_lt_one
    linarith)
  have hηζ : η ≤ ζ := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  let D := G.toPartialDiffeomorph.trans E
  let d := D.toOpenPartialHomeomorph
  have hdsource : closedBall (0 : Plane) 1 ⊆ d.source := by
    intro x hx
    change x ∈ univ ∧ G x ∈ e.source
    exact ⟨mem_univ _, hsource (hGclosed ▸ mem_image_of_mem G hx)⟩
  have hdapply (x : Plane) : d x = e (G x) := rfl
  refine ⟨d, D.contMDiffOn, D.symm.contMDiffOn, hdsource, ?_, ?_, ?_, q, η,
    hη, hηlim, ?_⟩
  · change (e ∘ G) '' closedBall 0 1 = _
    rw [image_comp, hGclosed]
  · change (e ∘ G) '' ball 0 1 = _
    rw [image_comp, hGball]
  · intro p
    rw [hdapply, hGfix]
  · intro p ρ hρ
    have hρ1 : |ρ - 1| < 1 := hρ.trans (hηlim.trans_le (min_le_right _ _))
    have hρpos : 0 < ρ := by have := (abs_lt.mp hρ1).1; linarith
    have hdist : dist (ρ • (p : Plane)) (p : Plane) = |ρ - 1| := by
      rw [dist_eq_norm, show ρ • (p : Plane) - (p : Plane) =
        (ρ - 1) • (p : Plane) by rw [sub_smul, one_smul], norm_smul]
      simp [Real.norm_eq_abs]
    have hxthick : ρ • (p : Plane) ∈ cthickening δ (sphere (0 : Plane) 1) :=
      mem_cthickening_of_dist_le (ρ • (p : Plane)) (p : Plane) δ
        (sphere (0 : Plane) 1) p.property (by rw [hdist]; exact hρ.le.trans hηδ)
    have hxU : ρ • (p : Plane) ∈ U := hδU hxthick
    have hxk : k (ρ • (p : Plane)) = P (ρ • (p : Plane)) :=
      show ρ • (p : Plane) ∈ {x | k x = P x} from interior_subset hxU.2
    have hxG : G (ρ • (p : Plane)) = P (ρ • (p : Plane)) := by
      rw [hGk _ (by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos] using
          hρ.trans_le hηζ), hxk]
    have htarget : T (q p, ρ - 1) ∈ e.target := by
      have hh := hxU.1
      change _ ∧ T (Q (radial (ρ • (p : Plane)))) ∈ e.target at hh
      have ht := hh.2
      rw [radial_smul p hρpos] at ht
      convert! ht using 1
    refine ⟨?_, ?_⟩
    · change ρ • (p : Plane) ∈ univ ∧ G (ρ • (p : Plane)) ∈ e.source
      refine ⟨mem_univ _, ?_⟩
      rw [hxG, hPformula p hρpos]
      exact e.map_target htarget
    · rw [hdapply, hxG, hPformula p hρpos, e.right_inv htarget]

end Poincare.Manifold.Schoenflies
