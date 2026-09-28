import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Radial
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Normal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open CircleCollar
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1



theorem exists_radial_ambient_diffeomorph_of_circle_diffeomorph
    (q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞) :
    ∃ H : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      H '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
      H '' ball (0 : E2) 1 = ball (0 : E2) 1 ∧
      ∃ η : Real, 0 < η ∧ η < 1 ∧
        ∀ p : S1, ∀ ρ : Real, |ρ - 1| < η ->
          H (ρ • (p : E2)) = ρ • (q p : E2) := by
  obtain ⟨G, hGq, hGclosed, hGball⟩ :=
    exists_ambient_diffeomorph_of_circle_diffeomorph q
  let Q := q.prodCongr (Diffeomorph.refl 𝓘(Real, Real) Real (n := ∞))
  let P := ((radial.trans Q.toPartialDiffeomorph).trans radial.symm).trans
    G.symm.toPartialDiffeomorph
  have hPformula (p : S1) {ρ : Real} (hρ : 0 < ρ) :
      P (ρ • (p : E2)) = G.symm (ρ • (q p : E2)) := by
    change G.symm (radial.symm (Q (radial (ρ • (p : E2))))) = _
    rw [radial_smul p hρ]
    change G.symm ((1 + (ρ - 1)) • (q p : E2)) = _
    congr 2
    ring
  have hpP (p : S1) : (p : E2) ∈ P.source := by
    change (((p : E2) ∈ radial.source ∧ radial p ∈ Q.toPartialDiffeomorph.source) ∧
      Q (radial p) ∈ radial.target) ∧ radial.symm (Q (radial p)) ∈ univ
    rw [radial_circle]
    exact ⟨⟨⟨ne_zero_of_mem_unit_sphere p, mem_univ _⟩,
      ⟨mem_univ _, by change (-1 : Real) < 0; norm_num⟩⟩, mem_univ _⟩
  have hPfix (p : S1) : P p = (p : E2) := by
    simpa only [one_smul, ← hGq p, G.symm_apply_apply] using hPformula p zero_lt_one
  obtain ⟨k, hk, _, hkP⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_sphere (0 : E2) 1) P.open_source (fun p hp => hpP ⟨p, hp⟩)
    P.contMDiffOn.contDiffOn
  have hkfix (p : S1) : k p = p := (hkP p p.property).eq_of_nhds.trans (hPfix p)
  have hkinj (p : S1) : Injective (fderiv Real k p) := by
    rw [(hkP p p.property).fderiv_eq]
    have hl := P.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hpP p)
    have hh : Injective (mfderiv (𝓡 2) (𝓡 2) P p) :=
      (hl.mfderivToContinuousLinearEquiv (by simp)).injective
    rw [mfderiv_eq_fderiv] at hh
    convert! hh using 1
  have hkinward (p : S1) :
      ∀ᶠ t in 𝓝[<] (0 : Real), ‖k ((1 + t) • (p : E2))‖ < 1 := by
    have hc : ContinuousAt (fun t : Real => (1 + t) • (p : E2)) 0 := by fun_prop
    have heq : ∀ᶠ t in 𝓝 (0 : Real), k ((1 + t) • (p : E2)) =
        P ((1 + t) • (p : E2)) := by
      exact (hkP p p.property).comp_tendsto (show
        Tendsto (fun t : Real => (1 + t) • (p : E2)) (𝓝 0) (𝓝 (p : E2)) by
          simpa using hc.tendsto)
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsLT (show (-1 : Real) < 0 by norm_num)] with t ht ht1
    rw [ht, hPformula p (by linarith [ht1.1])]
    have hy : (1 + t) • (q p : E2) ∈ ball (0 : E2) 1 := by
      rw [mem_ball_zero_iff, norm_smul]
      simp only [norm_eq_of_mem_sphere, Real.norm_eq_abs, mul_one,
        abs_of_pos (by linarith [ht1.1] : 0 < 1 + t)]
      linarith [ht1.2]
    rw [← hGball] at hy
    obtain ⟨x, hx, hxe⟩ := hy
    rw [← hxe, G.symm_apply_apply]
    exact mem_ball_zero_iff.mp hx
  have hnormal (p : S1) : 0 < inner Real (p : E2) (fderiv Real k p p) :=
    normal_derivative_pos_of_inward hk hkfix hkinj hkinward p
  obtain ⟨ζ, hζ, _, S, _, _, L, _, hLk, _, hLclosed, hLball⟩ :=
    exists_ambient_circle_collar_extension hk hkfix hnormal isOpen_univ (subset_univ _)
  let U : Set E2 := interior {x | k x = P x}
  have hcircleU : sphere (0 : E2) 1 ⊆ U := by
    intro p hp
    exact mem_interior_iff_mem_nhds.mpr (hkP p hp)
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere (0 : E2) 1).exists_cthickening_subset_open
    isOpen_interior hcircleU
  let η := min (min ζ δ) (1 / 2)
  have hη : 0 < η := lt_min (lt_min hζ hδ) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηζ : η ≤ ζ := (min_le_left _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨L.trans G, ?_, ?_, η, hη, hη1, ?_⟩
  · change (G ∘ L) '' closedBall 0 1 = _
    rw [image_comp, hLclosed, hGclosed]
  · change (G ∘ L) '' ball 0 1 = _
    rw [image_comp, hLball, hGball]
  · intro p ρ hρ
    have hρpos : 0 < ρ := by have := (abs_lt.mp (hρ.trans hη1)).1; linarith
    have hdist : dist (ρ • (p : E2)) (p : E2) = |ρ - 1| := by
      rw [dist_eq_norm, show ρ • (p : E2) - (p : E2) =
        (ρ - 1) • (p : E2) by rw [sub_smul, one_smul], norm_smul]
      simp [Real.norm_eq_abs]
    have hxthick : ρ • (p : E2) ∈ cthickening δ (sphere (0 : E2) 1) :=
      mem_cthickening_of_dist_le (ρ • (p : E2)) (p : E2) δ
        (sphere (0 : E2) 1) p.property (by rw [hdist]; exact hρ.le.trans hηδ)
    have hxk : k (ρ • (p : E2)) = P (ρ • (p : E2)) :=
      show ρ • (p : E2) ∈ {x | k x = P x} from interior_subset (hδU hxthick)
    change G (L (ρ • (p : E2))) = _
    rw [hLk _ (by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos] using
        hρ.trans_le hηζ), hxk, hPformula p hρpos, G.apply_symm_apply]

end Poincare.Manifold.Schoenflies
