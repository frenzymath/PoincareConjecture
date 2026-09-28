import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarDifferential
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Localized
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody
import Mathlib.Topology.MetricSpace.Thickening










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem mem_cthickening_sphere_of_abs_norm_sub_one_lt
    {δ ε : Real} (hεδ : ε ≤ δ) (hε : ε < 1) {x : E2}
    (hx : |‖x‖ - 1| < ε) : x ∈ cthickening δ (sphere (0 : E2) 1) := by
  have hx0 : x ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_sub, abs_neg, abs_one] at hx
    linarith
  let p : S1 := ((homeomorphUnitSphereProd E2) ⟨x, hx0⟩).1
  have hxp : x = ‖x‖ • (p : E2) := by
    rw [show (p : E2) = ‖x‖⁻¹ • x from homeomorphUnitSphereProd_apply_fst_coe _ _,
      smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
  have hdist : dist x (p : E2) = |‖x‖ - 1| := by
    calc
      dist x (p : E2) = ‖‖x‖ • (p : E2) - (p : E2)‖ := by
        rw [dist_eq_norm]
        exact congrArg (fun y : E2 => ‖y - (p : E2)‖) hxp
      _ = ‖(‖x‖ - 1) • (p : E2)‖ := by rw [sub_smul, one_smul]
      _ = |‖x‖ - 1| := by simp [norm_smul, Real.norm_eq_abs]
  exact mem_cthickening_of_dist_le x p δ _ p.property (hdist ▸ hx.le.trans hεδ)




theorem exists_ambient_circle_collar_extension
    {e : E2 -> E2} (he : ContDiff Real ∞ e)
    (hfix : ∀ p : S1, e p = p)
    (hnormal : ∀ p : S1, 0 < inner Real (p : E2) (fderiv Real e p p))
    {U : Set E2} (hU : IsOpen U) (hcircleU : sphere (0 : E2) 1 ⊆ U) :
    ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
      ∃ S : Set E2, IsCompact S ∧ S ⊆ U ∧
      ∃ G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∉ S, G x = x) ∧
        (∀ x : E2, |‖x‖ - 1| < ε -> G x = e x) ∧
        (∀ p : S1, G p = p) ∧
        G '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
        G '' ball (0 : E2) 1 = ball (0 : E2) 1 := by
  let H : Real × E2 -> E2 := fun z => (1 - z.1) • z.2 + z.1 • e z.2
  have hH : ContDiff Real ∞ H :=
    ((contDiff_const.sub contDiff_fst).smul contDiff_snd).add
      (contDiff_fst.smul (he.comp contDiff_snd))
  have hHp (t : Real) (p : S1) : H (t, p) = p := by
    simp only [H, hfix p, ← add_smul, sub_add_cancel, one_smul]
  obtain ⟨F, hsource, heq, _, hinverse⟩ :=
    exists_spacetime_neighborhood_of_codimZero_isotopy (a := 0) (b := 1)
      (isCompact_sphere (0 : E2) 1) H hH
      (by
        intro t _ x hx y hy hxy
        simpa only [hHp t ⟨x, hx⟩, hHp t ⟨y, hy⟩] using hxy)
      (fun t ht x hx => bijective_fderiv_circle_collar_homotopy he hfix hnormal ht ⟨x, hx⟩)
  have hopen : IsOpen (F.source ∩ H ⁻¹' U) := F.open_source.inter (hU.preimage hH.continuous)
  have htrace : Icc (0 : Real) 1 ×ˢ sphere (0 : E2) 1 ⊆ F.source ∩ H ⁻¹' U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨hsource ⟨ht, hx⟩, ?_⟩
    change H (t, x) ∈ U
    rw [hHp t ⟨x, hx⟩]
    exact hcircleU hx
  obtain ⟨T, V, _, hV, hIT, hcircleV, hTV⟩ :=
    generalized_tube_lemma isCompact_Icc (isCompact_sphere (0 : E2) 1) hopen htrace
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_sphere (0 : E2) 1).exists_cthickening_subset_open hV hcircleV
  let K := cthickening δ (sphere (0 : E2) 1)
  have hK : IsCompact K := (isCompact_sphere (0 : E2) 1).cthickening
  have hKF : Icc (0 : Real) 1 ×ˢ K ⊆ F.source := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact (hTV ⟨hIT ht, hδV hx⟩).1
  have hagreeK : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, F (t, x) = (t, H (t, x)) := by
    intro t ht x hx
    exact heq (hKF ⟨ht, hx⟩)
  have htraceK : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, H (t, x) ∈ U := by
    intro t ht x hx
    have hz : (t, x) ∈ F.source ∩ H ⁻¹' U := hTV ⟨hIT ht, hδV hx⟩
    exact hz.2
  obtain ⟨S, hS, hSU, Phi, _, _, hPhifix, hmotion⟩ :=
    exists_ambient_isotopy_of_compact_isotopy_within (a := 0) (b := 1)
      (K := K) (U := U) hK hU H hH F hKF hinverse hagreeK htraceK
  let ε := min δ (1 / 2)
  have hεpos : 0 < ε := lt_min hδ (by norm_num)
  have hεone : ε < 1 := (min_le_right δ (1 / 2)).trans_lt (by norm_num)
  have hGe (x : E2) (hx : x ∈ K) : Phi 1 x = e x := by
    simpa only [H, sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add] using
      hmotion 1 ⟨by norm_num, le_rfl⟩ x hx
  have hGp (p : S1) : Phi 1 p = p :=
    (hGe p (self_subset_cthickening (δ := δ) (sphere (0 : E2) 1) p.property)).trans (hfix p)
  have hsphere : (Phi 1).toHomeomorph '' sphere (0 : E2) 1 =
      (Homeomorph.refl E2) '' sphere (0 : E2) 1 := by
    simp only [Homeomorph.refl_apply, id_eq, image_id']
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change Phi 1 x ∈ sphere (0 : E2) 1
      rw [hGp ⟨x, hx⟩]
      exact hx
    · intro hy
      exact ⟨y, hy, hGp ⟨y, hy⟩⟩
  have hdim : 1 < Module.rank Real E2 := by rw [← Module.finrank_eq_rank]; norm_num
  have hclosed := (Phi 1).toHomeomorph.image_closedBall_eq_of_image_sphere_eq
    (Homeomorph.refl E2) hdim hsphere
  have hball := (Phi 1).toHomeomorph.image_ball_eq_of_image_sphere_eq
    (Homeomorph.refl E2) hdim hsphere
  refine ⟨ε, hεpos, hεone, S, hS, hSU, Phi 1, hPhifix 1, ?_, hGp, ?_, ?_⟩
  · intro x hx
    exact hGe x (mem_cthickening_sphere_of_abs_norm_sub_one_lt (min_le_left δ _) hεone hx)
  · simpa using hclosed
  · simpa using hball

end Poincare.Manifold.Schoenflies
