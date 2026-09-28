import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ArbitraryC2IntrinsicRegularity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedLabelSpatialSmoothness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_smooth_positive_time_relabeling
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioc a b) :
    ∃ phi : ℝ ≃ₜ ℝ,
      ContDiff ℝ 2 (phi : ℝ → ℝ) ∧ ContDiff ℝ 2 (phi.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv phi x) ∧ (∀ x, 0 < deriv phi.symm x) ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      (∀ x, phi.symm (x + curvePeriod) = phi.symm x + curvePeriod) ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c (phi.symm x) t) ∧
      Function.Periodic (fun x => c (phi.symm x) t) curvePeriod ∧
      (∀ x, c (phi.symm (phi x)) t = c x t) := by
  classical
  have hab : a < b := ht.1.trans_le ht.2
  obtain ⟨alpha, haa, hat⟩ := exists_between ht.1
  have halpha : alpha ∈ Icc a b := ⟨haa.le, hat.le.trans ht.2⟩
  have hi := M63.c2ShrinkingCurve_intrinsic_regularity F isCompact_univ hab le_rfl
    (Or.inl rfl) hc
  obtain ⟨_hell, phi, _hformula, hphi, hpsi, _hzero, hpos, hpsipos,
      hshift, hpsishift, _hperiod, _hregular, _himm, hanchor, _hprincipal⟩ :=
    M63.exists_c2_constant_speed_relabeling F (fun x => c x alpha) alpha
      (hc.periodic alpha halpha) (hc.spatial_regular alpha halpha) (hc.immersed alpha halpha)
  let : Nonempty M := ⟨c 0 a⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hre, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  have hslab : Icc alpha t ⊆ Icc a b := Icc_subset_Icc haa.le ht.2
  obtain ⟨_Q, _hQvalue, _hQ, hspace, _hjets⟩ :=
    M63.fixedLabel_embedded_path_smooth_of_constant_speed F hc hi haa hat hslab
      hpsi hpsipos hpsishift hanchor he hU heU hrho hre
  refine ⟨phi, hphi, hpsi, hpos, hpsipos, hshift, hpsishift,
    hspace t ⟨hat.le, le_rfl⟩, ?_, ?_⟩
  · intro x
    change c (phi.symm (x + curvePeriod)) t = c (phi.symm x) t
    rw [hpsishift]
    exact hc.periodic t ⟨ht.1.le, ht.2⟩ (phi.symm x)
  · intro x
    rw [phi.symm_apply_apply]

end PoincareConjecture.M64
