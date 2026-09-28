import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_lower_level_transport
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (a : ℝ)
    (hla : W.level ≤ a)
    (hac : a < ⟪(u : E3), psi (D.point, 0)⟫_ℝ) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let c0 : Fin 2 → UnitCircle → E2 := fun i theta =>
      pi (j (W.leg i (theta, W.level)))
    let m := (W.level + a) / 2
    (∀ q : UnitTwoSphere,
      ⟪(u : E3), j q⟫_ℝ ∈ Icc W.level a → q ∈ D.sourceCore ∧
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), j p⟫_ℝ) q ≠ 0) ∧
    (∀ i : Fin 2, IsPlanarEmbedding (c0 i) ∧ range (c0 i) = (W.disc i).boundary) ∧
    ∃ (d : ℝ)
      (T : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞),
    let C : Fin 2 → ℝ → UnitCircle → E2 := fun i z theta => T z (c0 i theta)
    let B : ℝ → Fin 2 → BallNeighborhoodChart E2 E2 :=
      fun z i => (W.disc i).mapDiffeomorph (T z)
    0 < d ∧ Icc W.level a ⊆ Ioo (m - d) (m + d) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E2 => T p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E2 => (T p.1).symm p.2) ∧
    (∀ x : E2, T W.level x = x) ∧
    (∀ z : ℝ, HasCompactSupport (fun x => T z x - x) ∧
      HasCompactSupport (fun x => (T z).symm x - x)) ∧
    (∀ i : Fin 2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C i p.1 p.2) ∧
      ∀ z : ℝ, IsPlanarEmbedding (C i z) ∧ range (C i z) = (B z i).boundary) ∧
    (∀ z : ℝ, Disjoint (B z 0).boundary (B z 1).boundary) ∧
    (∀ z ∈ Ioo (m - d) (m + d), ∀ x : E2,
      (L.symm (T z x, z) ∈ range j ↔ L.symm (x, W.level) ∈ range j)) ∧
    (∀ z ∈ Ioo (m - d) (m + d),
      {x : E2 | L.symm (x, z) ∈ range j} = ⋃ i : Fin 2, (B z i).boundary) ∧
    (∀ z : ℝ,
      (Disjoint (B z 0).closedRegion (B z 1).closedRegion ↔
        Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion) ∧
      ((B z 0).closedRegion ⊆ (B z 1).inside ↔
        (W.disc 0).closedRegion ⊆ (W.disc 1).inside) ∧
      ((B z 1).closedRegion ⊆ (B z 0).inside ↔
        (W.disc 1).closedRegion ⊆ (W.disc 0).inside)) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let c0 : Fin 2 → UnitCircle → E2 := fun i theta =>
    pi (j (W.leg i (theta, W.level)))
  let m := (W.level + a) / 2
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j := collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro q r hqr
    have h := hpsi.2.1 (x₁ := (q, 0)) (x₂ := (r, 0))
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hqr
    exact congrArg Prod.fst h
  have hcap (i : Fin D.capCount) (y : E3) (hy : y ∈ (D.cap i).cap) :
      (D.cap i).sign * (⟪(u : E3), y⟫_ℝ - (D.cap i).cutHeight) ≤
        (D.cap i).removal := by
    rw [(D.cap i).cap_eq_image] at hy
    rcases hy with ⟨q, hq, rfl⟩
    let C := D.cap i
    change C.sign *
      (⟪(u : E3), C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q⟫_ℝ -
        C.cutHeight) ≤ C.removal
    have hp : ((C.profile.model q).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2)) ∈
          C.tube.source := C.tube_source ⟨by
            simpa only [mem_closedBall, dist_zero_right] using C.profile.model_fst_norm_le q,
          mem_univ _⟩
    rw [SurgeryCapProfile.capMap_apply, C.tube_height _ hp]
    have h := surgeryCapCoordinates_south_height_bounds
      C.profile.horizontal C.profile.vertical C.profile.horizontal_smooth
      C.profile.vertical_smooth (fun z => (C.profile.horizontal_pos z).ne')
      (fun x => (C.profile.vertical_pos x).ne') C.profile.vertical_pos
      C.cutHeight C.sign C.removal C.scale C.profile.heightBound
      C.sign_abs C.scale_pos C.scale_small q hq (C.profile.height_bound q)
    exact h.2
  have hregular (q : UnitTwoSphere)
      (hq : ⟪(u : E3), j q⟫_ℝ ∈ Icc W.level a) :
      q ∈ D.sourceCore ∧ mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), j p⟫_ℝ) q ≠ 0 := by
    have hcore : q ∈ D.sourceCore := by
      have hcover : q ∈ D.sourceCore ∪ (⋃ i, (D.cap i).sourceCap) := by
        rw [D.source_cover]
        exact mem_univ q
      rcases hcover with hqcore | hqcap
      · exact hqcore
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hqcap
        have hy : j q ∈ (D.cap i).cap := ⟨q, hi, rfl⟩
        have hbound := hcap i (j q) hy
        rcases D.cut_side i with ⟨hs, _⟩ | ⟨hs, hcut⟩
        · have hseam := W.lower_seams_lt_level i hs
          rw [hs] at hbound hseam
          nlinarith [hq.1]
        · have hgap := D.cutRadius_lt_gap i
          change D.cutRadius i <
            |(D.cap i).cutHeight - ⟪(u : E3), j D.point⟫_ℝ| at hgap
          rw [abs_of_pos (sub_pos.mpr hcut)] at hgap
          rw [hs] at hbound
          nlinarith [D.removal_lt_cutRadius i, hq.2, hac]
    refine ⟨hcore, ?_⟩
    intro hcrit
    have hqp : q = D.point := (D.unique_critical q hcore).mp hcrit
    subst q
    exact (not_le_of_gt hac) hq.2
  have htop_source (i : Fin 2) (theta : UnitCircle) :
      (theta, W.level) ∈ (W.leg i).source :=
    W.leg_source i ⟨mem_univ _,
      (W.lower_seams_lt_level (W.label i) (W.label_lower i)).le, le_rfl⟩
  have htop_height (i : Fin 2) (theta : UnitCircle) :
      ⟪(u : E3), j (W.leg i (theta, W.level))⟫_ℝ = W.level :=
    W.leg_height i _ (htop_source i theta)
  have htop_rec (i : Fin 2) (theta : UnitCircle) :
      L.symm (c0 i theta, W.level) = j (W.leg i (theta, W.level)) :=
    heightPlaneCoordinates_reconstruct u _ W.level (htop_height i theta)
  have hc0 (i : Fin 2) : IsPlanarEmbedding (c0 i) := by
    obtain ⟨hs, hi, hd⟩ := source_collar_slice_smooth_immersion
      (W.leg i) (W.leg_smooth i) (W.leg_inverse i) W.level (htop_source i)
    let v : UnitCircle → E3 := fun theta => j (W.leg i (theta, W.level))
    have hvs : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ v := hj.comp hs
    have hvi : Injective v := hji.comp hi
    have hvd (theta : UnitCircle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) v theta) := by
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3)
        (j ∘ fun theta => W.leg i (theta, W.level)) theta)
      rw [mfderiv_comp theta (hj.mdifferentiable (by simp) _)
        (hs.mdifferentiable (by simp) theta)]
      exact (collar_central_mfderiv_injective psi hpsi _).comp (hd theta)
    exact isPlanarEmbedding_height_projection u v hvs hvi hvd W.level (htop_height i)
  have hc0range (i : Fin 2) : range (c0 i) = (W.disc i).boundary := by
    ext x
    constructor
    · rintro ⟨theta, rfl⟩
      have hm : L.symm (c0 i theta, W.level) ∈
          (fun y => L.symm (y, W.level)) '' (W.disc i).boundary := by
        rw [W.disc_boundary i]
        exact ⟨theta, (htop_rec i theta).symm⟩
      rcases hm with ⟨y, hy, heq⟩
      have hxy : y = c0 i theta := congrArg Prod.fst (L.symm.injective heq)
      exact hxy ▸ hy
    · intro hx
      have hm : L.symm (x, W.level) ∈
          range (fun theta => psi (W.leg i (theta, W.level), 0)) := by
        rw [← W.disc_boundary i]
        exact ⟨x, hx, rfl⟩
      rcases hm with ⟨theta, htheta⟩
      refine ⟨theta, ?_⟩
      change psi (W.leg i (theta, W.level), 0) = L.symm (x, W.level) at htheta
      change pi (psi (W.leg i (theta, W.level), 0)) = x
      rw [htheta]
      exact horizontalBandProjection_lift u W.level x
  have hlevel0 : {x : E2 | L.symm (x, W.level) ∈ range j} =
      ⋃ i : Fin 2, (W.disc i).boundary := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      have hfq : ⟪(u : E3), j q⟫_ℝ = W.level := by
        rw [hq]
        exact horizontalBandLift_height u W.level x
      have hqcore : q ∈ D.sourceCore :=
        (hregular q (by rw [hfq]; exact ⟨le_rfl, hla⟩)).1
      have hqleg : q ∈ ⋃ i : Fin 2, (W.leg i) ''
          (univ ×ˢ Icc
            ((D.cap (W.label i)).cutHeight +
              (D.cap (W.label i)).sign * (D.cap (W.label i)).removal) W.level) := by
        rw [W.leg_cover]
        exact ⟨hqcore, hfq.le⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hqleg
      rcases hi with ⟨⟨theta, z⟩, hp, hpq⟩
      have hz : z = W.level := by
        have hh := W.leg_height i (theta, z) (W.leg_source i hp)
        change ⟪(u : E3), j (W.leg i (theta, z))⟫_ℝ = z at hh
        rw [hpq, hfq] at hh
        exact hh.symm
      subst z
      refine mem_iUnion.mpr ⟨i, ?_⟩
      rw [← hc0range i]
      refine ⟨theta, ?_⟩
      change pi (j (W.leg i (theta, W.level))) = x
      rw [hpq, hq]
      exact horizontalBandProjection_lift u W.level x
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [← hc0range i] at hi
      rcases hi with ⟨theta, rfl⟩
      exact ⟨W.leg i (theta, W.level), (htop_rec i theta).symm⟩
  have hdisjoint0 : Disjoint (W.disc 0).boundary (W.disc 1).boundary := by
    apply Set.disjoint_left.mpr
    intro x hx0 hx1
    rw [← hc0range 0] at hx0
    rw [← hc0range 1] at hx1
    rcases hx0 with ⟨theta, htheta⟩
    rcases hx1 with ⟨eta, heta⟩
    have heq : c0 0 theta = c0 1 eta := htheta.trans heta.symm
    have hjq : j (W.leg 0 (theta, W.level)) = j (W.leg 1 (eta, W.level)) :=
      (htop_rec 0 theta).symm.trans
        ((congrArg (fun y => L.symm (y, W.level)) heq).trans (htop_rec 1 eta))
    have hqq : W.leg 0 (theta, W.level) = W.leg 1 (eta, W.level) := hji hjq
    apply Set.disjoint_left.mp W.leg_disjoint
    · exact ⟨(theta, W.level), ⟨mem_univ _,
        (W.lower_seams_lt_level (W.label 0) (W.label_lower 0)).le, le_rfl⟩, rfl⟩
    · exact ⟨(eta, W.level), ⟨mem_univ _,
        (W.lower_seams_lt_level (W.label 1) (W.label_lower 1)).le, le_rfl⟩, hqq.symm⟩
  obtain ⟨d, hd, hId, Phi, hPhi, hPhii, _, hPhiC, hPhiLevel⟩ :=
    exists_regular_collar_horizontal_transport psi hpsi u W.level a hla
      (fun q hq => (hregular q hq).2)
  let T : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun z => (Phi W.level).symm.trans (Phi z)
  let C : Fin 2 → ℝ → UnitCircle → E2 := fun i z theta => T z (c0 i theta)
  let B : ℝ → Fin 2 → BallNeighborhoodChart E2 E2 :=
    fun z i => (W.disc i).mapDiffeomorph (T z)
  have hTs : ContDiff ℝ ∞ (fun p : ℝ × E2 => T p.1 p.2) :=
    hPhi.comp (contDiff_fst.prodMk ((Phi W.level).symm.contDiff.comp contDiff_snd))
  have hTi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (T p.1).symm p.2) :=
    (Phi W.level).contDiff.comp hPhii
  have hTzero (x : E2) : T W.level x = x := (Phi W.level).apply_symm_apply x
  have hTsupport (z : ℝ) : HasCompactSupport (fun x => T z x - x) ∧
      HasCompactSupport (fun x => (T z).symm x - x) := by
    obtain ⟨K0, hK0, hK0zero⟩ := exists_compact_iff_hasCompactSupport.mpr (hPhiC W.level)
    obtain ⟨Kz, hKz, hKzzero⟩ := exists_compact_iff_hasCompactSupport.mpr (hPhiC z)
    have hfixed (x : E2) (hx : x ∉ K0 ∪ Kz) : T z x = x ∧ (T z).symm x = x := by
      have h0 : Phi W.level x = x :=
        sub_eq_zero.mp (hK0zero x (fun hx0 => hx (Or.inl hx0)))
      have hz : Phi z x = x := sub_eq_zero.mp (hKzzero x (fun hxz => hx (Or.inr hxz)))
      have hi0 : (Phi W.level).symm x = x := by
        calc
          (Phi W.level).symm x = (Phi W.level).symm (Phi W.level x) :=
            congrArg (Phi W.level).symm h0.symm
          _ = x := (Phi W.level).symm_apply_apply x
      have hiz : (Phi z).symm x = x := by
        calc
          (Phi z).symm x = (Phi z).symm (Phi z x) := congrArg (Phi z).symm hz.symm
          _ = x := (Phi z).symm_apply_apply x
      constructor
      · change Phi z ((Phi W.level).symm x) = x
        rw [hi0, hz]
      · change Phi W.level ((Phi z).symm x) = x
        rw [hiz, h0]
    exact ⟨HasCompactSupport.intro (hK0.union hKz)
        (fun x hx => sub_eq_zero.mpr (hfixed x hx).1),
      HasCompactSupport.intro (hK0.union hKz)
        (fun x hx => sub_eq_zero.mpr (hfixed x hx).2)⟩
  have hmapEmbedding
      (G : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (v : UnitCircle → E2) (hv : IsPlanarEmbedding v) :
      IsPlanarEmbedding (fun theta => G (v theta)) := by
    refine ⟨G.contMDiff.comp hv.1, G.injective.comp hv.2.1, ?_⟩
    intro theta
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) ((G : E2 → E2) ∘ v) theta)
    rw [mfderiv_comp theta (G.mdifferentiable (by simp) (v theta))
      (hv.1.mdifferentiable (by simp) theta)]
    exact ((G.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (x := v theta) (mem_univ _)).comp (hv.2.2 theta)
  have hC (i : Fin 2) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C i p.1 p.2) ∧
      ∀ z : ℝ, IsPlanarEmbedding (C i z) ∧ range (C i z) = (B z i).boundary := by
    refine ⟨?_, fun z => ⟨hmapEmbedding (T z) (c0 i) (hc0 i), ?_⟩⟩
    · exact hTs.contMDiff.comp
        (contMDiff_fst.prodMk_space ((hc0 i).1.comp contMDiff_snd))
    · change range (fun theta => T z (c0 i theta)) =
        ((W.disc i).mapDiffeomorph (T z)).boundary
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary, ← hc0range i]
      exact range_comp' (T z) (c0 i)
  have hBdisjoint (z : ℝ) : Disjoint (B z 0).boundary (B z 1).boundary := by
    change Disjoint ((W.disc 0).mapDiffeomorph (T z)).boundary
      ((W.disc 1).mapDiffeomorph (T z)).boundary
    rw [BallNeighborhoodChart.mapDiffeomorph_boundary,
      BallNeighborhoodChart.mapDiffeomorph_boundary]
    exact disjoint_image_of_injective (T z).injective hdisjoint0
  have hTlevel (z : ℝ) (hz : z ∈ Ioo (m - d) (m + d)) (x : E2) :
      L.symm (T z x, z) ∈ range j ↔ L.symm (x, W.level) ∈ range j := by
    have hl : W.level ∈ Ioo (m - d) (m + d) := hId ⟨le_rfl, hla⟩
    have hh := (hPhiLevel z hz ((Phi W.level).symm x)).trans
      (hPhiLevel W.level hl ((Phi W.level).symm x)).symm
    change L.symm (Phi z ((Phi W.level).symm x), z) ∈ range j ↔
      L.symm (Phi W.level ((Phi W.level).symm x), W.level) ∈ range j at hh
    change L.symm (Phi z ((Phi W.level).symm x), z) ∈ range j ↔
      L.symm (x, W.level) ∈ range j
    simpa only [Diffeomorph.apply_symm_apply] using hh
  have hlevels (z : ℝ) (hz : z ∈ Ioo (m - d) (m + d)) :
      {x : E2 | L.symm (x, z) ∈ range j} = ⋃ i : Fin 2, (B z i).boundary := by
    ext x
    constructor
    · intro hx
      change L.symm (x, z) ∈ range j at hx
      have hx0 : L.symm ((T z).symm x, W.level) ∈ range j := by
        apply (hTlevel z hz ((T z).symm x)).mp
        simpa only [Diffeomorph.apply_symm_apply] using hx
      have hx0' : (T z).symm x ∈ ⋃ i : Fin 2, (W.disc i).boundary := by
        rw [← hlevel0]
        exact hx0
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx0'
      refine mem_iUnion.mpr ⟨i, ?_⟩
      change x ∈ ((W.disc i).mapDiffeomorph (T z)).boundary
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary]
      exact ⟨(T z).symm x, hi, (T z).apply_symm_apply x⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      change x ∈ ((W.disc i).mapDiffeomorph (T z)).boundary at hi
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary] at hi
      rcases hi with ⟨y, hy, rfl⟩
      apply (hTlevel z hz y).mpr
      change y ∈ {x : E2 | L.symm (x, W.level) ∈ range j}
      rw [hlevel0]
      exact mem_iUnion.mpr ⟨i, hy⟩
  have hcases (z : ℝ) :
      (Disjoint (B z 0).closedRegion (B z 1).closedRegion ↔
        Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion) ∧
      ((B z 0).closedRegion ⊆ (B z 1).inside ↔
        (W.disc 0).closedRegion ⊆ (W.disc 1).inside) ∧
      ((B z 1).closedRegion ⊆ (B z 0).inside ↔
        (W.disc 1).closedRegion ⊆ (W.disc 0).inside) := by
    simp only [B, BallNeighborhoodChart.mapDiffeomorph_closedRegion,
      BallNeighborhoodChart.mapDiffeomorph_inside]
    exact ⟨disjoint_image_iff (T z).injective,
      image_subset_image_iff (T z).injective, image_subset_image_iff (T z).injective⟩
  exact ⟨hregular, fun i => ⟨hc0 i, hc0range i⟩, d, T, hd, hId, hTs, hTi,
    hTzero, hTsupport, hC, hBdisjoint, hTlevel, hlevels, hcases⟩

end PoincareConjecture.M25.Topology3D
