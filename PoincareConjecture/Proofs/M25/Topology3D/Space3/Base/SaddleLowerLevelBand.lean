import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerSourceSublevel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic.FinCases











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D




theorem SaddleLowerLevelData.exists_source_level_band
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (tau : ℝ) (htau : 0 < tau) :
    ∃ eta : ℝ, 0 < eta ∧ eta < tau ∧
      (∀ i : Fin 2, (univ : Set UnitCircle) ×ˢ
        Icc (W.level - eta) (W.level + eta) ⊆ (W.leg i).source) ∧
      ∀ z ∈ Icc (W.level - eta) (W.level + eta),
        {q : UnitTwoSphere | inner ℝ (u : E3) (psi (q, 0)) = z} =
          ⋃ i : Fin 2, range (fun theta : UnitCircle => W.leg i (theta, z)) := by
  classical
  let f : UnitTwoSphere → ℝ := fun q => inner ℝ (u : E3) (psi (q, 0))
  let ell : Fin 2 → ℝ := fun i =>
    (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal
  let O := ⋃ i : Fin 2, (W.leg i).target
  have hf : Continuous f := continuous_const.inner
    (collar_central_contMDiff psi hpsi).continuous
  have hO : IsOpen O := isOpen_iUnion (fun i => (W.leg i).open_target)
  have hell (i : Fin 2) : ell i < W.level := by
    simpa only [ell, W.label_lower i, one_mul] using
      W.lower_seams_lt_level (W.label i) (W.label_lower i)
  have hlegsource (i : Fin 2) :
      (univ : Set UnitCircle) ×ˢ Icc (ell i) W.level ⊆ (W.leg i).source := by
    simpa only [ell, W.label_lower i, one_mul] using W.leg_source i
  have hcapbelow (i : Fin 2) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap (W.label i)).sourceCap) : f q < W.level := by
    obtain ⟨p, hp, rfl⟩ := hq
    let C := D.cap (W.label i)
    have hsign : C.sign = 1 := W.label_lower i
    have hmp : (C.profile.model p).2 ≤ 0 := by
      change C.profile.vertical _ * (heightCoordinates (p : E3)).2 ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (C.profile.vertical_pos _).le hp
    change inner ℝ (u : E3) (psi (C.sourceChart p, 0)) < W.level
    rw [C.central_eq p (lt_of_le_of_lt hp C.overlap_pos),
      SurgeryCapProfile.capMap_apply, C.tube_height
        ((C.profile.model p).1, C.cutHeight + C.sign *
          (C.removal + C.scale * (C.profile.model p).2))
        (C.tube_source ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le p),
          mem_univ _⟩), hsign, one_mul]
    have hneg := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hmp
    have hseam : C.cutHeight + C.removal < W.level := hell i
    linarith
  obtain ⟨_hlabels, hsub, _hcompact, _hdis⟩ :=
    SaddleLowerLevelData.source_sublevel_decomposition psi hpsi u D W
  change {q : UnitTwoSphere | f q ≤ W.level} =
    ⋃ i : Fin 2, (D.cap (W.label i)).sourceCap ∪
      W.leg i '' ((univ : Set UnitCircle) ×ˢ Icc (ell i) W.level) at hsub
  have hlevelO (q : UnitTwoSphere) (hq : f q = W.level) : q ∈ O := by
    have hqsub : q ∈ {q : UnitTwoSphere | f q ≤ W.level} := hq.le
    rw [hsub] at hqsub
    obtain ⟨i, hi⟩ := mem_iUnion.mp hqsub
    rcases hi with hcap | ⟨p, hp, rfl⟩
    · exact False.elim ((ne_of_lt (hcapbelow i q hcap)) hq)
    · exact mem_iUnion.mpr ⟨i, (W.leg i).map_source (hlegsource i hp)⟩
  have hnear : ∀ᶠ z in 𝓝 W.level, ∀ q ∈ f ⁻¹' ({z} : Set ℝ), q ∈ O :=
    hf.isClosedMap.eventually_nhds_fiber W.level (fun q hq =>
      hO.mem_nhds (hlevelO q (mem_singleton_iff.mp hq)))
  obtain ⟨e, he, hecover⟩ := Metric.mem_nhds_iff.mp hnear
  have hbuffers (i : Fin 2) : ∃ d : ℝ, 0 < d ∧
      (univ : Set UnitCircle) ×ˢ Icc (W.level - d) (W.level + d) ⊆ (W.leg i).source :=
    exists_saddle_end_circle_buffer (W.leg i).source (W.leg i).open_source
      W.level W.level le_rfl (fun p hp => hlegsource i
        ⟨hp.1, (hell i).le.trans hp.2.1, hp.2.2⟩)
  choose d hd hbuffer using hbuffers
  let m := min tau (min e (min (d 0) (d 1)))
  let eta := m / 2
  have hm : 0 < m := lt_min htau (lt_min he (lt_min (hd 0) (hd 1)))
  have heta : 0 < eta := half_pos hm
  have hetaM : eta < m := half_lt_self hm
  have hmtau : m ≤ tau := min_le_left _ _
  have hme : m ≤ e := (min_le_right _ _).trans (min_le_left _ _)
  have hmd (i : Fin 2) : m ≤ d i := by
    have hsmall : m ≤ min (d 0) (d 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    fin_cases i
    · exact hsmall.trans (min_le_left _ _)
    · exact hsmall.trans (min_le_right _ _)
  have hsourceBand (i : Fin 2) :
      (univ : Set UnitCircle) ×ˢ Icc (W.level - eta) (W.level + eta) ⊆
        (W.leg i).source := by
    apply Subset.trans ?_ (hbuffer i)
    apply prod_mono subset_rfl
    have hetad := hetaM.trans_le (hmd i)
    exact Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨eta, heta, hetaM.trans_le hmtau, hsourceBand, ?_⟩
  intro z hz
  ext q
  constructor
  · intro hq
    have hzball : z ∈ ball W.level e := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      have hetae := hetaM.trans_le hme
      constructor <;> linarith [hz.1, hz.2]
    have hqO : q ∈ O := hecover hzball q (show q ∈ f ⁻¹' ({z} : Set ℝ) from hq)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hqO
    let p := (W.leg i).symm q
    have hp : p ∈ (W.leg i).source := (W.leg i).map_target hi
    have hpq : W.leg i p = q := (W.leg i).right_inv hi
    have hpz : p.2 = z := (W.leg_height i p hp).symm.trans (by rw [hpq]; exact hq)
    refine mem_iUnion.mpr ⟨i, ⟨p.1, ?_⟩⟩
    rw [← hpz]
    exact hpq
  · intro hq
    obtain ⟨i, theta, rfl⟩ := mem_iUnion.mp hq
    exact W.leg_height i (theta, z) (hsourceBand i ⟨mem_univ _, hz⟩)




theorem SaddleLowerLevelData.exists_physical_level_band
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (V : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (tau : ℝ) (htau : 0 < tau)
    (hcircle : ∀ i z, z ∈ Icc (W.level - tau) (W.level + tau) →
      V i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        range (fun theta : UnitCircle => psi (W.leg i (theta, z), 0))) :
    ∃ eta : ℝ, 0 < eta ∧ eta < tau ∧
      ∀ y ∈ range (fun q : UnitTwoSphere => psi (q, 0)),
        inner ℝ (u : E3) y ∈ Icc (W.level - eta) (W.level + eta) →
          ∃ i : Fin 2, y ∈ V i '' (sphere (0 : E2) 1 ×ˢ
            ({inner ℝ (u : E3) y} : Set ℝ)) := by
  obtain ⟨eta, heta, hetatau, _hsource, hlevels⟩ :=
    W.exists_source_level_band psi hpsi u D tau htau
  refine ⟨eta, heta, hetatau, ?_⟩
  rintro y ⟨q, rfl⟩ hheight
  let z := inner ℝ (u : E3) (psi (q, 0))
  have hq : q ∈ ⋃ i : Fin 2, range (fun theta : UnitCircle => W.leg i (theta, z)) := by
    rw [← hlevels z hheight]
    rfl
  obtain ⟨i, theta, htheta⟩ := mem_iUnion.mp hq
  refine ⟨i, ?_⟩
  rw [hcircle i z ⟨by linarith [hheight.1], by linarith [hheight.2]⟩]
  exact ⟨theta, congrArg (fun p => psi (p, 0)) htheta⟩

end PoincareConjecture.M25.Topology3D
