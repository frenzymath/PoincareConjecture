import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.sourceCore_mem_nhds_of_not_seam
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (q : UnitTwoSphere) (hq : q ∈ S.sourceCore i)
    (hseam : ∀ a : Fin S.capCount, S.owner a = i →
      q ∉ (S.cap a).sourceSeam) :
    S.sourceCore i ∈ 𝓝 q := by
  classical
  let I := {a : Fin S.capCount // S.owner a = i}
  let U : Set UnitTwoSphere := (⋃ a : I, (S.cap a.1).sourceCap)ᶜ
  have hU : IsOpen U :=
    (isClosed_iUnion_of_finite (fun a : I => (S.cap a.1).sourceCap_isCompact.isClosed)).isOpen_compl
  have hqU : q ∈ U := by
    intro hqUnion
    obtain ⟨a, ha⟩ := mem_iUnion.mp hqUnion
    apply hseam a.1 a.2
    rw [← (S.cap a.1).sourceCap_diff_interior]
    refine ⟨ha, ?_⟩
    intro hi
    exact hq.2 (mem_iUnion.mpr ⟨a, hi⟩)
  have hsub : U ⊆ S.sourceCore i := by
    intro x hx
    refine ⟨mem_univ _, ?_⟩
    intro hi
    obtain ⟨a, ha⟩ := mem_iUnion.mp hi
    exact hx (mem_iUnion.mpr ⟨a, (S.cap a.1).sourceCapInterior_subset ha⟩)
  exact mem_of_superset (hU.mem_nhds hqU) hsub


theorem FamilyCutState.sourceCore_extremum_on_seam
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) (q : UnitTwoSphere) (hq : q ∈ S.sourceCore i)
    (hregular : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0)
    (hextreme :
      IsMinOn (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ)
        (S.sourceCore i) q ∨
      IsMaxOn (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ)
        (S.sourceCore i) q) :
    ∃ a : Fin S.capCount, S.owner a = i ∧ q ∈ (S.cap a).sourceSeam ∧
      ∀ y ∈ (S.cap a).sourceSeam,
        ⟪(u : E3), psi i (y, 0)⟫_ℝ =
          (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi i (p, 0)⟫_ℝ
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
      (collar_central_contMDiff (psi i) (S.embedding i))
  have hfermat (hloc : IsLocalMin f q ∨ IsLocalMax f q) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0 := by
    let c := chartAt E2 q
    let F : E2 → ℝ := f ∘ c.symm
    have hqc : q ∈ c.source := mem_chart_source E2 q
    have hcq : c q ∈ c.target := c.map_source hqc
    have hcs : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ c c.source := contMDiffOn_chart
    have hci : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ c.symm c.target :=
      contMDiffOn_chart_symm
    have hcd : c.MDifferentiable (𝓡 2) 𝓘(ℝ, E2) :=
      ⟨hcs.mdifferentiableOn (by simp), hci.mdifferentiableOn (by simp)⟩
    have hFzero : fderiv ℝ F (c q) = 0 := by
      rcases hloc with hmin | hmax
      · have hmin' : IsLocalMin f (c.symm (c q)) := by rwa [c.left_inv hqc]
        exact (hmin'.comp_continuous (c.continuousAt_symm hcq)).fderiv_eq_zero
      · have hmax' : IsLocalMax f (c.symm (c q)) := by rwa [c.left_inv hqc]
        exact (hmax'.comp_continuous (c.continuousAt_symm hcq)).fderiv_eq_zero
    have hcomp : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (c.symm (c q))).comp
        (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm (c q)) = 0 := by
      have h := mfderiv_comp (c q) (hf.mdifferentiable (by simp) (c.symm (c q)))
        (hcd.mdifferentiableAt_symm hcq)
      rw [mfderiv_eq_fderiv] at h
      exact h.symm.trans hFzero
    have hnative : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (c.symm (c q)) = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, hw⟩ := hcd.symm.mfderiv_surjective hcq v
      have hvalue := congrArg
        (fun L : TangentSpace 𝓘(ℝ, E2) (c q) →L[ℝ] ℝ => L w) hcomp
      change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (c.symm (c q))
        (mfderiv 𝓘(ℝ, E2) (𝓡 2) c.symm (c q) w) = 0 at hvalue
      rwa [hw] at hvalue
    rw [c.left_inv hqc] at hnative
    exact hnative
  have hex : ∃ a : Fin S.capCount, S.owner a = i ∧ q ∈ (S.cap a).sourceSeam := by
    by_contra hnot
    have hn := S.sourceCore_mem_nhds_of_not_seam i q hq
      (fun a ha hqa => hnot ⟨a, ha, hqa⟩)
    apply hregular
    apply hfermat
    exact hextreme.elim (fun h => Or.inl (h.isLocalMin hn))
      (fun h => Or.inr (h.isLocalMax hn))
  obtain ⟨a, ha, hqa⟩ := hex
  refine ⟨a, ha, hqa, ?_⟩
  intro y hy
  let C := S.cap a
  have hym : psi (S.owner a) (y, 0) ∈ C.seam := ⟨y, hy, rfl⟩
  rw [C.seam_eq_image, surgery_cap_equator_image] at hym
  obtain ⟨⟨x, z⟩, ⟨hx, hz⟩, heq⟩ := hym
  have hz' : z = C.cutHeight + C.sign * C.removal := hz
  have hsource : (x, z) ∈ C.tube.source :=
    C.tube_source ⟨mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hx).le,
      mem_univ _⟩
  have hheight : ⟪(u : E3), psi (S.owner a) (y, 0)⟫_ℝ = z := by
    rw [← heq, C.tube_height _ hsource]
  simpa only [ha] using hheight.trans hz'


theorem FamilyCutState.exists_sourceCore_height_ends
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n)
    (hregular : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ (a b : Fin S.capCount) (p q : UnitTwoSphere),
      S.owner a = i ∧ S.owner b = i ∧ a ≠ b ∧
      p ∈ S.sourceCore i ∧ q ∈ S.sourceCore i ∧
      p ∈ (S.cap a).sourceSeam ∧ q ∈ (S.cap b).sourceSeam ∧
      IsMinOn (fun y : UnitTwoSphere => ⟪(u : E3), psi i (y, 0)⟫_ℝ)
        (S.sourceCore i) p ∧
      IsMaxOn (fun y : UnitTwoSphere => ⟪(u : E3), psi i (y, 0)⟫_ℝ)
        (S.sourceCore i) q ∧
      (∀ y ∈ (S.cap a).sourceSeam,
        ⟪(u : E3), psi i (y, 0)⟫_ℝ =
          (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) ∧
      (∀ y ∈ (S.cap b).sourceSeam,
        ⟪(u : E3), psi i (y, 0)⟫_ℝ =
          (S.cap b).cutHeight + (S.cap b).sign * (S.cap b).removal) ∧
      (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal <
        (S.cap b).cutHeight + (S.cap b).sign * (S.cap b).removal := by
  classical
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi i (p, 0)⟫_ℝ
  have hescape (a : Fin S.capCount) (ha : S.owner a = i)
      (p : UnitTwoSphere) (hp : p ∈ (S.cap a).sourceSeam) :
      ∃ y ∈ S.sourceCore i, f y ≠ f p := by
    let C := S.cap a
    obtain ⟨xi, hxi, hxip⟩ := hp
    let x := (heightCoordinates (xi : E3)).1
    have hx : ‖x‖ = 1 := by
      have hsq := sphere_height_coordinates_sq xi
      rw [hxi] at hsq
      change ‖x‖ ^ 2 + 0 ^ 2 = 1 at hsq
      nlinarith [norm_nonneg x]
    have hxpoint : northSpherePoint x = xi := by
      apply Subtype.ext
      apply heightCoordinates.injective
      have h := northSpherePoint_equator
        (⟨x, mem_sphere_zero_iff_norm.mpr hx⟩ : UnitCircle)
      exact h.trans (Prod.ext rfl hxi.symm)
    let xiPath : ℝ → UnitTwoSphere := fun t => northSpherePoint ((1 - t) • x)
    let z : ℝ → ℝ := fun t => (heightCoordinates (xiPath t : E3)).2
    let y : ℝ → UnitTwoSphere := fun t => C.sourceChart (xiPath t)
    have hxi0 : xiPath 0 = xi := by simp only [xiPath, sub_zero, one_smul, hxpoint]
    have hz0 : z 0 = 0 := by change (heightCoordinates (xiPath 0 : E3)).2 = 0; rwa [hxi0]
    have hxiCont : Continuous xiPath :=
      northSpherePoint_contMDiff.continuous.comp
        ((continuous_const.sub continuous_id).smul continuous_const)
    have hzCont : Continuous z :=
      (heightCoordinates.continuous.comp (continuous_subtype_val.comp hxiCont)).snd
    have hyCont : ContinuousAt y 0 := by
      apply (C.sourceChart.continuousAt ?_).comp hxiCont.continuousAt
      rw [hxi0]
      exact C.south_mem_source xi hxi.le
    have hy0 : y 0 = p := by change C.sourceChart (xiPath 0) = p; rwa [hxi0]
    let J := {d : Fin S.capCount // S.owner d = i ∧ d ≠ a}
    let V : Set UnitTwoSphere := (⋃ d : J, (S.cap d.1).sourceCap)ᶜ
    have hV : IsOpen V :=
      (isClosed_iUnion_of_finite
        (fun d : J => (S.cap d.1).sourceCap_isCompact.isClosed)).isOpen_compl
    have hpV : p ∈ V := by
      intro hU
      obtain ⟨d, hd⟩ := mem_iUnion.mp hU
      have hpcap : p ∈ C.sourceCap := ⟨xi, hxi.le, hxip⟩
      have hpa : psi i (p, 0) ∈ C.cap := by
        simpa only [ha] using (show psi (S.owner a) (p, 0) ∈ C.cap from ⟨p, hpcap, rfl⟩)
      have hpd : psi i (p, 0) ∈ (S.cap d.1).cap := by
        simpa only [d.2.1] using
          (show psi (S.owner d.1) (p, 0) ∈ (S.cap d.1).cap from ⟨p, hd, rfl⟩)
      exact disjoint_left.mp (S.caps_disjoint d.2.2) hpd hpa
    have hnearV : ∀ᶠ t in 𝓝 (0 : ℝ), y t ∈ V := by
      apply hyCont
      rw [hy0]
      exact hV.mem_nhds hpV
    have hnearZ : ∀ᶠ t in 𝓝 (0 : ℝ), z t < C.overlapWidth := by
      apply (hzCont.continuousAt : ContinuousAt z 0).preimage_mem_nhds
        (t := Iio C.overlapWidth)
      exact Iio_mem_nhds (by rw [hz0]; exact C.overlap_pos)
    obtain ⟨delta, hdelta, hdeltaSub⟩ := Metric.mem_nhds_iff.mp (hnearV.and hnearZ)
    let t : ℝ := min (delta / 2) (1 / 2)
    have ht : 0 < t := lt_min (by linarith) (by norm_num)
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have htDelta : t < delta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htBall : t ∈ ball (0 : ℝ) delta := by
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
      exact htDelta
    obtain ⟨hytV, hztSmall⟩ := hdeltaSub htBall
    have hxtNorm : ‖(1 - t) • x‖ = 1 - t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1), hx, mul_one]
    have hzt : 0 < z t := by
      change 0 < (heightCoordinates (northSpherePoint ((1 - t) • x) : E3)).2
      rw [northSpherePoint_coordinates, hxtNorm]
      apply div_pos
      · nlinarith
      · positivity
    have hztAbs : |z t| ≤ 1 / 4 := by
      rw [abs_of_pos hzt]
      exact hztSmall.le.trans C.overlap_le
    have hqtSource : xiPath t ∈ C.sourceChart.source := C.source_band _ hztSmall
    have hnotOwn : y t ∉ C.sourceCap := by
      rintro ⟨eta, heta, heq⟩
      have he : eta = xiPath t :=
        C.sourceChart.injOn (C.south_mem_source eta heta) hqtSource heq
      have hnonpos : z t ≤ 0 := by
        change (heightCoordinates (xiPath t : E3)).2 ≤ 0
        rw [← he]
        exact heta
      exact (not_le_of_gt hzt) hnonpos
    have hytCore : y t ∈ S.sourceCore i := by
      refine ⟨mem_univ _, ?_⟩
      intro hi
      obtain ⟨d, hd⟩ := mem_iUnion.mp hi
      have hfull := (S.cap d.1).sourceCapInterior_subset hd
      by_cases hda : d.1 = a
      · apply hnotOwn
        change y t ∈ (S.cap a).sourceCap
        rw [← hda]
        exact hfull
      · exact hytV (mem_iUnion.mpr ⟨⟨d.1, d.2, hda⟩, hfull⟩)
    have hplaced (w : UnitTwoSphere)
        (hw : (heightCoordinates (w : E3)).2 < C.overlapWidth)
        (hwAbs : |(heightCoordinates (w : E3)).2| ≤ 1 / 4) :
        f (C.sourceChart w) = C.cutHeight +
          C.sign * (C.removal + C.scale * (heightCoordinates (w : E3)).2) := by
      have hsource : ((C.profile.model w).1,
          C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model w).2)) ∈
          C.tube.source :=
        C.tube_source ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le w), mem_univ _⟩
      have hmodel : (C.profile.model w).2 = (heightCoordinates (w : E3)).2 := by
        have h := surgeryCapModel_cylinder
          C.profile.horizontal C.profile.vertical
          C.profile.horizontal_smooth C.profile.vertical_smooth
          (fun z => (C.profile.horizontal_pos z).ne') (fun x => (C.profile.vertical_pos x).ne')
          C.profile.horizontal_near C.profile.vertical_far w hwAbs
        have hsnd := congrArg (fun v : E2 × ℝ => v.2) h
        exact hsnd
      have hheight : ⟪(u : E3), psi (S.owner a) (C.sourceChart w, 0)⟫_ℝ =
          C.cutHeight + C.sign * (C.removal + C.scale * (heightCoordinates (w : E3)).2) := by
        rw [C.central_eq w hw, SurgeryCapProfile.capMap_apply, C.tube_height _ hsource, hmodel]
      simpa only [ha] using hheight
    have hpHeight : f p = C.cutHeight + C.sign * C.removal := by
      have h := hplaced xi (by rw [hxi]; exact C.overlap_pos) (by rw [hxi]; norm_num)
      rw [hxip, hxi, mul_zero, add_zero] at h
      exact h
    have hyHeight : f (y t) = C.cutHeight + C.sign * C.removal +
        C.sign * C.scale * z t := by
      calc
        f (y t) = C.cutHeight + C.sign * (C.removal + C.scale * z t) :=
          hplaced (xiPath t) hztSmall hztAbs
        _ = _ := by ring
    refine ⟨y t, hytCore, ?_⟩
    intro heq
    have hsign : C.sign ≠ 0 := by
      intro hs
      have h := C.sign_abs
      rw [hs, abs_zero] at h
      norm_num at h
    apply mul_ne_zero (mul_ne_zero hsign C.scale_pos.ne') hzt.ne'
    rw [hyHeight, hpHeight] at heq
    linarith
  obtain ⟨hcompact, hconnected⟩ := S.sourceCore_compact_connected i
  have hf : Continuous f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).continuous.comp
      (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn hconnected.nonempty hf.continuousOn
  obtain ⟨q, hq, hmax⟩ := hcompact.exists_isMaxOn hconnected.nonempty hf.continuousOn
  obtain ⟨a, ha, hpa, hha⟩ :=
    S.sourceCore_extremum_on_seam i p hp (hregular p hp) (Or.inl hmin)
  obtain ⟨b, hb, hqb, hhb⟩ :=
    S.sourceCore_extremum_on_seam i q hq (hregular q hq) (Or.inr hmax)
  obtain ⟨y, hy, hne⟩ := hescape a ha p hpa
  have hlt : f p < f q := (lt_of_le_of_ne (hmin hy) (Ne.symm hne)).trans_le (hmax hy)
  have hheights : (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal <
      (S.cap b).cutHeight + (S.cap b).sign * (S.cap b).removal := by
    change ⟪(u : E3), psi i (p, 0)⟫_ℝ < ⟪(u : E3), psi i (q, 0)⟫_ℝ at hlt
    rwa [hha p hpa, hhb q hqb] at hlt
  have hab : a ≠ b := by
    intro heq
    rw [heq] at hheights
    exact (lt_irrefl _) hheights
  exact ⟨a, b, p, q, ha, hb, hab, hp, hq, hpa, hqb, hmin, hmax, hha, hhb, hheights⟩

end PoincareConjecture.M25.Topology3D
