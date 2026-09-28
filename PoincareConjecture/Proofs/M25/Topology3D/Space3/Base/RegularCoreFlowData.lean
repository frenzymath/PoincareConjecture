import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutSides
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularBandField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Compactness.LocallyCompact











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.exists_common_seam_height
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (i : Fin n) :
    ∃ z0 : ℝ,
      (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = 1 →
        (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal < z0) ∧
      (∀ a : Fin S.capCount, S.owner a = i → (S.cap a).sign = -1 →
        z0 < (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal) := by
  classical
  let h : Fin S.capCount → ℝ := fun a =>
    (S.cap a).cutHeight + (S.cap a).sign * (S.cap a).removal
  have hgap (a b : Fin S.capCount) (hai : S.owner a = i)
      (has : (S.cap a).sign = 1) (hbi : S.owner b = i)
      (hbs : (S.cap b).sign = -1) : h a < h b := by
    have ha : ∀ q : UnitTwoSphere,
        (S.cap a).cutHeight < ⟪(u : E3), psi i (q, 0)⟫_ℝ := by
      rcases S.cap_points_on_birth_side a (hzero (S.birth a)) with ⟨_, ha⟩ | ⟨hs, _⟩
      · simpa only [hai] using ha
      · rw [has] at hs
        norm_num at hs
    have hb : ∀ q : UnitTwoSphere,
        ⟪(u : E3), psi i (q, 0)⟫_ℝ < (S.cap b).cutHeight := by
      rcases S.cap_points_on_birth_side b (hzero (S.birth b)) with ⟨hs, _⟩ | ⟨_, hb⟩
      · rw [hbs] at hs
        norm_num at hs
      · simpa only [hbi] using hb
    obtain ⟨q, _hq⟩ := (S.cap a).sourceSeam_isConnected.nonempty
    have hcut : cut (S.birth a) < cut (S.birth b) := by
      rw [← S.cap_cut a, ← S.cap_cut b]
      exact (ha q).trans (hb q)
    have hbirth : S.birth a ≠ S.birth b := by
      intro heq
      rw [heq] at hcut
      exact (lt_irrefl _ hcut)
    have hbuffer : cut (S.birth a) + D < cut (S.birth b) - D := by
      by_contra hnot
      have hleft : cut (S.birth a) + D ∈
          Icc (cut (S.birth a) - D) (cut (S.birth a) + D) := by
        constructor <;> linarith [S.buffer_pos]
      have hright : cut (S.birth a) + D ∈
          Icc (cut (S.birth b) - D) (cut (S.birth b) + D) := by
        exact ⟨le_of_not_gt hnot, by linarith⟩
      exact disjoint_left.mp (S.buffers_separated hbirth) hleft hright
    dsimp only [h]
    rw [has, hbs, one_mul, neg_one_mul, S.cap_cut a, S.cap_cut b]
    linarith [S.cap_removal a, S.cap_removal b]
  let lower : Finset ℝ :=
    (Finset.univ.filter (fun a : Fin S.capCount =>
      S.owner a = i ∧ (S.cap a).sign = 1)).image h
  let upper : Finset ℝ :=
    (Finset.univ.filter (fun a : Fin S.capCount =>
      S.owner a = i ∧ (S.cap a).sign = -1)).image h
  have hlower (a : Fin S.capCount) (hai : S.owner a = i)
      (has : (S.cap a).sign = 1) : h a ∈ lower :=
    Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai, has⟩, rfl⟩
  have hupper (a : Fin S.capCount) (hai : S.owner a = i)
      (has : (S.cap a).sign = -1) : h a ∈ upper :=
    Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai, has⟩, rfl⟩
  have hsep {x y : ℝ} (hx : x ∈ lower) (hy : y ∈ upper) : x < y := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hgap a b (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  by_cases hl : lower.Nonempty
  · by_cases hu : upper.Nonempty
    · let l := lower.max' hl
      let v := upper.min' hu
      have hlv : l < v := hsep (lower.max'_mem hl) (upper.min'_mem hu)
      refine ⟨(l + v) / 2, ?_, ?_⟩
      · intro a hai has
        have ha : h a ≤ l := lower.le_max' (h a) (hlower a hai has)
        change h a < (l + v) / 2
        linarith
      · intro a hai has
        have ha : v ≤ h a := upper.min'_le (h a) (hupper a hai has)
        change (l + v) / 2 < h a
        linarith
    · refine ⟨lower.max' hl + 1, ?_, ?_⟩
      · intro a hai has
        have ha := lower.le_max' (h a) (hlower a hai has)
        change h a < lower.max' hl + 1
        linarith
      · intro a hai has
        exact (hu ⟨h a, hupper a hai has⟩).elim
  · by_cases hu : upper.Nonempty
    · refine ⟨upper.min' hu - 1, ?_, ?_⟩
      · intro a hai has
        exact (hl ⟨h a, hlower a hai has⟩).elim
      · intro a hai has
        have ha := upper.min'_le (h a) (hupper a hai has)
        change upper.min' hu - 1 < h a
        linarith
    · exact ⟨0, fun a hai has => (hl ⟨h a, hlower a hai has⟩).elim,
        fun a hai has => (hu ⟨h a, hupper a hai has⟩).elim⟩


theorem FamilyCutState.exists_seam_source_half_neighborhood
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (a : Fin S.capCount) (q0 : UnitTwoSphere)
    (hq0 : q0 ∈ (S.cap a).sourceSeam) :
    let C := S.cap a
    ∃ W : Set UnitTwoSphere,
      IsOpen W ∧ q0 ∈ W ∧ W ⊆ C.sourceChart.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.sourceChart.symm W ∧
      ∀ q ∈ W,
        let p := C.sourceChart.symm q
        let z := (heightCoordinates (p : E3)).2
        let xi : E2 × ℝ :=
          ((circleDirection (heightCoordinates (p : E3)).1 : E2),
            C.cutHeight + C.sign * (C.removal + C.scale * z))
        p ∈ C.sourceChart.source ∧
          |z| < C.overlapWidth / 2 ∧ |z| < 1 / 4 ∧
          C.sourceChart p = q ∧ xi ∈ C.tube.source ∧
          psi (S.owner a) (q, 0) = C.tube xi ∧
          ⟪(u : E3), psi (S.owner a) (q, 0)⟫_ℝ =
            C.cutHeight + C.sign * (C.removal + C.scale * z) ∧
          (q ∈ S.sourceCore (S.owner a) ↔ 0 ≤ z) ∧
          (q ∈ C.sourceSeam ↔ z = 0) ∧
          ∀ b : Fin S.capCount, b ≠ a →
            psi (S.owner a) (q, 0) ∉ (S.cap b).cap := by
  classical
  let C := S.cap a
  let h : UnitTwoSphere → ℝ := fun p => (heightCoordinates (p : E3)).2
  let O : Set UnitTwoSphere := {p | |h p| < C.overlapWidth / 2}
  let f : UnitTwoSphere → E3 := fun q => psi (S.owner a) (q, 0)
  let A : Set E3 := ⋃ b : {b : Fin S.capCount // b ≠ a}, (S.cap b.1).cap
  let W : Set UnitTwoSphere := C.sourceChart '' O ∩ (f ⁻¹' A)ᶜ
  have hh : Continuous h := (heightCoordinates.continuous.comp continuous_subtype_val).snd
  have hO : IsOpen O := isOpen_lt hh.abs continuous_const
  have hOS : O ⊆ C.sourceChart.source := by
    intro p hp
    apply C.source_band
    change h p < C.overlapWidth
    have hp' : |h p| < C.overlapWidth / 2 := hp
    linarith [le_abs_self (h p), C.overlap_pos]
  have hA : IsCompact A := isCompact_iUnion (fun b => (S.cap b.1).cap_isCompact)
  have hf : Continuous f :=
    (collar_central_contMDiff (psi (S.owner a)) (S.embedding (S.owner a))).continuous
  have hW : IsOpen W := (C.sourceChart.isOpen_image_of_subset_source hO hOS).inter
    (hA.isClosed.preimage hf).isOpen_compl
  have hq0W : q0 ∈ W := by
    obtain ⟨p, hp, hpq⟩ := hq0
    refine ⟨⟨p, ?_, hpq⟩, ?_⟩
    · change |h p| < C.overlapWidth / 2
      change h p = 0 at hp
      rw [hp, abs_zero]
      exact div_pos C.overlap_pos (by norm_num)
    · intro hy
      obtain ⟨b, hb⟩ := mem_iUnion.mp hy
      have hcap : f q0 ∈ C.cap := ⟨q0, ⟨p, hp.le, hpq⟩, rfl⟩
      exact disjoint_left.mp (S.caps_disjoint b.2) hb hcap
  have hWt : W ⊆ C.sourceChart.target := by
    rintro q ⟨⟨p, hp, rfl⟩, _⟩
    exact C.sourceChart.map_source (hOS hp)
  refine ⟨W, hW, hq0W, hWt, C.source_inverse.mono hWt, ?_⟩
  intro q hq
  let p := C.sourceChart.symm q
  let z := (heightCoordinates (p : E3)).2
  let xi : E2 × ℝ :=
    ((circleDirection (heightCoordinates (p : E3)).1 : E2),
      C.cutHeight + C.sign * (C.removal + C.scale * z))
  have hp : p ∈ C.sourceChart.source := C.sourceChart.map_target (hWt hq)
  have hinv : C.sourceChart p = q := C.sourceChart.right_inv (hWt hq)
  have hpO : p ∈ O := by
    obtain ⟨p', hp', heq⟩ := hq.1
    change C.sourceChart.symm q ∈ O
    rw [← heq, C.sourceChart.left_inv (hOS hp')]
    exact hp'
  have hsmall : |z| < C.overlapWidth / 2 := hpO
  have hquarter : |z| < 1 / 4 := by linarith [C.overlap_le]
  have hparam : z < C.overlapWidth := by
    linarith [le_abs_self z, C.overlap_pos]
  have hmodel : C.profile.model p =
      ((circleDirection (heightCoordinates (p : E3)).1 : E2), z) :=
    surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
      C.profile.horizontal_smooth C.profile.vertical_smooth
      (fun t => (C.profile.horizontal_pos t).ne')
      (fun x => (C.profile.vertical_pos x).ne')
      C.profile.horizontal_near C.profile.vertical_far p hquarter.le
  have hxis : xi ∈ C.tube.source := C.tube_source
    ⟨mem_closedBall_zero_iff.mpr
      (norm_eq_of_mem_sphere (circleDirection (heightCoordinates (p : E3)).1)).le,
      mem_univ _⟩
  have heq : psi (S.owner a) (q, 0) = C.tube xi := by
    calc
      psi (S.owner a) (q, 0) = psi (S.owner a) (C.sourceChart p, 0) :=
        congrArg (fun v : UnitTwoSphere => psi (S.owner a) (v, 0)) hinv.symm
      _ = C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale p :=
        C.central_eq p hparam
      _ = C.tube xi := by rw [SurgeryCapProfile.capMap_apply, hmodel]
  have hheight : ⟪(u : E3), psi (S.owner a) (q, 0)⟫_ℝ =
      C.cutHeight + C.sign * (C.removal + C.scale * z) := by
    rw [heq, C.tube_height xi hxis]
  have hinterior : q ∈ C.sourceCapInterior ↔ z < 0 := by
    constructor
    · rintro ⟨p', hp', heq'⟩
      have hpp : p' = p := C.sourceChart.injOn
        (C.south_mem_source p' hp'.le) hp (heq'.trans hinv.symm)
      change (heightCoordinates (p : E3)).2 < 0
      rw [← hpp]
      exact hp'
    · intro hz
      exact ⟨p, hz, hinv⟩
  have hseam : q ∈ C.sourceSeam ↔ z = 0 := by
    constructor
    · rintro ⟨p', hp', heq'⟩
      have hpp : p' = p := C.sourceChart.injOn
        (C.south_mem_source p' hp'.le) hp (heq'.trans hinv.symm)
      change (heightCoordinates (p : E3)).2 = 0
      rw [← hpp]
      exact hp'
    · intro hz
      exact ⟨p, hz, hinv⟩
  have hother : ∀ b : Fin S.capCount, b ≠ a →
      psi (S.owner a) (q, 0) ∉ (S.cap b).cap := by
    intro b hb hqb
    exact hq.2 (mem_iUnion.mpr ⟨⟨b, hb⟩, hqb⟩)
  have hcore : q ∈ S.sourceCore (S.owner a) ↔ 0 ≤ z := by
    constructor
    · intro hc
      by_contra hz
      have hi : q ∈ C.sourceCapInterior := hinterior.mpr (lt_of_not_ge hz)
      exact hc.2 (mem_iUnion.mpr ⟨⟨a, rfl⟩, hi⟩)
    · intro hz
      refine ⟨mem_univ _, ?_⟩
      intro hm
      obtain ⟨b, hb⟩ := mem_iUnion.mp hm
      by_cases hba : b.1 = a
      · have hi : q ∈ C.sourceCapInterior :=
          (congrArg (fun k : Fin S.capCount => q ∈ (S.cap k).sourceCapInterior) hba).mp hb
        exact (not_lt_of_ge hz) (hinterior.mp hi)
      · have hy : psi (S.owner b.1) (q, 0) ∈ (S.cap b.1).cap :=
          ⟨q, (S.cap b.1).sourceCapInterior_subset hb, rfl⟩
        exact hother b.1 hba (by simpa only [b.2] using hy)
  exact ⟨hp, hsmall, hquarter, hinv, hxis, heq, hheight, hcore, hseam, hother⟩


theorem FamilyCutState.exists_regular_core_flow_data
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n)
    (hreg : ∀ q ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q ≠ 0) :
    let U : Set E3 := psi i '' (univ ×ˢ Ioo (-1) 1)
    ∃ rho : E3 → ℝ,
      ContDiffOn ℝ ∞ rho U ∧
      (∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
        rho (psi i p) = p.2) ∧
      (∀ y ∈ U, fderiv ℝ rho y ≠ 0) ∧
      ∃ N : Set E3,
        IsCompact N ∧ S.retainedCore i ⊆ interior N ∧ N ⊆ U ∧
        (∀ y ∈ N, tangentHeightVector (gradient rho y) (u : E3) ≠ 0) ∧
        ∃ F : E3 → E3,
          ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ U ∧
          (∀ y : E3, fderiv ℝ rho y (F y) = 0) ∧
          (∀ y ∈ N, ⟪(u : E3), F y⟫_ℝ = 1) ∧
          ∃ K M : ℝ≥0, ∃ hK : LipschitzWith K F,
            ∃ hM : ∀ y : E3, ‖F y‖ ≤ M,
              ContDiff ℝ ∞
                (fun p : E3 × ℝ => boundedFlow F hK hM p.1 p.2) ∧
              (∀ t : ℝ,
                (fun y : E3 => boundedFlow F hK hM y t) ''
                    range (fun q : UnitTwoSphere => psi i (q, 0)) =
                  range (fun q : UnitTwoSphere => psi i (q, 0))) ∧
              ∀ y : E3, y ∉ U → ∀ t : ℝ,
                boundedFlow F hK hM y t = y := by
  obtain ⟨rho, hrho, hrhopsi, hrhonz⟩ :=
    exists_sphere_collar_defining_function (psi i) (S.embedding i)
  let U : Set E3 := psi i '' (univ ×ˢ Ioo (-1) 1)
  let V : E3 → E3 := fun y => tangentHeightVector (gradient rho y) (u : E3)
  let R : Set E3 := U ∩ V ⁻¹' ({0} : Set E3)ᶜ
  have hU : IsOpen U := collar_image_open (psi i) (S.embedding i)
  have hn (y : E3) (hy : y ∈ U) : gradient rho y ≠ 0 := by
    intro hz
    apply hrhonz y hy
    rw [← toDual_gradient, hz, map_zero]
  have hV : ContDiffOn ℝ ∞ V U := tangentHeightVector_contDiffOn (gradient rho)
    (contDiffOn_gradient_of_isOpen hU rho hrho) hn (u : E3)
  have hR : IsOpen R :=
    hV.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hKR : S.retainedCore i ⊆ R := by
    rintro y ⟨q, hq, rfl⟩
    refine ⟨⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩, ?_⟩
    exact tangentHeightVector_ne_zero_of_heightCross _ _
      (collar_regular_height_cross_ne_zero (psi i) (S.embedding i)
        rho hrho hrhopsi hrhonz (u : E3) q (hreg q hq))
  obtain ⟨N, hN, hKN, hNR⟩ :=
    exists_compact_between (S.retainedCore_geometry i).1 hR hKR
  have hNU : N ⊆ U := fun y hy => (hNR hy).1
  have hNV : ∀ y ∈ N, tangentHeightVector (gradient rho y) (u : E3) ≠ 0 :=
    fun y hy => (hNR hy).2
  obtain ⟨F, hF, hFc, hFs, hFrho, hFH⟩ :=
    exists_compact_height_band_field hN hU hNU rho hrho hn (u : E3)
      (fun _ : ℝ => (1 : ℝ)) contDiff_const (fun y hy _ => hNV y hy)
  obtain ⟨K, M, hK, hM⟩ := compactField_bounds F hF hFc
  have hzero (y : E3) (hy : y ∉ U) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hy (hFs hm))
  have hpreserve (y : E3) (hy : y ∈ range (fun q : UnitTwoSphere => psi i (q, 0)))
      (t : ℝ) : boundedFlow F hK hM y t ∈
        range (fun q : UnitTwoSphere => psi i (q, 0)) := by
    obtain ⟨q, rfl⟩ := hy
    have hqU : psi i (q, 0) ∈ U := ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
    have hflowU := boundedFlow_mapsTo_set F hK hM hzero t hqU
    have hrhoflow := boundedFlow_preserves_firstIntegral F hK hM hzero rho
      (fun v hv => (hrho.contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp))
      (fun v _ => hFrho v) (psi i (q, 0)) hqU t
    have hrhozero : rho (boundedFlow F hK hM (psi i (q, 0)) t) = 0 :=
      hrhoflow.trans (hrhopsi (q, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨p, s⟩, hps, heq⟩ := hflowU
    have hs : s = 0 :=
      (hrhopsi (p, s) hps).symm.trans ((congrArg rho heq).trans hrhozero)
    subst s
    exact ⟨p, heq⟩
  refine ⟨rho, hrho, hrhopsi, hrhonz, N, hN, hKN, hNU, hNV,
    F, hF, hFc, hFs, hFrho, hFH, K, M, hK, hM,
    boundedFlow_contDiff F hK hM hF hFc, ?_, ?_⟩
  · intro t
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hpreserve x hx t
    · intro y hy
      refine ⟨boundedFlow F hK hM y (-t), hpreserve y hy (-t), ?_⟩
      simpa only [neg_neg] using boundedFlow_neg F hK hM y (-t)
  · intro y hy t
    exact boundedFlow_eq_self F hK hM y (hzero y hy) t

end PoincareConjecture.M25.Topology3D
