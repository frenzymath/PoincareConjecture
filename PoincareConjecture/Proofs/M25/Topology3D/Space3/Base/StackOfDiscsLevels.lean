import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularBandTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelCircle
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection











set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D



theorem SurgeryCapTag.cap_seam_signed_height
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) :
    let s := C.cutHeight + C.sign * C.removal
    ∀ y ∈ C.cap,
      C.sign * (⟪(u : E3), y⟫_ℝ - s) ≤ 0 ∧
      (C.sign * (⟪(u : E3), y⟫_ℝ - s) = 0 ↔ y ∈ C.seam) ∧
      (C.sign * (⟪(u : E3), y⟫_ℝ - s) < 0 ↔ y ∉ C.seam) := by
  dsimp only
  have hs : C.sign * C.sign = 1 := by nlinarith [C.sign_abs, sq_abs C.sign]
  have hheight (q : UnitTwoSphere) :
      C.sign * (⟪(u : E3),
        C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q⟫_ℝ -
          (C.cutHeight + C.sign * C.removal)) = C.scale * (C.profile.model q).2 := by
    rw [SurgeryCapProfile.capMap_apply, C.tube_height
      ((C.profile.model q).1, C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2))
      (C.tube_source ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q),
        mem_univ _⟩)]
    calc
      C.sign * (C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) -
        (C.cutHeight + C.sign * C.removal)) =
          (C.sign * C.sign) * (C.scale * (C.profile.model q).2) := by ring
      _ = C.scale * (C.profile.model q).2 := by rw [hs, one_mul]
  have hzero (q : UnitTwoSphere) :
      (C.profile.model q).2 = 0 ↔ (heightCoordinates (q : E3)).2 = 0 := by
    change C.profile.vertical
      (C.profile.horizontal (heightCoordinates (q : E3)).2 •
        (heightCoordinates (q : E3)).1) * (heightCoordinates (q : E3)).2 = 0 ↔ _
    simp only [mul_eq_zero, (C.profile.vertical_pos _).ne', false_or]
  intro y hy
  obtain ⟨q, hq, rfl⟩ := C.cap_eq_image ▸ hy
  have hn : (C.profile.model q).2 ≤ 0 :=
    (surgeryCapModel_snd_nonpos_iff C.profile.horizontal C.profile.vertical
      C.profile.horizontal_smooth C.profile.vertical_smooth
      (fun z => (C.profile.horizontal_pos z).ne')
      (fun x => (C.profile.vertical_pos x).ne') C.profile.vertical_pos q).mpr hq
  have hz : C.sign * (⟪(u : E3),
      C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q⟫_ℝ -
        (C.cutHeight + C.sign * C.removal)) = 0 ↔
      C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q ∈ C.seam := by
    constructor
    · intro h
      rw [hheight, mul_eq_zero] at h
      rw [C.seam_eq_image]
      exact ⟨q, (hzero q).mp (h.resolve_left C.scale_pos.ne'), rfl⟩
    · intro h
      obtain ⟨p, hp, he⟩ := C.seam_eq_image ▸ h
      rw [← he, hheight, (hzero p).mpr hp, mul_zero]
  have hle := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hn
  refine ⟨by rwa [hheight], hz, ?_⟩
  rw [← hz]
  exact lt_iff_le_and_ne.trans ⟨fun h => h.2, fun h => ⟨by rwa [hheight], h⟩⟩



theorem exists_stackCircleFamily_of_connected_regular_band
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (a b : ℝ) (hab : a < b)
    (K : Set E3) (hK : IsConnected K)
    (hband : K = {y : E3 | y ∈ range (fun q => psi (q, 0)) ∧
      ⟪(u : E3), y⟫_ℝ ∈ Icc a b})
    (hreg : ∀ q : UnitTwoSphere, psi (q, 0) ∈ K →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ c : ℝ → UnitCircle → E2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => c p.1 p.2) ∧
      (∀ z ∈ Icc (a - eta) (b + eta), IsPlanarEmbedding (c z)) ∧
      ∀ z ∈ Icc (a - eta) (b + eta),
        range (c z) = {x : E2 |
          (heightPlaneCoordinates u).symm (x, z) ∈
            range (fun q : UnitTwoSphere => psi (q, 0))} := by
  have hregular q (hq : ⟪(u : E3), psi (q, 0)⟫_ℝ ∈ Icc a b) :=
    hreg q (hband.symm ▸ ⟨mem_range_self q, hq⟩)
  obtain ⟨d, hd, hbandd, Phi, hPhi, hPhi0, hPhiadd, hPhiS, hPhih, hPhib⟩ :=
    exists_regular_collar_band_transport psi hpsi (u : E3) a b hab.le hregular
  let m := (a + b) / 2
  let S := range (fun q : UnitTwoSphere => psi (q, 0))
  let L := collarHeightLevel psi (u : E3) m
  have hm : m ∈ Icc a b := by dsimp [m]; constructor <;> linarith
  have hLmem (y : E3) : y ∈ L ↔ y ∈ S ∧ ⟪(u : E3), y⟫_ℝ = m := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mem_range_self q, hq⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, hq, rfl⟩
  let R : E3 → E3 := fun y => Phi (m - ⟪(u : E3), y⟫_ℝ) y
  have hR : Continuous R :=
    hPhi.continuous.comp (continuous_id.prodMk
      (continuous_const.sub (continuous_const.inner continuous_id)))
  have hRL : R '' K = L := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hy' := hband ▸ hy
      exact (hLmem _).mpr ⟨hPhiS _ hy'.1, hPhib y hy'.1 (hbandd hy'.2)⟩
    · intro y hy
      have hy' := (hLmem y).mp hy
      refine ⟨y, hband.symm ▸ ⟨hy'.1, hy'.2.symm ▸ hm⟩, ?_⟩
      dsimp [R]
      rw [hy'.2, sub_self, hPhi0]
  have hL : IsConnected L := hRL ▸ hK.image R hR.continuousOn
  let : ConnectedSpace L := isConnected_iff_connectedSpace.mp hL
  obtain ⟨y, hy⟩ := hL.nonempty
  let y0 : L := ⟨y, hy⟩
  have hregularm q (hq : ⟪(u : E3), psi (q, 0)⟫_ℝ = m) :=
    hregular q (hq.symm ▸ hm)
  obtain ⟨e, he, hed⟩ :=
    exists_regular_collar_component_circle psi hpsi (u : E3) m hregularm y0
  let k : UnitCircle → E3 := fun q => ((e q).1 : E3)
  have hk : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ k := he
  have hki : Injective k := by
    intro p q hpq
    exact e.injective (Subtype.ext (Subtype.ext hpq))
  have hkL : range k = L := by
    apply Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      exact (e q).1.2
    · intro x hx
      let p : connectedComponent y0 := ⟨⟨x, hx⟩, by
        rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial⟩
      obtain ⟨q, hq⟩ := e.surjective p
      exact ⟨q, congrArg (fun z : connectedComponent y0 => (z.1 : E3)) hq⟩
  have hkheight (q : UnitCircle) : ⟪(u : E3), k q⟫_ℝ = m :=
    ((hLmem _).mp (hkL ▸ mem_range_self q)).2
  have hkS (q : UnitCircle) : k q ∈ S :=
    ((hLmem _).mp (hkL ▸ mem_range_self q)).1
  let eta := min (a - (m - d)) ((m + d) - b) / 2
  have ha := (hbandd (left_mem_Icc.mpr hab.le)).1
  have hb := (hbandd (right_mem_Icc.mpr hab.le)).2
  have heta : 0 < eta := by
    exact div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)
  have he1 : eta ≤ (a - (m - d)) / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he2 : eta ≤ ((m + d) - b) / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hetaband : Icc (a - eta) (b + eta) ⊆ Ioo (m - d) (m + d) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  let c : ℝ → UnitCircle → E2 :=
    fun z q => (heightPlaneCoordinates u (Phi (z - m) (k q))).1
  have hparameter : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E3 × ℝ) ∞
      (fun p : ℝ × UnitCircle => (k p.2, p.1 - m)) :=
    (hk.comp contMDiff_snd).prodMk_space (contMDiff_fst.sub contMDiff_const)
  have hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2) :=
    contDiff_fst.contMDiff.comp ((heightPlaneCoordinates u).contDiff.contMDiff.comp
      (hPhi.contMDiff.comp hparameter))
  have hztime (z : ℝ) (hz : z ∈ Icc (a - eta) (b + eta)) : z - m ∈ Ioo (-d) d := by
    have hz' := hetaband hz
    constructor <;> linarith [hz'.1, hz'.2]
  have hheight (z : ℝ) (hz : z ∈ Icc (a - eta) (b + eta)) (q : UnitCircle) :
      ⟪(u : E3), Phi (z - m) (k q)⟫_ℝ = z := by
    have h := hPhih (k q) (hkS q) (hkheight q) (z - m) (hztime z hz)
    dsimp [m] at h ⊢
    linarith
  refine ⟨eta, heta, c, hc, ?_, ?_⟩
  · intro z hz
    apply isPlanarEmbedding_height_projection u (fun q => Phi (z - m) (k q))
      ((Phi (z - m)).contMDiff.comp hk) ((Phi (z - m)).injective.comp hki) ?_ z
      (hheight z hz)
    intro q
    have hdPhi := ((Phi (z - m)).toOpenPartialHomeomorph_mdifferentiable
      (by simp)).mfderiv_injective (x := k q) (mem_univ _)
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) ((Phi (z - m) : E3 → E3) ∘ k) q)
    rw [mfderiv_comp q ((Phi (z - m)).mdifferentiable (by simp) (k q))
      (hk.mdifferentiable (by simp) q)]
    exact hdPhi.comp (hed q)
  · intro z hz
    apply Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      change (heightPlaneCoordinates u).symm
        ((heightPlaneCoordinates u (Phi (z - m) (k q))).1, z) ∈ S
      rw [heightPlaneCoordinates_reconstruct u _ z (hheight z hz q)]
      exact hPhiS _ (hkS q)
    · intro x hx
      let y := (heightPlaneCoordinates u).symm (x, z)
      have hyS : y ∈ S := hx
      have hyheight : ⟪(u : E3), y⟫_ℝ = z := by
        rw [← heightPlaneCoordinates_snd]
        exact congrArg Prod.snd ((heightPlaneCoordinates u).apply_symm_apply (x, z))
      have hyL : Phi (m - z) y ∈ L := (hLmem _).mpr
        ⟨hPhiS _ hyS, by
          simpa only [hyheight] using hPhib y hyS (hyheight.symm ▸ hetaband hz)⟩
      obtain ⟨q, hq⟩ := hkL.symm ▸ hyL
      refine ⟨q, ?_⟩
      dsimp [c]
      rw [hq, ← hPhiadd, show m - z + (z - m) = 0 by ring, hPhi0]
      exact congrArg Prod.fst ((heightPlaneCoordinates u).apply_symm_apply (x, z))



theorem exists_stackCircleFamily_of_two_caps
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (Cm Cp : SurgeryCapTag psi u)
    (hCm : Cm.sign = 1) (hCp : Cp.sign = -1)
    (K : Set E3)
    (hcover : range (fun q : UnitTwoSphere => psi (q, 0)) = K ∪ Cm.cap ∪ Cp.cap)
    (hm : K ∩ Cm.cap = Cm.seam) (hp : K ∩ Cp.cap = Cp.seam)
    (hdisjoint : Disjoint Cm.cap Cp.cap)
    (horder : Cm.cutHeight + Cm.sign * Cm.removal <
      Cp.cutHeight + Cp.sign * Cp.removal)
    (hheight : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ∈
      Icc (Cm.cutHeight + Cm.sign * Cm.removal)
        (Cp.cutHeight + Cp.sign * Cp.removal))
    (hreg : ∀ q : UnitTwoSphere, psi (q, 0) ∈ K →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    let ell := Cm.cutHeight + Cm.sign * Cm.removal
    let r := Cp.cutHeight + Cp.sign * Cp.removal
    K = (fun q : UnitTwoSphere => psi (q, 0)) ''
      ((univ : Set UnitTwoSphere) \ (Cm.sourceCapInterior ∪ Cp.sourceCapInterior)) ∧
    IsCompact K ∧ IsConnected K ∧
    K = {y : E3 | y ∈ range (fun q => psi (q, 0)) ∧
      ⟪(u : E3), y⟫_ℝ ∈ Icc ell r} ∧
    ∃ eta : ℝ, 0 < eta ∧ ∃ c : ℝ → UnitCircle → E2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => c p.1 p.2) ∧
      (∀ z ∈ Icc (ell - eta) (r + eta), IsPlanarEmbedding (c z)) ∧
      ∀ z ∈ Icc (ell - eta) (r + eta),
        range (c z) = {x : E2 |
          (heightPlaneCoordinates u).symm (x, z) ∈
            range (fun q : UnitTwoSphere => psi (q, 0))} := by
  classical
  let C : Fin 2 → SurgeryCapTag psi u := ![Cm, Cp]
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ∀ j ∈ (Finset.univ : Finset (Fin 2)), i ≠ j → Disjoint (C i).cap (C j).cap := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hij rfl).elim
  have hcover' : range (fun q : UnitTwoSphere => psi (q, 0)) =
      K ∪ ⋃ i ∈ (Finset.univ : Finset (Fin 2)), (C i).cap := by
    have he : (⋃ i ∈ (Finset.univ : Finset (Fin 2)), (C i).cap) = Cm.cap ∪ Cp.cap := by
      ext x
      simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr hi
      · rintro (hx | hx)
        · exact ⟨0, hx⟩
        · exact ⟨1, hx⟩
    rw [he, ← union_assoc]
    exact hcover
  have hinter : ∀ i ∈ (Finset.univ : Finset (Fin 2)), K ∩ (C i).cap = (C i).seam := by
    intro i _
    fin_cases i
    · exact hm
    · exact hp
  obtain ⟨hsource, hcompact, hconnected⟩ :=
    tagged_retained_core_compact_connected hpsi Finset.univ C hdis K hcover' hinter
  have hsource' : K = (fun q : UnitTwoSphere => psi (q, 0)) ''
      ((univ : Set UnitTwoSphere) \ (Cm.sourceCapInterior ∪ Cp.sourceCapInterior)) := by
    have he : (⋃ i ∈ (Finset.univ : Finset (Fin 2)), (C i).sourceCapInterior) =
        Cm.sourceCapInterior ∪ Cp.sourceCapInterior := by
      ext x
      simp only [mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr hi
      · rintro (hx | hx)
        · exact ⟨0, hx⟩
        · exact ⟨1, hx⟩
    rwa [he] at hsource
  let ell := Cm.cutHeight + Cm.sign * Cm.removal
  let r := Cp.cutHeight + Cp.sign * Cp.removal
  have hband : K = {y : E3 | y ∈ range (fun q => psi (q, 0)) ∧
      ⟪(u : E3), y⟫_ℝ ∈ Icc ell r} := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨hcover.symm ▸ Or.inl (Or.inl hy), hheight y hy⟩
    · rintro y ⟨hy, hyl, hyr⟩
      rcases hcover ▸ hy with (hy | hy) | hy
      · exact hy
      · have hh := Cm.cap_seam_signed_height y hy
        have hz : Cm.sign * (⟪(u : E3), y⟫_ℝ - ell) = 0 := by
          have hn := hh.1
          change Cm.sign * (⟪(u : E3), y⟫_ℝ - ell) ≤ 0 at hn
          simp only [hCm, one_mul] at hn ⊢
          exact sub_eq_zero.mpr (le_antisymm (by linarith) hyl)
        exact (hm.symm ▸ (hh.2.1.mp hz)).1
      · have hh := Cp.cap_seam_signed_height y hy
        have hz : Cp.sign * (⟪(u : E3), y⟫_ℝ - r) = 0 := by
          have hn := hh.1
          change Cp.sign * (⟪(u : E3), y⟫_ℝ - r) ≤ 0 at hn
          rw [hCp] at hn ⊢
          linarith
        exact (hp.symm ▸ (hh.2.1.mp hz)).1
  exact ⟨hsource', hcompact, hconnected, hband,
    exists_stackCircleFamily_of_connected_regular_band psi hpsi u ell r horder K
      hconnected hband hreg⟩

end PoincareConjecture.M25.Topology3D
