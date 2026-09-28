import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CriticalHorizontalChart












set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D





theorem exists_collar_ambient_morse_chart
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u q : UnitTwoSphere)
    (hq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hqe : q ∈ e.source) (heq : e q = 0)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (σ τ : ℝ)
    (hform : ∀ p ∈ e.source, ⟪(u : E3), ψ (p, 0)⟫_ℝ =
      ⟪(u : E3), ψ (q, 0)⟫_ℝ + σ * (e p).1 ^ 2 + τ * (e p).2 ^ 2) :
    ∃ A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3,
      (0, ⟪(u : E3), ψ (q, 0)⟫_ℝ) ∈ A.source ∧
      ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
      ∀ p ∈ A.source,
        p.1 ∈ e.target ∧
        A p = (heightPlaneCoordinates u).symm
          ((heightPlaneCoordinates u (ψ (e.symm p.1, 0))).1, p.2) ∧
        ⟪(u : E3), A p⟫_ℝ = p.2 ∧
        (A p ∈ range (fun r : UnitTwoSphere => ψ (r, 0)) ↔
          p.2 = ⟪(u : E3), ψ (q, 0)⟫_ℝ + σ * p.1.1 ^ 2 + τ * p.1.2 ^ 2) := by
  let j : UnitTwoSphere → E3 := fun p => ψ (p, 0)
  let L := heightPlaneCoordinates u
  let c := ⟪(u : E3), j q⟫_ℝ
  obtain ⟨H, hqH, hHsub, hH, hHs, hHi⟩ :=
    exists_collar_critical_horizontal_chart ψ hψ u q hq e.open_source hqe
  let P := e.symm.trans H
  have h0e : (0 : ℝ × ℝ) ∈ e.target := heq ▸ e.map_source hqe
  have he0 : e.symm 0 = q := by rw [← heq, e.left_inv hqe]
  have h0P : (0 : ℝ × ℝ) ∈ P.source := by
    refine ⟨h0e, ?_⟩
    change e.symm 0 ∈ H.source
    rw [he0]
    exact hqH
  have hPs : ContDiffOn ℝ ∞ P P.source :=
    (hHs.comp (hei.mono inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hPi : ContDiffOn ℝ ∞ P.symm P.target :=
    (he.comp (hHi.mono inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  let C := P.prod (OpenPartialHomeomorph.refl ℝ)
  have hCs : ContDiffOn ℝ ∞ C C.source := hPs.prodMap contDiff_id.contDiffOn
  have hCi : ContDiffOn ℝ ∞ C.symm C.target := hPi.prodMap contDiff_id.contDiffOn
  let A0 := C.trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hA0s : ContDiffOn ℝ ∞ A0 A0.source :=
    L.symm.contDiff.comp_contDiffOn (hCs.mono inter_subset_left)
  have hA0i : ContDiffOn ℝ ∞ A0.symm A0.target :=
    hCi.comp L.contDiff.contDiffOn (fun _ hp => hp.2)
  have h0A0 : (0, c) ∈ A0.source := ⟨⟨h0P, mem_univ _⟩, mem_univ _⟩
  have hA0form (p : (ℝ × ℝ) × ℝ) (hp : p ∈ A0.source) :
      A0 p = L.symm ((L (j (e.symm p.1))).1, p.2) := by
    change L.symm (H (e.symm p.1), p.2) = _
    have hpH : e.symm p.1 ∈ H.source := hp.1.1.2
    rw [hH hpH]
  have hA00 : A0 (0, c) = j q := by
    rw [hA0form _ h0A0, he0]
    exact heightPlaneCoordinates_reconstruct u (j q) c rfl
  have hj : Continuous j := (collar_central_contMDiff ψ hψ).continuous
  have hji : Injective j := by
    intro p r hpr
    have h := hψ.2.1 (show (p, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by
      exact ⟨mem_univ _, by norm_num⟩)
      (show (r, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by
        exact ⟨mem_univ _, by norm_num⟩) hpr
    exact congrArg Prod.fst h
  let W := (j '' H.sourceᶜ)ᶜ
  have hW : IsOpen W := (H.open_source.isClosed_compl.isCompact.image hj).isClosed.isOpen_compl
  have hqW : j q ∈ W := by
    rintro ⟨r, hr, hrq⟩
    exact hr ((hji hrq).symm ▸ hqH)
  let V := A0.source ∩ A0 ⁻¹' W
  have hV : IsOpen V := A0.isOpen_inter_preimage hW
  let A := A0.restrOpen V hV
  have h0A : (0, c) ∈ A.source := by
    refine ⟨h0A0, h0A0, ?_⟩
    change A0 (0, c) ∈ W
    rw [hA00]
    exact hqW
  have hAs : ContDiffOn ℝ ∞ A A.source := hA0s.mono inter_subset_left
  have hAi : ContDiffOn ℝ ∞ A.symm A.target := hA0i.mono inter_subset_left
  refine ⟨A, h0A, hAs, hAi, ?_⟩
  intro p hp
  have hpP : p.1 ∈ P.source := hp.1.1.1
  have hpH : e.symm p.1 ∈ H.source := hpP.2
  have hpform : A p = L.symm ((L (j (e.symm p.1))).1, p.2) := hA0form p hp.1
  have hpheight : ⟪(u : E3), A p⟫_ℝ = p.2 := by
    rw [← heightPlaneCoordinates_snd, hpform]
    exact congrArg Prod.snd (L.apply_symm_apply _)
  refine ⟨hpP.1, hpform, hpheight, ?_⟩
  have hm := hform (e.symm p.1) (e.map_target hpP.1)
  rw [e.right_inv hpP.1] at hm
  constructor
  · rintro ⟨r, hr⟩
    have hrH : r ∈ H.source := by
      by_contra hrH
      exact hp.2.2 ⟨r, hrH, hr⟩
    have hcoords : H r = H (e.symm p.1) := by
      rw [hH hrH, hH hpH]
      have h := congrArg (fun y => (L y).1) hr
      rw [hpform, L.apply_symm_apply] at h
      exact h
    have her : r = e.symm p.1 := H.injOn hrH hpH hcoords
    subst r
    have hheight := congrArg (fun y => ⟪(u : E3), y⟫_ℝ) hr
    exact (hheight.trans hpheight).symm.trans hm
  · intro hz
    refine ⟨e.symm p.1, ?_⟩
    apply L.injective
    rw [hpform, L.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact (heightPlaneCoordinates_snd u _).trans (hm.trans hz.symm)

end PoincareConjecture.M25.Topology3D
