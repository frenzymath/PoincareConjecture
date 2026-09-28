import PoincareConjecture.Proofs.M25.Topology3D.Plane.NearbyCurveTransport
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothTransportTimes
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_supported_curve_family_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    {a b : ℝ} (hab : a < b)
    (hi : ∀ z ∈ Icc a b, Injective (c z))
    (hm : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z) q)) :
    ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      (∃ K : Set E, IsCompact K ∧ ∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x)) ∧
      (∀ x, F a x = x) ∧ ∀ z ∈ Icc a b,
        range (fun q : sphere (0 : E) 1 => F z (c a q)) = range (c z) := by
  classical
  have hlocal (t : Icc a b) : ∃ r : ℝ, 0 < r ∧ ∃ D : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2) ∧
      ∃ Q : Set E, IsCompact Q ∧
        (∀ z x, x ∉ Q → D z x = x ∧ (D z).symm x = x) ∧
        ∀ z ∈ Icc (t.1 - r) (t.1 + r), D z '' range (c t.1) = range (c z) := by
    obtain ⟨r, hr, D, hD, hDi, ⟨Q, hQ, hfix⟩, _, _, hDrange⟩ :=
      exists_nearby_curve_transport e o q0 c hc t.1 (hi t.1 t.2) (hm t.1 t.2)
    refine ⟨r, hr, D, hD, hDi, Q, hQ, hfix, ?_⟩
    intro z hz
    rw [← range_comp']
    exact hDrange z hz
  choose r hr D hD hDi Q hQ hfix hDrange using hlocal
  let W : Icc a b → Set ℝ := fun t => Ioo (t.1 - r t) (t.1 + r t)
  have hcover : Icc a b ⊆ ⋃ t, W t := by
    intro z hz
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    have hpos := hr ⟨z, hz⟩
    change z ∈ Ioo (z - r ⟨z, hz⟩) (z + r ⟨z, hz⟩)
    constructor <;> linarith
  obtain ⟨ε, hε, hwindow⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun t => (isOpen_Ioo : IsOpen (W t))) hcover
  obtain ⟨n, _hn, _hh, _hmesh, hpoints, β, hβ, hβzero, hβa, hβlast, hβclose⟩ :=
    exists_smooth_curve_transport_times hab hε
  let h : ℝ := (b - a) / n
  have hstep (i : ℕ) (hi : i ≤ n) : ∃ R : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => R p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (R p.1).symm p.2) ∧
      ∃ K : Set E, IsCompact K ∧
        (∀ z x, x ∉ K → R z x = x ∧ (R z).symm x = x) ∧
        (∀ x, R a x = x) ∧
        ∀ z ∈ Icc a b, R z '' range (c (β i z)) = range (c (β (i + 1) z)) := by
    obtain ⟨t, ht⟩ := hwindow (a + (i : ℝ) * h) (hpoints i hi)
    let R : ℝ → (E ≃ₘ[ℝ] E) := fun z => (D t (β i z)).symm.trans (D t (β (i + 1) z))
    have hDu : ContDiff ℝ ∞ (fun p : ℝ × E => D t (β i p.1) p.2) :=
      (hD t).comp (((hβ i).comp contDiff_fst).prodMk contDiff_snd)
    have hDui : ContDiff ℝ ∞ (fun p : ℝ × E => (D t (β i p.1)).symm p.2) :=
      (hDi t).comp (((hβ i).comp contDiff_fst).prodMk contDiff_snd)
    have hDv : ContDiff ℝ ∞ (fun p : ℝ × E => D t (β (i + 1) p.1) p.2) :=
      (hD t).comp (((hβ (i + 1)).comp contDiff_fst).prodMk contDiff_snd)
    have hDvi : ContDiff ℝ ∞ (fun p : ℝ × E => (D t (β (i + 1) p.1)).symm p.2) :=
      (hDi t).comp (((hβ (i + 1)).comp contDiff_fst).prodMk contDiff_snd)
    refine ⟨R, hDv.comp (contDiff_fst.prodMk hDui),
      hDu.comp (contDiff_fst.prodMk hDvi), Q t, hQ t, ?_, ?_, ?_⟩
    · intro z x hx
      change D t (β (i + 1) z) ((D t (β i z)).symm x) = x ∧
        D t (β i z) ((D t (β (i + 1) z)).symm x) = x
      rw [(hfix t (β i z) x hx).2, (hfix t (β (i + 1) z) x hx).1,
        (hfix t (β (i + 1) z) x hx).2, (hfix t (β i z) x hx).1]
      exact ⟨rfl, rfl⟩
    · intro x
      change D t (β (i + 1) a) ((D t (β i a)).symm x) = x
      rw [hβa, hβa, Diffeomorph.apply_symm_apply]
    · intro z hz
      rcases hβclose i hi z hz with heq | hclose
      · change (fun x => D t (β (i + 1) z) ((D t (β i z)).symm x)) '' _ = _
        simp only [heq, Diffeomorph.apply_symm_apply, image_id']
      · have hu : β i z ∈ Icc (t.1 - r t) (t.1 + r t) := by
          have hm := ht (show β i z ∈ ball (a + (i : ℝ) * h) ε by
            simpa only [mem_ball, Real.dist_eq] using hclose.1)
          exact ⟨hm.1.le, hm.2.le⟩
        have hv : β (i + 1) z ∈ Icc (t.1 - r t) (t.1 + r t) := by
          have hm := ht (show β (i + 1) z ∈ ball (a + (i : ℝ) * h) ε by
            simpa only [mem_ball, Real.dist_eq] using hclose.2)
          exact ⟨hm.1.le, hm.2.le⟩
        have huinv : (D t (β i z)).symm '' range (c (β i z)) = range (c t.1) := by
          rw [← hDrange t (β i z) hu, image_image]
          simp only [Diffeomorph.symm_apply_apply, image_id']
        change (fun x => D t (β (i + 1) z) ((D t (β i z)).symm x)) '' _ = _
        rw [← image_image, huinv]
        exact hDrange t (β (i + 1) z) hv
  have hind (k : ℕ) (hk : k ≤ n + 1) : ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      ∃ K : Set E, IsCompact K ∧
        (∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
        (∀ x, F a x = x) ∧
        ∀ z ∈ Icc a b,
          range (fun q : sphere (0 : E) 1 => F z (c a q)) = range (c (β k z)) := by
    induction k with
    | zero =>
      refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, E) E ∞,
        contDiff_snd, contDiff_snd, ∅, isCompact_empty,
        (fun _ _ _ => ⟨rfl, rfl⟩), (fun _ => rfl), ?_⟩
      intro z _
      simp only [hβzero, Diffeomorph.coe_refl, id_eq]
    | succ k ih =>
      obtain ⟨F, hF, hFi, K, hK, hFfix, hFa, hFrange⟩ := ih (by omega)
      obtain ⟨R, hR, hRi, Q, hQ, hRfix, hRa, hRrange⟩ := hstep k (by omega)
      let G : ℝ → (E ≃ₘ[ℝ] E) := fun z => (F z).trans (R z)
      refine ⟨G, hR.comp (contDiff_fst.prodMk hF),
        hFi.comp (contDiff_fst.prodMk hRi), K ∪ Q, hK.union hQ, ?_, ?_, ?_⟩
      · intro z x hx
        have hxK : x ∉ K := fun hxK => hx (Or.inl hxK)
        have hxQ : x ∉ Q := fun hxQ => hx (Or.inr hxQ)
        change R z (F z x) = x ∧ (F z).symm ((R z).symm x) = x
        rw [(hFfix z x hxK).1, (hRfix z x hxQ).1,
          (hRfix z x hxQ).2, (hFfix z x hxK).2]
        exact ⟨rfl, rfl⟩
      · intro x
        change R a (F a x) = x
        rw [hFa, hRa]
      · intro z hz
        change range (fun q : sphere (0 : E) 1 => R z (F z (c a q))) = _
        rw [range_comp', hFrange z hz]
        exact hRrange z hz
  obtain ⟨F, hF, hFi, K, hK, hfix, hFa, hFrange⟩ := hind (n + 1) le_rfl
  refine ⟨F, hF, hFi, ⟨K, hK, hfix⟩, ?_, hFa, ?_⟩
  · intro z
    exact ⟨HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfix z x hx).1),
      HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfix z x hx).2)⟩
  · intro z hz
    simpa only [hβlast z hz] using hFrange z hz

end PoincareConjecture.M25.Topology3D
