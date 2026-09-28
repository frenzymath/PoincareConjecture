import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.PeriodicReduction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.ContactReflection

set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

private theorem affine_conjugate_track (A : V ≃ᴬ[ℝ] V) {F : (ℝ × V) → V}
    (hF : ∀ K : SimplicialComplex ℝ V, K.faces.Finite →
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space)) :
    ∀ K : SimplicialComplex ℝ V, K.faces.Finite →
      FinitePiecewiseAffineOn (fun z : ℝ × V => A.symm (F (z.1, A z.2)))
        (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  intro K hK
  have hAK : FinitePiecewiseAffineOn A K.space := by
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      (K.affineOnFaces_affine A.toContinuousAffineMap).finitePiecewiseAffineOn hK
  obtain ⟨K', hK', hKs, _⟩ := hAK.inverse (fun x _ => A.symm_apply_apply x)
  have hf := hF K' hK'
  rw [hKs] at hf
  let j : (ℝ × V) ≃ᴬ[ℝ] (ℝ × V) :=
    (ContinuousAffineEquiv.refl ℝ ℝ).prodCongr A
  have hjdom : j.symm '' (Icc (0 : ℝ) 1 ×ˢ (A '' K.space)) = Icc (0 : ℝ) 1 ×ˢ K.space := by
    ext p
    constructor
    · rintro ⟨q, ⟨ht, ⟨x, hx, hax⟩⟩, rfl⟩
      refine ⟨ht, ?_⟩
      change A.symm q.2 ∈ K.space
      rw [← hax, A.symm_apply_apply]
      exact hx
    · intro hp
      exact ⟨j p, ⟨hp.1, ⟨p.2, hp.2, rfl⟩⟩, j.symm_apply_apply p⟩
  have h := (hf.precomp_affineEquiv j).postcomp A.symm.toContinuousAffineMap
  rw [hjdom] at h
  exact h

theorem exists_strict_plane_periodic_contact_reduction_of_nonempty {r : ℝ → V}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hbottom : (r 0).2 = -1) (htop : (r 1).2 = 1)
    (hang0 : (r 0).1 = 0) (hang1 : (r 1).1 = 0)
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 32)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x))
    (hcontact : ∃ x ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)) :
    ∃ (n : ℤ) (lo hi : ℝ) (D D' : Set V) (H J : I → V ≃ₜ V)
        (F Fi G Gi : (ℝ × V) → V),
      -32 < lo ∧ lo < 0 ∧ 0 < hi ∧ hi < 32 ∧ hi - lo < 32 ∧
      IsFinitePLBallPair V D (frontier D) ∧ IsFinitePLBallPair V D' (frontier D') ∧
      D ∪ D' ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc lo hi ∧
      H 0 = Homeomorph.refl V ∧ J 0 = Homeomorph.refl V ∧
      Continuous (fun z : I × V => H z.1 z.2) ∧
      Continuous (fun z : I × V => (H z.1).symm z.2) ∧
      Continuous (fun z : I × V => J z.1 z.2) ∧
      Continuous (fun z : I × V => (J z.1).symm z.2) ∧
      (∀ t : I, ∀ x : V, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ x : V, x ∉ interior D' → J t x = x) ∧
      (∀ t : I, ∀ x : V, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : V, Fi ((t : ℝ), x) = (H t).symm x) ∧
      (∀ t : I, ∀ x : V, G ((t : ℝ), x) = J t x) ∧
      (∀ t : I, ∀ x : V, Gi ((t : ℝ), x) = (J t).symm x) ∧
      (∀ K : SimplicialComplex ℝ V, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Gi (Icc (0 : ℝ) 1 ×ˢ K.space)) ∧
      let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * (n : ℝ) + 32 * (j : ℝ))
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.Finite ∧
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.ncard + 2 =
        {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.ncard ∧
      (∀ j : ℤ, ∀ x ∈ Icc (0 : ℝ) 1, (J 1 (H 1 (Q j x))).2 = 0 →
        ∃ u v m : ℝ, 0 ≤ u ∧ u < x ∧ x < v ∧ v ≤ 1 ∧ m ≠ 0 ∧
          ∀ y ∈ Icc u v, (J 1 (H 1 (Q j y))).2 = m * (y - x)) := by
  rcases contact_has_positive_or_reflected_excursion hreg hcontact with habove | habove
  · exact exists_strict_plane_periodic_contact_reduction hr hi hheight hproper hbottom htop
      hang0 hang1 htranslate hc.1 hfinite hreg habove
  obtain ⟨n, lo, up, D, D', H, J, F, Fi, G, Gi, hlo, hlo0, hup0, hup, hwidth,
    hD, hD', hstrip, hH0, hJ0, hHc, hHci, hJc, hJci, hHfix, hJfix,
    hF, hFi, hG, hGi, hPL, hfin, hcount, hregular⟩ :=
    exists_strict_plane_periodic_contact_reduction
      (finitePiecewiseAffineOn_reflectedAnnularLift hr) (injOn_reflectedAnnularLift hi)
      hheight hproper hbottom htop
      (by change -(r 0).1 = 0; rw [hang0, neg_zero])
      (by change -(r 1).1 = 0; rw [hang1, neg_zero])
      (reflectedAnnularLift_translates_disjoint htranslate) (by linarith [hc.2])
      (finite_reflectedAnnularLift_contacts hfinite) (reflectedAnnularLift_regular_contacts hreg) habove
  let A : V ≃ᴬ[ℝ] V := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)).toContinuousAffineEquiv
  have hA (x : V) : A x = (x.1, -x.2) := rfl
  have hAi (x : V) : A.symm x = (x.1, -x.2) := rfl
  let H' (t : I) : V ≃ₜ V := A.toHomeomorph.trans ((H t).trans A.symm.toHomeomorph)
  let J' (t : I) : V ≃ₜ V := A.toHomeomorph.trans ((J t).trans A.symm.toHomeomorph)
  let F' (z : ℝ × V) := A.symm (F (z.1, A z.2))
  let Fi' (z : ℝ × V) := A.symm (Fi (z.1, A z.2))
  let G' (z : ℝ × V) := A.symm (G (z.1, A z.2))
  let Gi' (z : ℝ × V) := A.symm (Gi (z.1, A z.2))
  have hball {S : Set V} (hS : IsFinitePLBallPair V S (frontier S)) :
      IsFinitePLBallPair V (A.symm '' S) (frontier (A.symm '' S)) := by
    have hh := hS.affine_image A.symm.toContinuousAffineMap A.symm.injective.injOn
    change IsFinitePLBallPair V (A.symm.toHomeomorph '' S)
      (A.symm.toHomeomorph '' frontier S) at hh
    rw [A.symm.toHomeomorph.image_frontier] at hh
    exact hh
  have hfix {S : Set V} {M : I → V ≃ₜ V}
      (hM : ∀ t : I, ∀ x : V, x ∉ interior S → M t x = x) :
      ∀ t : I, ∀ x : V, x ∉ interior (A.symm '' S) →
        A.symm (M t (A x)) = x := by
    intro t x hx
    rw [hM t (A x) (fun hi => hx ?_), A.symm_apply_apply]
    change x ∈ interior (A.symm.toHomeomorph '' S)
    rw [← A.symm.toHomeomorph.image_interior]
    exact ⟨A x, hi, A.symm_apply_apply x⟩
  let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * ((-n - 1 : ℤ) : ℝ) + 32 * (j : ℝ))
  let Qr (j : ℤ) := annularLiftAboveAxis (reflectedAnnularLift r)
    ((32 - c) + 32 * (n : ℝ) + 32 * (j : ℝ))
  have hQ (j : ℤ) (x : ℝ) : A (Q j x) = Qr (-j) x := by
    apply Prod.ext
    · rfl
    · change -((r x).1 - (c + 32 * ((-n - 1 : ℤ) : ℝ) + 32 * (j : ℝ))) =
        -(r x).1 - ((32 - c) + 32 * (n : ℝ) + 32 * ((-j : ℤ) : ℝ))
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring
  have hvalue (j : ℤ) (x : ℝ) : (J' 1 (H' 1 (Q j x))).2 =
      -(J 1 (H 1 (Qr (-j) x))).2 := by
    change (A.symm (J 1 (A (A.symm (H 1 (A (Q j x))))))).2 = _
    rw [A.apply_symm_apply, hQ, hAi]
  have hcontacts : {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J' 1 (H' 1 (Q j x))).2 = 0} =
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Qr j x))).2 = 0} := by
    ext x
    constructor
    · rintro ⟨hx, j, hj⟩
      rw [hvalue, neg_eq_zero] at hj
      exact ⟨hx, -j, hj⟩
    · rintro ⟨hx, j, hj⟩
      refine ⟨hx, -j, ?_⟩
      rw [hvalue, neg_neg, hj, neg_zero]
  refine ⟨-n - 1, -up, -lo, A.symm '' D, A.symm '' D', H', J', F', Fi', G', Gi',
    by linarith, by linarith, by linarith, by linarith, by linarith,
    hball hD, hball hD', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfix hHfix, hfix hJfix,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · have hh := hstrip (Or.inl hy)
      exact ⟨hh.1, ⟨neg_le_neg hh.2.2, neg_le_neg hh.2.1⟩⟩
    · have hh := hstrip (Or.inr hy)
      exact ⟨hh.1, ⟨neg_le_neg hh.2.2, neg_le_neg hh.2.1⟩⟩
  · apply Homeomorph.ext
    intro x
    change A.symm (H 0 (A x)) = x
    rw [hH0]
    exact A.symm_apply_apply x
  · apply Homeomorph.ext
    intro x
    change A.symm (J 0 (A x)) = x
    rw [hJ0]
    exact A.symm_apply_apply x
  · exact A.symm.continuous.comp (hHc.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd)))
  · exact A.symm.continuous.comp (hHci.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd)))
  · exact A.symm.continuous.comp (hJc.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd)))
  · exact A.symm.continuous.comp (hJci.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd)))
  · intro t x
    change A.symm (F ((t : ℝ), A x)) = A.symm (H t (A x))
    rw [hF]
  · intro t x
    change A.symm (Fi ((t : ℝ), A x)) = A.symm ((H t).symm (A x))
    rw [hFi]
  · intro t x
    change A.symm (G ((t : ℝ), A x)) = A.symm (J t (A x))
    rw [hG]
  · intro t x
    change A.symm (Gi ((t : ℝ), A x)) = A.symm ((J t).symm (A x))
    rw [hGi]
  · intro K hK
    exact ⟨affine_conjugate_track A (fun L hL => (hPL L hL).1) K hK,
      affine_conjugate_track A (fun L hL => (hPL L hL).2.1) K hK,
      affine_conjugate_track A (fun L hL => (hPL L hL).2.2.1) K hK,
      affine_conjugate_track A (fun L hL => (hPL L hL).2.2.2) K hK⟩
  · change _ ∧ _ ∧ ∀ j : ℤ, ∀ x ∈ Icc (0 : ℝ) 1,
        (J' 1 (H' 1 (Q j x))).2 = 0 → _
    refine ⟨?_, ?_, ?_⟩
    · rw [hcontacts]
      exact hfin
    · rw [hcontacts]
      rw [reflectedAnnularLift_periodic_contacts_eq] at hcount
      exact hcount
    · intro j x hx hz
      rw [hvalue, neg_eq_zero] at hz
      obtain ⟨u, v, m, hu, hux, hxv, hv, hm, hformula⟩ := hregular (-j) x hx hz
      refine ⟨u, v, -m, hu, hux, hxv, hv, neg_ne_zero.mpr hm, ?_⟩
      intro y hy
      rw [hvalue, hformula y hy]
      ring

end PoincareConjecture.M76.Dehn
