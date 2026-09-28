import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ResidualMotion



set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_returning_arc_motion_fixing_residual_at_level
    {W B U E : Set V} {a b : V} {c : ℝ}
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a.2 = c) (hb : b.2 = c)
    (hup : ∀ x ∈ W, c ≤ x.2) (haxis : W ∩ {x : V | x.2 = c} = {a, b})
    (hB : IsFinitePLBallPair V B (segment ℝ a b ∪ W))
    (hU : IsOpen U) (hBU : B ⊆ U) (hE : IsClosed E) (hBE : Disjoint B E)
    (T : SimplicialComplex ℝ V) (hT : T.faces.Finite)
    (hlower : ∀ x ∈ T.space, x.2 ≤ c)
    (hTaxis : ∀ x ∈ T.space, x.2 = c → x = a ∨ x = b) :
    ∃ (D : Set V) (H : I → V ≃ₜ V) (F Fi : (ℝ × V) → V),
      IsFinitePLBallPair V D (frontier D) ∧ D ⊆ U ∧
      H 0 = Homeomorph.refl V ∧
      Continuous (fun z : I × V => H z.1 z.2) ∧
      Continuous (fun z : I × V => (H z.1).symm z.2) ∧
      (∀ t : I, ∀ x : V, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ x ∈ T.space ∪ E, H t x = x) ∧
      H 1 '' W = segment ℝ a b ∧
      (∀ t : I, ∀ x : V, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : V, Fi ((t : ℝ), x) = (H t).symm x) ∧
      ∀ K : SimplicialComplex ℝ V, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  wlog habx : a.1 < b.1 generalizing a b
  · have hba : b.1 < a.1 := by
      have hne : a.1 ≠ b.1 := fun h => hab (Prod.ext h (ha.trans hb.symm))
      exact lt_of_le_of_ne (le_of_not_gt habx) (Ne.symm hne)
    have hh := this (by simpa only [pair_comm] using hW) hab.symm hb ha
      (by simpa only [pair_comm] using haxis)
      (by simpa only [segment_symm] using hB)
      (fun x hx hz => (hTaxis x hx hz).symm) hba
    simpa only [segment_symm] using hh
  let A : V ≃ᴬ[ℝ] V := ContinuousAffineEquiv.constVAdd ℝ V (0, -c)
  have hA (x : V) : (A x).2 = x.2 - c := by change -c + x.2 = x.2 - c; ring
  have hAf (x : V) : (A x).1 = x.1 := by change 0 + x.1 = x.1; ring
  have hinverse (S : Set V) : A.symm '' (A '' S) = S := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨A x, mem_image_of_mem A hx, A.symm_apply_apply x⟩
  have hseg : A '' segment ℝ a b = segment ℝ (A a) (A b) :=
    image_segment ℝ A.toAffineEquiv.toAffineMap a b
  have hWA : IsFinitePLBallPair ℝ (A '' W) {A a, A b} := by
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap, image_pair] using
      hW.affine_image A.toContinuousAffineMap A.injective.injOn
  have hBA : IsFinitePLBallPair V (A '' B) (segment ℝ (A a) (A b) ∪ A '' W) := by
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap, image_union, hseg] using
      hB.affine_image A.toContinuousAffineMap A.injective.injOn
  have hAT : FinitePiecewiseAffineOn A T.space := by
    simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      (T.affineOnFaces_affine A.toContinuousAffineMap).finitePiecewiseAffineOn hT
  obtain ⟨T', hT', hTspace, _⟩ := hAT.inverse (fun x _ => A.symm_apply_apply x)
  have haxisA : (A '' W) ∩ {x : V | x.2 = 0} = {A a, A b} := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      have he : x.2 = c := by change (A x).2 = 0 at hz; rw [hA] at hz; linarith
      simpa only [image_pair] using mem_image_of_mem A (haxis.subset ⟨hx, he⟩)
    · rintro (rfl | rfl)
      · exact ⟨mem_image_of_mem A (hW.1 (by simp)), by simp [hA, ha]⟩
      · exact ⟨mem_image_of_mem A (hW.1 (by simp)), by simp [hA, hb]⟩
  obtain ⟨D₀, H₀, F₀, Fi₀, hD₀, hDU, hzero, hc, hci, hfixed, hres, hterminal,
      hFv, hFiv, hPL⟩ := exists_returning_arc_motion_fixing_residual
    hWA (by simpa only [hAf] using habx) (by rw [hA, ha, sub_self])
    (by rw [hA, hb, sub_self])
    (by rintro _ ⟨x, hx, rfl⟩; rw [hA]; exact sub_nonneg.mpr (hup x hx)) haxisA hBA
    (A.toHomeomorph.isOpenMap _ hU) (image_mono hBU)
    (A.toHomeomorph.isClosedMap _ hE)
    (by rw [disjoint_left]; rintro _ ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
        exact disjoint_left.mp hBE hx (A.injective (hxy.trans hzy.symm) ▸ hz)) T' hT'
    (by rw [hTspace]; rintro _ ⟨x, hx, rfl⟩; rw [hA]; exact sub_nonpos.mpr (hlower x hx))
    (by rw [hTspace]; rintro _ ⟨x, hx, rfl⟩ hz
        have he : x.2 = c := by rw [hA] at hz; linarith
        rcases hTaxis x hx he with h | h <;> simp [h])
  let D := A.symm '' D₀
  let H (t : I) : V ≃ₜ V := A.toHomeomorph.trans ((H₀ t).trans A.symm.toHomeomorph)
  let j : (ℝ × V) ≃ᴬ[ℝ] (ℝ × V) :=
    (ContinuousAffineEquiv.refl ℝ ℝ).prodCongr A
  let F (z : ℝ × V) := A.symm (F₀ (j z))
  let Fi (z : ℝ × V) := A.symm (Fi₀ (j z))
  have hD : IsFinitePLBallPair V D (frontier D) := by
    have hh := hD₀.affine_image A.symm.toContinuousAffineMap A.symm.injective.injOn
    change IsFinitePLBallPair V (A.symm.toHomeomorph '' D₀)
      (A.symm.toHomeomorph '' frontier D₀) at hh
    rw [A.symm.toHomeomorph.image_frontier] at hh
    exact hh
  refine ⟨D, H, F, Fi, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hDU hy
    change A.symm (A z) ∈ U
    simpa using hz
  · apply Homeomorph.ext
    intro x
    change A.symm (H₀ 0 (A x)) = x
    rw [hzero]
    exact A.symm_apply_apply x
  · exact A.symm.continuous.comp (hc.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd)))
  · exact A.symm.continuous.comp (hci.comp (continuous_fst.prodMk (A.continuous.comp continuous_snd)))
  · intro t x hx
    change A.symm (H₀ t (A x)) = x
    rw [hfixed t (A x) (fun hi => hx ?_), A.symm_apply_apply]
    change x ∈ interior (A.symm.toHomeomorph '' D₀)
    rw [← A.symm.toHomeomorph.image_interior]
    exact ⟨A x, hi, A.symm_apply_apply x⟩
  · intro t x hx
    change A.symm (H₀ t (A x)) = x
    rw [hres t (A x) ?_, A.symm_apply_apply]
    rcases hx with hx | hx
    · exact Or.inl (hTspace.symm ▸ mem_image_of_mem A hx)
    · exact Or.inr (mem_image_of_mem A hx)
  · have heq : H 1 '' W = A.symm '' (H₀ 1 '' (A '' W)) := by
      simp only [image_image]; rfl
    rw [heq, hterminal, ← hseg, hinverse]
  · intro t x
    change A.symm (F₀ ((t : ℝ), A x)) = A.symm (H₀ t (A x))
    rw [hFv]
  · intro t x
    change A.symm (Fi₀ ((t : ℝ), A x)) = A.symm ((H₀ t).symm (A x))
    rw [hFiv]
  · intro K hK
    have hAK : FinitePiecewiseAffineOn A K.space := by
      simpa only [ContinuousAffineEquiv.coe_toContinuousAffineMap] using
        (K.affineOnFaces_affine A.toContinuousAffineMap).finitePiecewiseAffineOn hK
    obtain ⟨K', hK', hKs, _⟩ := hAK.inverse (fun x _ => A.symm_apply_apply x)
    obtain ⟨hF, hFi⟩ := hPL K' hK'
    rw [hKs] at hF hFi
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
    have hFP := (hF.precomp_affineEquiv j).postcomp A.symm.toContinuousAffineMap
    have hFiP := (hFi.precomp_affineEquiv j).postcomp A.symm.toContinuousAffineMap
    rw [hjdom] at hFP hFiP
    exact ⟨hFP, hFiP⟩

end PoincareConjecture.M76.Dehn
