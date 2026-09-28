import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.NormalFactorization







set_option autoImplicit false

open Set Geometry SignType

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

private theorem exists_open_constant {X Y : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsOpen s) (f : s → Y) (hf : IsLocallyConstant f) (p : s) :
    ∃ U, IsOpen U ∧ (p : X) ∈ U ∧ U ⊆ s ∧
      ∀ q : s, (q : X) ∈ U → f q = f p := by
  obtain ⟨V, hV, hp, hc⟩ := (IsLocallyConstant.iff_exists_open _).mp hf p
  refine ⟨Subtype.val '' V, hs.isOpenMap_subtype_val _ hV, ⟨p, hp, rfl⟩,
    ?_, ?_⟩
  · rintro _ ⟨q, _, rfl⟩
    exact q.property
  · intro q hq
    obtain ⟨r, hr, he⟩ := hq
    have : r = q := Subtype.ext he
    subst r
    exact hc q hr

private theorem exists_open_affine_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    {W : Set E} (hW : IsOpen W) (hp : (h.source ∩ W).Nonempty) :
    ∃ (A : E ≃ᴬ[ℝ] E) (V : Set E), IsOpen V ∧ V.Nonempty ∧
      V ⊆ h.source ∩ W ∧ EqOn h A V := by
  obtain ⟨p, hps, hpW⟩ := hp
  let r := h.restr W
  have hr : r ∈ piecewiseAffineGroupoid E := closedUnderRestriction' hh hW
  have hpr : p ∈ r.source := ⟨hps, by simpa [hW.interior_eq] using hpW⟩
  obtain ⟨B, K, hK, hpK, hKs, hf, t, ht, htc, hpt, hB⟩ :=
    exists_plAffineWitness r hr hpr
  let b := (K.indep ht).affineBasisOfCard htc
  have hspan : affineSpan ℝ (t : Set E) = ⊤ := by simpa [b] using b.tot
  have hBi : Function.Injective B := by
    have hi : InjOn B (convexHull ℝ (t : Set E)) := by
      intro x hx y hy he
      exact r.injOn (hKs (K.convexHull_subset_space ht hx))
        (hKs (K.convexHull_subset_space ht hy)) ((hB hx).trans (he.trans (hB hy).symm))
    have hall := B.toAffineMap.injOn_affineSpan_of_injOn_convex
      (convex_convexHull ℝ _) ⟨p, hpt⟩ hi
    rw [affineSpan_convexHull, hspan] at hall
    exact fun x y he => hall (by simp) (by simp) he
  have hBs : Function.Surjective B := B.toAffineMap.linear_surjective_iff.mp
    (LinearMap.surjective_of_injective (B.toAffineMap.linear_injective_iff.mpr hBi))
  let e := AffineEquiv.ofBijective (φ := B.toAffineMap) ⟨hBi, hBs⟩
  let A : E ≃ᴬ[ℝ] E := { e with
    continuous_toFun := B.continuous
    continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨A, interior (convexHull ℝ (t : Set E)), isOpen_interior,
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan, ?_, ?_⟩
  · intro x hx
    have hs := hKs (K.convexHull_subset_space ht (interior_subset hx))
    exact ⟨hs.1, interior_subset hs.2⟩
  · intro x hx
    exact hB (interior_subset hx)

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)



theorem plLocalSign_eq_tangentialPL_mul_normalTransitionSign
    (h : OpenPartialHomeomorph C3 C3)
    (hh : h ∈ piecewiseAffineGroupoid C3)
    (hpair : ∀ z ∈ h.source, (h z).2 = 0 ↔ z.2 = 0)
    (h₀ : OpenPartialHomeomorph P2 P2)
    (hh₀ : h₀ ∈ piecewiseAffineGroupoid P2)
    (htangent : ∀ z ∈ h₀.source, (z, (0 : ℝ)) ∈ h.source →
      h (z, 0) = (h₀ z, 0))
    (p : {p : P2 // (p, (0 : ℝ)) ∈ h.source}) (hp₀ : (p : P2) ∈ h₀.source) :
    plLocalSign h hh ⟨(p, 0), p.property⟩ =
      plLocalSign h₀ hh₀ ⟨p, hp₀⟩ * BrownCollar.normalTransitionSign h hpair p := by
  obtain ⟨U, hU, hpU, hUs, hUc⟩ := exists_open_constant h.open_source
    (plLocalSign h hh) (isLocallyConstant_plLocalSign h hh) ⟨(p, 0), p.property⟩
  obtain ⟨V, hV, hpV, hVs, hVc⟩ := exists_open_constant h₀.open_source
    (plLocalSign h₀ hh₀) (isLocallyConstant_plLocalSign h₀ hh₀) ⟨p, hp₀⟩
  obtain ⟨W, hW, hpW, hWsign⟩ :=
    (BrownCollar.normalTransitionSign_spec h hpair p).exists_open
  let T := ((fun z : P2 => (z, (0 : ℝ))) ⁻¹' U) ∩ (V ∩ W)
  have hT : IsOpen T := (hU.preimage (continuous_id.prodMk continuous_const)).inter
    (hV.inter hW)
  obtain ⟨A, O, hO, ⟨q, hqO⟩, hOs, hA⟩ := exists_open_affine_patch h₀ hh₀ hT
    ⟨p, hp₀, hpU, hpV, hpW⟩
  have hqT := (hOs hqO).2
  have hq : (q, (0 : ℝ)) ∈ h.source := hUs hqT.1
  let r := h.restr (Prod.fst ⁻¹' O)
  have hOr : IsOpen (Prod.fst ⁻¹' O : Set C3) := hO.preimage continuous_fst
  have hr : r ∈ piecewiseAffineGroupoid C3 := closedUnderRestriction' hh hOr
  have hqr : (q, (0 : ℝ)) ∈ r.source :=
    ⟨hq, by simpa only [hOr.interior_eq, mem_preimage, Prod.fst] using hqO⟩
  have hrpair : ∀ z ∈ r.source, (r z).2 = 0 ↔ z.2 = 0 :=
    fun z hz => hpair z hz.1
  have hrtangent : ∀ z ∈ r.source, z.2 = 0 → r z = (A z.1, 0) := by
    intro z hz hz0
    have hzO : z.1 ∈ O := (interior_subset hz.2 : z ∈ Prod.fst ⁻¹' O)
    have he : z = (z.1, (0 : ℝ)) := Prod.ext rfl hz0
    change h z = _
    rw [he, htangent z.1 (hOs hzO).1 (by simpa only [← he] using hz.1), hA hzO]
  have hfactor := plLocalSign_eq_tangent_mul_normalTransitionSign r hr hrpair A
    hrtangent ⟨q, hqr⟩
  have hnormal : BrownCollar.normalTransitionSign r hrpair ⟨q, hqr⟩ =
      BrownCollar.normalTransitionSign h hpair p := by
    obtain ⟨hs, Z, hZ, hqZ, hZs, hsign⟩ :=
      BrownCollar.normalTransitionSign_spec r hrpair ⟨q, hqr⟩
    have hn : BrownCollar.NormalSignAt h q
        (BrownCollar.normalTransitionSign r hrpair ⟨q, hqr⟩) :=
      ⟨hs, Z, hZ, hqZ, fun z hz => (hZs hz).1, hsign⟩
    exact hn.unique (hWsign q hqT.2.2)
  have hsignA : plLocalSign h₀ hh₀ ⟨q, (hOs hqO).1⟩ =
      SignType.sign (LinearMap.det A.toContinuousAffineMap.toAffineMap.linear) := by
    have hAP : A.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid P2 :=
      ⟨locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ,
        locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ⟩
    exact (plLocalSign_eq_of_eqOn h₀ A.toHomeomorph.toOpenPartialHomeomorph
      hh₀ hAP (hOs hqO).1 (mem_univ _) hO hqO hA).trans
        (plLocalSign_affineEquiv A hAP ⟨q, mem_univ _⟩)
  rw [plLocalSign_restr h hh hOr ⟨(q, 0), hqr⟩, hnormal,
    ← hsignA, hUc ⟨(q, 0), hq⟩ hqT.1, hVc ⟨q, (hOs hqO).1⟩ hqT.2.1] at hfactor
  exact hfactor

end PoincareConjecture.M76.Dehn.Annuli.RimBands
