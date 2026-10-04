import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Simplicial.CompactFaceNormalBall

/-!
# A controlled three-ball around the whole planar circle disk

The actual plane coordinates extend to ambient normal coordinates. A single
positive width thickens the complete disk inside the prescribed neighborhood,
meeting the old surface only in a chosen open neighborhood of its rim.
The two end disks and full lateral cylinder are retained as literal images.
These end disks are not identified with separately constructed surgery caps.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

/-- Construct the normal ball and all three boundary pieces from the actual
empty planar disk. Neither a normal width nor a three-ball is supplied. -/
theorem exists_circle_surgery_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    {D rim : Set E} (hD : IsFinitePLBallPair P2 D rim)
    (F : P2 →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F) (hFR : EqOn (F ∘ R) id D)
    {M O V : Set E} (hM : IsClosed M) (hDM : D ∩ M = rim)
    (hO : IsOpen O) (hDO : D ⊆ O) (hV : IsOpen V) (hrV : rim ⊆ V) :
    ∃ (T : C3 ≃ᴬ[ℝ] E) (D0 rim0 : Set P2) (r : ℝ),
      0 < r ∧ IsFinitePLBallPair P2 D0 rim0 ∧
      (∀ z, T (z, 0) = F z) ∧
      T '' (D0 ×ˢ {(0 : ℝ)}) = D ∧
      T '' (rim0 ×ˢ {(0 : ℝ)}) = rim ∧
      let ball := T '' (D0 ×ˢ Icc (-r) r)
      let side := T '' (rim0 ×ˢ Icc (-r) r)
      let caps : Bool → Set E := fun b => T '' (D0 ×ˢ {if b then r else -r})
      let rims : Bool → Set E := fun b => T '' (rim0 ×ˢ {if b then r else -r})
      IsFinitePLBallPair C3 ball (side ∪ (caps false ∪ caps true)) ∧
      (∀ b, IsFinitePLBallPair P2 (caps b) (rims b) ∧
        side ∩ caps b = rims b ∧ Disjoint (caps b) (range F)) ∧
      Disjoint (caps true) (caps false) ∧
      D ⊆ ball ∧ ball ∩ range F = D ∧ side ∩ D = rim ∧
      ball ⊆ O ∧ ball ∩ M ⊆ V := by
  have hRi : InjOn R D := by
    intro x hx y hy hxy
    exact (hFR hx).symm.trans ((congrArg F hxy).trans (hFR hy))
  let D0 := R '' D
  let rim0 := R '' rim
  have hD0 : IsFinitePLBallPair P2 D0 rim0 := hD.affine_image R hRi
  obtain ⟨T, hzero, hinverse, hplane⟩ := F.exists_normal_extension hRF.injective h3
  have himage (C : Set E) (hCD : C ⊆ D) :
      T '' ((R '' C) ×ˢ {(0 : ℝ)}) = C := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z, t⟩, ⟨⟨x, hx, rfl⟩, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      rw [ht0, hzero, show F (R x) = x from hFR (hCD hx)]
      exact hx
    · intro x hx
      exact ⟨(R x, 0), ⟨⟨x, hx, rfl⟩, rfl⟩,
        (hzero (R x)).trans (hFR (hCD hx))⟩
  have hcentral : T '' (D0 ×ˢ {(0 : ℝ)}) = D := himage D subset_rfl
  have hrim : T '' (rim0 ×ˢ {(0 : ℝ)}) = rim := himage rim hD.1
  let U := O \ (M \ V)
  have hU : IsOpen U := hO.sdiff (hM.sdiff hV)
  have hDU : D ⊆ U := by
    intro x hx
    exact ⟨hDO hx, fun hm => hm.2 (hrV (hDM.subset ⟨hx, hm.1⟩))⟩
  obtain ⟨r, hr, hproduct⟩ := hD0.isCompact.exists_closed_normal_interval
    (hU.preimage T.continuous) (fun x hx => hDU (hcentral.subset ⟨x, hx, rfl⟩))
  have hprod : IsFinitePLBallPair C3 (D0 ×ˢ Icc (-r) r)
      ((rim0 ×ˢ Icc (-r) r) ∪ (D0 ×ˢ {-r, r})) :=
    hD0.prod (isFinitePLBallPair_Icc (show -r < r by linarith))
  have hboundary :
      T '' ((rim0 ×ˢ Icc (-r) r) ∪ (D0 ×ˢ {-r, r})) =
        T '' (rim0 ×ˢ Icc (-r) r) ∪
          (T '' (D0 ×ˢ {-r}) ∪ T '' (D0 ×ˢ {r})) := by
    rw [image_union, show ({-r, r} : Set ℝ) = {-r} ∪ {r} by ext x; simp [or_comm],
      prod_union, image_union]
  have hball : IsFinitePLBallPair C3 (T '' (D0 ×ˢ Icc (-r) r))
      (T '' ((rim0 ×ˢ Icc (-r) r) ∪ (D0 ×ˢ {-r, r}))) :=
    hprod.affine_image T.toContinuousAffineMap T.injective.injOn
  rw [hboundary] at hball
  have hslices (t : ℝ) : IsFinitePLBallPair P2 (T '' (D0 ×ˢ {t}))
      (T '' (rim0 ×ˢ {t})) := by
    let f : P2 →ᴬ[ℝ] E := T.toContinuousAffineMap.comp
      ((ContinuousAffineMap.id ℝ P2).prod (ContinuousAffineMap.const ℝ P2 t))
    have hf : Function.Injective f := by
      intro x y hxy
      exact congrArg Prod.fst (T.injective hxy)
    have heq (C : Set P2) : f '' C = T '' (C ×ˢ {t}) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x, t), ⟨hx, rfl⟩, rfl⟩
      · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
        have hut : u = t := hu
        subst u
        exact ⟨x, hx, rfl⟩
    simpa only [heq] using hD0.affine_image f hf.injOn
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  refine ⟨T, D0, rim0, r, hr, hD0, hzero, hcentral, hrim, hball, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    let t : ℝ := if b then r else -r
    have ht : t ∈ Icc (-r) r := by cases b <;> simp [t, hr.le]
    have htn : t ≠ 0 := by cases b <;> simp [t, hr.ne']
    refine ⟨hslices t, ?_, disjoint_left.mpr ?_⟩
    · apply Subset.antisymm
      · rintro x ⟨⟨p, hp, hpx⟩, q, hq, hqx⟩
        have hpq := T.injective (hpx.trans hqx.symm)
        exact ⟨p, ⟨hp.1, hpq ▸ hq.2⟩, hpx⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact ⟨⟨p, ⟨hp.1, (show p.2 = t from hp.2) ▸ ht⟩, rfl⟩,
          p, ⟨hD0.1 hp.1, hp.2⟩, rfl⟩
    · rintro x ⟨p, hp, rfl⟩ hxF
      have hp0 := (hplane (T p)).mp hxF
      rw [T.symm_apply_apply] at hp0
      exact htn ((show p.2 = t from hp.2).symm.trans hp0)
  · apply disjoint_left.mpr
    rintro x ⟨p, hp, hpx⟩ ⟨q, hq, hqx⟩
    have heq := congrArg Prod.snd (T.injective (hpx.trans hqx.symm))
    have hp' : p.2 = r := hp.2
    have hq' : q.2 = -r := hq.2
    linarith
  · rw [← hcentral]
    exact image_mono (prod_mono_right (singleton_subset_iff.mpr h0))
  · apply Subset.antisymm
    · rintro x ⟨⟨p, hp, rfl⟩, hxF⟩
      have hp0 := (hplane (T p)).mp hxF
      rw [T.symm_apply_apply] at hp0
      exact hcentral.subset ⟨p, ⟨hp.1, hp0⟩, rfl⟩
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := hcentral.symm.subset hx
      exact ⟨⟨p, ⟨hp.1, (show p.2 = 0 from hp.2) ▸ h0⟩, rfl⟩,
        (hplane (T p)).mpr (by rw [T.symm_apply_apply]; exact hp.2)⟩
  · rw [← hcentral, ← hrim]
    apply Subset.antisymm
    · rintro x ⟨⟨p, hp, hpx⟩, q, hq, hqx⟩
      have hpq := T.injective (hpx.trans hqx.symm)
      exact ⟨p, ⟨hp.1, hpq ▸ hq.2⟩, hpx⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨⟨p, ⟨hp.1, (show p.2 = 0 from hp.2) ▸ h0⟩, rfl⟩,
        p, ⟨hD0.1 hp.1, hp.2⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hproduct hp).1
  · rintro _ ⟨⟨p, hp, rfl⟩, hpM⟩
    exact not_not.mp (fun hpV => (hproduct hp).2 ⟨hpM, hpV⟩)

end PoincareMT.M76
