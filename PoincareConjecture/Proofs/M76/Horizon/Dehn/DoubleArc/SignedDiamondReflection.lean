import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondMaps








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

def signedTubeReindex (keep sign : Bool) : Bool := if keep then sign else !sign

@[simp] theorem signedTubeReindex_involutive (keep sign : Bool) :
    signedTubeReindex keep (signedTubeReindex keep sign) = sign := by
  cases keep <;> cases sign <;> rfl

noncomputable def signedTubeReflection (eta : Fin 2 → Bool) : P2 ≃L[ℝ] P2 :=
  ((LinearEquiv.smulOfNeZero ℝ ℝ (if eta 0 then 1 else -1)
      (by split <;> norm_num)).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ (if eta 1 then 1 else -1)
      (by split <;> norm_num))).toContinuousLinearEquiv

theorem signedTubeReflection_apply (eta : Fin 2 → Bool) (x : P2) :
    signedTubeReflection eta x =
      ((if eta 0 then 1 else -1) * x.1, (if eta 1 then 1 else -1) * x.2) := rfl

@[simp] theorem signedTubeReflection_zero (eta : Fin 2 → Bool) :
    signedTubeReflection eta (0, 0) = (0, 0) := by
  simp [signedTubeReflection_apply]

@[simp] theorem signedTubeReflection_corner (eta : Fin 2 → Bool) (i : Fin 2)
    (sign : Bool) :
    signedTubeReflection eta (signedTubeCorner i sign) =
      signedTubeCorner i (signedTubeReindex (eta i.rev) sign) := by
  fin_cases i <;> cases h0 : eta 0 <;> cases h1 : eta 1 <;> cases sign <;>
    norm_num [signedTubeReflection_apply, signedTubeCorner, signedTubeReindex,
      Fin.rev, Fin.last, h0, h1]

theorem signedTubeReflection_involutive (eta : Fin 2 → Bool) (x : P2) :
    signedTubeReflection eta (signedTubeReflection eta x) = x := by
  cases h0 : eta 0 <;> cases h1 : eta 1 <;>
    simp [signedTubeReflection_apply, h0, h1]

theorem signedTubeReflection_radius (eta : Fin 2 → Bool) (i : Fin 2) (sign : Bool) :
    signedTubeReflection eta '' signedTubeRadius i sign =
      signedTubeRadius i (signedTubeReindex (eta i.rev) sign) := by
  have h := image_segment ℝ ((signedTubeReflection eta).toLinearMap.toAffineMap) (0, 0)
    (signedTubeCorner i sign)
  change signedTubeReflection eta '' segment ℝ (0, 0) (signedTubeCorner i sign) =
    segment ℝ (signedTubeReflection eta (0, 0))
      (signedTubeReflection eta (signedTubeCorner i sign)) at h
  simpa only [signedTubeRadius, signedTubeReflection_zero, signedTubeReflection_corner] using h

theorem signedTubeReflection_quarter (eta : Fin 2 → Bool) (eps delta : Bool) :
    signedTubeReflection eta '' signedTubeQuarter eps delta =
      signedTubeQuarter (signedTubeReindex (eta 0) eps) (signedTubeReindex (eta 1) delta) := by
  rw [signedTubeQuarter, show (signedTubeReflection eta : P2 → P2) =
    (signedTubeReflection eta).toLinearMap from rfl,
    LinearMap.image_convexHull, ← range_comp]
  unfold signedTubeQuarter
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [Function.comp_def, signedTubeReflection_corner, Fin.rev, Fin.last]

theorem signedTubeReflection_mem_quarter (eta : Fin 2 → Bool) (eps delta : Bool) (x : P2) :
    signedTubeReflection eta x ∈
      signedTubeQuarter (signedTubeReindex (eta 0) eps) (signedTubeReindex (eta 1) delta) ↔
        x ∈ signedTubeQuarter eps delta := by
  rw [← signedTubeReflection_quarter]
  exact (signedTubeReflection eta).injective.mem_set_image

theorem signedTubeReflection_mem_radius (eta : Fin 2 → Bool) (i : Fin 2)
    (sign : Bool) (x : P2) :
    signedTubeReflection eta x ∈ signedTubeRadius i (signedTubeReindex (eta i.rev) sign) ↔
      x ∈ signedTubeRadius i sign := by
  rw [← signedTubeReflection_radius]
  exact (signedTubeReflection eta).injective.mem_set_image

theorem signedTubeReflection_mem_diamond (eta : Fin 2 → Bool) (x : P2) :
    x ∈ signedTubeDiamond ↔ signedTubeReflection eta x ∈ signedTubeDiamond := by
  have hf (x : P2) (hx : x ∈ signedTubeDiamond) :
      signedTubeReflection eta x ∈ signedTubeDiamond := by
    obtain ⟨eps, delta, hx⟩ := by simpa only [signedTubeDiamond, mem_iUnion] using hx
    exact mem_iUnion.mpr ⟨signedTubeReindex (eta 0) eps, mem_iUnion.mpr
      ⟨signedTubeReindex (eta 1) delta, (signedTubeReflection_mem_quarter eta eps delta x).mpr hx⟩⟩
  exact ⟨hf x, fun hx => by simpa only [signedTubeReflection_involutive] using hf _ hx⟩

noncomputable def signedTubeDiamondReflection (eta : Fin 2 → Bool) :
    signedTubeDiamond ≃ₜ signedTubeDiamond :=
  (signedTubeReflection eta).toHomeomorph.subtype (signedTubeReflection_mem_diamond eta)

theorem signedTubeDiamondReflection_isFinitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {G : signedTubeDiamond ≃ₜ s} (hG : G.IsFinitePL) (eta : Fin 2 → Bool) :
    (signedTubeDiamondReflection eta).IsFinitePL := by
  obtain ⟨f, ⟨K, hK, hspace, _⟩, _⟩ := hG
  exact ⟨signedTubeReflection eta, ⟨K, hK, hspace,
    K.affineOnFaces_affine (signedTubeReflection eta).toContinuousLinearMap.toContinuousAffineMap⟩,
      fun _ => rfl⟩

theorem signedTubeDiamondReflection_trans_isFinitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {G : signedTubeDiamond ≃ₜ s} (hG : G.IsFinitePL) (eta : Fin 2 → Bool) :
    ((signedTubeDiamondReflection eta).trans G).IsFinitePL :=
  (signedTubeDiamondReflection_isFinitePL hG eta).trans hG

theorem signedTubeDiamondReflection_trans_quarter
    {E : Type*} [TopologicalSpace E] {s : Set E}
    (G : signedTubeDiamond ≃ₜ s) (Q : Bool → Bool → Set E)
    (hQ : ∀ eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ Q eps delta)
    (eta : Fin 2 → Bool) (eps delta : Bool) (x : signedTubeDiamond) :
    (x : P2) ∈ signedTubeQuarter eps delta ↔
      ((signedTubeDiamondReflection eta).trans G x : E) ∈
        Q (signedTubeReindex (eta 0) eps) (signedTubeReindex (eta 1) delta) :=
  (signedTubeReflection_mem_quarter eta eps delta x).symm.trans
    (hQ _ _ (signedTubeDiamondReflection eta x))

theorem signedTubeDiamondReflection_trans_radius
    {E : Type*} [TopologicalSpace E] {s : Set E}
    (G : signedTubeDiamond ≃ₜ s) (rad : Fin 2 → Bool → Set E)
    (hRad : ∀ i sign (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign)
    (eta : Fin 2 → Bool) (i : Fin 2) (sign : Bool) (x : signedTubeDiamond) :
    (x : P2) ∈ signedTubeRadius i sign ↔
      ((signedTubeDiamondReflection eta).trans G x : E) ∈
        rad i (signedTubeReindex (eta i.rev) sign) :=
  (signedTubeReflection_mem_radius eta i sign x).symm.trans
    (hRad _ _ (signedTubeDiamondReflection eta x))

theorem signedTubeDiamondReflection_trans_apply
    {E : Type*} [TopologicalSpace E] {s : Set E}
    (G : signedTubeDiamond ≃ₜ s) (eta : Fin 2 → Bool) (x : signedTubeDiamond) :
    (signedTubeDiamondReflection eta).trans G x =
      G ⟨signedTubeReflection eta x, (signedTubeReflection_mem_diamond eta x).mp x.property⟩ := rfl

end PoincareConjecture.M76.Dehn
