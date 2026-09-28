import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.PrescribedIntervalSourceFibers









set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)



theorem exists_prescribed_interval_image_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S W : Set E} {T : Set F} {a b : E}
    (H : S ≃ₜ T) (hH : H.IsFinitePL)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hWS : W ⊆ S)
    (p : I01 ≃ₜ W) (hp : p.IsFinitePL) :
    ∃ q : I01 ≃ₜ ((fun x : S ↦ (H x : F)) '' (Subtype.val ⁻¹' W)),
      q.IsFinitePL ∧ ∀ t : I01, (q t : F) = H ⟨p t, hWS (p t).property⟩ := by
  obtain ⟨f, hf, hval⟩ := hH
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hfW : FinitePiecewiseAffineOn f W := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hWS)
  obtain ⟨j, hj, hjval⟩ := hfW.exists_homeomorph_image (hinj.mono hWS)
  have himage : f '' W = (fun x : S ↦ (H x : F)) '' (Subtype.val ⁻¹' W) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hWS hx⟩, hx, hval ⟨x, hWS hx⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hval x).symm⟩
  let j' := j.trans (Homeomorph.setCongr himage)
  have hj' : j'.IsFinitePL := ⟨f, hfW, hjval⟩
  refine ⟨p.trans j', hp.trans hj', ?_⟩
  intro t
  exact (hjval (p t)).trans (hval ⟨p t, hWS (p t).property⟩).symm



theorem prescribed_attachment_complement_inter
    {E0 E1 : Type*} [TopologicalSpace E0] [TopologicalSpace E1]
    {S0 W0 B0 : Set E0} {S1 W1 B1 : Set E1}
    {a0 b0 : E0} {a1 b1 : E1}
    (hW0S : W0 ⊆ S0) (hW1S : W1 ⊆ S1)
    (hB0S : B0 ⊆ S0) (hB1S : B1 ⊆ S1)
    (hWB0 : W0 ∩ B0 = {a0, b0}) (hWB1 : W1 ∩ B1 = {a1, b1})
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1) (p : I01 ≃ₜ TE)
    (hp00 : (p0 (0 : unitInterval) : E0) = a0)
    (hp01 : (p0 (1 : unitInterval) : E0) = b0)
    (hp10 : (p1 (0 : unitInterval) : E1) = a1)
    (hp11 : (p1 (1 : unitInterval) : E1) = b1)
    (h0 : ∀ t : I01, (n0 ⟨p0 t, hW0S (p0 t).property⟩ : P2) = p t)
    (h1 : ∀ t : I01, (n1 ⟨p1 t, hW1S (p1 t).property⟩ : P2) = p t) :
    ((fun x : S0 ↦ (n0 x : P2)) '' (Subtype.val ⁻¹' B0)) ∩
      ((fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' B1)) =
        {(p (0 : unitInterval) : P2), (p (1 : unitInterval) : P2)} := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, y, hy, heq⟩
    obtain ⟨t, hxt, _⟩ :=
      (prescribed_interval_source_eq_iff hW0S hW1S n0 n1 p0 p1 p h0 h1 x y).mp
        heq.symm
    have htB : (p0 t : E0) ∈ B0 := hxt ▸ hx
    have htend : (p0 t : E0) ∈ ({a0, b0} : Set E0) :=
      hWB0.subset ⟨(p0 t).property, htB⟩
    have hx' : x = ⟨p0 t, hW0S (p0 t).property⟩ := Subtype.ext hxt
    change (n0 x : P2) ∈ {(p (0 : unitInterval) : P2), (p (1 : unitInterval) : P2)}
    rw [hx', h0]
    rcases htend with ht | ht
    · have ht0 : t = 0 := p0.injective (Subtype.ext (ht.trans hp00.symm))
      simp [ht0]
    · have ht1 : t = 1 := p0.injective (Subtype.ext (ht.trans hp01.symm))
      simp [ht1]
  · have hmem (t : I01) (ht : t = 0 ∨ t = 1) :
        (p t : P2) ∈ ((fun x : S0 ↦ (n0 x : P2)) '' (Subtype.val ⁻¹' B0)) ∩
          ((fun x : S1 ↦ (n1 x : P2)) '' (Subtype.val ⁻¹' B1)) := by
      have hb0 : (p0 t : E0) ∈ B0 := by
        apply (hWB0.symm.subset ?_).2
        rcases ht with rfl | rfl <;> simp [hp00, hp01]
      have hb1 : (p1 t : E1) ∈ B1 := by
        apply (hWB1.symm.subset ?_).2
        rcases ht with rfl | rfl <;> simp [hp10, hp11]
      exact ⟨⟨⟨p0 t, hB0S hb0⟩, hb0, h0 t⟩,
        ⟨⟨p1 t, hB1S hb1⟩, hb1, h1 t⟩⟩
    intro hz
    rcases hz with hz | hz
    · simpa only [hz] using hmem 0 (Or.inl rfl)
    · simpa only [mem_singleton_iff.mp hz] using hmem 1 (Or.inr rfl)

end PoincareConjecture.M76.Dehn
