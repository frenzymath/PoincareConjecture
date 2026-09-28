import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionStripBoundary

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

def stripEnd (t : ℝ) : Set P2 := {t} ×ˢ Icc (-1 : ℝ) 1

theorem stripEnd_subset_source (t : unitInterval) : stripEnd t ⊆ source := by
  rintro x ⟨hx, hy⟩
  exact ⟨hx ▸ t.property, hy⟩

theorem stripEnds_eq_union : stripEnds = stripEnd 0 ∪ stripEnd 1 := by
  ext x
  simp only [stripEnds, stripEnd, mem_prod, mem_insert_iff, mem_singleton_iff, mem_union]
  tauto

theorem exists_stripEnd_parameter (t : ℝ) :
    IsFinitePLBallPair ℝ (stripEnd t) {(t, -1), (t, 1)} ∧
      ∃ p : I01 ≃ₜ stripEnd t, p.IsFinitePL ∧
        ∀ s : I01, (p s : P2) = (t, 2 * (s : ℝ) - 1) := by
  let A : ℝ →ᴬ[ℝ] P2 := (ContinuousAffineMap.const ℝ ℝ t).prod
    ((2 : ℝ) • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ 1)
  have hAval (s : ℝ) : A s = (t, 2 * s - 1) := rfl
  have hinj : InjOn A I01 := by
    intro x _ y _ h
    have heq := congrArg Prod.snd h
    change 2 * x - 1 = 2 * y - 1 at heq
    linarith
  have himage : A '' I01 = stripEnd t := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨rfl, by constructor <;> dsimp [A] <;> linarith [hs.1, hs.2]⟩
    · rintro ⟨hx, hy⟩
      refine ⟨(x.2 + 1) / 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      rw [hAval]
      exact Prod.ext hx.symm (by ring)
  have hball : IsFinitePLBallPair ℝ (stripEnd t) {(t, -1), (t, 1)} := by
    have h := isFinitePLBallPair_affine_interval zero_lt_one A hinj
    rw [himage] at h
    simpa only [hAval, mul_zero, zero_sub, mul_one, sub_self,
      show (2 : ℝ) - 1 = 1 by norm_num] using h
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  have hA : FinitePiecewiseAffineOn A I01 :=
    ⟨K, hK, hKs, K.affineOnFaces_affine A⟩
  have hparam := hA.exists_homeomorph_image hinj
  rw [himage] at hparam
  obtain ⟨p, hp, hpval⟩ := hparam
  exact ⟨hball, p, hp, hpval⟩

theorem exists_embedded_stripEnd_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : P2 → E) (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (t : unitInterval) :
    IsFinitePLBallPair ℝ (c '' stripEnd t) {c (t, -1), c (t, 1)} ∧
      c (t, -1) ≠ c (t, 1) ∧
      ∃ p : I01 ≃ₜ (c '' stripEnd t), p.IsFinitePL ∧
        ∀ s : I01, (p s : E) = c (t, 2 * (s : ℝ) - 1) := by
  have hsub := stripEnd_subset_source t
  obtain ⟨hW, q, hq, hqval⟩ := exists_stripEnd_parameter t
  have hball : IsFinitePLBallPair ℝ (c '' stripEnd t) {c (t, -1), c (t, 1)} := by
    simpa only [image_pair] using hW.image_of_subset hcPL hsub hci
  have hends : c (t, -1) ≠ c (t, 1) := by
    intro h
    have heq := hci ⟨t.property, by norm_num⟩ ⟨t.property, by norm_num⟩ h
    have h11 := congrArg Prod.snd heq
    norm_num at h11
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hcW : FinitePiecewiseAffineOn c (stripEnd t) := by
    rw [← hKs]
    exact hcPL.restrict K hK (hKs.subset.trans hsub)
  obtain ⟨j, hj, hjval⟩ := hcW.exists_homeomorph_image (hci.mono hsub)
  refine ⟨hball, hends, q.trans j, hq.trans hj, ?_⟩
  intro s
  exact (hjval (q s)).trans (congrArg c (hqval s))

theorem embedded_strip_inter_old_rim
    {E : Type*} {Q : Set E} (c : P2 → E)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1) :
    (c '' source) ∩ Q = c '' stripEnds := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxQ⟩
    exact ⟨x, ⟨(hcQ x hx).mp hxQ, hx.2⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxS := stripEnds_subset_source hx
    exact ⟨⟨x, hxS, rfl⟩, (hcQ x hxS).mpr hx.1⟩

theorem embedded_stripEnd_inter_arm
    {E : Type*} (c : P2 → E) (hci : InjOn c source)
    (t : unitInterval) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (c '' stripEnd t) ∩ (c '' arm u) = {c (t, u)} := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨z, hz, heq⟩⟩
    have hzx := hci (show z ∈ source from ⟨hz.1, hz.2.symm ▸ hu⟩)
      (stripEnd_subset_source t hx) heq
    have hx2 : x.2 = u := by rw [← hzx]; exact hz.2
    exact congrArg c (Prod.ext hx.1 hx2)
  · rintro rfl
    exact ⟨⟨(t, u), ⟨rfl, hu⟩, rfl⟩, ⟨(t, u), ⟨t.property, rfl⟩, rfl⟩⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
