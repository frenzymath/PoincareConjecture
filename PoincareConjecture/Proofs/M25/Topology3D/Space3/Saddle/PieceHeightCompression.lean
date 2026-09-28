import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D1" => Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




noncomputable def SaddlePieceData.heightCompress
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData psi u) (hpsi : IsCollarEmbedding psi)
    (h : D1) (G0 G : D3) (k delta : ℝ)
    (R o w : Fin D.capCount → ℝ) (hk : 0 < k) (hdelta : 0 < delta)
    (hmono : StrictMono (fun z => h z))
    (hfix : ∀ z, |z - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤ delta → h z = z)
    (hG0 : ∀ y : E3, ⟪(u : E3), G0 y⟫_ℝ = h ⟪(u : E3), y⟫_ℝ)
    (hRadius : ∀ i, D.cutRadius i ≤ R i)
    (hWidths : ∀ i, 0 < o i ∧ o i ≤ (D.cap i).overlapWidth / 4 ∧
      0 < w i ∧ w i ≤ (D.cap i).collarWidth / 4)
    (hAffine : ∀ i z, |z - (D.cap i).cutHeight| ≤ R i →
      h z = ⟪(u : E3), psi (D.point, 0)⟫_ℝ +
        k * (z - ⟪(u : E3), psi (D.point, 0)⟫_ℝ))
    (hCap : ∀ i (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 ≤ 2 * o i →
      |(D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model q).2) -
        (D.cap i).cutHeight| ≤ R i)
    (hCol : ∀ i s, |s| ≤ 2 * w i →
      |(D.cap i).cutHeight + (D.cap i).sign * ((D.cap i).removal - (D.cap i).scale) +
        (D.cap i).beta * s - (D.cap i).cutHeight| ≤ R i)
    (hAgree : EqOn G G0 (range (fun q : UnitTwoSphere => psi (q, 0)) ∪
      ⋃ i, (D.cap i).tube '' (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i)))) :
    SaddlePieceData (fun p => G (psi p)) u := by
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
      (collar_central_contMDiff psi hpsi)
  have hnew (q : UnitTwoSphere) : ⟪(u : E3), G (psi (q, 0))⟫_ℝ = h (f q) := by
    rw [hAgree (Or.inl (mem_range_self q)), hG0]
  have hc : h c = c := hfix c (by
    change |c - c| ≤ delta
    simpa only [sub_self, abs_zero] using hdelta.le)
  have hR (i : Fin D.capCount) : 0 < R i :=
    ((D.cap i).removal_pos.trans (D.removal_lt_cutRadius i)).trans_le (hRadius i)
  have hm (i : Fin D.capCount) :
      h (D.cap i).cutHeight = c + k * ((D.cap i).cutHeight - c) :=
    hAffine i _ (by simpa only [sub_self, abs_zero] using (hR i).le)
  have hanchor (i : Fin D.capCount) (z : ℝ) (hz : |z - (D.cap i).cutHeight| ≤ R i) :
      h z = h (D.cap i).cutHeight + k * (z - (D.cap i).cutHeight) := by
    rw [hAffine i z hz, hm i]
    ring
  let Cnew (i : Fin D.capCount) : SurgeryCapTag (fun p => G (psi p)) u :=
    (D.cap i).heightCompress h G0 G k (R i) (o i) (w i) hk
      (hWidths i).1 ((hWidths i).2.1.trans (by linarith [(D.cap i).overlap_pos]))
      (hWidths i).2.2.1 ((hWidths i).2.2.2.trans (by linarith [(D.cap i).collar_pos]))
      hG0 (hanchor i)
      (fun q hq => hCap i q (by linarith [(hWidths i).1]))
      (fun s hs => hCol i s (by linarith [(hWidths i).2.2.1]))
      (fun y hy => hAgree (Or.inr (mem_iUnion.mpr ⟨i, hy⟩)))
  have hfun : (fun q : UnitTwoSphere => ⟪(u : E3), G (psi (q, 0))⟫_ℝ) =
      (h : ℝ → ℝ) ∘ f := funext hnew
  have hcrit (q : UnitTwoSphere) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪(u : E3), G (psi (p, 0))⟫_ℝ) q =
          0 ↔ mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0 := by
    have hhinj := (h.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (x := f q) (mem_univ _)
    rw [hfun, mfderiv_comp q (h.mdifferentiable (by simp) (f q))
      (hf.mdifferentiable (by simp) q)]
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h (f q) : ℝ →L[ℝ] ℝ).comp
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q : TangentSpace (𝓡 2) q →L[ℝ] ℝ) = 0 ↔
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q : TangentSpace (𝓡 2) q →L[ℝ] ℝ) = 0
    constructor
    · intro hz
      ext v
      apply hhinj
      exact (congrArg (fun A => A v) hz).trans
        (map_zero (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h (f q))).symm
    · intro hz
      simp only [hz, ContinuousLinearMap.comp_zero]
  have habs : Continuous (fun q : UnitTwoSphere => |f q - c|) :=
    (hf.continuous.sub continuous_const).abs
  let U : Set UnitTwoSphere := {q | |f q - c| < delta}
  let V : Set UnitTwoSphere := {q | |f q - c| < delta / 2}
  have hU : IsOpen U := isOpen_lt habs continuous_const
  have hV : IsOpen V := isOpen_lt habs continuous_const
  exact {
    capCount := D.capCount
    cap := Cnew
    sourceCore := D.sourceCore
    sourceCore_compact := D.sourceCore_compact
    sourceCore_connected := D.sourceCore_connected
    source_cover := D.source_cover
    source_incidence := D.source_incidence
    sourceCap_disjoint := D.sourceCap_disjoint
    point := D.point
    slabLower := h D.slabLower
    slabUpper := h D.slabUpper
    core_in_slab := by
      rintro y ⟨q, hq, rfl⟩
      have hqold := D.core_in_slab ⟨q, hq, rfl⟩
      change h D.slabLower ≤ ⟪(u : E3), G (psi (q, 0))⟫_ℝ ∧
        ⟪(u : E3), G (psi (q, 0))⟫_ℝ ≤ h D.slabUpper
      rw [hnew q]
      exact ⟨hmono.monotone hqold.1, hmono.monotone hqold.2⟩
    point_in_slab := by
      rw [hnew D.point]
      exact ⟨hmono D.point_in_slab.1, hmono D.point_in_slab.2⟩
    unique_critical := fun q hq => (hcrit q).trans (D.unique_critical q hq)
    morse := D.morse.restrOpen U hU
    morse_smooth := D.morse_smooth.mono inter_subset_left
    morse_inverse := D.morse_inverse.mono inter_subset_left
    morse_point := D.morse_point
    morseSign1 := D.morseSign1
    morseSign2 := D.morseSign2
    morseSign1_sq := D.morseSign1_sq
    morseSigns_opposite := D.morseSigns_opposite
    morse_height := by
      intro q hq
      change ⟪(u : E3), G (psi (q, 0))⟫_ℝ = ⟪(u : E3), G (psi (D.point, 0))⟫_ℝ +
        D.morseSign1 * (D.morse q).1 ^ 2 + D.morseSign2 * (D.morse q).2 ^ 2
      rw [hnew q, hnew D.point, hc, hfix (f q) hq.2.le]
      exact D.morse_height q hq.1
    protectedSet := D.protectedSet ∩ V
    protected_open := D.protected_open.inter hV
    point_mem_protected := ⟨D.point_mem_protected, by
      change |c - c| < delta / 2
      rw [sub_self, abs_zero]
      positivity⟩
    protected_closure := by
      intro q hq
      have hqold := D.protected_closure (closure_mono inter_subset_left hq)
      have hsub : D.protectedSet ∩ V ⊆ {p | |f p - c| ≤ delta / 2} := by
        intro p hp
        exact (show |f p - c| < delta / 2 from hp.2).le
      have hqval : |f q - c| ≤ delta / 2 :=
        (closure_minimal hsub (isClosed_le habs continuous_const)) hq
      exact ⟨⟨hqold.1, hqval.trans_lt (by linarith)⟩, hqold.2⟩
    cutRadius := fun i => k * D.cutRadius i
    removal_lt_cutRadius := fun i => mul_lt_mul_of_pos_left (D.removal_lt_cutRadius i) hk
    cutRadius_lt_gap := by
      intro i
      change k * D.cutRadius i < |h (D.cap i).cutHeight -
        ⟪(u : E3), G (psi (D.point, 0))⟫_ℝ|
      rw [hnew D.point, hc, hm i, add_sub_cancel_left, abs_mul, abs_of_pos hk]
      exact mul_lt_mul_of_pos_left (D.cutRadius_lt_gap i) hk
    cut_side := by
      intro i
      change ((D.cap i).sign = 1 ∧ h (D.cap i).cutHeight <
          ⟪(u : E3), G (psi (D.point, 0))⟫_ℝ) ∨
        ((D.cap i).sign = -1 ∧ ⟪(u : E3), G (psi (D.point, 0))⟫_ℝ < h (D.cap i).cutHeight)
      rw [hnew D.point]
      rcases D.cut_side i with ⟨hs, hi⟩ | ⟨hs, hi⟩
      · exact Or.inl ⟨hs, hmono hi⟩
      · exact Or.inr ⟨hs, hmono hi⟩ }

end PoincareConjecture.M25.Topology3D
