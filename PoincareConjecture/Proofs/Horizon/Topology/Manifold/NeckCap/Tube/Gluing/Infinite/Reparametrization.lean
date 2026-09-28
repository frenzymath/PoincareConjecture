import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.AxialCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_relative_reparametrization
    (H E : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (K : Set RoundCylinderSpace) (hK : IsCompact K)
    (hE : ∀ p : RoundCylinderSpace, p.2 ≤ 0 → (E.symm p).2 < 0) :
    ∃ H' : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p : RoundCylinderSpace, (H p).2 ≤ 0 → H' p = E.symm (H p)) ∧
      (∀ p ∈ K, (H' p).2 < 0) := by
  let V : Opens RoundCylinderSpace := ⟨{p | (E.symm p).2 < 0},
    isOpen_lt (continuous_snd.comp E.symm.continuous) continuous_const⟩
  obtain ⟨b, hb⟩ := hK.bddAbove_image (continuous_snd.comp H.continuous).continuousOn
  obtain ⟨C, _, hCfixed, hCV⟩ := exists_compression_into_open V 0 b hE
  refine ⟨(H.trans C).trans E.symm, ?_, ?_⟩
  · intro p hp
    change E.symm (C (H p)) = E.symm (H p)
    rw [hCfixed _ hp]
  · intro p hp
    exact hCV (H p) (hb (mem_image_of_mem _ hp))

theorem exists_exhausting_reparametrizations
    (E : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (hE : ∀ n (p : RoundCylinderSpace), p.2 ≤ 0 → ((E n).symm p).2 < 0) :
    ∃ H : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      H 0 = Diffeomorph.refl CylModel RoundCylinderSpace ∞ ∧
      (∀ n (p : RoundCylinderSpace), (H n p).2 ≤ 0 →
        H (n + 1) p = (E n).symm (H n p)) ∧
      (∀ (n : ℕ) (p : RoundCylinderSpace), |p.2| < (n : ℝ) → (H n p).2 < 0) := by
  classical
  let K (n : ℕ) : Set RoundCylinderSpace :=
    (univ : Set UnitTwoSphere) ×ˢ Icc (-(n + 1 : ℝ)) (n + 1 : ℝ)
  have hK (n : ℕ) : IsCompact (K n) := isCompact_univ.prod isCompact_Icc
  have hnext (n : ℕ)
      (H : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞) :=
    exists_relative_reparametrization H (E n) (K n) (hK n) (hE n)
  let H : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ :=
    Nat.rec (Diffeomorph.refl CylModel RoundCylinderSpace ∞)
      (fun n H => (hnext n H).choose)
  have hstep (n : ℕ) :
      (∀ p : RoundCylinderSpace, (H n p).2 ≤ 0 →
        H (n + 1) p = (E n).symm (H n p)) ∧
      (∀ p ∈ K n, (H (n + 1) p).2 < 0) := (hnext n (H n)).choose_spec
  refine ⟨H, rfl, fun n => (hstep n).1, ?_⟩
  intro n p hp
  cases n with
  | zero => exact False.elim ((not_lt_of_ge (abs_nonneg p.2)) (by simpa using hp))
  | succ n =>
    apply (hstep n).2
    refine ⟨mem_univ _, ?_⟩
    apply abs_le.mp
    exact hp.le.trans (by norm_num)

end PoincareConjecture.CylinderGluing
