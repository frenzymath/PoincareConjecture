import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.AngularCollar









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


theorem exists_supported_angular_extension
    (D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (hD : ∀ p : RoundCylinderSpace, (D p).2 = p.2)
    (R : ℝ) (hR : 0 < R) :
    ∃ (r : ℝ)
      (E : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ r < R ∧
      (∀ p : RoundCylinderSpace, (E p).2 = p.2) ∧
      (∀ p : RoundCylinderSpace, |p.2| < r → E p = D p) ∧
      (∀ p : RoundCylinderSpace, R ≤ |p.2| → E p = ((D (p.1, 0)).1, p.2)) := by
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r, R, hr, hrR⟩
  let σ : ℝ → ℝ := fun t => t * b t
  have hσ : ContDiff ℝ ∞ σ := contDiff_id.mul b.contDiff
  have hσnear (t : ℝ) (ht : |t| < r) : σ t = t := by
    have hb : b t = 1 := b.one_of_mem_closedBall
      (by simpa [Metric.mem_closedBall, Real.dist_eq] using ht.le)
    simp only [σ, hb, mul_one]
  have hσfar (t : ℝ) (ht : R ≤ |t|) : σ t = 0 := by
    have hb : b t = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq] using ht)
    simp only [σ, hb, mul_zero]
  have hDi (p : RoundCylinderSpace) : (D.symm p).2 = p.2 := by
    simpa only [D.apply_symm_apply] using (hD (D.symm p)).symm
  let F : RoundCylinderSpace → RoundCylinderSpace :=
    fun p => ((D (p.1, σ p.2)).1, p.2)
  let G : RoundCylinderSpace → RoundCylinderSpace :=
    fun p => ((D.symm (p.1, σ p.2)).1, p.2)
  have hpair (p : RoundCylinderSpace) :
      ((D (p.1, σ p.2)).1, σ p.2) = D (p.1, σ p.2) :=
    Prod.ext rfl (hD (p.1, σ p.2)).symm
  have hpairi (p : RoundCylinderSpace) :
      ((D.symm (p.1, σ p.2)).1, σ p.2) = D.symm (p.1, σ p.2) :=
    Prod.ext rfl (hDi (p.1, σ p.2)).symm
  let E : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toFun := F
    invFun := G
    left_inv := by
      intro p
      change ((D.symm ((D (p.1, σ p.2)).1, σ p.2)).1, p.2) = p
      rw [hpair, D.symm_apply_apply]
    right_inv := by
      intro p
      change ((D ((D.symm (p.1, σ p.2)).1, σ p.2)).1, p.2) = p
      rw [hpairi, D.apply_symm_apply]
    contMDiff_toFun :=
      (contMDiff_fst.comp (D.contMDiff.comp
        (contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)))).prodMk contMDiff_snd
    contMDiff_invFun :=
      (contMDiff_fst.comp (D.symm.contMDiff.comp
        (contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)))).prodMk contMDiff_snd }
  refine ⟨r, E, hr, hrR, fun _ => rfl, ?_, ?_⟩
  · intro p hp
    change ((D (p.1, σ p.2)).1, p.2) = D p
    rw [hσnear p.2 hp, Prod.eta]
    exact Prod.ext rfl (hD p).symm
  · intro p hp
    change ((D (p.1, σ p.2)).1, p.2) = _
    rw [hσfar p.2 hp]

end PoincareConjecture.CylinderGluing
