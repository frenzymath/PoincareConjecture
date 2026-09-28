import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyInterface














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}






def M64AnnulusConformalGram (A : M64Annulus g c0 c1) : Prop :=
  ∀ p ∈ interior m64AnnulusDomain, ∃ scale : ℝ, 0 ≤ scale ∧
    ∀ v w : TangentSpace (𝓡 2) p,
      g.inner (A.map p)
          (mfderiv (𝓡 2) (𝓡 n) A.map p v)
          (mfderiv (𝓡 2) (𝓡 n) A.map p w) =
        scale * inner ℝ v w





theorem m64Annulus_injective_off_branch_of_conformal
    (A : M64Annulus g c0 c1)
    (hconformal : M64AnnulusConformalGram A)
    {p : LoopPlane} (hp : p ∈ interior m64AnnulusDomain)
    (hbranch : p ∉ m64AnnulusBranchSet A) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 n) A.map p) := by
  let d := mfderiv (𝓡 2) (𝓡 n) A.map p
  let : NormedAddCommGroup (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (NormedAddCommGroup LoopPlane)
  let : InnerProductSpace ℝ (TangentSpace (𝓡 2) p) :=
    inferInstanceAs (InnerProductSpace ℝ LoopPlane)
  obtain ⟨scale, hscale, hpair⟩ := hconformal p hp
  have hscale_pos : 0 < scale := by
    by_contra hnot
    have hscale_zero : scale = 0 := le_antisymm (not_lt.mp hnot) hscale
    apply hbranch
    change p ∈ interior m64AnnulusDomain ∧ d = 0
    refine ⟨hp, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    by_contra hv
    have hpos := g.pos (A.map p) (d v) hv
    have hzero := hpair v v
    rw [hscale_zero, zero_mul] at hzero
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  intro v w hvw
  apply sub_eq_zero.mp
  have hzero : d (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  by_contra hne
  have hinner : 0 < inner ℝ (v - w) (v - w) :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (by
      intro h
      apply hne
      simp [h]))
  have hpair_sub := hpair (v - w) (v - w)
  have hprod_zero : scale * inner ℝ (v - w) (v - w) = 0 := by
    rw [← hpair_sub, hzero]
    simp
  exact (ne_of_gt (mul_pos hscale_pos hinner)) hprod_zero






structure M64AnnulusConformalBranchAwareCertificate
    (A : M64Annulus g c0 c1) : Prop where
  regularity : M64AnnulusRegularityCertificate A
  area_stationary : M64AnnulusAreaStationary A
  finite_branch_set : (m64AnnulusBranchSet A).Finite
  conformal_gram : M64AnnulusConformalGram A





theorem M64AnnulusConformalBranchAwareCertificate.toBranchAware
    {A : M64Annulus g c0 c1}
    (C : M64AnnulusConformalBranchAwareCertificate A) :
    M64AnnulusBranchAwareFirstVariationCertificate A :=
  { regularity := C.regularity
    area_stationary := C.area_stationary
    finite_branch_set := C.finite_branch_set
    injective_off_branch_set := fun _p hp hbranch =>
      m64Annulus_injective_off_branch_of_conformal A C.conformal_gram hp hbranch }

end

end PoincareConjecture
