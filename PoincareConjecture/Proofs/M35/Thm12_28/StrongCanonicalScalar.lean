import PoincareConjecture.Proofs.M35.Thm12_28.SliceScalarEvolution
import PoincareConjecture.Proofs.M35.Thm12_28.ReturnedNeck
import PoincareConjecture.Proofs.M35.Thm12_28.EvolvingNeckScalar
import PoincareConjecture.Proofs.M35.Thm12_28.CapScalarEstimates










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem component_noncompact {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (x : (slice J t).carrier) : ¬ IsCompact (connectedComponent x) := by
  have : ConnectedSpace (slice J t).carrier :=
    (sliceDiffeomorph ht).toHomeomorph.connectedSpace_iff.mpr inferInstance
  intro hc
  rw [PreconnectedSpace.connectedComponent_eq_univ] at hc
  have him : (sliceDiffeomorph ht) '' (univ : Set (slice J t).carrier) = univ := by
    rw [image_univ]
    exact (sliceDiffeomorph ht).surjective.range_eq
  exact noncompact_univ StandardCapSpace
    (him ▸ hc.image (sliceDiffeomorph ht).continuous)




theorem exists_strong_canonical_scalar_bounds (P : M35StandardCapPredecessors) :
    ∃ delta A : ℝ, 0 < delta ∧ 0 < A ∧
      ∀ epsilon C : ℝ, epsilon ≤ delta →
        ∀ (_atlas : StandardCylinderAtlas) (g₀ : StandardInitialMetric)
          (F : MaximalStandardCapFlow g₀) (t : ℝ)
          (x : ((generalizedFlow F.base.flow).slice t).carrier),
          GeneralizedCanonicalControl (F := generalizedFlow F.base.flow) t x epsilon C →
          (∀ v : TangentSpace (𝓡 3) x,
            ((generalizedFlow F.base.flow).metric t).inner x v v = 1 →
            |mvfderiv (𝓡 3) ((generalizedFlow F.base.flow).connection t).scalarCurvature x v| ≤
              max A C * ((generalizedFlow F.base.flow).connection t).scalarCurvature x ^
                (3 / 2 : ℝ)) ∧
          |(F.connection t).laplacian (F.connection t).scalarCurvature x.val +
              2 * (F.connection t).ricciNormSq x.val| ≤
            max A C * ((F.connection t).scalarCurvature x.val) ^ 2 := by
  obtain ⟨delta, A, hdelta, hA, hneck⟩ := exists_half_neck_scalar_bounds P
  refine ⟨min delta (1 / 4), A, lt_min hdelta (by norm_num), hA, ?_⟩
  intro epsilon C he atlas g₀ F t x hcanonical
  have hedelta : epsilon ≤ delta := he.trans (min_le_left _ _)
  have hehalf : epsilon < 1 / 2 := lt_of_le_of_lt (he.trans (min_le_right _ _)) (by norm_num)
  have hretained : Icc (-(1 / 2) : ℝ) 0 ⊆ Ioc (-1 : ℝ) 0 := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  cases hcanonical with
  | neck N hcenter =>
    subst x
    obtain ⟨hspace, htime⟩ := hneck epsilon hedelta atlas g₀ F t N.center.val _
      (standardNeckOfGeneralizedNeck P atlas N hehalf) hretained
    have hs := scalar_eq P F.base.flow N.center.property N.center.val
    constructor
    · intro v hv
      calc
        _ = |mvfderiv (𝓡 3) (F.connection t).scalarCurvature N.center.val
            (mfderiv (𝓡 3) (𝓡 3)
              (Subtype.val : (slice (Ico 0 F.base.lifetime) t).carrier → StandardCapSpace)
              N.center v)| :=
          congrArg abs (scalar_directional_eq P F.base.flow N.center.property N.center v)
        _ ≤ A * (F.connection t).scalarCurvature N.center.val ^ (3 / 2 : ℝ) := hspace _ hv
        _ ≤ max A C * (F.connection t).scalarCurvature N.center.val ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg
            (standardNeckOfGeneralizedNeck P atlas N hehalf).scalar_pos.le _)
        _ = _ := congrArg (fun r : ℝ => max A C * r ^ (3 / 2 : ℝ)) hs.symm
    · exact htime.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  | cap N _ hC hD hx =>
    have hb := capCertificate_scalar_analytic_bounds N hx
    have hxU : x ∈ N.carrier := by
      have hc := N.core_eq_interior_closed_core ▸ hx
      have hclosed := interior_subset hc
      exact (N.closed_core_eq_complement_end ▸ hclosed).1
    have hpos := N.scalar_pos x hxU
    rw [hD] at hb
    rw [hD] at hpos
    have hs := scalar_eq P F.base.flow x.property x.val
    constructor
    · intro v hv
      exact (hb.1 v hv).trans (mul_le_mul_of_nonneg_right
        (hC.trans (le_max_right _ _)) (Real.rpow_nonneg hpos.le _))
    · calc
        _ = |((generalizedFlow F.base.flow).connection t).laplacian
            ((generalizedFlow F.base.flow).connection t).scalarCurvature x +
            2 * ((generalizedFlow F.base.flow).connection t).ricciNormSq x| :=
          congrArg abs (scalar_evolution_eq P F.base.flow x.property x.val).symm
        _ ≤ N.cap_constant *
            (((generalizedFlow F.base.flow).connection t).scalarCurvature x) ^ 2 := hb.2
        _ ≤ max A C * (((generalizedFlow F.base.flow).connection t).scalarCurvature x) ^ 2 :=
          mul_le_mul_of_nonneg_right (hC.trans (le_max_right _ _)) (sq_nonneg _)
        _ = _ := congrArg (fun r : ℝ => max A C * r ^ 2) hs
  | component N _ =>
    exact (component_noncompact x.property N.basepoint
      (N.component_eq ▸ N.compact)).elim
  | round N _ =>
    exact (component_noncompact x.property N.basepoint
      (N.component_eq ▸ N.compact)).elim

end PoincareConjecture.M35.OrdinaryRealization
