import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.LinearPath
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.OrthogonalCharts









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace Poincare.Manifold.SphereIsotopy

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := PoincareConjecture.UnitTwoSphere



theorem exists_orthogonal_germ
    (d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞) (p : S2) :
    ∃ A : E3 ≃ₗᵢ[ℝ] E3,
      ∃ a : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
      (∀ q, (a q : E3) = A (q : E3)) ∧
      ∃ Φ : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞,
      (∀ q, Φ 0 q = q) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : ℝ × S2 => Φ z.1 z.2) ∧
      ∃ U : Set S2, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, Φ 1 (d q) = a q := by
  obtain ⟨r, hr, L, _, _, _, P, hP0, hPs, _, hP⟩ := exists_local_linearization d p
  obtain ⟨Q, hQ⟩ := exists_orthogonal_linear_interpolation L
  let B (t : ℝ) : E2 →L[ℝ] E2 :=
    (1 - t) • L.toContinuousLinearMap + t • Q.toContinuousLinearEquiv.toContinuousLinearMap
  let G : ℝ × E2 → E2 := fun z => B z.1 z.2
  have hG : ContDiff ℝ ∞ G :=
    ((contDiff_const.sub contDiff_fst).smul (L.contDiff.comp contDiff_snd)).add
      (contDiff_fst.smul (Q.contDiff.comp contDiff_snd))
  obtain ⟨R, hR0, hRs, ⟨S, hS, hRfix⟩, hR⟩ :=
    Schoenflies.exists_ambient_isotopy_of_codimZero_isotopy
      (isCompact_closedBall (0 : E2) r) G hG
      (fun t ht => (hQ t ht).1.injOn)
      (fun t ht x _ => by
        change Function.Bijective (fderiv ℝ (B t) x)
        rw [(B t).fderiv]
        exact hQ t ht)
  let c := centeredChart (d p)
  have hcm := centeredChart_mem_maximalAtlas (d p)
  obtain ⟨_, _, T, hT0, hTs, _, hT⟩ :=
    Schoenflies.exists_supported_chart_isotopy c.symm
      (contMDiffOn_symm_of_mem_maximalAtlas hcm)
      (contMDiffOn_of_mem_maximalAtlas hcm) hS (by simp [c]) R hR0 hRs hRfix
  let Φ : ℝ → Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞ := fun t => (P t).trans (T t)
  obtain ⟨A, a, ha, _, hachart⟩ := exists_orthogonal_chart_map p (d p) Q
  let U := (centeredChart p).source ∩ centeredChart p ⁻¹' ball (0 : E2) r
  have hU : IsOpen U := (centeredChart p).continuousOn_toFun.isOpen_inter_preimage
    (centeredChart p).open_source isOpen_ball
  have hpU : p ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa using ne_neg_of_mem_unit_sphere ℝ p
    · simpa [mem_ball, dist_zero_right] using hr
  refine ⟨A, a, ha, Φ, ?_, hTs.comp (contMDiff_fst.prodMk hPs), U, hU, hpU, ?_⟩
  · intro q
    change T 0 (P 0 q) = q
    rw [hP0, hT0]
  intro q hq
  let x := centeredChart p q
  have hx : x ∈ closedBall (0 : E2) r := ball_subset_closedBall hq.2
  have hcx : (centeredChart p).symm x = q := (centeredChart p).left_inv hq.1
  have hR1 : R 1 (L x) = Q x := by
    simpa [G, B] using hR 1 (show (1 : ℝ) ∈ Icc 0 1 by simp) x hx
  change T 1 (P 1 (d q)) = a q
  rw [← hcx, hP x hx, hT 1 (L x) (by simp [c]), hR1, hachart]

end Poincare.Manifold.SphereIsotopy
