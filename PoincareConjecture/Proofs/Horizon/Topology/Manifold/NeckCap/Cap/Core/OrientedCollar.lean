import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.Standardization

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)

theorem exists_outward_ball_coordinate_collar
    (b : OpenPartialHomeomorph E3 M)
    (hs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hclosed : b '' Metric.closedBall 0 1 = C.closed_core)
    (hsphere : b '' Metric.sphere 0 1 = C.boundary_sphere)
    (hboundary : ∀ q : UnitTwoSphere, b q = C.boundary_neck.coordinate_map (q, 0)) :
    ∃ r : ℝ, 0 < r ∧ r < C.epsilon⁻¹ ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ e : OpenPartialHomeomorph RoundCylinderSpace E3,
        univ ×ˢ Ioo (-r) r ⊆ e.source ∧ e.target ⊆ b.source ∧
        ContMDiffOn CylModel (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target ∧
        (∀ q : UnitTwoSphere, e (q, 0) = (q : E3)) ∧
        (∀ q : UnitTwoSphere, ∀ t ∈ Ioo 0 r, 1 < ‖e (q, t)‖) ∧
        (∀ q : UnitTwoSphere, ∀ t ∈ Ioo (-r) 0, ‖e (q, t)‖ < 1) ∧
        ∀ z ∈ e.source, b (e z) = C.boundary_neck.coordinate_map (z.1, σ * z.2) := by
  obtain ⟨r, hr, hrC, e, hes, het, he, hei, _, heq⟩ :=
    C.exists_ball_coordinate_collar b hs hb hbi hsphere
  have he0 (q : UnitTwoSphere) : e (q, 0) = (q : E3) := by
    have hz : (q, (0 : ℝ)) ∈ e.source := hes ⟨mem_univ _, by constructor <;> linarith⟩
    exact b.injOn (het (e.map_source hz)) (hs (Metric.sphere_subset_closedBall q.property))
      ((heq _ hz).trans (hboundary q).symm)
  rcases C.ball_coordinate_collar_sides b hs hclosed e hrC hes het heq with
    ⟨hin, hout⟩ | ⟨hin, hout⟩
  · refine ⟨r, hr, hrC, 1, Or.inl rfl, e, hes, het, he, hei, he0, ?_, ?_, ?_⟩
    · intro q t ht
      have h := hout (mem_image_of_mem e
        (show (q, t) ∈ univ ×ˢ Ioo 0 r from ⟨mem_univ q, ht⟩))
      simpa using h
    · intro q t ht
      have h := hin (mem_image_of_mem e
        (show (q, t) ∈ univ ×ˢ Ioo (-r) 0 from ⟨mem_univ q, ht⟩))
      simpa using h
    · intro z hz
      simpa only [one_mul, Prod.eta] using heq z hz
  · let J : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
      toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
      contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
      contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
    let c := J.toHomeomorph.toOpenPartialHomeomorph.trans e
    have hcf (z : RoundCylinderSpace) : c z = e (z.1, -z.2) := rfl
    have hct : c.target = e.target := by simp [c]
    have hcs : univ ×ˢ Ioo (-r) r ⊆ c.source := by
      intro z hz
      refine ⟨mem_univ _, ?_⟩
      change (z.1, -z.2) ∈ e.source
      apply hes
      exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    refine ⟨r, hr, hrC, -1, Or.inr rfl, c, hcs, hct.symm ▸ het, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact he.comp J.contMDiff.contMDiffOn inter_subset_right
    · exact J.symm.contMDiff.comp_contMDiffOn (hei.mono inter_subset_left)
    · intro q
      rw [hcf, neg_zero, he0]
    · intro q t ht
      rw [hcf]
      have h := hout (mem_image_of_mem e
        (show (q, -t) ∈ univ ×ˢ Ioo (-r) 0 from ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩))
      simpa using h
    · intro q t ht
      rw [hcf]
      have h := hin (mem_image_of_mem e
        (show (q, -t) ∈ univ ×ˢ Ioo 0 r from ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩))
      simpa using h
    · intro z hz
      have hh := heq (J z) hz.2
      change b (e (z.1, -z.2)) = C.boundary_neck.coordinate_map (z.1, -z.2) at hh
      simpa only [hcf, neg_one_mul] using hh

end PoincareConjecture.CapCertificate
