import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine









noncomputable section
set_option autoImplicit false

open Set TopologicalSpace IsManifold
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SphereCharts

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem embedding_in_sphere_chart
    (F : UnitTwoSphere → UnitThreeSphere)
    (hF : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F)
    (p : OpenPartialHomeomorph UnitThreeSphere E3)
    (hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p p.source)
    (hpi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p.symm p.target)
    (hFs : ∀ q, F q ∈ p.source) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => p (F q)) := by
  have hsm : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => p (F q)) := by
    intro q
    exact (hp.contMDiffAt (p.open_source.mem_nhds (hFs q))).comp q (hF.contMDiff q)
  refine ⟨?_, (hsm.continuous.isClosedEmbedding ?_).isEmbedding⟩
  · have himm := hF.isImmersion
    refine ⟨himm.complement, inferInstance, inferInstance, ?_⟩
    intro q
    have hi := himm.isImmersionOfComplement_complement q
    have hchart : p.symm.trans hi.codChart ∈ maximalAtlas (𝓡 3) ∞ E3 := by
      apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas hi.codChart_mem_maximalAtlas).comp
          (hpi.mono inter_subset_left) inter_subset_right
      · exact hp.comp
          ((contMDiffOn_symm_of_mem_maximalAtlas hi.codChart_mem_maximalAtlas).mono
            inter_subset_left) inter_subset_right
    refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      hsm.continuous.continuousAt hi.equiv hi.domChart (p.symm.trans hi.codChart)
      hi.mem_domChart_source ?_ hi.domChart_mem_maximalAtlas hchart ?_
    · refine ⟨p.map_source (hFs q), ?_⟩
      change p.symm (p (F q)) ∈ hi.codChart.source
      rw [p.left_inv (hFs q)]
      exact hi.mem_codChart_source
    · intro y hy
      convert hi.writtenInCharts hy using 1
      dsimp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe]
      change hi.codChart (p.symm (p (F ((hi.domChart.extend (𝓡 2)).symm y)))) = _
      rw [p.left_inv (hFs _)]
      rfl
  · intro q w hqw
    exact hF.isEmbedding.injective (p.injOn (hFs q) (hFs w) hqw)



theorem exists_embeddedSphere_collar_avoiding_point
    (F : UnitTwoSphere → UnitThreeSphere)
    (hF : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F)
    (a : UnitThreeSphere) (ha : a ∉ range F) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere,
        e.source = univ ×ˢ Ioo (-δ) δ ∧
        e.target ⊆ {a}ᶜ ∧
        ContMDiffOn CylModel (𝓡 3) ∞ e e.source ∧
        ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target ∧
        ∀ q : UnitTwoSphere, e (q, 0) = F q := by
  let p := threeSphereStereographic a
  have hps : p.source = {a}ᶜ := threeSphereStereographic_source a
  have hpt : p.target = univ := threeSphereStereographic_target a
  have hp := contMDiffOn_of_mem_maximalAtlas (threeSphereStereographic_mem_maximalAtlas a)
  have hpi := contMDiffOn_symm_of_mem_maximalAtlas (threeSphereStereographic_mem_maximalAtlas a)
  have hFs (q : UnitTwoSphere) : F q ∈ p.source := by
    rw [hps]
    intro h
    exact ha ⟨q, mem_singleton_iff.mp h⟩
  obtain ⟨b, hbs, _, hb, hbi, hbF⟩ := Poincare.Manifold.Schoenflies.exists_sphere_neighborhood
    (fun q => p (F q)) (embedding_in_sphere_chart F hF p hp hpi hFs)
  let j := (Poincare.radialPartialDiffeomorph.toOpenPartialHomeomorph.trans b).trans p.symm
  have hjzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ j.source := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (q, (0 : ℝ)) ∈ Poincare.radialPartialDiffeomorph.source
      simp
    · change Poincare.radialPartialDiffeomorph (q, 0) ∈ b.source
      simpa only [Poincare.radialPartialDiffeomorph_apply,
        Poincare.sphereCylinderDiffeomorphPunctured_zero] using hbs q.property
    · change b (Poincare.radialPartialDiffeomorph (q, 0)) ∈ p.target
      rw [hpt]
      exact mem_univ _
  have hj : ContMDiffOn CylModel (𝓡 3) ∞ j j.source := hpi.comp
    (hb.comp (Poincare.radialPartialDiffeomorph.contMDiffOn.mono
      (fun _ hz => hz.1.1)) (fun _ hz => hz.1.2)) (fun _ hz => hz.2)
  have hji : ContMDiffOn (𝓡 3) CylModel ∞ j.symm j.target :=
    (Poincare.radialPartialDiffeomorph.symm.contMDiffOn.comp
      (hbi.mono inter_subset_left) inter_subset_right).comp
      (hp.mono inter_subset_left) inter_subset_right
  let W : Opens RoundCylinderSpace := ⟨j.source, j.open_source⟩
  obtain ⟨δ, hδ, hδs⟩ := CylinderGluing.exists_cylinder_collar W hjzero
  let V : Set RoundCylinderSpace := univ ×ˢ Ioo (-δ) δ
  have hVs : V ⊆ j.source := fun z hz => hδs z (abs_lt.mpr hz.2)
  let e := j.restrOpen V (isOpen_univ.prod isOpen_Ioo)
  have hes : e.source = V := inter_eq_right.mpr hVs
  refine ⟨δ, hδ, e, hes, ?_, hj.mono inter_subset_left, hji.mono inter_subset_left, ?_⟩
  · intro x hx
    exact hps.subset hx.1.1
  · intro q
    change p.symm (b (Poincare.radialPartialDiffeomorph (q, 0))) = F q
    rw [Poincare.radialPartialDiffeomorph_apply, Poincare.sphereCylinderDiffeomorphPunctured_zero,
      hbF, p.left_inv (hFs q)]

end PoincareConjecture.SphereCharts
