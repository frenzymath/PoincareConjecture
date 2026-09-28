import PoincareConjecture.Proofs.M25.Topology3D.Space3.TubeBoundaryImmersion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldPatchChart












set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_source_tube_chart
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (e : OpenPartialHomeomorph (E2 × ℝ) E3)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {J : Set ℝ} (hJ : IsOpen J) (hs : sphere 0 1 ×ˢ J ⊆ e.source)
    (hc : ∀ θ : UnitCircle, ∀ z ∈ J,
      e (θ.1, z) ∈ range (fun q : UnitTwoSphere => ψ (q, 0))) :
    ∃ Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere,
      Q.source = univ ×ˢ J ∧
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target ∧
      ∀ θ : UnitCircle, ∀ z ∈ J, ψ (Q (θ, z), 0) = e (θ.1, z) := by
  obtain ⟨hcm, hci, hcd⟩ := tube_boundary_smooth_immersion e he hei hs
  obtain ⟨q, hqm, hqi, hqd, hrec⟩ := exists_collar_surface_source_pullback
    ((𝓡 1).prod 𝓘(ℝ, ℝ)) ψ hψ
    (fun p : UnitCircle × ℝ => e (p.1.1, p.2))
    (isOpen_univ.prod hJ) hcm hci hcd (fun p hp => hc p.1 p.2 hp.2)
  let : ChartedSpace ((EuclideanSpace ℝ (Fin 1)) × ℝ) (UnitCircle × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 1)) UnitCircle ℝ ℝ
  let : IsManifold 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1)) × ℝ) ∞ (UnitCircle × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod UnitCircle ℝ
  have : Nonempty UnitCircle :=
    (NormedSpace.sphere_nonempty (E := E2) (x := 0) |>.mpr zero_le_one).coe_sort
  have hqm' : ContMDiffOn 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1)) × ℝ) (𝓡 2) ∞ q
      (univ ×ˢ J) := by
    rwa [modelWithCornersSelf_prod]
  have hqb (p : UnitCircle × ℝ) (hp : p ∈ (univ : Set UnitCircle) ×ˢ J) :
      Bijective (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1)) × ℝ) (𝓡 2) q p) := by
    have hinj : Injective
        (mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1)) × ℝ) (𝓡 2) q p) := by
      change Injective (fun w : (EuclideanSpace ℝ (Fin 1)) × ℝ =>
        mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1)) × ℝ) (𝓡 2) q p w)
      rw [modelWithCornersSelf_prod]
      exact hqd p hp
    let A : (EuclideanSpace ℝ (Fin 1) × ℝ) →L[ℝ] E2 :=
      mfderiv 𝓘(ℝ, (EuclideanSpace ℝ (Fin 1)) × ℝ) (𝓡 2) q p
    have hAi : Injective A := hinj
    have hAs : Surjective A :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := A.toLinearMap)
        (by simp [E2, Module.finrank_prod])).mp hAi
    exact ⟨hinj, hAs⟩
  let Q := manifoldPatchChart q (isOpen_univ.prod hJ) hqm' hqb hqi
  refine ⟨Q, rfl, hqm, ?_, fun θ z hz => hrec (θ, z) ⟨mem_univ _, hz⟩⟩
  have hi := manifoldPatchChart_symm_contMDiffOn q (isOpen_univ.prod hJ) hqm' hqb hqi
  rwa [modelWithCornersSelf_prod] at hi

end PoincareConjecture.M25.Topology3D
