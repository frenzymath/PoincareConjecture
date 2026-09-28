import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarLevelSphere
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {C : Set X}

theorem ChartwisePLBall.exists_finitePL_collar_level_parameter
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    {t : ℝ} (ht : t ∈ I)
    (b : ChartwisePLBall e C (c '' (L.space ×ˢ {t}))) :
    ∃ qH : Q ≃ₜ L.space, qH.IsFinitePL ∧
      ∀ z : Q, c ((qH z : E), t) = b.map z := by
  classical
  obtain ⟨H, hHval⟩ := exists_homeomorph_collar_level L hL c hc hi ht
  let rb : Q ≃ₜ (c '' (L.space ×ˢ {t}) : Set X) :=
    b.parametrization.restrictSubsets sphere_subset_closedBall b.boundary_subset
      (fun x => (b.boundary_eq x).symm)
  let qH : Q ≃ₜ L.space := rb.trans H.symm
  have hvalue (z : Q) : c ((qH z : E), t) = b.map z := by
    rw [← hHval]
    change (H (H.symm (rb z)) : X) = b.map z
    rw [H.apply_symm_apply]
    exact (b.map_eq ⟨z, sphere_subset_closedBall z.property⟩).symm
  let q : V3 → E := fun x => if hx : x ∈ Q then qH ⟨x, hx⟩ else 0
  have hqval (x : Q) : q x = (qH x : E) := by
    simp only [q, dif_pos x.property]
  have hqcont : ContinuousOn q Q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp qH.continuous).congr
      (fun x => (hqval x).symm)
  have hqmap : MapsTo q Q L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (qH ⟨x, hx⟩).property
  have hslice : PolyhedralPLInCharts e (fun z => c (z, t)) L.space :=
    PolyhedralPLInCharts.finite_product_slice L hL hc ht
  have hsliceInj : InjOn (fun z => c (z, t)) L.space := by
    intro x hx y hy hxy
    have hpairs : (⟨(x, t), ⟨hx, ht⟩⟩ : (L.space ×ˢ I : Set (E × ℝ))) =
        ⟨(y, t), ⟨hy, ht⟩⟩ := hi.injective hxy
    exact congrArg (fun z : (L.space ×ˢ I : Set (E × ℝ)) => z.1.1) hpairs
  obtain ⟨K, hK, hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hbQ : PolyhedralPLInCharts e b.map Q :=
    hKQ ▸ b.piecewiseAffine.restrict_finite K hK
      (hKQ.subset.trans sphere_subset_closedBall)
  have hcomp : PolyhedralPLInCharts e ((fun z => c (z, t)) ∘ q) Q :=
    hbQ.congr (by
      intro z hz
      change b.map z = c (q z, t)
      rw [hqval ⟨z, hz⟩, hvalue])
  have hq := hslice.finitePiecewiseAffineOn_lift hcompat hsliceInj K hK
    (hqcont.mono hKQ.subset) (fun _ hx => hqmap (hKQ.subset hx))
    (hKQ.symm ▸ hcomp)
  exact ⟨qH, ⟨q, hKQ ▸ hq, fun z => (hqval z).symm⟩, hvalue⟩

end PoincareConjecture.M76
