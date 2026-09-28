import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => closedBall (0 : V3) 1
local notation "Q3" => sphere (0 : V3) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {C S : Set X} {B : Set E}

theorem ChartwisePLBall.exists_finitePL_boundary_parameter
    (b : ChartwisePLBall e C S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKB : K.space = B)
    (H : B ≃ₜ S) (f : E → X) (hf : PolyhedralPLInCharts e f B)
    (hHval : ∀ z : B, (H z : X) = f z) :
    ∃ qH : B ≃ₜ Q3, qH.IsFinitePL ∧
      ∀ z : B, b.map (qH z) = f z := by
  classical
  let rb : Q3 ≃ₜ S :=
    b.parametrization.restrictSubsets sphere_subset_closedBall b.boundary_subset
      (fun x => (b.boundary_eq x).symm)
  let qH : B ≃ₜ Q3 := H.trans rb.symm
  have hvalue (z : B) : b.map (qH z) = f z := by
    rw [b.map_eq ⟨qH z, sphere_subset_closedBall (qH z).property⟩]
    change (rb (rb.symm (H z)) : X) = f z
    rw [rb.apply_symm_apply, hHval]
  let q : E → V3 := fun x => if hx : x ∈ B then qH ⟨x, hx⟩ else 0
  have hqval (x : B) : q x = (qH x : V3) := by
    simp only [q, dif_pos x.property]
  have hqcont : ContinuousOn q B := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp qH.continuous).congr
      (fun x => (hqval x).symm)
  have hqmap : MapsTo q B C3 := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact sphere_subset_closedBall (qH ⟨x, hx⟩).property
  have hbInj : InjOn b.map C3 := by
    intro x hx y hy hxy
    have h : (⟨x, hx⟩ : C3) = ⟨y, hy⟩ := b.isEmbedding.injective hxy
    exact congrArg Subtype.val h
  have hcomp : PolyhedralPLInCharts e (b.map ∘ q) B :=
    hf.congr (by
      intro x hx
      change f x = b.map (q x)
      rw [hqval ⟨x, hx⟩, hvalue])
  have hq := b.piecewiseAffine.finitePiecewiseAffineOn_lift hcompat hbInj K hK
    (hqcont.mono hKB.subset) (fun _ hx => hqmap (hKB.subset hx))
    (hKB.symm ▸ hcomp)
  exact ⟨qH, ⟨q, hKB ▸ hq, fun z => (hqval z).symm⟩, hvalue⟩

end PoincareConjecture.M76
