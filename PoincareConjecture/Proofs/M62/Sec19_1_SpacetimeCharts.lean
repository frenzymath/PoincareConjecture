import PoincareConjecture.Definitions.M62Geometry
import PoincareConjecture.Proofs.M62.Mathlib.LinearChartTransport
import PoincareConjecture.Proofs.M11.SpatialCalculus









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle Topology

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem nonempty_spacetimeCharts (a b : ℝ) :
    Nonempty (SpacetimeCharts n M a b) := by
  classical
  let : ChartedSpace ℝ (OpenTime a b) := inferInstance
  let : IsManifold 𝓘(ℝ, ℝ) ∞ (OpenTime a b) := inferInstance
  let : NormedAddCommGroup (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n) × ℝ))
  let : NormedSpace ℝ (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n) × ℝ))
  let : FiniteDimensional ℝ (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n) × ℝ))
  let productCharts : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) ℝ)
      (SpacetimeCarrier M a b) := inferInstance
  let : IsManifold ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (SpacetimeCarrier M a b) := inferInstance
  have hprod : IsManifold 𝓘(ℝ, ModelProd (EuclideanSpace ℝ (Fin n)) ℝ) ∞
      (SpacetimeCarrier M a b) := by
    simpa [ModelProd, modelWithCornersSelf_prod] using
      (inferInstance : IsManifold ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (SpacetimeCarrier M a b))
  let e : ModelProd (EuclideanSpace ℝ (Fin n)) ℝ ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) = _
      simp [Module.finrank_prod])
  obtain ⟨C, hC, hfrom, hto⟩ :=
    ContinuousLinearEquiv.exists_compatibleChartedSpace (r := ∞) e
      (SpacetimeCarrier M a b)
  let Φ : Diffeomorph (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (SpacetimeCarrier M a b) (SpacetimeCarrier M a b) ∞ :=
    { toEquiv := Equiv.refl _
      contMDiff_toFun := by
        simpa [ModelProd, modelWithCornersSelf_prod] using hto
      contMDiff_invFun := by
        simpa [ModelProd, modelWithCornersSelf_prod] using hfrom }
  let splitMap : ∀ q : SpacetimeCarrier M a b,
      TangentSpace (𝓡 (n + 1)) q ≃L[ℝ]
        (TangentSpace (𝓡 n) q.1 × ℝ) := fun q =>
    let A : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) q ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ) := by
      change (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ)
      exact ContinuousLinearEquiv.refl ℝ _
    let B : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
        (TangentSpace (𝓡 n) q.1 × ℝ) := by
      change (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ)
      exact ContinuousLinearEquiv.refl ℝ _
    (Φ.mfderivToContinuousLinearEquiv (by simp) q).trans (A.trans B)
  refine ⟨{
    chartedSpace := C
    isManifold := hC
    from_product_smooth := by
      simpa [ModelProd, modelWithCornersSelf_prod] using hfrom
    to_product_smooth := by
      simpa [ModelProd, modelWithCornersSelf_prod] using hto
    split := splitMap
    split_space := by
      intro q V
      have hcomp := mfderiv_comp_apply (f := Φ)
        (g := (Prod.fst : SpacetimeCarrier M a b → M))
        q mdifferentiableAt_fst (Φ.contMDiff.mdifferentiableAt (x := q) (by simp)) V
      change ((mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) Φ q) V).1 = _
      rw [mfderiv_fst] at hcomp
      exact hcomp.symm
    split_time := by
      intro q V
      have hval : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
          (Subtype.val : OpenTime a b → ℝ) (Φ q).2 :=
        contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
      have hclock : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (fun p : SpacetimeCarrier M a b => (p.2 : ℝ)) (Φ q) :=
        hval.comp (Φ q) mdifferentiableAt_snd
      have hcomp := mfderiv_comp_apply (f := Φ)
        (g := fun p : SpacetimeCarrier M a b => (p.2 : ℝ)) q hclock
        (Φ.contMDiff.mdifferentiableAt (x := q) (by simp)) V
      have htime := mfderiv_comp (I := (𝓡 n).prod 𝓘(ℝ, ℝ))
        (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
        (f := (Prod.snd : SpacetimeCarrier M a b → OpenTime a b))
        (g := (Subtype.val : OpenTime a b → ℝ)) (Φ q) hval mdifferentiableAt_snd
      rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val, mfderiv_snd] at htime
      change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (fun p : SpacetimeCarrier M a b => (p.2 : ℝ)) (Φ q) =
        ContinuousLinearMap.snd ℝ (TangentSpace (𝓡 n) (Φ q).1)
          (TangentSpace 𝓘(ℝ, ℝ) (Φ q).2) at htime
      change ((mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) Φ q) V).2 = _
      rw [htime] at hcomp
      exact hcomp.symm
  }⟩

end PoincareConjecture.M62
