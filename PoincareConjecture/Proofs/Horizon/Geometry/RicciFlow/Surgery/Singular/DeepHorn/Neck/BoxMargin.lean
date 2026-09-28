import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.ScalarMargin
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientHomothety

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.DeepHorn

theorem box_scalar_evolution_eq
    (hM04 : RicciFlowCurvatureTheory.{u}) (F : GeneralizedRicciFlowData.{u})
    (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval)
    (z : (F.box b).carrier.carrier) :
    ((F.box b).flow.connection t).laplacian
        ((F.box b).flow.connection t).scalarCurvature z +
        2 * ((F.box b).flow.connection t).ricciNormSq z =
      (F.connection t).laplacian (F.connection t).scalarCurvature ((F.box b).forward t ht z) +
        2 * (F.connection t).ricciNormSq ((F.box b).forward t ht z) := by
  have hmetric (y : (F.box b).carrier.carrier) (_ : y ∈ Set.univ)
      (v w : TangentSpace (𝓡 3) y) := ((F.box b).metric_pullback t ht y v w).symm
  rw [scalar_laplacian_eq_of_local_isometry ((F.box b).flow.connection t) (F.connection t)
    isOpen_univ ((F.box b).forward_smooth t ht).contMDiffOn hmetric (mem_univ z),
    LeviCivitaData.ricciNormSq_eq_of_local_isometry ((F.box b).flow.connection t)
      (F.connection t) (hM04.tensor_calculus 3 _ (F.metric t) (F.connection t))
      isOpen_univ ((F.box b).forward_smooth t ht).contMDiffOn hmetric (mem_univ z)]

end PoincareConjecture.DeepHorn

namespace PoincareConjecture.GeneralizedStrongNeck

theorem exists_box_scalar_time_derivative_margin
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t ε : ℝ}
        (N : GeneralizedStrongNeck F t ε), ε ≤ ε₀ →
      ∀ (b : F.box_index) (ht : t ∈ (F.box b).interval)
        (z : (F.box b).carrier.carrier), (F.box b).forward t ht z = N.center →
        ∃ d : ℝ,
          HasDerivWithinAt (fun s => ((F.box b).flow.connection s).scalarCurvature z) d
            (F.box b).interval t ∧
          (1 / 2 : ℝ) * (F.connection t).scalarCurvature N.center ^ 2 ≤ d := by
  obtain ⟨ε₀, hε₀, hsmall, hmargin⟩ := EpsilonNeck.exists_scalar_evolution_margin.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro F t ε N hε b ht z hcenter
  have hhalf : ε < 1 / 2 := lt_of_le_of_lt (hε.trans hsmall) (by norm_num)
  have hbound := hmargin (N.spatialNeck hhalf) (F.connection t) hε
  refine ⟨_, hM04.scalar_evolution 3 _ _ (F.box b).flow t ht z, ?_⟩
  rw [DeepHorn.box_scalar_evolution_eq hM04 F b t ht z, hcenter]
  exact hbound

end PoincareConjecture.GeneralizedStrongNeck
