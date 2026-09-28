import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M04.RicciNullReaction
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.OperatorRicci
import Mathlib.Analysis.Calculus.Deriv.Slope










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u



theorem HasDerivWithinAt.nonpos_of_right_endpoint_min
    {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (hf : HasDerivWithinAt f d (Icc a b) b)
    (hmin : ∀ t ∈ Icc a b, f b ≤ f t) : d ≤ 0 := by
  have hset : Icc a b \ {b} = Ico a b := by
    ext t
    simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ico]
    constructor
    · rintro ⟨⟨hat, htb⟩, hne⟩
      exact ⟨hat, lt_of_le_of_ne htb hne⟩
    · rintro ⟨hat, htb⟩
      exact ⟨⟨hat, htb.le⟩, htb.ne⟩
  have htend := hasDerivWithinAt_iff_tendsto_slope.mp hf
  rw [hset] at htend
  have : (𝓝[Ico a b] b).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hab]
    infer_instance
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmin t ⟨ht.1, ht.2.le⟩))
    (sub_nonpos.mpr ht.2.le)

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]





theorem terminal_null_ricci_laplacian_nonpos
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hRic : ∀ t ∈ Icc a b, (F.connection t).NonnegativeRicciCurvature)
    (x : M) (v : TangentSpace (𝓡 3) x)
    (hnull : (F.connection b).ricci x v v = 0) :
    (F.connection b).tensorLaplacian (F.connection b).ricciEvaluation x ![v, v] ≤ 0 := by
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hd := P.ricci_evolution 3 M (Icc a b) F b hb x v v
  have hderiv := hd.nonpos_of_right_endpoint_min hab (fun t ht => by
    rw [hnull]
    exact hRic t ht x v)
  have hreaction := M04.ricciReaction_nonneg_of_nonnegativeRicciAt_null
    (F.connection b) x (hRic b hb x) v hnull
  linarith




theorem no_positive_terminal_null_ricci_laplacian
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hRic : ∀ t ∈ Icc a b, (F.connection t).NonnegativeRicciCurvature)
    (x : M) (v : TangentSpace (𝓡 3) x)
    (hnull : (F.connection b).ricci x v v = 0)
    (hpositive : 0 < (F.connection b).tensorLaplacian
      (F.connection b).ricciEvaluation x ![v, v]) : False :=
  (not_lt_of_ge (terminal_null_ricci_laplacian_nonpos P hab F hRic x v hnull)) hpositive



theorem no_positive_terminal_null_ricci_laplacian_of_operator
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v : TangentSpace (𝓡 3) x)
    (hnull : (F.connection b).ricci x v v = 0)
    (hpositive : 0 < (F.connection b).tensorLaplacian
      (F.connection b).ricciEvaluation x ![v, v]) : False := by
  apply no_positive_terminal_null_ricci_laplacian P hab F
    (fun t ht => LeviCivitaData.nonnegativeRicci_of_nonnegativeOperator
      (F.connection t) (hoperator t ht)) x v hnull hpositive

end PoincareConjecture.M28
