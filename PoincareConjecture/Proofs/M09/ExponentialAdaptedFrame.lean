import PoincareConjecture.Proofs.M09.AdaptedOrthonormalFrame
import PoincareConjecture.Proofs.M09.FamilyEndpointEquation
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_exists_adapted_frame
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ∃ (D : Set ℝ) (P : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s)),
      IsOpen D ∧ IsPreconnected D ∧ Set.Icc 0 (Real.sqrt b) ⊆ D ∧
        D ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ∧
        ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) D ∧
        (∀ i, IsAdaptedFieldOn F T (A.squareFamily Z) (P i) D) ∧
        ∀ s ∈ D, ∀ i j, (F.metric (T - s ^ 2)).inner (A.squareFamily Z s)
          (P i s) (P j s) = if i = j then 1 else 0 := by
  let W := ((fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain) ∩
    Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hW : IsOpen W := (A.square_open.preimage
    (continuous_const.prodMk continuous_id)).inter isOpen_Ioo
  have hKW : Set.Icc 0 (Real.sqrt b) ⊆ W := by
    intro s hs
    have hsmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact ⟨A.square_contains ⟨Set.mem_univ _, hs.1, hsmax⟩,
      (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1, hsmax⟩
  let U := connectedComponentIn W 0
  have hU : IsOpen U := hW.connectedComponentIn
  have hconn : IsPreconnected U := isPreconnected_connectedComponentIn
  have hKU : Set.Icc 0 (Real.sqrt b) ⊆ U :=
    isPreconnected_Icc.subset_connectedComponentIn ⟨le_rfl, Real.sqrt_nonneg b⟩ hKW
  have hUW : U ⊆ W := connectedComponentIn_subset W 0
  have htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    fun _ hs ↦ (hUW hs).2
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U :=
    (lExponentialFamily_squareSlice_contMDiffOn A Z).mono (fun _ hs ↦ (hUW hs).1)
  obtain ⟨e, he⟩ := exists_initial_orthonormal_vectors (F.metric (T - (0 : ℝ) ^ 2))
    (A.squareFamily Z 0)
  obtain ⟨D, P, hD, hconnD, hKD, hDU, _, hP, hpair⟩ :=
    exists_adapted_orthonormal_frame F T τmax hτmax hwindow (A.squareFamily Z) U hU
      hconn htime hα 0 (Real.sqrt b) 0 hKU ⟨le_rfl, Real.sqrt_nonneg b⟩ e he
  exact ⟨D, P, hD, hconnD, hKD, hDU.trans htime, hα.mono hDU, hP, hpair⟩

end PoincareConjecture.Proofs.M09
