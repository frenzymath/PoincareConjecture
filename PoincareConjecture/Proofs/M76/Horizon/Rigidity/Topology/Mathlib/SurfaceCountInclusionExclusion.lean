import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def surfaceFaceWeight (s : Finset E) : ℤ :=
  (if s.card = 1 then 1 else 0) - (if s.card = 2 then 1 else 0) +
    (if s.card = 3 then 1 else 0)

theorem surfaceEulerCount_eq_sum (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    K.surfaceEulerCount = ∑ s ∈ hK.toFinset, surfaceFaceWeight s := by
  classical
  have hcard (n : ℕ) : Nat.card (K.FaceOfCard n) =
      (hK.toFinset.filter (fun s => s.card = n)).card :=
    Nat.subtype_card _ (by intro s; simp)
  simp only [surfaceEulerCount, hcard, surfaceFaceWeight,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_boole]

variable {ι : Type*}

theorem faces_finset_inf' (C : ι → SimplicialComplex ℝ E)
    (S : Finset ι) (hne : S.Nonempty) :
    (S.inf' hne C).faces = ⋂ i ∈ S, (C i).faces := by
  ext s
  induction hne using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i S hi hS ih =>
    rw [Finset.inf'_cons hS]
    change (s ∈ (C i).faces ∧ s ∈ (S.inf' hS C).faces) ↔ _
    rw [ih]
    simp

theorem surfaceEulerCount_inclusion_exclusion
    (C : ι → SimplicialComplex ℝ E) (hC : ∀ i, (C i).faces.Finite)
    (S : Finset ι) (U : SimplicialComplex ℝ E)
    (hU : U.faces = ⋃ i ∈ S, (C i).faces) :
    U.surfaceEulerCount =
      ∑ T : S.powerset.filter (·.Nonempty), (-1 : ℤ) ^ (T.val.card + 1) *
        (T.val.inf' (Finset.mem_filter.mp T.property).2 C).surfaceEulerCount := by
  classical
  have hUf : U.faces.Finite := hU ▸ S.finite_toSet.biUnion (fun i _ => hC i)
  have hfinset : hUf.toFinset = S.biUnion (fun i => (hC i).toFinset) := by
    ext s
    simp [hU]
  rw [U.surfaceEulerCount_eq_sum hUf, hfinset, Finset.inclusion_exclusion_sum_biUnion]
  apply Finset.sum_congr rfl
  intro T _
  let hT := (Finset.mem_filter.mp T.property).2
  have hTf : (T.val.inf' hT C).faces.Finite := by
    obtain ⟨i, hi⟩ := hT
    exact (hC i).subset (Finset.inf'_le C hi)
  have hTint : hTf.toFinset = T.val.inf' hT (fun i => (hC i).toFinset) := by
    ext s
    simp only [Set.Finite.mem_toFinset, faces_finset_inf', mem_iInter]
    rw [Finset.mem_inf']
    simp
  rw [(T.val.inf' hT C).surfaceEulerCount_eq_sum hTf, hTint]
  rfl

end Geometry.SimplicialComplex
