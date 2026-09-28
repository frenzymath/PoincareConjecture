import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric

namespace EuclideanSpace

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "S" => {x : V // x ∈ sphere (0 : V) 1}

noncomputable def unitSphereBasisPoint (i : Fin 3) : S :=
  ⟨EuclideanSpace.single i 1, mem_sphere_zero_iff_norm.mpr (by simp)⟩

theorem exists_linearIsometryEquiv_of_gram_close {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ v : Fin 3 → S,
      (∀ i j, |inner ℝ (v i).1 (v j).1 - (if i = j then 1 else 0)| ≤ δ) →
      ∃ A : V ≃ₗᵢ[ℝ] V, ∀ i, ‖(v i).1 - A (EuclideanSpace.single i 1)‖ < η := by
  classical
  let X := Fin 3 → S
  let R : X → ℝ := fun v => ‖fun ij : Fin 3 × Fin 3 =>
    inner ℝ (v ij.1).1 (v ij.2).1 - (if ij.1 = ij.2 then 1 else 0)‖
  let G : Set X := {v | ∃ A : V ≃ₗᵢ[ℝ] V,
    ∀ i, ‖(v i).1 - A (EuclideanSpace.single i 1)‖ < η}
  have hR : Continuous R := by
    apply Continuous.norm
    apply continuous_pi
    intro ij
    exact (((continuous_apply ij.1).subtype_val).inner
      ((continuous_apply ij.2).subtype_val)).sub continuous_const
  have hG : IsOpen G := by
    have heq : G = ⋃ A : V ≃ₗᵢ[ℝ] V,
        ⋂ i : Fin 3, {v : X | ‖(v i).1 - A (EuclideanSpace.single i 1)‖ < η} := by
      ext v
      simp only [G, mem_ofPred_eq, mem_iUnion, mem_iInter]
    rw [heq]
    apply isOpen_iUnion
    intro A
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (((continuous_apply i).subtype_val).sub continuous_const).norm
      continuous_const
  have hzero (v : X) (hv : R v = 0) : v ∈ G := by
    have heq : (fun ij : Fin 3 × Fin 3 =>
        inner ℝ (v ij.1).1 (v ij.2).1 - (if ij.1 = ij.2 then 1 else 0)) = 0 :=
      norm_eq_zero.mp hv
    have horth : Orthonormal ℝ (fun i : Fin 3 => (v i).1) := by
      apply orthonormal_iff_ite.mpr
      intro i j
      exact sub_eq_zero.mp (congrFun heq (i, j))
    have horth' : Orthonormal ℝ ((univ : Set (Fin 3)).domRestrict
        (fun i => (v i).1)) :=
      horth.comp (fun i : (univ : Set (Fin 3)) => i.1) Subtype.val_injective
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := V) (ι := Fin 3) (v := fun i => (v i).1) (s := univ)
      (by simp) horth'
    refine ⟨b.repr.symm, ?_⟩
    intro i
    rw [b.repr_symm_single, hb i (mem_univ i), sub_self, norm_zero]
    exact hη
  have hpositive : ∀ v ∈ Gᶜ, 0 < R v := by
    intro v hv
    by_contra h
    have hz : R v = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    exact hv (hzero v hz)
  obtain ⟨c, hc, hbound⟩ := hG.isClosed_compl.isCompact.exists_forall_le'
    hR.continuousOn hpositive
  let δ := min 1 (c / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro v hv
  change v ∈ G
  by_contra hnot
  have hle : R v ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
    intro ij
    simpa only [Real.norm_eq_abs] using hv ij.1 ij.2
  have hsmall : δ < c := (min_le_right _ _).trans_lt (by linarith)
  exact (not_lt_of_ge (hbound v hnot)) (hle.trans_lt hsmall)

theorem sphere_norm_sub_le_of_frame
    (f : S → S) (A : V ≃ₗᵢ[ℝ] V) {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hpair : ∀ p q, |inner ℝ (f p).1 (f q).1 - inner ℝ p.1 q.1| ≤ ρ)
    (hframe : ∀ i, ‖(f (unitSphereBasisPoint i)).1 - A (EuclideanSpace.single i 1)‖ ≤ β)
    (q : S) : ‖(f q).1 - A q.1‖ ≤ 3 * (ρ + β) := by
  let z := A.symm (f q).1 - q.1
  have hcoord (i : Fin 3) : |z i| ≤ ρ + β := by
    let e : V := EuclideanSpace.single i 1
    have hinner : inner ℝ (A.symm (f q).1) e = inner ℝ (f q).1 (A e) := by
      simpa only [A.apply_symm_apply] using (A.inner_map_map (A.symm (f q).1) e).symm
    have heq : z i = inner ℝ (f q).1 (A e) - inner ℝ q.1 e := by
      dsimp only [z]
      have hleft : inner ℝ (A.symm (f q).1) e = (A.symm (f q).1) i := by
        simp [e, EuclideanSpace.inner_single_right]
      have hright : inner ℝ q.1 e = q.1 i := by
        simp [e, EuclideanSpace.inner_single_right]
      rw [← hinner, hleft, hright]
      rfl
    have hnorm : ‖(f q).1‖ = 1 := mem_sphere_zero_iff_norm.mp (f q).2
    have herror : |inner ℝ (f q).1 (A e - (f (unitSphereBasisPoint i)).1)| ≤ β := by
      calc
        _ ≤ ‖(f q).1‖ * ‖A e - (f (unitSphereBasisPoint i)).1‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖(f (unitSphereBasisPoint i)).1 - A e‖ := by
          rw [hnorm, one_mul, norm_sub_rev]
        _ ≤ β := hframe i
    rw [heq]
    calc
      |inner ℝ (f q).1 (A e) - inner ℝ q.1 e| =
          |inner ℝ (f q).1 (A e - (f (unitSphereBasisPoint i)).1) +
            (inner ℝ (f q).1 (f (unitSphereBasisPoint i)).1 - inner ℝ q.1 e)| := by
        rw [inner_sub_right]
        congr 1
        ring
      _ ≤ |inner ℝ (f q).1 (A e - (f (unitSphereBasisPoint i)).1)| +
          |inner ℝ (f q).1 (f (unitSphereBasisPoint i)).1 - inner ℝ q.1 e| :=
        abs_add_le _ _
      _ ≤ β + ρ := add_le_add herror (hpair q (unitSphereBasisPoint i))
      _ = ρ + β := add_comm _ _
  have hsum : ‖z‖ ^ 2 ≤ 3 * (ρ + β) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, (z i) ^ 2 ≤ ∑ _i : Fin 3, (ρ + β) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (z i)) (add_nonneg hρ hβ)).mpr (hcoord i)
      _ = 3 * (ρ + β) ^ 2 := by simp
  have hz : ‖z‖ ≤ 3 * (ρ + β) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖z‖ ^ 2 ≤ 3 * (ρ + β) ^ 2 := hsum
      _ ≤ (3 * (ρ + β)) ^ 2 := by nlinarith [sq_nonneg (ρ + β)]
  have heq : A z = (f q).1 - A q.1 := by simp only [z, map_sub, A.apply_symm_apply]
  rw [← heq, A.norm_map]
  exact hz

theorem exists_linearIsometryEquiv_of_sphere_inner_close {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ f : S → S,
      (∀ p q, |inner ℝ (f p).1 (f q).1 - inner ℝ p.1 q.1| ≤ δ) →
      ∃ A : V ≃ₗᵢ[ℝ] V, ∀ q, ‖(f q).1 - A q.1‖ < ζ := by
  obtain ⟨ε, hε, hcap, hframe⟩ :=
    exists_linearIsometryEquiv_of_gram_close (η := ζ / 8) (by positivity)
  let δ := min ε (ζ / 8)
  have hδ : 0 < δ := lt_min hε (by positivity)
  refine ⟨δ, hδ, (min_le_left _ _).trans hcap, ?_⟩
  intro f hf
  have hgram (i j : Fin 3) :
      |inner ℝ (f (unitSphereBasisPoint i)).1 (f (unitSphereBasisPoint j)).1 -
        (if i = j then 1 else 0)| ≤ ε := by
    have h := hf (unitSphereBasisPoint i) (unitSphereBasisPoint j)
    have heq : inner ℝ (unitSphereBasisPoint i).1 (unitSphereBasisPoint j).1 =
        (if i = j then 1 else 0) :=
      orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j
    rw [heq] at h
    exact h.trans (min_le_left _ _)
  obtain ⟨A, hA⟩ := hframe (fun i => f (unitSphereBasisPoint i)) hgram
  refine ⟨A, ?_⟩
  intro q
  have h := sphere_norm_sub_le_of_frame f A hδ.le (by positivity : 0 ≤ ζ / 8)
    hf (fun i => (hA i).le) q
  have hsmall : δ ≤ ζ / 8 := min_le_right _ _
  exact h.trans_lt (by linarith)

end EuclideanSpace
