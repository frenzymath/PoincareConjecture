import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallStraightening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.LinearPath



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies



theorem exists_supported_ball_normalization {n : Nat}
    (A : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    {r : Real} (hr : 0 < r) :
    ∃ Q : EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n),
      ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, F x = x) ∧
        ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin n)) r, F (A x) = Q x := by
  let E := EuclideanSpace Real (Fin n)
  let T : Diffeomorph (𝓡 n) (𝓡 n) E E ∞ := {
    toEquiv := Equiv.addRight (A 0)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  obtain ⟨L, _, K, hK, _, Phi, _, _, hfix, hPhi⟩ :=
    exists_supported_ball_straightening A.toHomeomorph.toOpenPartialHomeomorph
      T.toHomeomorph.toOpenPartialHomeomorph A.contMDiff.contMDiffOn
      A.symm.contMDiff.contMDiffOn T.contMDiff.contMDiffOn T.symm.contMDiff.contMDiffOn
      hr (subset_univ _) (mem_univ _) (by change A 0 = 0 + A 0; simp)
  have hPhi' (x : E) (hx : x ∈ closedBall 0 r) : Phi 1 (A x) = L x + A 0 :=
    hPhi x hx
  obtain ⟨Q, hQ⟩ := Poincare.Manifold.SphereIsotopy.exists_orthogonal_linear_interpolation L
  let B (t : Real) : E →L[Real] E :=
    (1-t) • L.toContinuousLinearMap + t • Q.toContinuousLinearEquiv.toContinuousLinearMap
  let G : Real × E → E := fun z => (1-z.1) • A 0 + B z.1 z.2
  have hG : ContDiff Real ∞ G := by
    change ContDiff Real ∞ (fun z : Real × E =>
      (1-z.1) • A 0 + ((1-z.1) • L z.2 + z.1 • Q z.2))
    fun_prop
  have hGi (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      InjOn (fun x => G (t,x)) (closedBall (0 : E) r) := by
    intro x _ y _ hxy
    exact (hQ t ht).1 (add_left_cancel hxy)
  have hGd (t : Real) (ht : t ∈ Icc (0 : Real) 1)
      (x : E) (_hx : x ∈ closedBall (0 : E) r) :
      Function.Bijective (fderiv Real (fun y => G (t,y)) x) := by
    have hd : HasFDerivAt (fun y => G (t,y)) (B t) x :=
      (B t).hasFDerivAt.const_add ((1-t) • A 0)
    rw [hd.fderiv]
    exact hQ t ht
  obtain ⟨Psi, _, _, ⟨C, hC, hCfix⟩, hPsi⟩ :=
    exists_ambient_isotopy_of_codimZero_isotopy (isCompact_closedBall (0 : E) r) G hG hGi hGd
  let F := (Phi 1).trans (Psi 1)
  refine ⟨Q, K ∪ C, hK.union hC, F, ?_, ?_⟩
  · intro x hx
    change Psi 1 (Phi 1 x) = x
    rw [hfix 1 x (fun h => hx (Or.inl h)), hCfix 1 x (fun h => hx (Or.inr h))]
  · intro x hx
    change Psi 1 (Phi 1 (A x)) = Q x
    rw [hPhi' x hx]
    have h := hPsi 1 (show (1 : Real) ∈ Icc 0 1 by simp) x hx
    convert! h using 1 <;> simp [G, B, add_comm] <;> rfl



theorem exists_supported_matching_of_ball_embeddings {n : Nat}
    (A B : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    {r : Real} (hr : 0 < r) :
    ∃ Q : EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n),
      ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, F x = x) ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin n)) r, F (A x) = B (Q x)) ∧
        F '' (A '' closedBall 0 r) = B '' closedBall 0 r := by
  obtain ⟨QA, KA, hKA, FA, hFAfix, hFA⟩ := exists_supported_ball_normalization A hr
  obtain ⟨QB, KB, hKB, FB, hFBfix, hFB⟩ := exists_supported_ball_normalization B hr
  let Q := QA.trans QB.symm
  let F := FA.trans FB.symm
  have hQmem (x : EuclideanSpace Real (Fin n)) :
      Q x ∈ closedBall 0 r ↔ x ∈ closedBall 0 r := by
    simp only [mem_closedBall_zero_iff, Q.norm_map]
  have hF (x : EuclideanSpace Real (Fin n)) (hx : x ∈ closedBall 0 r) :
      F (A x) = B (Q x) := by
    change FB.symm (FA (A x)) = _
    rw [hFA x hx]
    apply FB.injective
    change FB (FB.symm (QA x)) = FB (B (Q x))
    rw [FB.apply_symm_apply, hFB (Q x) ((hQmem x).mpr hx)]
    exact (QB.apply_symm_apply (QA x)).symm
  refine ⟨Q, KA ∪ KB, hKA.union hKB, F, ?_, hF, ?_⟩
  · intro x hx
    change FB.symm (FA x) = x
    rw [hFAfix x (fun h => hx (Or.inl h))]
    apply FB.injective
    change FB (FB.symm x) = FB x
    rw [FB.apply_symm_apply, hFBfix x (fun h => hx (Or.inr h))]
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Q x, (hQmem x).mpr hx, (hF x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hi : Q.symm x ∈ closedBall 0 r := by
        simpa only [mem_closedBall_zero_iff, Q.symm.norm_map] using hx
      refine ⟨A (Q.symm x), ⟨Q.symm x, hi, rfl⟩, ?_⟩
      rw [hF _ hi, Q.apply_symm_apply]

end Poincare.Manifold.Schoenflies
