import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport.Chart



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private theorem exists_ball_coordinates {n : Nat}
    (e : OpenPartialHomeomorph (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (A : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    {r : Real} (hr : 0 < r) (hA : A '' closedBall 0 r ⊆ e.target) :
    ∃ B : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
      ∀ x ∈ closedBall 0 r, B x = e.symm (A x) := by
  let d := A.toHomeomorph.toOpenPartialHomeomorph.trans e.symm
  have hd : ContMDiffOn (𝓡 n) (𝓡 n) ∞ d d.source :=
    hei.comp A.contMDiff.contMDiffOn (fun _ hx => hx.2)
  have hdi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ d.symm d.target :=
    A.symm.contMDiff.comp_contMDiffOn (he.mono inter_subset_left)
  let P : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞ := {
    d.toPartialEquiv with
    open_source := d.open_source
    open_target := d.open_target
    contMDiffOn_toFun := hd
    contMDiffOn_invFun := hdi }
  have hloc (x : EuclideanSpace Real (Fin n)) (hx : x ∈ closedBall 0 r) :
      IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (fun y => e.symm (A y)) x :=
    ⟨P, ⟨mem_univ _, hA ⟨x, hx, rfl⟩⟩, fun _ _ => rfl⟩
  exact exists_global_extension_of_local_ball_embedding hr (fun x => e.symm (A x))
    (fun x hx y hy hxy => A.injective
      (e.symm.injOn (hA ⟨x, hx, rfl⟩) (hA ⟨y, hy, rfl⟩) hxy)) hloc



theorem exists_supported_matching_of_balls_in_chart {n : Nat}
    (e : OpenPartialHomeomorph (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)))
    (hes : e.source = univ)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (A B : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    {r : Real} (hr : 0 < r)
    (hA : A '' closedBall 0 r ⊆ e.target) (hB : B '' closedBall 0 r ⊆ e.target) :
    ∃ Q : EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n),
      ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧ K ⊆ e.target ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, D x = x) ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin n)) r, D (A x) = B (Q x)) ∧
        D '' (A '' closedBall 0 r) = B '' closedBall 0 r := by
  obtain ⟨a, ha⟩ := exists_ball_coordinates e he hei A hr hA
  obtain ⟨b, hb⟩ := exists_ball_coordinates e he hei B hr hB
  obtain ⟨Q, K, hK, F, hfix, hF, _⟩ := exists_supported_matching_of_ball_embeddings a b hr
  obtain ⟨hK', hKU, D, hDfix, hD⟩ :=
    Diffeomorph.exists_chart_extension_of_isCompact e hes he hei F hK hfix
  have hQmem (x : EuclideanSpace Real (Fin n)) :
      Q x ∈ closedBall 0 r ↔ x ∈ closedBall 0 r := by
    simp only [mem_closedBall_zero_iff, Q.norm_map]
  have hmotion (x : EuclideanSpace Real (Fin n)) (hx : x ∈ closedBall 0 r) :
      D (A x) = B (Q x) := by
    have h := hF x hx
    rw [ha x hx, hb (Q x) ((hQmem x).mpr hx)] at h
    calc
      D (A x) = D (e (e.symm (A x))) := by rw [e.right_inv (hA ⟨x, hx, rfl⟩)]
      _ = e (F (e.symm (A x))) := hD _
      _ = e (e.symm (B (Q x))) := congrArg e h
      _ = B (Q x) := e.right_inv (hB ⟨Q x, (hQmem x).mpr hx, rfl⟩)
  refine ⟨Q, e '' K, hK', hKU, D, hDfix, hmotion, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Q x, (hQmem x).mpr hx, (hmotion x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hi : Q.symm x ∈ closedBall 0 r := by
      simpa only [mem_closedBall_zero_iff, Q.symm.norm_map] using hx
    refine ⟨A (Q.symm x), ⟨Q.symm x, hi, rfl⟩, ?_⟩
    rw [hmotion _ hi, Q.apply_symm_apply]

end Poincare.Manifold.Schoenflies
