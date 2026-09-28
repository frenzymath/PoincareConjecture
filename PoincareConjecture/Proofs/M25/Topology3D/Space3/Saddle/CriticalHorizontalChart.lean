import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldOpenChart











set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem collar_horizontal_mfderiv_injective_at_critical
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u q : UnitTwoSphere)
    (hq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0) :
    Injective (mfderiv (𝓡 2) 𝓘(ℝ, E2)
      (fun p : UnitTwoSphere => (heightPlaneCoordinates u (ψ (p, 0))).1) q) := by
  let j : UnitTwoSphere → E3 := fun p => ψ (p, 0)
  let L := heightPlaneCoordinates u
  let J : E2 →L[ℝ] E3 := mfderiv (𝓡 2) 𝓘(ℝ, E3) j q
  let P : E3 →L[ℝ] E2 := (ContinuousLinearMap.fst ℝ E2 ℝ).comp L.toContinuousLinearMap
  have hj := ((collar_central_contMDiff ψ hψ).mdifferentiable (by simp) q).hasMFDerivAt
  have hp := P.hasFDerivAt.hasMFDerivAt.comp q hj
  have hp' : (mfderiv (𝓡 2) 𝓘(ℝ, E2)
      (fun p : UnitTwoSphere => (heightPlaneCoordinates u (ψ (p, 0))).1) q :
      E2 →L[ℝ] E2) = P.comp J := hp.mfderiv
  have hh := (InnerProductSpace.toDual ℝ E3 (u : E3)).hasFDerivAt.hasMFDerivAt.comp q hj
  have hzero (v : E2) : ⟪(u : E3), J v⟫_ℝ = 0 :=
    congrArg (fun A => A v) (hh.mfderiv.symm.trans hq)
  intro v w hvw
  apply collar_central_mfderiv_injective ψ hψ q
  apply L.injective
  apply Prod.ext
  · change (P.comp J) v = (P.comp J) w
    rw [← hp']
    exact hvw
  · change (heightPlaneCoordinates u (J v)).2 = (heightPlaneCoordinates u (J w)).2
    rw [heightPlaneCoordinates_snd, heightPlaneCoordinates_snd]
    exact (hzero v).trans (hzero w).symm




theorem exists_collar_critical_horizontal_chart
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u q : UnitTwoSphere)
    (hq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0)
    {U : Set UnitTwoSphere} (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ e : OpenPartialHomeomorph UnitTwoSphere E2,
      q ∈ e.source ∧ e.source ⊆ U ∧
      EqOn e (fun p : UnitTwoSphere => (heightPlaneCoordinates u (ψ (p, 0))).1)
        e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e.symm e.target := by
  let g : UnitTwoSphere → E2 := fun p => (heightPlaneCoordinates u (ψ (p, 0))).1
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ g :=
    contDiff_fst.contMDiff.comp ((heightPlaneCoordinates u).contDiff.contMDiff.comp
      (collar_central_contMDiff ψ hψ))
  have hi : Injective (mfderiv (𝓡 2) 𝓘(ℝ, E2) g q) :=
    collar_horizontal_mfderiv_injective_at_critical ψ hψ u q hq
  let A : E2 →L[ℝ] E2 := mfderiv (𝓡 2) 𝓘(ℝ, E2) g q
  have hiA : Injective A := hi
  have hsA : Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hiA
  have hb : Bijective (mfderiv (𝓡 2) 𝓘(ℝ, E2) g q) := ⟨hiA, hsA⟩
  obtain ⟨e, hqe, heU, he, hei⟩ :=
    exists_manifold_source_local_inverse g hU hg.contMDiffOn q hqU hb
  exact ⟨e, hqe, heU, he, hg.contMDiffOn.congr he, hei⟩

end PoincareConjecture.M25.Topology3D
