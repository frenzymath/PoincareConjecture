import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedEndpointCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Tactic










set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D1" =>
  Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞





theorem saddle_reference_critical_endpoint_germs
    (delta eta1 nu : ℝ)
    (b0 b1 : Fin 2 → ℝ → ℝ)
    (Theta : Fin 2 → D1)
    (E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere)
    (alphaLow : Fin 2 → ℝ → UnitTwoSphere)
    (phase : Fin 2 → ℝ → UnitCircle)
    (labelRef : Equiv.Perm (Fin 2))
    (Cphys : Fin 2 → UnitCircle → E2)
    (alphaRef : Fin 2 → ℝ → E2)
    (kappa : OpenPartialHomeomorph E2 E2)
    (port : Fin 4 → E2)
    (hEndpointStart : ∀ i : Fin 2, ∀ t : ℝ,
      t ∈ Ioo (-eta1) eta1 →
      (E (finProdFinEquiv (i, (0 : Fin 2)))).symm (alphaLow i t) =
          (-delta, b0 i t) ∧
      E (finProdFinEquiv (i, (0 : Fin 2))) (-delta, b0 i t) =
          alphaLow i t ∧
      b0 i t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8))
    (hEndpointFinish : ∀ i : Fin 2, ∀ t : ℝ,
      t ∈ Ioo (1 - eta1) (1 + eta1) →
      (E (finProdFinEquiv (i, (1 : Fin 2)))).symm (alphaLow i t) =
          (-delta, b1 i t) ∧
      E (finProdFinEquiv (i, (1 : Fin 2))) (-delta, b1 i t) =
          alphaLow i t ∧
      b1 i t ∈ Ioo (-(1 / 8) : ℝ) (1 / 8))
    (hThetaStartMap : ∀ i : Fin 2, ∀ t : ℝ,
      t ∈ Icc (-nu) nu → Theta i t ∈ Ioo (-eta1) eta1)
    (hThetaFinishMap : ∀ i : Fin 2, ∀ t : ℝ,
      t ∈ Icc (1 - nu) (1 + nu) →
        Theta i t ∈ Ioo (1 - eta1) (1 + eta1))
    (hThetaStart : ∀ i : Fin 2, ∀ t : ℝ,
      t ∈ Icc (-nu) nu → b0 i (Theta i t) = t)
    (hThetaFinish : ∀ i : Fin 2, ∀ t : ℝ,
      t ∈ Icc (1 - nu) (1 + nu) →
        1 - b1 i (Theta i t) = t)
    (hCriticalPort : ∀ i : Fin 2, ∀ k : Fin 2, ∀ s a : ℝ,
      a ∈ Ioo (-(1 / 8) : ℝ) (1 / 8) →
      alphaLow i s =
          E (finProdFinEquiv (i, k)) (-delta, a) →
      Cphys (labelRef i) (phase i s) =
        kappa ((1 + a) • port (finProdFinEquiv (i, k))))
    (hAlphaRef : ∀ i : Fin 2, ∀ t : ℝ,
      alphaRef i t = Cphys (labelRef i) (phase i (Theta i t))) :
    (∀ i : Fin 2, ∀ t : ℝ, t ∈ Icc (-nu) nu →
      alphaRef i t =
        kappa ((1 + t) • port (finProdFinEquiv (i, (0 : Fin 2))))) ∧
    (∀ i : Fin 2, ∀ t : ℝ, t ∈ Icc (1 - nu) (1 + nu) →
      alphaRef i t =
        kappa ((2 - t) • port (finProdFinEquiv (i, (1 : Fin 2))))) := by
  constructor
  · intro i t ht
    have hmap := hThetaStartMap i t ht
    have hcoord := hEndpointStart i (Theta i t) hmap
    have hport := hCriticalPort i 0 (Theta i t) (b0 i (Theta i t))
      hcoord.2.2 hcoord.2.1.symm
    rw [hAlphaRef i t, hport, hThetaStart i t ht]
  · intro i t ht
    have hmap := hThetaFinishMap i t ht
    have hcoord := hEndpointFinish i (Theta i t) hmap
    have hport := hCriticalPort i 1 (Theta i t) (b1 i (Theta i t))
      hcoord.2.2 hcoord.2.1.symm
    rw [hAlphaRef i t, hport]
    have hb := hThetaFinish i t ht
    have hr : 1 + b1 i (Theta i t) = 2 - t := by
      linarith only [hb]
    rw [hr]

end PoincareConjecture.M25.Topology3D
