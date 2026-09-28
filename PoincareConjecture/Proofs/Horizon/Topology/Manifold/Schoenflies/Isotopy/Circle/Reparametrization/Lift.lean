import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.Deriv.Slope



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

open PoincareConjecture



theorem contDiff_circle_lift {f : Real → S1}
    (hf : ContMDiff 𝓘(Real, Real) (𝓡 1) ∞ f)
    {L : Real → Real} (hL : Continuous L)
    (hlift : ∀ t, unitCircleExp (L t) = f t) : ContDiff Real ∞ L := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let H := isLocalDiffeomorph_unitCircleExp (L t)
  have hs : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (fun s => H.localInverse (f s)) t := by
    have h := H.localInverse_contMDiffAt
    rw [hlift t] at h
    exact h.comp t (hf t)
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hL.continuousAt
    (H.localInverse.open_target.mem_nhds H.localInverse_mem_target)] with s hs
  rw [← hlift s]
  exact (H.localInverse_left_inv hs).symm



theorem exists_real_diffeomorph_lift_circle
    (q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞) :
    ∃ L : Real ≃ₘ[Real] Real, ∀ t,
      unitCircleExp (L t) = q (unitCircleExp t) := by
  obtain ⟨b, hb⟩ := unitCircleExp_surjective (q (unitCircleExp 0))
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := isCoveringMap_unitCircleExp.existsUnique_continuousMap_lifts
    ⟨fun t => q (unitCircleExp t), q.continuous.comp contMDiff_unitCircleExp.continuous⟩
    0 b hb
  have hLt (t : Real) : unitCircleExp (L t) = q (unitCircleExp t) := congrFun hL t
  have hb' : unitCircleExp 0 = q.symm (unitCircleExp (L 0)) := by rw [hLt]; simp
  obtain ⟨K, ⟨hK0, hK⟩, _⟩ := isCoveringMap_unitCircleExp.existsUnique_continuousMap_lifts
    ⟨fun t => q.symm (unitCircleExp t),
      q.symm.continuous.comp contMDiff_unitCircleExp.continuous⟩ (L 0) 0 hb'
  have hKt (t : Real) : unitCircleExp (K t) = q.symm (unitCircleExp t) := congrFun hK t
  have hKL : (fun t => K (L t)) = id :=
    isCoveringMap_unitCircleExp.eq_of_comp_eq (K.continuous.comp L.continuous)
      continuous_id (by ext t; simp [hKt, hLt]) 0 hK0
  have hLK : (fun t => L (K t)) = id :=
    isCoveringMap_unitCircleExp.eq_of_comp_eq (L.continuous.comp K.continuous)
      continuous_id (by ext t; simp [hKt, hLt]) (L 0) (by simp [hK0])
  let D : Real ≃ₘ[Real] Real := {
    toFun := L
    invFun := K
    left_inv := congrFun hKL
    right_inv := congrFun hLK
    contMDiff_toFun := (contDiff_circle_lift
      (q.contMDiff.comp contMDiff_unitCircleExp) L.continuous hLt).contMDiff
    contMDiff_invFun := (contDiff_circle_lift
      (q.symm.contMDiff.comp contMDiff_unitCircleExp) K.continuous hKt).contMDiff }
  exact ⟨D, hLt⟩



theorem add_one_of_strictMono_circle_lift {L : Real → Real}
    (hL : Continuous L) (hm : StrictMono L)
    (hperiod : ∀ t, unitCircleExp (L (t + 1)) = unitCircleExp (L t))
    (hinj : ∀ s t, unitCircleExp (L s) = unitCircleExp (L t) →
      unitCircleExp s = unitCircleExp t) :
    ∀ t, L (t + 1) = L t + 1 := by
  intro t
  obtain ⟨n, hn⟩ := unitCircleExp_eq_iff.mp (hperiod t)
  have hnpos : (0 : Real) < n := by linarith [hm (show t < t + 1 by linarith)]
  have hn1 : (1 : Real) ≤ n := by
    exact_mod_cast (show (1 : Int) ≤ n by exact Int.add_one_le_iff.mpr (by exact_mod_cast hnpos))
  have hlow : L t + 1 ≤ L (t + 1) := by linarith
  apply le_antisymm _ hlow
  by_contra h
  have hhigh : L t + 1 < L (t + 1) := lt_of_not_ge h
  obtain ⟨u, hu, hLu⟩ := intermediate_value_Ioo
    (show t ≤ t + 1 by linarith) hL.continuousOn
    (show L t + 1 ∈ Ioo (L t) (L (t + 1)) from ⟨by linarith, hhigh⟩)
  have huexp : unitCircleExp u = unitCircleExp t := hinj u t (by
    rw [hLu, unitCircleExp_periodic])
  obtain ⟨k, hk⟩ := unitCircleExp_eq_iff.mp huexp
  have hk0 : (0 : Real) < k := by linarith [hu.1]
  have hk1 : (k : Real) < 1 := by linarith [hu.2]
  have : (0 : Int) < k := by exact_mod_cast hk0
  have : (k : Int) < 1 := by exact_mod_cast hk1
  omega


theorem deriv_real_diffeomorph_ne_zero (L : Real ≃ₘ[Real] Real) (t : Real) :
    deriv L t ≠ 0 := by
  have hd := ((L.symm.contDiff.differentiable (by simp)) (L t)).hasDerivAt.comp t
    ((L.contDiff.differentiable (by simp)) t).hasDerivAt
  have he : (fun s => L.symm (L s)) = (fun s : Real => s) := by ext s; simp
  change HasDerivAt (fun s => L.symm (L s)) _ t at hd
  rw [he] at hd
  have hv := hd.unique (hasDerivAt_id t)
  intro hz
  simp [hz] at hv

end Poincare.Manifold.Schoenflies
