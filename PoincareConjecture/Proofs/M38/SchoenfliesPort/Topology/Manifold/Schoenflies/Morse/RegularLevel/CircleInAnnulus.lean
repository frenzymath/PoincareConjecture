import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.Compact
import Mathlib.Analysis.Normed.Module.Connected







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)



theorem range_eq_annular_slice_of_immersed_circle
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b c : Real}
    (hFs : F.source = univ ×ˢ Ioo a b)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    {h : S2 -> Real} (hheight : ∀ q t, t ∈ Ioo a b -> h (F (q, t)) = t)
    (hc : c ∈ Ioo a b)
    (γ : S1 -> S2) (hγ : ContMDiff (𝓡 1) (𝓡 2) ∞ γ)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 1) (𝓡 2) γ q))
    (htarget : range γ ⊆ F.target) (hγheight : ∀ q, h (γ q) = c) :
    range γ = range (fun q : S1 => F (q, c)) := by
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E2) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  let k : S1 -> S1 := fun q => (F.symm (γ q)).1
  have hcoords : ContMDiff (𝓡 1) Iprod ∞ (fun q => F.symm (γ q)) := by
    intro q
    exact (hFi.contMDiffAt (F.open_target.mem_nhds (htarget (mem_range_self q)))).comp q (hγ q)
  have hk : ContMDiff (𝓡 1) (𝓡 1) ∞ k := contMDiff_fst.comp hcoords
  have hsecond (q : S1) : (F.symm (γ q)).2 = c := by
    have hs := F.map_target (htarget (mem_range_self q))
    rw [hFs] at hs
    have hh := hheight (F.symm (γ q)).1 (F.symm (γ q)).2 hs.2
    rw [F.right_inv (htarget (mem_range_self q)), hγheight] at hh
    exact hh.symm
  have hfactor (q : S1) : F (k q, c) = γ q := by
    rw [← hsecond q]
    exact F.right_inv (htarget (mem_range_self q))
  have hsource (q : S1) : (k q, c) ∈ F.source := by
    rw [hFs]
    exact ⟨mem_univ _, hc⟩
  have hkbij (q : S1) : Function.Bijective (mfderiv (𝓡 1) (𝓡 1) k q) := by
    have hkd := (hk q).mdifferentiableAt (by simp)
    have hconst : MDifferentiableAt (𝓡 1) 𝓘(Real, Real) (fun _ : S1 => c) q :=
      mdifferentiableAt_const
    have hkd' := hkd.prodMk hconst
    have hchain := mfderiv_comp q
      ((hF.contMDiffAt (F.open_source.mem_nhds (hsource q))).mdifferentiableAt (by simp)) hkd'
    have heq : (F ∘ fun p : S1 => (k p, c)) = γ := funext hfactor
    rw [heq, mfderiv_prodMk hkd hconst, mfderiv_const] at hchain
    have hki : Function.Injective (mfderiv (𝓡 1) (𝓡 1) k q) := by
      intro u w huw
      apply hinj q
      rw [hchain]
      change mfderiv Iprod (𝓡 2) F (k q, c) (mfderiv (𝓡 1) (𝓡 1) k q u, 0) =
        mfderiv Iprod (𝓡 2) F (k q, c) (mfderiv (𝓡 1) (𝓡 1) k q w, 0)
      rw [huw]
    exact ⟨hki, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E1) (V₂ := E1) rfl).mp hki⟩
  have hsurj := Poincare.Geometry.Manifold.surjective_of_compact_of_bijective_mfderiv hk hkbij
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨k q, hfactor q⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨u, hu⟩ := hsurj q
    exact ⟨u, (hfactor u).symm.trans (congrArg (fun z => F (z, c)) hu)⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
