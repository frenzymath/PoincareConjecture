import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Suspension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev P2 := Real × E2

theorem exists_supported_cylinder_parametrization
    {r : Real} (hr : 0 < r) (f : Real × S1 -> E2)
    (hf : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ f)
    (hemb : ∀ t ∈ Icc (-r) r,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun p : S1 => f (t, p))) :
    ∃ F : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
      (∀ z, (F z).1 = z.1) ∧
      (∃ K : Set P2, IsCompact K ∧ ∀ z ∉ K, F z = z) ∧
      ∀ t ∈ Icc (-r) r, ∀ p : S1, F (t, f (0, p)) = (t, f (t, p)) := by
  obtain ⟨Phi, _, hs, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_circle_isotopy (by linarith : -r ≤ r) f hf hemb
  let Psi (t : Real) := (Phi 0).symm.trans (Phi t)
  have hPsi : ContDiff Real ∞ (fun z : P2 => Psi z.1 z.2) :=
    hs.comp (contDiff_fst.prodMk ((Phi 0).symm.contMDiff.contDiff.comp contDiff_snd))
  have hPsi0 (x : E2) : Psi 0 x = x := (Phi 0).apply_symm_apply x
  have hPsifix (t : Real) (x : E2) (hx : x ∉ K) : Psi t x = x := by
    have hsymm : (Phi 0).symm x = x := by
      apply (Phi 0).injective
      change Phi 0 ((Phi 0).symm x) = Phi 0 x
      rw [(Phi 0).apply_symm_apply, hfix 0 x hx]
    change Phi t ((Phi 0).symm x) = x
    rw [hsymm, hfix t x hx]
  obtain ⟨F, hheight, hF, hsupport, hFfix⟩ :=
    exists_supported_family_suspension Psi hPsi hPsi0 hK hPsifix hr (lt_add_one r)
  refine ⟨F, hheight, ⟨closedBall (0 : Real) (r + 1) ×ˢ K, hsupport, hFfix⟩, ?_⟩
  intro t ht p
  have htb : t ∈ closedBall (0 : Real) r := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht
  rw [hF t htb]
  congr 1
  change Phi t ((Phi 0).symm (f (0, p))) = f (t, p)
  rw [← hmotion 0 (by constructor <;> linarith) p, (Phi 0).symm_apply_apply]
  exact hmotion t ht p

end Poincare.Manifold.Schoenflies
