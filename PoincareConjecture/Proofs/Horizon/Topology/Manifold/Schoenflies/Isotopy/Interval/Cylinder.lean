import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.Local
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Suspension







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev P2 := Real × E2



theorem exists_supported_interval_cylinder_within
    {r R l u : Real} (hr : 0 < r) (hrR : r < R)
    {U : Set E2} (hU : IsOpen U) (f : Real × Real → E2)
    {W : Set (Real × Real)} (hW : IsOpen W)
    (hrect : Icc (-r) r ×ˢ Icc l u ⊆ W)
    (hf : ContDiffOn Real ∞ f W)
    (hinj : ∀ t ∈ Icc (-r) r, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u,
      deriv (fun y => f (t, y)) s ≠ 0)
    (htrace : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, f (t, s) ∈ U) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ U ∧
      ∃ F : Diffeomorph 𝓘(Real, P2) 𝓘(Real, P2) P2 P2 ∞,
        (∀ z, (F z).1 = z.1) ∧
        (∀ x, F (0, x) = (0, x)) ∧
        (∀ z ∉ closedBall (0 : Real) R ×ˢ K, F z = z) ∧
        ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u,
          F (t, f (0, s)) = (t, f (t, s)) := by
  obtain ⟨K, hK, hKU, Phi, _, hs, hfix, hmotion⟩ :=
    exists_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
      hU f hW hrect hf hinj hder htrace
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
  obtain ⟨F, hheight, hF, _, hFfix⟩ :=
    exists_supported_family_suspension Psi hPsi hPsi0 hK hPsifix hr hrR
  refine ⟨K, hK, hKU, F, hheight, ?_, hFfix, ?_⟩
  · intro x
    rw [hF 0 (mem_closedBall_self hr.le), hPsi0]
  · intro t ht s hs
    have htb : t ∈ closedBall (0 : Real) r := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht
    rw [hF t htb]
    congr 1
    change Phi t ((Phi 0).symm (f (0, s))) = f (t, s)
    rw [← hmotion 0 (by constructor <;> linarith) s hs, (Phi 0).symm_apply_apply]
    exact hmotion t ht s hs

end Poincare.Manifold.Schoenflies
