import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.CyclicStripAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.CyclicStripBlocks

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem BoundaryCircleBlockData.exists_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {A L : SimplicialComplex ℝ E} [Fintype A.faces]
    (hLA : L ≤ A)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    {n : ℕ} {p : Fin (n + 3) → E} (hpi : Function.Injective p)
    (hpv : range p = L.vertices)
    (hpf : ∀ s : Finset E, s ∈ L.faces ↔ s.Nonempty ∧
      ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)})
    (D : BoundaryCircleBlockData A L p) :
    ∃ c : squareAnnulus 1 (1 / 8) ≃ₜ (A.barycentricNeighborhood L).space,
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ x : squareAnnulus 1 (1 / 8), (c x : E) ∈ L.space ↔ depth 1 x = 0) ∧
      ∃ sigma : P2 × ℝ → E,
        FinitePiecewiseAffineOn sigma (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)) ∧
        sigma '' (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)) =
          (A.barycentricNeighborhood L).space ∧
        ∀ (s : ℝ) (_hs : s ∈ Icc 0 4) (u : Icc (-(1 / 8 : ℝ)) (1 / 8)),
          (c ⟨annulusMap 1 (by norm_num) ((s : AddCircle (4 * (1 : ℝ))), u),
            _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) =
            sigma ((0, 8 * (u : ℝ)), ((n : ℝ) + 3) / 4 * s) := by
  classical
  let B := fun j ↦ (A.barycentricDualBlock {p j}).space
  let J := fun j ↦ (A.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space
  obtain ⟨hadj, hclose, _, _, hfar, _, _, hcover⟩ :=
    A.full_cyclic_dual_contacts_linear L hLA hfull p hpi hpv hpf
  have hnext (j : Fin (n + 2)) : finRotate (n + 3) j.castSucc = j.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · rfl
    · intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      omega
  have hadj' (j : Fin (n + 2)) : B j.castSucc ∩ B j.succ = J j.castSucc := by
    simpa only [B, J, hnext] using hadj j
  have hclose' : B 0 ∩ B (Fin.last (n + 2)) = J (Fin.last (n + 2)) := by
    simpa only [B, J, finRotate_last] using hclose
  obtain ⟨sigma, hsigma, himage, hvalues, hfib⟩ :=
    exists_cyclic_strip_map B J D.joint D.map D.mapPL D.lower D.upper hadj' hclose' hfar
  have haxis := cyclic_strip_axis_iff B D.map sigma hvalues L.space D.axis
  obtain ⟨c, hc, hci, hperiod, hcore⟩ :=
    exists_annulus_of_cyclic_strip sigma hsigma hfib L.space haxis
  have htarget : sigma '' (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)) =
      (A.barycentricNeighborhood L).space := himage.trans hcover
  let c' := c.trans (Homeomorph.setCongr htarget)
  have hc' : c'.IsFinitePL := by
    obtain ⟨f, hf, hval⟩ := hc
    exact ⟨f, hf, hval⟩
  exact ⟨c', hc', hc'.symm, hcore, sigma, hsigma, htarget, hperiod⟩

end PoincareConjecture.M76.Dehn
