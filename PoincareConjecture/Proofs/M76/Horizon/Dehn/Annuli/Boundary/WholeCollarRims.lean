import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Boundary.LateralCut



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem BoundaryCircleBlockData.exists_annulus_with_cut_rims
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {A L : SimplicialComplex ℝ E} [Fintype A.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 2)
    {n : ℕ} {p : Fin (n + 3) → E} (hpi : Function.Injective p)
    (hpv : range p = L.vertices)
    (hpf : ∀ s : Finset E, s ∈ L.faces ↔ s.Nonempty ∧
      ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)})
    (hlinks : ∀ v ∈ L.vertices, IsConnected (A.link v).space)
    (D : BoundaryCircleBlockData A L p) :
    ∃ c : squareAnnulus 1 (1 / 8) ≃ₜ (A.barycentricNeighborhood L).space,
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ x : squareAnnulus 1 (1 / 8), (c x : E) ∈ L.space ↔ depth 1 x = 0) ∧
      ∀ x : squareAnnulus 1 (1 / 8),
        (c x : E) ∈
          (A.barycentricSubdivision.closedFaceComplement (A.barycentricNeighborhood L)).space ↔
        depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8 := by
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
  have hcut : ∀ z ∈ signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3),
      sigma z ∈
        (A.barycentricSubdivision.closedFaceComplement (A.barycentricNeighborhood L)).space ↔
        z.1.2 = -1 ∨ z.1.2 = 1 := by
    let t : Fin (n + 4) → ℝ := fun i ↦ i.val
    have ht : StrictMono t := fun _ _ h ↦ Nat.cast_lt.mpr h
    intro z hz
    have hzt : z.2 ∈ Icc (t 0) (t (Fin.last (n + 3))) := by
      simpa only [t, Fin.val_zero, Fin.val_last, Nat.cast_zero, Nat.cast_add, Nat.cast_ofNat]
        using hz.2
    obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hzt
    have hi' : z.2 ∈ Icc (i.val : ℝ) (i.val + 1) := by
      simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hi
    rw [hvalues i ⟨z, hz.1, hi'⟩]
    exact D.map_mem_closed_complement_iff hpure hcofaces hLA hfull hLcard hpi hpv hpf hlinks i _
  refine ⟨c', hc', hc'.symm, hcore, ?_⟩
  intro x
  obtain ⟨s, hs, hx⟩ := exists_period_parameter_of_depth
    (show (0 : ℝ) < 1 / 8 by norm_num) (show 4 * (1 / 8 : ℝ) < 1 by norm_num) x
  have hu := mem_squareAnnulus_iff_depth.mp x.property
  let u : Icc (-(1 / 8 : ℝ)) (1 / 8) := ⟨depth 1 x, hu⟩
  have hxs : x = ⟨annulusMap 1 (by norm_num) ((s : AddCircle (4 * (1 : ℝ))), u),
      _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ :=
    Subtype.ext hx
  have hv : (c x : E) = sigma ((0, 8 * (u : ℝ)), ((n : ℝ) + 3) / 4 * s) := by
    rw [hxs]
    exact hperiod s (by simpa only [mul_one] using hs) u
  change (c x : E) ∈ _ ↔ _
  rw [hv]
  have hsource : ((0, 8 * (u : ℝ)), ((n : ℝ) + 3) / 4 * s) ∈
      signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3) := by
    refine ⟨(signedTubeSheet_zero_coordinates _).mpr ⟨rfl, ?_⟩, ?_⟩
    · constructor <;> linarith [u.property.1, u.property.2]
    · have hn : 0 < (n : ℝ) + 3 := by positivity
      have hs' : s ∈ Icc (0 : ℝ) 4 := by simpa only [mul_one] using hs
      constructor <;> nlinarith [hs'.1, hs'.2]
  rw [hcut _ hsource]
  change (8 * depth 1 x = -1 ∨ 8 * depth 1 x = 1) ↔ _
  constructor <;> rintro (h | h)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end PoincareConjecture.M76.Dehn
