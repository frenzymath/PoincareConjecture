import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.SourceAnnuli.OriginalIdentity

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem nonempty_local_identity_annuli_of_cyclic_map
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {R : Set X}
    {S : Set P2} {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hmate : old.mate i ≠ i) (hcore : D.core ⊆ interior R)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (K : Fin (n + 2) → SimplicialComplex ℝ (D.sample → ℝ × V3))
    (hK : ∀ k, (K k).faces.Finite) (hKK : ∀ k, (K k).space ⊆ D.complex.space)
    (x y : Fin (n + 2) → P2) (C : ∀ k, RawSourceCrossing e f S R (x k) (y k))
    (hLC : ∀ k, MapsTo (fun z ↦ (D.inverse z : X)) (K k).space (C k).chart.source)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (hsigma : ∀ k : Fin (n + 2), FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)))
    (himage : ∀ k, MapsTo sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) (K k).space)
    (label : Fin (n + 2) → Equiv.Perm (Fin 2))
    (hcoords : ∀ k j z, z ∈ signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ) →
      ((C k).chart (D.inverse (sigma z)) (label k j).castSucc = 0 ↔
        z.1 ∈ signedTubeSheet j))
    (closing : SignedAxisPermutation)
    (hfib : ∀ z w : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))),
      sigma z = sigma w ↔ z = w ∨
        ((z : P2 × ℝ).2 = t 0 ∧ (w : P2 × ℝ).2 = t (Fin.last (n + 2)) ∧
          closing.linear (z : P2 × ℝ).1 = (w : P2 × ℝ).1) ∨
        ((w : P2 × ℝ).2 = t 0 ∧ (z : P2 × ℝ).2 = t (Fin.last (n + 2)) ∧
          closing.linear (w : P2 × ℝ).1 = (z : P2 × ℝ).1))
    (haxis : ∀ z ∈ signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
      sigma z ∈ D.axis.space ↔ z.1 = (0, 0))
    (haxisimage : (fun s => sigma ((0, 0), s)) '' Icc (t 0) (t (Fin.last (n + 2))) = D.axis.space)

    (hsourceCore : ∀ x ∈ S, f x ∈ D.core → x ∈ interior S)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ T : ComponentIdentityAnnuliData (e := e) (R := R) old i L d,
      T.tube '' identityTube L d ⊆ D.core := by
  obtain ⟨hclosing, labels, phi, hPL, hvalue, hwhole, hselected, hcover, hphifib, htrace⟩ :=
    D.exists_paired_source_strips hmate hcore t ht K hK hKK x y C hLC sigma hsigma himage
      label hcoords closing hfib haxis haxisimage
  have hab : t 0 < t (Fin.last (n + 2)) := ht (by change 0 < n + 2; omega)
  have hL : 0 < L := by linarith
  let physical : P2 × ℝ → X := fun z ↦ (D.inverse (sigma z) : X)
  let tau := physical ∘ periodicTubeCoordinates L d (t 0) (t (Fin.last (n + 2)))
  obtain ⟨c, hc, hdis, hperiod, hmiddle, hmiddleImage⟩ :=
    exists_identity_source_annuli_of_cut_strips f (fun z ↦ (D.inverse z : X)) sigma hab hd hwidth
      phi hPL (fun j z hz ↦ (hvalue j z hz).2.1) hphifib
      (fun j ↦ if labels j = 0 then old.pieces i else old.pieces (old.mate i)) hselected hcover
  have hmaps : MapsTo sigma (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))))
      D.complex.space := by
    intro z hz
    obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
    exact hKK k (himage k ⟨hz.1, hk⟩)
  have hsource : (⋃ k : Fin (n + 2), signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) =
      signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact ⟨hk.1, (ht.monotone (Fin.zero_le _)).trans hk.2.1,
        hk.2.2.trans (ht.monotone (Fin.le_last _))⟩
    · intro hz
      obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
      exact mem_iUnion.mpr ⟨k, hz.1, hk⟩
  have hsigmaPL : FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) :=
    hsource ▸ FinitePiecewiseAffineOn.iUnion hsigma
  have hphysical : PolyhedralPLInCharts e physical
      (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) := by
    obtain ⟨J, hJ, hJs, hface⟩ := hsigmaPL
    have h := D.inverse_PL.comp_finitePiecewiseAffineOn J hJ ⟨J, hJ, rfl, hface⟩
      (fun z hz => hmaps (hJs.subset hz))
    rwa [hJs] at h

  have hphysicalFib : ∀ z ∈ signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
      ∀ w ∈ signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
      physical z = physical w ↔ z.1 = w.1 ∧
        (z.2 = w.2 ∨ (z.2 = t 0 ∧ w.2 = t (Fin.last (n + 2))) ∨
          (z.2 = t (Fin.last (n + 2)) ∧ w.2 = t 0)) := by
    intro z hz w hw
    have heq : physical z = physical w ↔ sigma z = sigma w := by
      constructor
      · intro h
        exact (D.graph_inverse _ (hmaps hz)).symm.trans
          ((congrArg D.graph h).trans (D.graph_inverse _ (hmaps hw)))
      · exact congrArg (fun q ↦ (D.inverse q : X))
    rw [heq]
    have h := hfib ⟨z, hz⟩ ⟨w, hw⟩
    simp only [Subtype.mk.injEq, hclosing, SignedAxisPermutation.linear_apply,
      SignedAxisPermutation.refl, if_true, one_mul, Prod.mk.eta] at h
    rw [h]
    constructor
    · rintro (h | ⟨hz0, hwb, hzw⟩ | ⟨hw0, hzb, hwz⟩)
      · exact ⟨congrArg Prod.fst h, Or.inl (congrArg Prod.snd h)⟩
      · exact ⟨hzw, Or.inr (Or.inl ⟨hz0, hwb⟩)⟩
      · exact ⟨hwz.symm, Or.inr (Or.inr ⟨hzb, hw0⟩)⟩
    · rintro ⟨hzw, ht | ht | ht⟩
      · exact Or.inl (Prod.ext hzw ht)
      · exact Or.inr (Or.inl ⟨ht.1, ht.2, hzw⟩)
      · exact Or.inr (Or.inr ⟨ht.2, ht.1, hzw.symm⟩)
  refine ⟨{
    depth_pos := hd, width_small := hwidth, label := labels, tube := tau,
    source := fun j ↦ phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2)))),
    chart := c, tube_PL := ?_,
    tube_fibers := normalized_identity_tube_fibers hL hd hab physical hphysicalFib,
    tube_interior := ?_, source_interior := ?_, disjoint := hdis,
    chart_PL := fun j ↦ (hc j).1, chart_inverse_PL := fun j ↦ (hc j).2,
    period_value := hperiod, full_preimage := ?_, double_trace := htrace,
    middle := hmiddle, middle_image := hmiddleImage },?_⟩
  · obtain ⟨J, hJ, hJs, hface⟩ :=
      periodicTubeCoordinates_finitePL hL hd (t 0) (t (Fin.last (n + 2)))
    have h := hphysical.comp_finitePiecewiseAffineOn J hJ ⟨J, hJ, rfl, hface⟩
      (fun z hz ↦ periodicTubeCoordinates_mapsTo hL hd hab (hJs.subset hz))
    rwa [hJs] at h
  · rintro q ⟨z, _hz, rfl⟩
    exact hcore (D.inverse _).property
  · intro j w hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hv := hvalue j z hz
    exact hsourceCore _ hv.1 (hv.2.1.symm ▸ (D.inverse _).property)
  · change S ∩ f ⁻¹' ((physical ∘ periodicTubeCoordinates L d (t 0)
      (t (Fin.last (n + 2)))) '' identityTube L d) = _
    rw [image_comp, periodicTubeCoordinates_image hL hd hab]
    exact hwhole
  · rintro z ⟨w,hw,rfl⟩
    exact (D.inverse _).property

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
